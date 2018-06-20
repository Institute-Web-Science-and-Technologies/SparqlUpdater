package de.unikoblenz.west.evowipe;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.io.IOException;
import java.lang.IllegalStateException;
import java.util.logging.FileHandler;
import java.util.logging.Formatter;
import java.util.logging.SimpleFormatter;
import java.util.logging.Logger;
import java.util.logging.Level;

import org.apache.commons.cli.*; // For parsing command line arguments
import org.apache.commons.io.FilenameUtils;

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.Future;

import java.util.List;
import java.util.Arrays;

/**
 * @brief Perform SparQL updates in the presence of OWL-DL TBoxes.
 */
public class SparqlUpdater {
    public static int verbose_level = 1;
    public static int timeout_seconds = 60; // this value doesn't matter, since there's either no timeout at all or the number is provided by users; for benchmark mode, 60 is used as default
    public static boolean benchmark = false;
    public static boolean timeout = false;
    public static boolean user_input = false; // whether or not to ask for user input, "Press Enter", or "Y/N" type interactions
    public static boolean full_benchmark = false; // if false, only attempt deletions of entailed axioms
    public final static Logger logger = Logger.getLogger( SparqlUpdater.class.getName() );
    private static FileHandler log_file;
    private static SimpleFormatter log_formatter;

    public static void main( String[] args )
    {
        // Set up logging
        try {
            logger.setLevel( Level.ALL );
            log_file = new FileHandler( "sparqlupdater.log" );
            log_formatter = new SimpleFormatter();
            log_file.setFormatter( log_formatter );
            logger.addHandler( log_file );
        }
        catch ( IOException e ) {
            System.err.println( e.getMessage() );
            return;
        }

        Options options = new Options();

        Option max_arg = new Option( "x", "max", true, "Maximum number of generated explanations for each inference (Default: 100)" );
        max_arg.setRequired( false );
        options.addOption( max_arg );

        Option verb_arg = new Option( "v", "verbose", true, "Level of talkativeness (0-4, default: 1)" );
        verb_arg.setRequired( false );
        options.addOption( verb_arg );

        Option glass_arg = new Option( "m", "method", true, "Method that will be used to generate explanations (Default: glass)" );
        glass_arg.setRequired( false );
        options.addOption( glass_arg );

        Option timeout_arg = new Option( "t", "timeout", true, "Timeout in seconds (default: none)" );
        timeout_arg.setRequired( false );
        options.addOption( timeout_arg );

        Option input_arg = new Option( "i", "input", true, "Ontology input file path" );
        input_arg.setRequired( true );
        options.addOption( input_arg );

        Option ont_arg = new Option( "o", "output", true, "Output file path for ontology/benchmark stats" );
        ont_arg.setRequired( false );
        options.addOption( ont_arg );

        Option query_arg = new Option( "q", "query", true, "Query/update input file path" );
        query_arg.setRequired( false );
        options.addOption( query_arg );

        Option sem_arg = new Option( "s", "semantics", true, "Semantics for choosing deletions/implementations. Options: custom, query_set, query_car, rigid, depend, rigdep" );
        sem_arg.setRequired( false );
        options.addOption( sem_arg );

        Option casc_arg = new Option( "c", "cascade", true, "Use cascading behaviour for update semantics" );
        casc_arg.setRequired( false );
        options.addOption( casc_arg );

        Option cus_arg1 = new Option( "c1", "custom1", true, "First option for custom update semantics (for use with -s custom ONLY)" );
        cus_arg1.setRequired( false );
        options.addOption( cus_arg1 );
        Option cus_arg2 = new Option( "c2", "custom2", true, "Second option for custom update semantics (for use with -s custom ONLY)" );
        cus_arg2.setRequired( false );
        options.addOption( cus_arg2 );

        options.addOption( "h", "help", false, "Show help" );
        options.addOption( "b", "benchmark", false, "Perform benchmarks" );
        options.addOption( "u", "user-input", false, "Ask for user input" );
        options.addOption( "f", "full", false, "Benchmark all possible axiom combinations" );

        CommandLineParser clparser = new DefaultParser();
        HelpFormatter formatter = new HelpFormatter();
        CommandLine cmd;
        boolean c_provided = false;
        boolean o_provided = false;
        boolean cascade_provided = false;
        boolean q_provided = false;

        try {
            cmd = clparser.parse( options, args );

            if ( cmd.hasOption( "h" ) ) {
                formatter.printHelp( "SPARQL-Updater", options );
                return;
            }

            if ( cmd.hasOption( "c1" ) && cmd.hasOption( "c2" ) ) {
                c_provided = true;
            }

            if ( cmd.hasOption( "o" ) ) {
                o_provided = true;
            }

            if ( cmd.hasOption( "u" ) ) {
                user_input = true;
            }

            if ( cmd.hasOption( "q" ) ) {
                q_provided = true;
            }

            if ( cmd.hasOption( "c" ) ) {
                cascade_provided = true;
            }

            if ( cmd.hasOption( "b" ) ) {
                benchmark = true;
            }

            if ( cmd.hasOption( "f" ) ) {
                full_benchmark = true;
            }

            if ( cmd.hasOption( "t" ) ) {
                timeout = true;
            }
        }
        catch ( ParseException e ) {
            System.out.println( e.getMessage() );
            formatter.printHelp( "SPARQL-Updater", options );

            return;
        }

        int max_explanations = 100;
        String method;
        String semantics = "query_car";
        String custom1 = "max";
        String custom2 = "max";

        try {
            verbose_level = Integer.parseInt( cmd.getOptionValue( "verbose", "1" ) );
            max_explanations = Integer.parseInt( cmd.getOptionValue( "max", "100" ) );

            // parse only if user wants to use timeout, i.e. -t is provided at all
            if ( timeout ) {
                timeout_seconds = Integer.parseInt( cmd.getOptionValue( "timeout", "60" ) ); // for benchmark, use 60 as default
            }

            // Don't accept negative input
            if ( max_explanations <= 0 ) {
                throw new NumberFormatException();
            }

            semantics = cmd.getOptionValue( "semantics", "query_car" ); // default is query-driven with maximum cardinality

            if ( ( !semantics.equals( "query_set" ) && !semantics.equals( "query_car" ) && !semantics.equals( "rigid" ) && !semantics.equals( "custom" ) && !semantics.equals( "depend" ) && !semantics.equals( "rigdep" ) ) || ( semantics.equals( "custom" ) && !c_provided ) ) {
                String message = new String( "--semantics option can be one of the following:\n" +
             "   -\"custom\" for semantics including insertion; requires -c1 max/meet -c2 max/meet as additional parameters\n" +
             "   -\"rigid\" for update semantics trying to minimize deletion of rigid concept assertions\n" +
             "   -\"depend\" for update semantics trying to minimize cascading deletions of concepts dependent on each other w.r.t. roles\n" +
             "   -\"rigdep\" combines the behaviour of rigidity- and dependency-guided semantics\n" +
             "   -\"query_car\" for query-driven update semantics with maximum cardinality\n" +
             "   -\"query_set\" for query-driven update semantics with set inclusion" );

                throw new IllegalArgumentException( message );
            }

            if ( semantics.equals( "custom" ) && c_provided ) {
                custom1 = cmd.getOptionValue( "custom1", "max" ); // default is max 
                custom2 = cmd.getOptionValue( "custom2", "max" ); // default is max

                if ( !custom1.equals( "meet" ) && !custom1.equals( "max" ) && !custom2.equals( "meet" ) && !custom2.equals( "max" ) ) {
                    String message = new String( "--custom1/--custom2 options can be one of the following:\n" +
                 "   -\"max\" for maxichoice semantics\n" +
                 "   -\"meet\" for meet semantics\n" );

                    throw new IllegalArgumentException( message );
                }
            }

            method = cmd.getOptionValue( "method", "glass" ); // default is glass box method

            if ( !method.equals( "glass" ) && !method.equals( "black" ) ) {
                String message = new String( "--method option can be one of the following:\n" +
             "   -\"glass\" for glass box\n"+
             "   -\"black\" for black box" );

                throw new IllegalArgumentException( message );
            }
        }
        catch ( NumberFormatException e ) {
            SparqlUpdater.logger.severe( "--max option requires a positive, non-zero integer value as its provided argument." );

            return;
        }
        catch ( IllegalArgumentException e ) {
            SparqlUpdater.logger.severe( e.getMessage() );

            return;
        }

        // We don't need a query for benchmark mode (benchmark mode just goes through all axiom, property, class combinations and performs deletions)
        String update_path = "";

        if ( !benchmark ) {
            if ( !q_provided ) {
                System.err.println( "[ ERROR ] You need to provide a SparQL-Query via the -q option if not running in benchmark mode!" );
                System.exit( 1 );
            }

            if ( full_benchmark ) {
                System.out.println( "Redundant -f option is ignored (not running benchmark mode)." );
            }

            update_path = cmd.getOptionValue( "query" );
        }
        else if ( q_provided ) {
            System.out.println( "Redundant -q option is ignored (running benchmark mode)." );
        }

        String ontology_path = cmd.getOptionValue( "input" ); // no default; argument required
        String output_path = o_provided ? cmd.getOptionValue( "output" ) : benchmark ?
            FilenameUtils.removeExtension( ontology_path ) + "_" + semantics + "_stats.txt" :
            FilenameUtils.removeExtension( ontology_path ) + "_updated.owl";

        if ( verbose_level > 0 ) {
            System.out.println( "************** SPARQL UPDATER **************" );
            System.out.println( "Update path: " + update_path );
            System.out.println( "Ontology input path: " + ontology_path );
            System.out.println( "Ontology/benchmark stats output path: " + output_path );
            System.out.println( "Max explanations: " + max_explanations );
            System.out.println( "Method: " + method );
            System.out.println( "Verbose level: " + verbose_level );
            System.out.println( "Semantics: " + semantics );
            System.out.println( "Cascading: " + cascade_provided );
            System.out.println( "Benchmark: " + ( ( benchmark && full_benchmark ) ? "full" : benchmark ) );
            System.out.println( "User input: " + user_input );

            if ( timeout ) {
                System.out.println( "Timeout: " + timeout_seconds + " seconds" );
            }
            else {
                System.out.println( "Timeout: " + timeout );
            }

            if ( semantics.equals( "custom" ) ) {
                System.out.println( "Custom1: " + custom1 );
                System.out.println( "Custom2: " + custom2 );
            }
        }

        try {
            // Store the actual update to execute as a string; might throw IOException
            String update = benchmark ? "" : new String( Files.readAllBytes( Paths.get( update_path ) ) );

            if ( benchmark ) {
                verbose_level = -1; // if benchmarking, no console output
                SparqlUpdaterImpl.benchmark( ontology_path, output_path, update, max_explanations, method, semantics, custom1, custom2, cascade_provided );
            }
            else {
                if ( timeout ) {
                    ExecutorService executor = Executors.newSingleThreadExecutor();

                    SparqlUpdaterImpl.PerformUpdate pupd = new SparqlUpdaterImpl.PerformUpdate( ontology_path, output_path, update, max_explanations, method, semantics, custom1, custom2, cascade_provided );
                    List< Future< Void > > futures = executor.invokeAll( Arrays.asList( pupd ), timeout_seconds, TimeUnit.SECONDS );
                    executor.shutdownNow();
                    executor.awaitTermination( timeout_seconds, TimeUnit.SECONDS );

                    for ( Future< Void > future : futures ) {
                        if ( future.isCancelled() ) {
                            SparqlUpdater.logger.severe( "Performing update was interrupted (timeout)." );
                        }
                    }

                    if ( pupd.error_ != null ) {
                        throw pupd.error_;
                    }
                }
                else {
                    SparqlUpdaterImpl.performUpdate( ontology_path, output_path, update, max_explanations, method, semantics, custom1, custom2, cascade_provided, null, null, null );
                }
            }
        }
        catch ( IOException e ) {
            SparqlUpdater.logger.severe( "IOException: " + e.getMessage() );
            e.printStackTrace();
        }
        catch ( IllegalStateException e ) {
            SparqlUpdater.logger.severe( "IllegalStateException: " + e.getMessage() );
            e.printStackTrace();
        }
        catch ( RuntimeException e ) {
            SparqlUpdater.logger.severe( "RuntimeException: " + e.getMessage() );
            e.printStackTrace();
        }
        catch ( Exception e ) {
            SparqlUpdater.logger.severe( "Exception: " + e.getMessage() );
            e.printStackTrace();
        }
        catch ( Throwable e ) {
            SparqlUpdater.logger.severe( "Error: " + e.getMessage() );
            e.printStackTrace();
        }

        System.exit( 0 ); // Need this to shut down all Jena threads that might not have been terminated
    }
}
