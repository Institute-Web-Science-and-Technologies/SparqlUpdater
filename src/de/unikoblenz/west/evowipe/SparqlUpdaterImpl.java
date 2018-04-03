package de.unikoblenz.west.evowipe;

import java.io.StringWriter;
import java.io.PrintWriter;
import java.io.IOException;
import java.io.FileNotFoundException;
import java.io.File;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.Map;
import java.util.Scanner;
import java.util.Arrays;
import java.util.Collections;

import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.io.SystemOutDocumentTarget;
import org.semanticweb.owlapi.formats.OWLXMLDocumentFormat;
import org.semanticweb.owlapi.model.IRI;
import com.clarkparsia.pellet.owlapiv3.EntailmentChecker;
import org.mindswap.pellet.jena.PelletReasonerFactory;
import com.clarkparsia.pellet.sparqldl.jena.SparqlDLExecutionFactory;
import com.hp.hpl.jena.query.QueryExecution;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.StmtIterator;
import com.hp.hpl.jena.rdf.model.Statement;
import com.hp.hpl.jena.rdf.model.RDFNode;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.rdf.model.Property;

import com.hp.hpl.jena.ontology.OntModel;
import com.hp.hpl.jena.query.Query;
import com.hp.hpl.jena.query.QueryExecution;
import com.hp.hpl.jena.query.QueryFactory;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.query.QueryExecution;
// !!!! if you change the JENA version to 3 upwards, need to use these imports: !!!!
//import org.apache.jena.query.QueryExecution;
//import org.apache.jena.rdf.model.Model;
//import org.apache.jena.rdf.model.StmtIterator;
//import org.apache.jena.rdf.model.Statement;

import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.apibinding.OWLManager;
//import org.semanticweb.owlapi.formats.OWLXMLDocumentFormat;
import org.semanticweb.owlapi.formats.RDFXMLDocumentFormat;
import org.semanticweb.owlapi.util.SimpleShortFormProvider;
import org.semanticweb.owlapi.manchestersyntax.renderer.ManchesterOWLSyntaxObjectRenderer;

import org.apache.commons.lang3.tuple.Pair;

import java.util.concurrent.TimeoutException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.Callable;
import java.util.concurrent.Future;
import java.lang.Runnable;

import uk.ac.manchester.cs.owl.owlapi.OWLObjectPropertyAssertionAxiomImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLClassAssertionAxiomImpl;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import com.clarkparsia.owlapiv3.OntologyUtils;

/**
 * @brief An implementation of performing SparQL updates in the presence of OWL-DL TBoxes.
 *
 * In order for deleted assertions to not be entailed by the ontology, this involves computing minimal hitting sets of root justifications for assertions to be deleted, the latter being computed by the OWL-DL reasoner Pellet (this takes place in _getAxiomsToDelete_.
 */
public class SparqlUpdaterImpl {
    private static Set< OWLAxiom > insert_axioms;

    static class PerformUpdate implements Callable< Void > {
        private final String ontology_path_;
        private final String output_path_;
        private final String update_;
        private final int max_explanations_;
        private final String method_;
        private final String semantics_arg_;
        private final String custom1_;
        private final String custom2_;
        private final boolean cascade_;
        public Throwable error_;
        public StringBuilder current_stats_;
        public HashMap< Integer, Integer > ways_to_delete_;
        public HashMap< Integer, Integer > assertions_to_delete_;

        public PerformUpdate( String ontology_path, String output_path, String update, int max_explanations, String method, String semantics_arg, String custom1, String custom2, boolean cascade ) {
            this.ontology_path_ = ontology_path;
            this.output_path_ = output_path;
            this.update_ =  update;
            this.max_explanations_ = max_explanations;
            this.method_ = method;
            this.semantics_arg_ = semantics_arg;
            this.custom1_ = custom1;
            this.custom2_ = custom2;
            this.cascade_ = cascade;
            this.error_ = null;
            this.current_stats_ = new StringBuilder( "" );
            this.ways_to_delete_ = new HashMap< Integer, Integer >();
            this.assertions_to_delete_ = new HashMap< Integer, Integer >();
        }

        public Void call() {
            // IMPORTANT. If an exception is thrown, it will not be caught by the parent thread. Therefore: store it inside the class.
            try {
                performUpdate( ontology_path_, output_path_, update_, max_explanations_, method_, semantics_arg_, custom1_, custom2_, cascade_, current_stats_, ways_to_delete_, assertions_to_delete_ );
            }
            catch ( Throwable e ) {
                error_ = e;
            }

            return null;
        }
    };

    /**
     * @brief Perform a SparQL update on a given ontology.
     * @param ontology_path the system file path to the knowledge base file
     * @param update_as_string the update to perform; NOT the file path, but the actual update contents
     * @param max_explanations the maximum number of justifications that should be computed
     * @param method method to use for explanation (glass box/black box)
     * @param semantics_arg Semantics for choosing deletions/implementations
     * @param custom1 Semantics for choosing deletions in custom update semantics
     * @param custom2 Semantics for choosing debuggings in custom update semantics
     * @param cascade Whether to add cascading behaviour for update semantics
     * @param stats, ways_to_delete, assertions_to_delete ONLY used in benchmark mode. Stores statistics for semantics
     * ...
     * @return a list of implementations
     */
    public static List< Implementation > getImplementations( String ontology_path, String update_as_string, int max_explanations, String method, String semantics_arg, String custom1, String custom2, boolean cascade, StringBuilder stats, HashMap< Integer, Integer > ways_to_delete, HashMap< Integer, Integer > assertions_to_delete ) {
        UpdateRewriter u_rewriter = new UpdateRewriter( ontology_path, update_as_string );
        insert_axioms = SparqlUpdaterImpl.getAxiomsToInsert( ontology_path, update_as_string, max_explanations, u_rewriter );
        Set< OWLAxiom > Ad = new HashSet< OWLAxiom >(); // fill with result of construct query for deletion
        Set< HittingSet< OWLAxiom > > delete_axioms = SparqlUpdaterImpl.getAxiomsToDelete( ontology_path, update_as_string, max_explanations, method, u_rewriter, Ad );

        if ( SparqlUpdater.verbose_level > 0 ) {
            System.out.println( "Minimal hitting sets:" );

            for ( HittingSet< OWLAxiom > hitting_set : delete_axioms ) {
                hitting_set.printAxioms();
                System.out.println();
            }

            Scanner scanner = new Scanner( System.in );

            if ( SparqlUpdater.user_input ) {
                System.out.println( "Press \"ENTER\" to continue..." );
                scanner.nextLine();
            }

            System.out.println( "Insertions:" );
            SparqlUpdaterImpl.printAxiomSet( insert_axioms );

            if ( SparqlUpdater.user_input ) {
                System.out.println( "Press \"ENTER\" to continue..." );
                scanner.nextLine();
            }
        }

        Semantics semantics = null;

        if ( semantics_arg.equals( "query_car" ) ) {
            semantics = new QueryDrivenSemantics( ontology_path, method, Ad );
        }
        else if ( semantics_arg.equals( "query_set" ) ) {
            semantics = new QueryDrivenSemanticsSet( ontology_path, method, Ad );
        }
        else if ( semantics_arg.equals( "rigid" ) ) {
            semantics = new RigidSemantics( ontology_path, update_as_string );
        }
        else if ( semantics_arg.equals( "depend" ) ) {
            semantics = new DependencyGuidedSemantics( ontology_path, update_as_string, 0 );
        }
        else if ( semantics_arg.equals( "custom" ) ) {
            semantics = new CustomSemantics( ontology_path, method, custom1, custom2 );
        }
        else {
            throw new IllegalArgumentException( "Semantics argument " + semantics_arg + " is not valid!" );
        }

        return semantics.filter( delete_axioms, insert_axioms, stats, ways_to_delete, assertions_to_delete );
    }

    /**
     * @brief Perform a SparQL update on a given ontology.
     * @param ontology_path the system file path to the knowledge base file
     * @param output_file_name the system file path where to store the updated knowledge base
     * @param update_as_string the update to perform; NOT the file path, but the actual update contents
     * @param max_explanations the maximum number of justifications that should be computed
     * @param method method to use for explanation (glass box/black box)
     * @param semantics_arg Semantics for choosing deletions/implementations
     * @param custom1 Semantics for choosing deletions in custom update semantics
     * @param custom2 Semantics for choosing debuggings in custom update semantics
     * @param cascade Whether to add cascading behaviour for update semantics
     * @param stats, ways_to_delete, assertions_to_delete ONLY used in benchmark mode. Stores statistics for semantics
     */
    public static void performUpdate( String ontology_path, String output_file_name, String update_as_string, int max_explanations, String method, String semantics_arg, String custom1, String custom2, boolean cascade, StringBuilder stats, HashMap< Integer, Integer > ways_to_delete, HashMap< Integer, Integer > assertions_to_delete ) {
        // Determine all axioms that have to be deleted in order for them not to be entailed by the ontology after removal. Might throw RuntimeException if the update is not valid input (regarding syntax) or if there are errors during computation of justifications.
        List< Implementation > implementations = getImplementations( ontology_path, update_as_string, max_explanations, method, semantics_arg, custom1, custom2, cascade, stats, ways_to_delete, assertions_to_delete );

        Implementation implementation = new Implementation();

        if ( !SparqlUpdater.benchmark ) {
            // Display options if necessary
            if ( implementations.size() > 1 ) {
                System.out.println( "[" + semantics_arg + "] Multiple possible implementations found:" );
                int ctr = 1;

                for ( Implementation i : implementations ) {
                    System.out.println();
                    System.out.println( ctr++ + ". Implementation:" );
                    System.out.println( "Deletion:" );
                    i.del_.printAxioms();
                    System.out.println( "Debug:" );
                    i.dbg_.printAxioms();

                    if ( semantics_arg.equals( "depend" ) ) {
                        System.out.println( "Cascaded deletions:" );
                        HittingSet< OWLAxiom > tmp = new HittingSet< OWLAxiom >( i.success_ );
                        tmp.printAxioms();
                    }

                    System.out.println();
                    System.out.println();
                    System.out.println( "====================================" );
                    System.out.println();
                }

                int choice = 1;

                if ( SparqlUpdater.user_input ) {
                    while ( true ) {
                        System.out.println();
                        System.out.print( "Choose an implementation (1-" + ( ctr - 1 ) + "): " );
                        Scanner in = new Scanner( System.in );
                        choice = in.nextInt();

                        if ( choice < 1 || choice >= ctr ) {
                            System.out.println( " Invalid choice." );
                        } 
                        else {
                            break;
                        }
                    }
                }

                implementation = implementations.get( choice - 1 );

                if ( semantics_arg.equals( "depend" ) ) {
                    // Cascaded deletions in _success__ formally belong to deletions, make sure our final output reflects that
                    implementation.del_.merge( implementation.success_ );
                }
            }
            else if ( implementations.size() > 0 ) {
                implementation = implementations.get( 0 );

                if ( semantics_arg.equals( "depend" ) ) {
                    // Cascaded deletions in _success__ formally belong to deletions, make sure our final output reflects that
                    implementation.del_.merge( implementation.success_ );
                }
            }
        }

        if ( !semantics_arg.equals( "depend" ) && cascade ) {
            SparqlUpdater.logger.warning( "Cascading behaviour for arbitrary update semantics has not yet been implemented." );
        }

        if ( SparqlUpdater.verbose_level >= 0 ) {
            System.out.println( "Chosen deletion: " );
            implementation.del_.printAxioms();

            if ( implementation.dbg_.size() > 0 ) {
                System.out.println( "Chosen debug: " );
                implementation.dbg_.printAxioms();
            }
        }

        if ( !SparqlUpdater.benchmark ) {
            // Perform update and write ontology to file system
            OWLOntology ontology = null;
            OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
            File file = new File( ontology_path );

            try {
                ontology = manager.loadOntologyFromOntologyDocument( file );
                manager.removeAxioms( ontology, implementation.del_.set() );
                manager.addAxioms( ontology, insert_axioms );
                manager.removeAxioms( ontology, implementation.dbg_.set() );
                File output = new File( output_file_name );

                try {
                    if ( !output.createNewFile() ) {
                        throw new IOException( "File " + output_file_name + " already exists." );
                    }

                    IRI documentIRI2 = IRI.create( output );
                    //manager.saveOntology( ontology, new OWLXMLDocumentFormat(), documentIRI2 );
                    manager.saveOntology( ontology, new RDFXMLDocumentFormat(), documentIRI2 );
                }
                catch( Exception e ) {
                    SparqlUpdater.logger.severe( "Could not save updated OWL ontology to file system: " + e );
                }
            }
            catch ( OWLOntologyCreationException e ) {
                SparqlUpdater.logger.severe( "Could not create OWL ontology for performing final update: " + e );
            }
        }
    }

    /**
     * @brief Build a SparQL update that deletes a class assertion for a specific (individual, class) pair
     * @param individual_iri the individual from the class assertion
     * @param cls_iri the class from the class assertion
     */
    private static String buildClassAssertionQuery( String individual_iri, String cls_iri ) {
        return new StringBuilder()
                           .append( "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\nPREFIX owl: <http://www.w3.org/2002/07/owl#>\n\n" )
                           .append( "DELETE { " )
                           .append( "<" + individual_iri + "> a <" + cls_iri + "> }\n" )
                           .append( "INSERT {}\n" )
                           .append( "WHERE { " )
                           .append( "<" + individual_iri + "> a <" + cls_iri + "> }" )
                           .toString();
    }

    /**
     * @brief Build a SparQL update that deletes an object property assertion for a specific (individual, property, individual) triple
     * @param individual_iri_a the left-side individual from the assertion
     * @param property_iri the property from the assertion
     * @param individual_iri_b the right-side individual from the assertion
     */
    private static String buildObjectPropertyQuery( String individual_iri_a, String property_iri, String individual_iri_b ) {
        return new StringBuilder()
                           .append( "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\nPREFIX owl: <http://www.w3.org/2002/07/owl#>\n\n" )
                           .append( "DELETE { " )
                           .append( "<" + individual_iri_a + "> <" + property_iri + "> <" + individual_iri_b + "> }\n" )
                           .append( "INSERT {}\n" )
                           .append( "WHERE { " )
                           .append( "<" + individual_iri_a + "> <" + property_iri + "> <" + individual_iri_b + "> }" )
                           .toString();
    }

    /**
     * @brief Benchmark SparQL updates on a given ontology.
     * @param ontology_path the system file path to the knowledge base file
     * @param output_file_name the system file path where to store the output stats
     * @param update_as_string the update to perform; NOT the file path, but the actual update contents
     * @param max_explanations the maximum number of justifications that should be computed
     * @param method method to use for explanation (glass box/black box)
     * @param semantics_arg Semantics for choosing deletions/implementations
     * @param custom1 Semantics for choosing deletions in custom update semantics
     * @param custom2 Semantics for choosing debuggings in custom update semantics
     * @param cascade Whether to add cascading behaviour for update semantics
     */
    public static void benchmark( String ontology_path, String output_file_name, String update_as_string, int max_explanations, String method, String semantics_arg, String custom1, String custom2, boolean cascade ) {
    // 0. Build ontology from file
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = null;

        try {
            ontology = manager.loadOntologyFromOntologyDocument( new File( ontology_path ) );
        }
        catch ( OWLOntologyCreationException e ) {
            throw new RuntimeException( "Could not create temporary OWL ontology: " + e );
        }

    // 0.5 Prepare output log
        PrintWriter writer = null;

        try {
            writer = new PrintWriter( output_file_name, "UTF-8" );
        }
        catch ( Exception e ) {
            throw new RuntimeException( e.getMessage() );
        }

        writer.println( "====== SPARQL-UPDATER BENCHMARK STATISTICS ======" );
        writer.println( "=== Ontology input path: " + ontology_path );
        writer.println( "=== Benchmark stats output path (this file): " + output_file_name );
        writer.println( "=== Full benchmark: " + SparqlUpdater.full_benchmark );
        writer.println( "=== Max explanations: " + max_explanations );
        writer.println( "=== Method: " + method );
        writer.println( "=== Semantics: " + semantics_arg );
        writer.println( "=== Cascading: " + cascade );

        if ( semantics_arg.equals( "custom" ) ) {
            writer.println( "===== Custom1: " + custom1 );
            writer.println( "===== Custom2: " + custom2 );
        }

        writer.println( "=================================================" );
        writer.println( "Axiom    Semantics    Amount of hitting sets    Number of axioms in each hitting set" );
        writer.println();

        // Benchmark Statistics
        HashMap< Integer, Integer > ways_to_delete = new HashMap< Integer, Integer >();
        HashMap< Integer, Integer > assertions_to_delete = new HashMap< Integer, Integer >();

    // 1.1 (optional) Retrieve entailed axioms
        if ( !SparqlUpdater.full_benchmark ) {
            // First create a Jena ontology model backed by the Pellet reasoner
            // (note, the Pellet reasoner is required)
            OntModel m = ModelFactory.createOntologyModel( PelletReasonerFactory.THE_SPEC );

            // Then read the data from the file into the ontology model
            m.read( ontology_path );

            // Build the construct query and execute
            String head = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\nPREFIX owl: <http://www.w3.org/2002/07/owl#>\n";
            String construct = "CONSTRUCT { ?Ind1 a ?Concept1 }\nWHERE {  ?Ind1 a ?Concept1 }";
            String query_string = head + construct;
            Query q = QueryFactory.create( query_string );

            // Create a SPARQL-DL query execution for the given query and ontology model
            QueryExecution qe = SparqlDLExecutionFactory.create( q, m );

            // Defensive programming
            if ( !qe.getQuery().isConstructType() ) {
                throw new RuntimeException( "Construct query for finding entailed axioms is not a valid construct query!" );
            }

            // Execute query
            Model model = qe.execConstruct();
            String syntax = "TURTLE"; // also try "N-TRIPLE" and "RDF/XML-ABBREV"
            StringWriter out = new StringWriter();
            model.write( out, syntax );

            StmtIterator stmts = model.listStatements();

            outer: while ( stmts.hasNext() ) {
                Statement stmt = stmts.next();
                RDFNode cl_node = stmt.getObject();
                Resource ind = stmt.getSubject();
                String class_string = cl_node.toString();
                String ind_string = ind.toString();
                OWLEntity subject = OntologyUtils.findEntity( ind_string, ontology );
                OWLEntity cla = OntologyUtils.findEntity( class_string, ontology );
                OWLNamedIndividual ind_a = ( OWLNamedIndividual ) subject;
                OWLClass cl = ( OWLClass ) cla;

                if ( ind_a == null || cl == null ) {
                    continue;
                }

                try {
                    try {
                        String update = buildClassAssertionQuery( ind_a.toStringID(), cl.toStringID() );

                        ExecutorService executor = Executors.newSingleThreadExecutor();

                        System.out.println( "Current: " + ind_a.getIRI().getFragment() + " a " + cl.getIRI().getFragment() );

                        PerformUpdate pupd = new PerformUpdate( ontology_path, "", update, max_explanations, method, semantics_arg, custom1, custom2, cascade );
                        List< Future< Void > > futures = executor.invokeAll( Arrays.asList( pupd ), SparqlUpdater.timeout_seconds, TimeUnit.SECONDS );
                        executor.shutdownNow();
                        executor.awaitTermination( SparqlUpdater.timeout_seconds, TimeUnit.SECONDS );

                        for ( Future< Void > future : futures ) {
                            if ( future.isCancelled() ) {
                                SparqlUpdater.logger.warning( "Performing update was interrupted (timeout) during benchmark for axiom " + ind_a.getIRI().getFragment() + " a " + cl.getIRI().getFragment() );
                                writer.println( ind_a.getIRI().getFragment() + " a " + cl.getIRI().getFragment() + "    " + semantics_arg + "    T" );
                                int count = ways_to_delete.containsKey( -2 ) ? ways_to_delete.get( -2 ) : 0;
                                ways_to_delete.put( -2, count + 1 );
                                count = assertions_to_delete.containsKey( -2 ) ? assertions_to_delete.get( -2 ) : 0;
                                assertions_to_delete.put( -2, count + 1 );
                                continue outer;
                            }
                        }

                        if ( pupd.error_ != null ) {
                            throw pupd.error_;
                        }

                        String current_stats = pupd.current_stats_.toString();

                        for ( Map.Entry< Integer, Integer > e : pupd.ways_to_delete_.entrySet() )
                            ways_to_delete.merge( e.getKey(), e.getValue(), Integer::sum );

                        for ( Map.Entry< Integer, Integer > e : pupd.assertions_to_delete_.entrySet() )
                            assertions_to_delete.merge( e.getKey(), e.getValue(), Integer::sum );
                        //pupd.ways_to_delete_.forEach( ( k, v ) -> ways_to_delete.merge( k, v, Integer:sum ) ); 
                        //pupd.assertions_to_delete_.forEach( ( k, v ) -> assertions_to_delete.merge( k, v, Integer:sum ) ); 

                        // current_stats now contains stats for this deleted axiom
                        writer.println( ind_a.getIRI().getFragment() + " a " + cl.getIRI().getFragment() + "    " + semantics_arg + "    " + current_stats );
                    }
                    catch ( Throwable e ) {
                        SparqlUpdater.logger.severe( "Error occured during benchmark for axiom " + ind_a.getIRI().getFragment() + " a " + cl.getIRI().getFragment() + ": " + e.getMessage() );
                        writer.println( ind_a.getIRI().getFragment() + " a " + cl.getIRI().getFragment() + "    " + semantics_arg + "    E" );
                        int count = ways_to_delete.containsKey( -1 ) ? ways_to_delete.get( -1 ) : 0;
                        ways_to_delete.put( -1, count + 1 );
                        count = assertions_to_delete.containsKey( -1 ) ? assertions_to_delete.get( -1 ) : 0;
                        assertions_to_delete.put( -1, count + 1 );
                    }
                }
                catch ( Exception e ) {
                    System.err.println( e.getMessage() );
                }
            }

            // Build the second construct query and execute
            construct = "CONSTRUCT { ?Ind1 ?Role ?Ind2 }\nWHERE { ?Role a owl:ObjectProperty . ?Ind1 ?Role ?Ind2 }";
            query_string = head + construct;
            q = QueryFactory.create( query_string );

            // Create a SPARQL-DL query execution for the given query and ontology model
            qe = SparqlDLExecutionFactory.create( q, m );

            // Defensive programming
            if ( !qe.getQuery().isConstructType() ) {
                throw new RuntimeException( "Construct query for finding entailed axioms is not a valid construct query!" );
            }

            // Execute query
            model = qe.execConstruct();
            out = new StringWriter();
            model.write( out, syntax );

            stmts = model.listStatements();

outer_: while ( stmts.hasNext() ) {
                Statement stmt = stmts.next();

                try {
                    //OWLAxiom axiom = AxiomConverter.convert( stmt, ontology );
                    RDFNode o = stmt.getObject();
                    Resource s = stmt.getSubject();
                    Property p = stmt.getPredicate();
                    String object_string = o.toString();
                    String subject_string = s.toString();
                    String property_string = p.getLocalName();
                    OWLEntity subject = OntologyUtils.findEntity( subject_string, ontology );
                    OWLEntity property = OntologyUtils.findEntity( property_string, ontology );
                    OWLObject object = OntologyUtils.findEntity( object_string, ontology );

                    if ( subject == null || property == null || object == null ) {
                        continue;
                    }

                    OWLNamedIndividual ind_a = ( OWLNamedIndividual ) subject;
                    OWLObjectProperty obj_pr = ( OWLObjectProperty ) property;
                    OWLNamedIndividual ind_b = ( OWLNamedIndividual ) object;

                    try {
                        String update = buildObjectPropertyQuery( ind_a.toStringID(), obj_pr.toStringID(), ind_b.toStringID() );

                        if ( obj_pr.getIRI().getFragment().equals( "topObjectProperty" ) ) {
                            continue;
                        }

                        ExecutorService executor = Executors.newSingleThreadExecutor();

                        System.out.println( "Current: " + ind_a.getIRI().getFragment() + " " + obj_pr.getIRI().getFragment() + " " + ind_b.getIRI().getFragment() );

                        PerformUpdate pupd = new PerformUpdate( ontology_path, "", update, max_explanations, method, semantics_arg, custom1, custom2, cascade );
                        List< Future< Void > > futures = executor.invokeAll( Arrays.asList( pupd ), SparqlUpdater.timeout_seconds, TimeUnit.SECONDS );
                        executor.shutdownNow();
                        executor.awaitTermination( SparqlUpdater.timeout_seconds, TimeUnit.SECONDS );

                        for ( Future< Void > future : futures ) {
                            if ( future.isCancelled() ) {
                                SparqlUpdater.logger.warning( "Performing update was interrupted (timeout) during benchmark for axiom " + ind_a.getIRI().getFragment() + " " + obj_pr.getIRI().getFragment() + " " + ind_b.getIRI().getFragment() );
                                writer.println( ind_a.getIRI().getFragment() + " " + obj_pr.getIRI().getFragment() + " " + ind_b.getIRI().getFragment() + "    " + semantics_arg + "    T" );
                                int count = ways_to_delete.containsKey( -2 ) ? ways_to_delete.get( -2 ) : 0;
                                ways_to_delete.put( -2, count + 1 );
                                count = assertions_to_delete.containsKey( -2 ) ? assertions_to_delete.get( -2 ) : 0;
                                assertions_to_delete.put( -2, count + 1 );
                                continue outer_;
                            }
                        }

                        if ( pupd.error_ != null ) {
                            throw pupd.error_;
                        }

                        String current_stats = pupd.current_stats_.toString();
                        //pupd.ways_to_delete_.forEach( ( k, v ) -> ways_to_delete.merge( k, v, Integer:sum ) ); 
                        //pupd.assertions_to_delete_.forEach( ( k, v ) -> assertions_to_delete.merge( k, v, Integer:sum ) ); 

                        for ( Map.Entry< Integer, Integer > e : pupd.ways_to_delete_.entrySet() )
                            ways_to_delete.merge( e.getKey(), e.getValue(), Integer::sum );

                        for ( Map.Entry< Integer, Integer > e : pupd.assertions_to_delete_.entrySet() )
                            assertions_to_delete.merge( e.getKey(), e.getValue(), Integer::sum );

                        // current_stats now contains stats for this deleted axiom
                        writer.println( ind_a.getIRI().getFragment() + " " + obj_pr.getIRI().getFragment() + " " + ind_b.getIRI().getFragment() + "    " + semantics_arg + "    " + current_stats );
                    }
                    catch ( Throwable e ) {
                        SparqlUpdater.logger.severe( "Error occured during benchmark for axiom " + ind_a.getIRI().getFragment() + " " + obj_pr.getIRI().getFragment() + " " + ind_b.getIRI().getFragment() + ": " + e.getMessage() );
                        writer.println( ind_a.getIRI().getFragment() + " " + obj_pr.getIRI().getFragment() + " " + ind_b.getIRI().getFragment() + "    " + semantics_arg + "    E" );

                        int count = ways_to_delete.containsKey( -1 ) ? ways_to_delete.get( -1 ) : 0;
                        ways_to_delete.put( -1, count + 1 );
                        count = assertions_to_delete.containsKey( -1 ) ? assertions_to_delete.get( -1 ) : 0;
                        assertions_to_delete.put( -1, count + 1 );
                    }
                }
                catch ( Exception e ) {
                    System.err.println( e.getMessage() );
                }

            }
        }
    // 1.2 (optional, full benchmark) Retrieve all concepts, roles and individuals
        else {
            Set< OWLClass > classes = ontology.getClassesInSignature();
            Set< OWLNamedIndividual > individuals = ontology.getIndividualsInSignature();
            Set< OWLDataProperty > data_properties = ontology.getDataPropertiesInSignature();
            Set< OWLObjectProperty > object_properties = ontology.getObjectPropertiesInSignature();

            for ( OWLNamedIndividual ind_a : individuals ) {

    inner: for ( OWLClass cl : classes ) {
                    try {
                        String update = buildClassAssertionQuery( ind_a.toStringID(), cl.toStringID() );

                        ExecutorService executor = Executors.newSingleThreadExecutor();

                        System.out.println( "Current: " + ind_a.getIRI().getFragment() + " a " + cl.getIRI().getFragment() );

                        PerformUpdate pupd = new PerformUpdate( ontology_path, "", update, max_explanations, method, semantics_arg, custom1, custom2, cascade );
                        List< Future< Void > > futures = executor.invokeAll( Arrays.asList( pupd ), SparqlUpdater.timeout_seconds, TimeUnit.SECONDS );
                        executor.shutdownNow();
                        executor.awaitTermination( SparqlUpdater.timeout_seconds, TimeUnit.SECONDS );

                        for ( Future< Void > future : futures ) {
                            if ( future.isCancelled() ) {
                                SparqlUpdater.logger.warning( "Performing update was interrupted (timeout) during benchmark for axiom " + ind_a.getIRI().getFragment() + " a " + cl.getIRI().getFragment() );
                                writer.println( ind_a.getIRI().getFragment() + " a " + cl.getIRI().getFragment() + "    " + semantics_arg + "    T" );
                                int count = ways_to_delete.containsKey( -2 ) ? ways_to_delete.get( -2 ) : 0;
                                ways_to_delete.put( -2, count + 1 );
                                count = assertions_to_delete.containsKey( -2 ) ? assertions_to_delete.get( -2 ) : 0;
                                assertions_to_delete.put( -2, count + 1 );
                                continue inner;
                            }
                        }

                        if ( pupd.error_ != null ) {
                            throw pupd.error_;
                        }

                        String current_stats = pupd.current_stats_.toString();

                        for ( Map.Entry< Integer, Integer > e : pupd.ways_to_delete_.entrySet() )
                            ways_to_delete.merge( e.getKey(), e.getValue(), Integer::sum );

                        for ( Map.Entry< Integer, Integer > e : pupd.assertions_to_delete_.entrySet() )
                            assertions_to_delete.merge( e.getKey(), e.getValue(), Integer::sum );

                        // current_stats now contains stats for this deleted axiom
                        writer.println( ind_a.getIRI().getFragment() + " a " + cl.getIRI().getFragment() + "    " + semantics_arg + "    " + current_stats );
                    }
                    catch ( Throwable e ) {
                        SparqlUpdater.logger.severe( "Error occured during benchmark for axiom " + ind_a.getIRI().getFragment() + " a " + cl.getIRI().getFragment() + ": " + e.getMessage() );
                        writer.println( ind_a.getIRI().getFragment() + " a " + cl.getIRI().getFragment() + "    " + semantics_arg + "    E" );
                        int count = ways_to_delete.containsKey( -1 ) ? ways_to_delete.get( -1 ) : 0;
                        ways_to_delete.put( -1, count + 1 );
                        count = assertions_to_delete.containsKey( -1 ) ? assertions_to_delete.get( -1 ) : 0;
                        assertions_to_delete.put( -1, count + 1 );
                    }
                }

                for ( OWLNamedIndividual ind_b : individuals ) {
                    // TODO doesn't hurt, but should perhaps skip ind_a == ind_b here
                    // TODO what about a r b, b r a?
    inner: for ( OWLObjectProperty obj_pr : object_properties ) {
                        try {
                            String update = buildObjectPropertyQuery( ind_a.toStringID(), obj_pr.toStringID(), ind_b.toStringID() );
                            
                            if ( obj_pr.getIRI().getFragment().equals( "topObjectProperty" ) ) {
                                continue;
                            }

                            ExecutorService executor = Executors.newSingleThreadExecutor();

                            System.out.println( "Current: " + ind_a.getIRI().getFragment() + " " + obj_pr.getIRI().getFragment() + " " + ind_b.getIRI().getFragment() );

                            PerformUpdate pupd = new PerformUpdate( ontology_path, "", update, max_explanations, method, semantics_arg, custom1, custom2, cascade );
                            List< Future< Void > > futures = executor.invokeAll( Arrays.asList( pupd ), SparqlUpdater.timeout_seconds, TimeUnit.SECONDS );
                            executor.shutdownNow();
                            executor.awaitTermination( SparqlUpdater.timeout_seconds, TimeUnit.SECONDS );

                            for ( Future< Void > future : futures ) {
                                if ( future.isCancelled() ) {
                                    SparqlUpdater.logger.warning( "Performing update was interrupted (timeout) during benchmark for axiom " + ind_a.getIRI().getFragment() + " " + obj_pr.getIRI().getFragment() + " " + ind_b.getIRI().getFragment() );
                                    writer.println( ind_a.getIRI().getFragment() + " " + obj_pr.getIRI().getFragment() + " " + ind_b.getIRI().getFragment() + "    " + semantics_arg + "    T" );
                                    int count = ways_to_delete.containsKey( -2 ) ? ways_to_delete.get( -2 ) : 0;
                                    ways_to_delete.put( -2, count + 1 );
                                    count = assertions_to_delete.containsKey( -2 ) ? assertions_to_delete.get( -2 ) : 0;
                                    assertions_to_delete.put( -2, count + 1 );
                                    continue inner;
                                }
                            }
                            
                            if ( pupd.error_ != null ) {
                                throw pupd.error_;
                            }

                            String current_stats = pupd.current_stats_.toString();

                            for ( Map.Entry< Integer, Integer > e : pupd.ways_to_delete_.entrySet() )
                                ways_to_delete.merge( e.getKey(), e.getValue(), Integer::sum );

                            for ( Map.Entry< Integer, Integer > e : pupd.assertions_to_delete_.entrySet() )
                                assertions_to_delete.merge( e.getKey(), e.getValue(), Integer::sum );

                            // current_stats now contains stats for this deleted axiom
                            writer.println( ind_a.getIRI().getFragment() + " " + obj_pr.getIRI().getFragment() + " " + ind_b.getIRI().getFragment() + "    " + semantics_arg + "    " + current_stats );
                        }
                        catch ( Throwable e ) {
                            SparqlUpdater.logger.severe( "Error occured during benchmark for axiom " + ind_a.getIRI().getFragment() + " " + obj_pr.getIRI().getFragment() + " " + ind_b.getIRI().getFragment() + ": " + e.getMessage() );
                            writer.println( ind_a.getIRI().getFragment() + " " + obj_pr.getIRI().getFragment() + " " + ind_b.getIRI().getFragment() + "    " + semantics_arg + "    E" );

                            int count = ways_to_delete.containsKey( -1 ) ? ways_to_delete.get( -1 ) : 0;
                            ways_to_delete.put( -1, count + 1 );
                            count = assertions_to_delete.containsKey( -1 ) ? assertions_to_delete.get( -1 ) : 0;
                            assertions_to_delete.put( -1, count + 1 );
                        }
                    }
                }
            }
        }

        writer.println();
        writer.println();
        writer.println( "====== OVERALL BENCHMARK STATISTICS ======" );
        writer.println();

        int max_key = Collections.max( ways_to_delete.keySet() );

        for ( int i = -2; i <= max_key; ++i ) {
            int value = ways_to_delete.containsKey( i ) ? ways_to_delete.get( i ) : 0;

            if ( i == -1 ) {
                writer.println( "Number of requests with errors: " + value );
            }
            else if ( i == -2 ) {
                writer.println( "Number of requests with timeouts: " + value );
            }
            else {
                writer.println( "Number of requests with " + i + " ways to delete: " + value );
            }
        }

        writer.println();

        max_key = Collections.max( assertions_to_delete.keySet() );

        if ( max_key > -1 ) {
            for ( int i = 0; i <= max_key; ++i ) {
                int value = assertions_to_delete.containsKey( i ) ? assertions_to_delete.get( i ) : 0;
                writer.println( "Number of requests where " + i + " assertions will be deleted: " + value );
            }
        }

        SparqlUpdater.logger.info( "Finished benchmarking." );
        writer.close();
    }

    /**
     * @brief Calculate and return all assertions to delete in order to successfully perfom the update.
     * @param ontology_path simply the system file path to the knowledge base file.
     * @param update_as_string the update to perform; NOT the file path, but the actual update contents.
     * @param max_explanations the maximum number of justifications that should be computed
     * @param method method to use for explanation (glass box/black box)
     * @param u_rewriter rewrites update query into a construct query for deletions
     * @param Ad fill this with Abox assertions for the result of asking CONSTRUCT P_d where P_w, P_d being the desired deletion from the SparQL input update
     * @return minimal hitting sets of axioms to delete
     */
    public static Set< HittingSet< OWLAxiom > > getAxiomsToDelete( String ontology_path, String update_as_string, int max_explanations, String method, UpdateRewriter u_rewriter, Set< OWLAxiom > Ad ) {
        // Re-write the update to be a construct query and create a SPARQL-DL query execution for the given ontology model
        QueryExecution qe = u_rewriter.makeSparqlDLQueryExecutionDelete();

        // This will probably happen when the "update" does not actually contain keywords in such a way that would make it a valid SPARQL-UPDATE.
        if ( !qe.getQuery().isConstructType() ) {
            throw new RuntimeException( "Rewritten update is not a valid construct query! Please refine input update." );
        }

        // Execute query and print results
        Model model = qe.execConstruct();
        String syntax = "TURTLE"; // also try "N-TRIPLE" and "RDF/XML-ABBREV"
        StringWriter out = new StringWriter();
        model.write( out, syntax );

        if ( SparqlUpdater.verbose_level > 2 ) {
            System.out.println( "Query result:" );
            System.out.println( out.toString() );
        }

        // Now, we wish to generate justifications for each triple in the constructed RDF graph.
        // This can be done using Pellet's explanation module

        // Iterate over all statements of the constructed RDF graph.
        StmtIterator stmts = model.listStatements();
        Set< Justification > all_justifications = new TreeSet < Justification >(); // the set of all justifications for any to-be-deleted assertion (use a TreeSet because the order of elements is important for hitting set computation).

        while ( stmts.hasNext() ) {
            Statement stmt = stmts.next();
            AxiomJustificator justificator = new AxiomJustificator( stmt, ontology_path, max_explanations, method );
            Ad.add( justificator.getAxiom() );
            Set< Justification > justifications = justificator.computeJustifications(); // NOTE THAT THIS WILL NOT CONTAIN TBOX-ASSERTIONS (i.e. subClassOf, sameAs, ...)
            all_justifications.addAll( justifications ); // merge with other sets of justifications
        }

        // Now, _all_justifications_ contains all justifications for any to-be-deleted assertion, the latter resulting from the RDF-Graph constructed by the query that was the result of transforming the SPARQL-DL update into a CONSTRUCT query.
        // Next, we should minimize this set of justifications, i.e. make it a set of root justifications.
        Set< Justification > root_justifications = Justification.minimize( all_justifications );

        if ( SparqlUpdater.verbose_level > 0 ) {
            if ( SparqlUpdater.user_input ) {
                System.out.println( "Press \"ENTER\" to continue..." );
                Scanner scanner = new Scanner( System.in );
                scanner.nextLine();
            }

            if ( SparqlUpdater.verbose_level > 1 ) {
                System.out.println( "All justifications:" );
                Justification.print( all_justifications );
                System.out.println();
            }

            System.out.println( "Root justifications:" );
            Justification.print( root_justifications );
        }

        // Compute minimal hitting sets of these root justifications
        SortedSet< WrappedSet< OWLAxiom > > wrapped_sets_of_axioms = new TreeSet< WrappedSet< OWLAxiom > >();

        for ( Justification justification : root_justifications ) {
            wrapped_sets_of_axioms.add( new WrappedSet< OWLAxiom >( justification ) );
        }

        // Note to self: These minimal hitting sets will always have at least 1 element for some weird reason.
        Set< HittingSet< OWLAxiom > > minimal_hitting_sets = HittingSet.constructMinimalHittingSets( wrapped_sets_of_axioms );

        return minimal_hitting_sets;
    }

    /**
     * @brief Calculate and return all assertions to insert within an update.
     * @param ontology_path simply the system file path to the knowledge base file.
     * @param update_as_string the update to perform; NOT the file path, but the actual update contents.
     * @param max_explanations the maximum number of justifications that should be computed
     * @param u_rewriter rewrites update query into a construct query for insertions 
     * @return set of axioms to insert 
     */
    public static Set< OWLAxiom > getAxiomsToInsert( String ontology_path, String update_as_string, int max_explanations, UpdateRewriter u_rewriter ) {
        // Re-write the update to be a construct query and create a SPARQL-DL query execution for the given ontology model
        QueryExecution qe = u_rewriter.makeSparqlDLQueryExecutionInsert();

        // This will probably happen when the "update" does not actually contain keywords in such a way that would make it a valid SPARQL-UPDATE.
        if ( !qe.getQuery().isConstructType() ) {
            throw new RuntimeException( "Rewritten update is not a valid construct query! Please refine input update." );
        }

        // TODO it's very awkward that we construct a knowledge base here, which will essentially be created in the Justificator as well. Should be re-used somehow
        File file = new File( ontology_path );
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology;

        try {
            ontology = manager.loadOntologyFromOntologyDocument( file );
        }
        catch ( OWLOntologyCreationException e ) {
           throw new RuntimeException( "Could not create or edit temporary OWL ontology: " + e );
        }

        // Execute query and print results
        Model model = qe.execConstruct();
        String syntax = "TURTLE"; // also try "N-TRIPLE" and "RDF/XML-ABBREV"
        StringWriter out = new StringWriter();
        model.write( out, syntax );

        if ( SparqlUpdater.verbose_level > 2 ) {
            System.out.println( "Query result:" );
            System.out.println( out.toString() );
        }

        // Iterate over all statements of the constructed RDF graph.
        StmtIterator stmts = model.listStatements();
        Set< OWLAxiom > insertions = new HashSet< OWLAxiom >();

        // Convert statements to 'OWLAxiom's
        while ( stmts.hasNext() ) {
            Statement stmt = stmts.next();
            insertions.add( AxiomConverter.convert( stmt, ontology ) );
        }

        return insertions;
    }

    /**
     * @brief Print all axioms from a set of axioms on the standard output stream.
     * @param set_axioms A set of axioms to print
     */
    public static void printAxiomSet( Set< OWLAxiom > set_axioms ) {
        for ( OWLAxiom a : ( Set< OWLAxiom > ) set_axioms ) {
            StringWriter writer = new StringWriter();
            ManchesterOWLSyntaxObjectRenderer renderer = new ManchesterOWLSyntaxObjectRenderer( writer, new SimpleShortFormProvider() );
            a.accept( renderer );
            System.out.println( "  " + writer.toString() );
        }
    }

    /**
     * @brief Print all axioms from a set of axioms on the standard output stream.
     * @param set_axioms A set of axioms to print
     * @param indent How many leading tabs to add to each line
     */
    public static void printAxiomSet( Set< OWLAxiom > set_axioms, int indent ) {
        for ( OWLAxiom a : ( Set< OWLAxiom > ) set_axioms ) {
            StringWriter writer = new StringWriter();
            ManchesterOWLSyntaxObjectRenderer renderer = new ManchesterOWLSyntaxObjectRenderer( writer, new SimpleShortFormProvider() );
            a.accept( renderer );

            for ( int i = 0; i < indent; ++i ) {
                System.out.print( "\t" );
            }

            System.out.print( "  " + writer.toString() );
            System.out.println();
        }
    }
}
