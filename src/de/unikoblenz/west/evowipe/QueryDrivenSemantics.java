package de.unikoblenz.west.evowipe;

import java.lang.Thread;
import java.util.HashMap;
import java.util.Set;
import java.util.List;
import java.util.ArrayList;
import java.util.Scanner;

import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.ImmutablePair;

import org.semanticweb.owlapi.model.OWLAxiom;
import com.clarkparsia.pellet.sparqldl.jena.SparqlDLExecutionFactory;
import com.hp.hpl.jena.ontology.OntModel;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.update.UpdateAction;

import java.util.HashSet;
import java.io.StringWriter;
import java.io.IOException;
import java.io.File;
import org.semanticweb.owlapi.model.OWLException;
import com.clarkparsia.owlapi.explanation.io.ExplanationRenderer;
import com.clarkparsia.owlapi.explanation.io.manchester.ManchesterSyntaxExplanationRenderer;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.apibinding.OWLManager;

import java.util.SortedSet;
import java.util.TreeSet;
import java.util.Arrays;
import org.mindswap.pellet.KBLoader;
import org.mindswap.pellet.KnowledgeBase;
import com.clarkparsia.pellet.owlapiv3.OWLAPILoader;
import com.clarkparsia.pellet.owlapiv3.PelletReasoner;
import com.clarkparsia.owlapi.explanation.SatisfiabilityConverter;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.io.SystemOutDocumentTarget;
import org.semanticweb.owlapi.formats.OWLXMLDocumentFormat;
import org.semanticweb.owlapi.model.IRI;
import com.clarkparsia.pellet.owlapiv3.EntailmentChecker;
import org.mindswap.pellet.utils.FileUtils;
// TODO tidy this up a bit

/**
 * @brief Semantics taking into account the interplay of deletion and insertion.
 *
 * The aim of query-driven semantics is to maximize the number of successful deletions and insertions.
 * CARDINALITY ONLY; CHECK QueryDrivenSemanticsSet for set inclusion choices
 * Here: count amount of successful insertions/deletions; maximize sum of both
 */
public class QueryDrivenSemantics implements Semantics {
    private String ontology_path_;
    private String method_;
    private Set< OWLAxiom > Ad_;

    /**
     * @brief Class constructor. Performs basic setup of member variables.
     * @param ontology_path the system file path to the knowledge base file.
     * @param method method to use for explanation (glass box/black box)
     * @param Ad Abox assertions for the result of asking CONSTRUCT P_d where P_w, P_d being the desired deletion from the SparQL input update
     */
	public QueryDrivenSemantics( String ontology_path, String method, Set< OWLAxiom > Ad ) {
        ontology_path_ = ontology_path;
        method_ = method;
        Ad_ = new HashSet< OWLAxiom >( Ad );
	}

    /**
     * @brief Applies the query-driven semantics to hitting sets of axioms.
     *
     * @param delete_axioms hitting sets of axioms to be deleted
     * @param insert_axioms set of axioms to be inserted
     * @param stats, ways_to_delete, assertions_to_delete ONLY used in benchmark mode. Stores statistics for semantics
     * @return a list of implementations, for each of which the first element is the selected deletion, and the second element is the debugging step after the insertion.
     */
    @Override
    public List< Implementation > filter( Set< HittingSet< OWLAxiom > > delete_axioms, Set< OWLAxiom > insert_axioms, StringBuilder stats, HashMap< Integer, Integer > ways_to_delete, HashMap< Integer, Integer > assertions_to_delete ) {
        if ( SparqlUpdater.verbose_level > 0 ) {
            System.out.println( "========== QUERY-DRIVEN SEMANTICS ==========" );
        }

        Scanner scanner = null;

        if ( delete_axioms.isEmpty() ) {
            if ( SparqlUpdater.benchmark ) {
                stats.append( "0|" ); // no hitting sets

                if ( !Thread.currentThread().isInterrupted() ) {
                    int count = ways_to_delete.containsKey( 0 ) ? ways_to_delete.get( 0 ) : 0;
                    ways_to_delete.put( 0, count + 1 );
                    count = assertions_to_delete.containsKey( 0 ) ? assertions_to_delete.get( 0 ) : 0;
                    assertions_to_delete.put( 0, count + 1 );
                }

                return new ArrayList< Implementation >();
            }

            delete_axioms.add( new HittingSet< OWLAxiom >() ); // add empty hitting set, so that loop is still executed once; behave like brave semantics!
        }

        // If insertions are empty, there will be no debugging, hence each hitting set will be maximal and they will be presented as alternatives.

        int current_best = -1;

        ArrayList< Implementation > best_implementations = new ArrayList< Implementation >();

        for ( HittingSet< OWLAxiom > hs : delete_axioms ) {
            OWLOntology ontology = null;
            OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
            File file = new File( ontology_path_ );

            try {
                ontology = manager.loadOntologyFromOntologyDocument( file );
            }
            catch ( OWLOntologyCreationException e ) {
               throw new RuntimeException( "Could not create temporary OWL ontology: " + e.getMessage() );
            }

            if ( SparqlUpdater.verbose_level > 1 ) {
                System.out.println( "Deletion: " );
                SparqlUpdaterImpl.printAxiomSet( Ad_ );

                System.out.println( "Hitting set: " );
                hs.printAxioms();
            }

    // 1. Deletion
            if ( SparqlUpdater.verbose_level > 1 ) {
                System.out.println( "Before deletion: " + ontology.getAxiomCount());
            }

            manager.removeAxioms( ontology, hs.set() );

            if ( SparqlUpdater.verbose_level > 1 ) {
                System.out.println( "After deletion: " + ontology.getAxiomCount());
            }

    // 2. Insertion
            if ( SparqlUpdater.verbose_level > 1 ) {
                System.out.println( "Before insertion: " + ontology.getAxiomCount());
            }

            manager.addAxioms( ontology, insert_axioms );

            if ( SparqlUpdater.verbose_level > 1 ) {
                System.out.println( "After insertion: " + ontology.getAxiomCount());
            }

    // 3. Debugging
            File output = null;

            try {
                output = File.createTempFile( "tmp", "owl" );
                IRI documentIRI2 = IRI.create( output );
                manager.saveOntology( ontology, new OWLXMLDocumentFormat(), documentIRI2 );
            }
            catch ( Exception e ) {
                SparqlUpdater.logger.severe( e.getMessage() );
            }

            if ( SparqlUpdater.verbose_level > 2 ) {
                System.out.println( output.getAbsolutePath() );
            }

            InconsistencyJustificator ijust = new InconsistencyJustificator( output.getAbsolutePath(), 10000, "glass" );
            Set< Justification > justifications = ijust.computeJustifications(); // NOTE THAT THIS WILL NOT CONTAIN TBOX-ASSERTIONS (i.e. subClassOf, sameAs, ...)

            // Minimize this set of justifications, i.e. make it a set of root justifications.
            justifications = Justification.minimize( justifications );

            // Compute minimal hitting sets of these root justifications
            SortedSet< WrappedSet< OWLAxiom > > wrapped_sets_of_axioms = new TreeSet< WrappedSet< OWLAxiom > >();

            for ( Justification justification : justifications ) {
                wrapped_sets_of_axioms.add( new WrappedSet< OWLAxiom >( justification ) );
            }

            Set< HittingSet< OWLAxiom > > minimal_hitting_sets = HittingSet.constructMinimalHittingSets( wrapped_sets_of_axioms );

            output.delete(); // Deletes from file system

            // This loop will do entailment checks after performing each considered debugging step.
            // In case that there is no debugging to be done, coincidentally, the above function call returns a hitting set with an empty axiom. Hence this loop will be executed, but no actual debugging is performed.
            for ( HittingSet< OWLAxiom > dbg : minimal_hitting_sets ) {
                if ( SparqlUpdater.verbose_level > 2 ) {
                    System.out.println( "=== DEBUGGING HITTING SET ===" );
                    dbg.printAxioms();
                    System.out.println( "Before debugging: " + ontology.getAxiomCount() );
                }

                manager.removeAxioms( ontology, dbg.set() );

                if ( SparqlUpdater.verbose_level > 2 ) {
                    System.out.println( "After debugging: " + ontology.getAxiomCount() );
                }

                PelletReasoner reasoner = null;

                try {
                    output = File.createTempFile( "tmp", "owl" );
                    IRI documentIRI2 = IRI.create( output );
                    manager.saveOntology( ontology, new OWLXMLDocumentFormat(), documentIRI2 );

                    KBLoader kbloader = new OWLAPILoader();
                    OWLAPILoader loader = ( OWLAPILoader ) kbloader;
                    KnowledgeBase kb = kbloader.createKB( new String[] { output.getAbsolutePath() } );
                    reasoner = loader.getReasoner();
                }
                catch ( Exception e ) {
                    SparqlUpdater.logger.severe( e.getMessage() );
                }

                if ( SparqlUpdater.verbose_level > 2 ) {
                    System.out.println( output.getAbsolutePath() );
                }

    // 4. Entailment checking
                EntailmentChecker checker = new EntailmentChecker( reasoner );
                int amnt_entailed_ins = 0;
                int amnt_not_entailed_del = 0;

                for ( OWLAxiom a : insert_axioms ) {
                    if ( checker.isEntailed( new HashSet< OWLAxiom >( Arrays.asList( a ) ) ) ) {
                        ++amnt_entailed_ins;
                    }
                }

                for ( OWLAxiom a : Ad_ ) {
                    if ( !( checker.isEntailed( new HashSet< OWLAxiom >( Arrays.asList( a ) ) ) ) ) {
                        ++amnt_not_entailed_del;
                    }
                }

                if ( SparqlUpdater.verbose_level > 1 ) {
                    System.out.println( "Insert axioms: " + insert_axioms.size() );
                    System.out.println( "Entailed: " + amnt_entailed_ins );
                    System.out.println( "Delete axioms: " + Ad_.size() );
                    System.out.println( "Not entailed: " + amnt_not_entailed_del );
                }

                output.delete(); // Deletes from file system

                int sum = amnt_entailed_ins + amnt_not_entailed_del;

                if ( sum > current_best ) {
                    best_implementations.clear();
                    current_best = sum;
                    best_implementations.add( new Implementation( hs, dbg ) );
                }
                else if ( sum == current_best ) {
                    best_implementations.add( new Implementation( hs, dbg ) );
                }

                if ( SparqlUpdater.verbose_level > 1 && SparqlUpdater.user_input ) {
                    System.out.println( "Press \"ENTER\" to continue..." );
                    scanner = new Scanner( System.in );
                    scanner.nextLine();
                }

                // Need to add these back to the ontology so that other entailment checks for other debuggings still use the original ontology...
                // Again, if there are no debuggings, this will add an empty axiom, hence nothing changes.
                manager.addAxioms( ontology, dbg.set() );
            }
        }

        if ( SparqlUpdater.verbose_level > 1 ) {
            System.out.println( "Best: " + current_best );
        }

        HittingSet< OWLAxiom > best_deletion = new HittingSet< OWLAxiom >();
        HittingSet< OWLAxiom > best_debug = new HittingSet< OWLAxiom >();

        if ( SparqlUpdater.benchmark ) {
            if ( best_implementations.isEmpty() || ( best_implementations.size() == 1 && best_implementations.get( 0 ).del_.isEmpty() ) ) {
                stats.append( "0|" ); // no hitting sets

                if ( !Thread.currentThread().isInterrupted() ) {
                    int count = ways_to_delete.containsKey( 0 ) ? ways_to_delete.get( 0 ) : 0;
                    ways_to_delete.put( 0, count + 1 );
                    count = assertions_to_delete.containsKey( 0 ) ? assertions_to_delete.get( 0 ) : 0;
                    assertions_to_delete.put( 0, count + 1 );
                }
            }
            else {
                stats.append( String.valueOf( best_implementations.size() ) );

                // There should be no debugging hitting set since we don't do insertions for benchmarks
                for ( Implementation impl : best_implementations ) {
                    stats.append( "|" + impl.del_.size() ); // left is the deletion
                    int count = assertions_to_delete.containsKey( impl.del_.size() ) ? assertions_to_delete.get( impl.del_.size() ) : 0;
                    assertions_to_delete.put( impl.del_.size(), count + 1 );
                }

                int count = ways_to_delete.containsKey( best_implementations.size() ) ? ways_to_delete.get( best_implementations.size() ) : 0;
                ways_to_delete.put( best_implementations.size(), count + 1 );
            }

            // Doesn't matter what is returned, won't be used. _stats_ matters and has been written to!
            return new ArrayList< Implementation >();
        }

        return best_implementations;
    }
}
