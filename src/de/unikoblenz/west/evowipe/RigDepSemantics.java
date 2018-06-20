package de.unikoblenz.west.evowipe;

import java.util.Set;
import java.util.List;
import java.util.HashMap;
import java.util.ArrayList;
import java.util.Scanner;
import java.util.Iterator;

import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.ImmutablePair;
import org.apache.commons.lang3.StringUtils;

import org.semanticweb.owlapi.model.OWLAxiom;
import com.clarkparsia.pellet.sparqldl.jena.SparqlDLExecutionFactory;
import com.clarkparsia.owlapiv3.OWL;
import com.clarkparsia.owlapiv3.OntologyUtils;
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
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLAnnotation;
import org.semanticweb.owlapi.model.OWLAnnotationProperty;
import org.semanticweb.owlapi.model.OWLAnnotationValue;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import uk.ac.manchester.cs.owl.owlapi.OWLClassAssertionAxiomImpl;
import org.semanticweb.owlapi.search.EntitySearcher;
import org.semanticweb.owlapi.model.AxiomType;
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
import org.semanticweb.owlapi.formats.RDFXMLDocumentFormat;
import org.semanticweb.owlapi.model.IRI;
import com.clarkparsia.pellet.owlapiv3.EntailmentChecker;
import org.mindswap.pellet.utils.FileUtils;
import org.mindswap.pellet.jena.PelletReasonerFactory;
import com.clarkparsia.pellet.sparqldl.jena.SparqlDLExecutionFactory;
// !!!! if you change the JENA version to 3 upwards, need to use these imports: !!!!
//import org.apache.jena.rdf.model.Statement;
//import org.apache.jena.rdf.model.RDFNode;
//import org.apache.jena.rdf.model.Resource;
//import org.apache.jena.rdf.model.Property;
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
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.StmtIterator;


// TODO tidy up imports 

/**
 * @brief Rigidity- and Dependency-Guided Semantics
 *
 * In the context of product development, it is desirable to combine the behavior of rigidity-guided and dependency-guided contraction.
 * For this, we have to take the following into account:
 * The cascading deletions caused by the dependency-guided contraction can lead to the contraction of rigid assertions which leads to the contraction of all assertions containing certain individuals. This can result into the violation of dependencies.
 */
public class RigDepSemantics implements Semantics {
    private String original_update_;
    private OWLOntology ontology_ = null;
    private OWLOntologyManager manager_ = null;
    private OntModel jena_m_;
    private String ontology_path_;
    private int recursion_depth_;
    static Set< OWLAxiom > to_be_deleted = new HashSet< OWLAxiom >();

    // This was taken from Stack Overflow:
    // https://stackoverflow.com/questions/426878/is-there-any-way-to-do-n-level-nested-loops-in-java
    // Cheers
    private static class NestedFor {
        public static interface IAction {
            public void act(int[] indices);
        }

        private final int lo;
        private final int hi;
        private final IAction action;

        public NestedFor(int lo, int hi, IAction action) {
            this.lo = lo;
            this.hi = hi;
            this.action = action;
        }

        public void nFor (int depth) {
            n_for (0, new int[0], depth);
        }

        private void n_for (int level, int[] indices, int maxLevel) {
            if (level == maxLevel) {
                action.act(indices);
            }
            else {
                int newLevel = level + 1;
                int[] newIndices = new int[newLevel];
                System.arraycopy(indices, 0, newIndices, 0, level);
                newIndices[level] = lo;
                while (newIndices[level] < hi) {
                    n_for(newLevel, newIndices, maxLevel);
                    ++newIndices[level];
                }
            }
        }
    }

    /**
     * @brief Class constructor. Performs basic setup of member variables.
     * @param ontology_path the system file path to the knowledge base file.
     * @param original_update the original update to be performed by the system
     * @param recursion_depth larger than 0 if recursive call of the filter method
     * @throws RuntimeException if can't load ontology from file
     */
    public RigDepSemantics( String ontology_path, String original_update, int recursion_depth ) {
        ontology_path_ = ontology_path;
        manager_ = OWLManager.createOWLOntologyManager();
        File file = new File( ontology_path );

        // Create OWL ontology from file path; for retrieving rigid concepts
        try {
            ontology_ = manager_.loadOntologyFromOntologyDocument( file );
        }
        catch ( OWLOntologyCreationException e ) {
            throw new RuntimeException( "Could not create temporary OWL ontology: " + e );
        }

        // Create a Jena ontology model backed by the Pellet reasoner; for running a SparqlDL construct query
        // (note, the Pellet reasoner is required)
        jena_m_ = ModelFactory.createOntologyModel( PelletReasonerFactory.THE_SPEC );

        // Then read the data from the file into the ontology model
        jena_m_.read( ontology_path );
        original_update_ = original_update;

        original_update_ = original_update;
        recursion_depth_ = recursion_depth;
    }

    /**
     * @brief Recursively delete an axiom for which a dependency has been violated.
     * @param axiom the axiom in question
     * @param ontology the current ontology, usually NOT EQUAL to the original ontology (already has some axioms removed).
     * @return a set of possible implementations for this deletion (formally; naturally there will be no insertions, hence no debugging)
     */
    private Set< Implementation > recurseDel( OWLAxiom axiom, OWLOntology ontology ) {
        to_be_deleted.add( axiom ); // Don't try to delete this again

        if ( SparqlUpdater.verbose_level > 1 ) {
            for ( int i = 0; i < recursion_depth_; ++i ) {
                System.out.print( "\t" );
            }

            System.out.print( "========== RECURSE ==========\n" );
        }

        File output = null;

        // If this throws, abort everything:
        try {
            OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
            output = File.createTempFile( "tmp", "owl" );
            IRI documentIRI2 = IRI.create( output );
            manager.saveOntology( ontology, new RDFXMLDocumentFormat(), documentIRI2 );
        // ^ save ontology so that we can read it again. Awkward way to do it, but that's how we can make the recursion work.
        }
        catch ( Exception e ) {
            SparqlUpdater.logger.severe( "Problem in recurseDel(): " + e );
            return null;
        }

        // Get hitting sets for deletion
        Set< OWLAxiom > insert_axioms = new HashSet< OWLAxiom >(); // no insertions, naturally; this is just because we're calling a function that normally would expect insertions as well
        String ontology_path = output.getAbsolutePath();

        AxiomJustificator justificator = new AxiomJustificator( axiom, ontology_path, 100, "glass" );
        Set< Justification > justifications = justificator.computeJustifications(); // NOTE THAT THIS WILL NOT CONTAIN TBOX-ASSERTIONS (i.e. subClassOf, sameAs, ...)

        // Next, we should minimize this set of justifications, i.e. make it a set of root justifications.
        Set< Justification > root_justifications = Justification.minimize( justifications );

        // Compute minimal hitting sets of these root justifications
        SortedSet< WrappedSet< OWLAxiom > > wrapped_sets_of_axioms = new TreeSet< WrappedSet< OWLAxiom > >();

        for ( Justification justification : root_justifications ) {
            wrapped_sets_of_axioms.add( new WrappedSet< OWLAxiom >( justification ) );
        }

        // Note to self: These minimal hitting sets will always have at least 1 element for some weird reason.
        Set< HittingSet< OWLAxiom > > delete_axioms = HittingSet.constructMinimalHittingSets( wrapped_sets_of_axioms );

        Semantics semantics = new RigDepSemantics( ontology_path, original_update_, recursion_depth_ + 1 );

        // dummy objects, not used afterwards
        StringBuilder stats = new StringBuilder( "" );
        HashMap< Integer, Integer > ways_to_delete = new HashMap< Integer, Integer >();
        HashMap< Integer, Integer > assertions_to_delete = new HashMap< Integer, Integer >();

        List< Implementation > implementations = semantics.filter( delete_axioms, insert_axioms, stats, ways_to_delete, assertions_to_delete );
        output.delete();

        return new HashSet< Implementation >( implementations );
    }

    /**
     * @brief Applies rigidity- and dependency-guided semantics to hitting sets of axioms.
     * @param delete_axioms hitting sets of axioms to be deleted
     * @param insert_axioms set of axioms to be inserted
     * @param stats, ways_to_delete, assertions_to_delete ONLY used in benchmark mode. Stores statistics for semantics
     * @return a list of implementations, for each of which the first element is the selected deletion, and the second element is the debugging step after the insertion.
     */
    @Override
    public List< Implementation > filter( Set< HittingSet< OWLAxiom > > delete_axioms, Set< OWLAxiom > insert_axioms, StringBuilder stats, HashMap< Integer, Integer > ways_to_delete, HashMap< Integer, Integer > assertions_to_delete ) {
        if ( SparqlUpdater.verbose_level > 0 && recursion_depth_ == 0 ) {
            System.out.println( "========== RIGIDITY- AND DEPENDENCY-GUIDED SEMANTICS ==========" );
        }

        Scanner scanner = null;

        if ( delete_axioms.isEmpty() ) {
            if ( SparqlUpdater.benchmark && recursion_depth_ == 0 ) {
                stats.append( "-2|" ); // no hitting sets

                int count = ways_to_delete.containsKey( 0 ) ? ways_to_delete.get( 0 ) : 0;
                ways_to_delete.put( 0, count + 1 );
                count = assertions_to_delete.containsKey( 0 ) ? assertions_to_delete.get( 0 ) : 0;
                assertions_to_delete.put( 0, count + 1 );

                return new ArrayList< Implementation >();
            }

            // If there are neither insertions nor deletions, nothing should be returned
            if ( insert_axioms.isEmpty() ) {
                return new ArrayList< Implementation >();
            }

            delete_axioms.add( new HittingSet< OWLAxiom >() ); // add empty hitting set, so that loop is still executed once
        }

        // If insertions are empty, there will be no debugging, but due to dependency cascading there may still be more deletions than for other hitting sets

        Set< Implementation > best_implementations = new HashSet< Implementation >();

        for ( HittingSet< OWLAxiom > hs : delete_axioms ) {
            OWLOntology ontology = null;
            OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
            File file = new File( ontology_path_ );

            try {
                ontology = manager.loadOntologyFromOntologyDocument( file );
            }
            catch ( OWLOntologyCreationException e ) {
                SparqlUpdater.logger.severe( "Could not create temporary OWL ontology: " + e );
                break;
            }

            if ( SparqlUpdater.verbose_level > 1 ) {
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
                break;
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

            // In case that there is no debugging to be done, coincidentally, the above function call returns a hitting set with an empty axiom. Hence this loop will be executed, but no actual debugging is performed.
            for ( HittingSet< OWLAxiom > dbg : minimal_hitting_sets ) {
                if ( SparqlUpdater.verbose_level > 1 ) {
                    for ( int i = 0; i < recursion_depth_; ++i ) {
                        System.out.print( "\t" );
                    }

                    System.out.print( "Debugging set:\n" );
                    dbg.printAxioms( recursion_depth_ );
                }

                manager.removeAxioms( ontology, dbg.set() );
                Set< OWLAxiom > cascaded = cascade( ontology, ontology_, manager_, hs, insert_axioms, dbg, original_update_ ); //= new Implementation( (hs, dbg) + cascaded );

                Set< OWLAxiom > new_through_cascade = new HashSet< OWLAxiom >( cascaded );
                Implementation tmp_impl = new Implementation();
                tmp_impl.success_ = new HashSet< OWLAxiom >( cascaded );

                if ( SparqlUpdater.verbose_level > 1 ) {
                    for ( int i = 0; i < recursion_depth_; ++i ) {
                        System.out.print( "\t" );
                    }

                    System.out.print( "Cascaded:\n" );
                }

                HittingSet< OWLAxiom > more_tmp = new HittingSet< OWLAxiom >( tmp_impl.success_ );

                if ( SparqlUpdater.verbose_level > 1 ) {
                    more_tmp.printAxioms( recursion_depth_ );
                }

                new_through_cascade.addAll( rigidRemoved( tmp_impl ) );
                new_through_cascade.removeAll( dbg.set() );
                new_through_cascade.removeAll( hs.set() );

                if ( SparqlUpdater.verbose_level > 1 ) {
                    for ( int i = 0; i < recursion_depth_; ++i ) {
                        System.out.print( "\t" );
                    }

                    System.out.print( "New through cascade (after rigid removal):\n" );
                }

                more_tmp = new HittingSet< OWLAxiom >( new_through_cascade );

                if ( SparqlUpdater.verbose_level > 1 ) {
                    more_tmp.printAxioms( recursion_depth_ );
                }

                if ( new_through_cascade.isEmpty() ) {
                    Implementation tracker = new Implementation( hs, dbg );
                    tracker.success_.addAll( cascaded );

                    // Add rigid deletions
                    tracker.success_.addAll( rigidRemoved( tracker ) );

                    boolean should_add = true;

                    // This iteratively removes all implementations being supersets of the current implementation, and ultimately
                    // flags the current implementation to be added if there is no other currently recorded implementation that is
                    // in a fact a subset (only in that case we are minimal).
                    for ( Iterator< Implementation > iterator = best_implementations.iterator(); iterator.hasNext(); ) {
                        Implementation other = iterator.next();
                        boolean first_pass = false;

                        // Check if we are a subset
                        if ( other.success_.containsAll( tracker.success_ ) ) {
                            first_pass = true;
                        }

                        if ( tracker.success_.containsAll( other.success_ ) ) {
                            if ( first_pass ) {
                                // Sets are equal. Keep both
                            }
                            else {
                                // We are not minimal since the other is a subset of us
                                should_add = false;
                                break; // It's not possible for another implementation to be here that's not minimal, so we may stop.
                            }
                        }
                        // If the other contains us, and we don't contain it:
                        // The other is NOT minimal.
                        else if ( first_pass ) {
                            iterator.remove();
                        }
                    }

                    if ( should_add ) {
                        best_implementations.add( tracker );
                    }
                }
                else {
                    /*
                    for ( OWLAxiom new_a : new_through_cascade ) {
                        Set< Implementation > hsets_new_a = recurseDel( new_a, ontology ); // need to use updated ontology to avoid deadlocks!

                        for ( Implementation impl : hsets_new_a ) {
                            Implementation tracker = new Implementation( hs, dbg );
                            tracker.success_.addAll( cascaded );
                            tracker.success_.addAll( impl.success_ );
                            boolean should_add = true;


                            if ( should_add ) {
                                best_implementations.add( tracker );
                            }
                        }
                    }
                }
                */
                    // It is required that we perform a recursive deletion of all axioms that were newly added by the cascading operation.
                    List< List< Implementation > > ntc_impls = new ArrayList< List< Implementation > >();

                    for ( OWLAxiom new_a : new_through_cascade ) {
                        // If there is any bug, the following three lines are probably the first thing you should try removing and see if that fixes it
                        //if ( to_be_deleted.contains( new_a ) ) {
                        //   continue;
                        //}

                        List< Implementation > tmp = new ArrayList< Implementation >( recurseDel( new_a, ontology ) );
                        
                        if ( !tmp.isEmpty() ) {
                            ntc_impls.add( tmp );
                        }
                    }

                    // Print what's new (if sufficient verbosity)
                    if ( SparqlUpdater.verbose_level > 2 ) {
                        for ( List< Implementation > simpl : ntc_impls ) {
                            for ( Implementation hm : simpl ) {
                                for ( int i = 0; i < recursion_depth_; ++i ) {
                                    System.out.print( "\t" );
                                }

                                System.out.print( "==== NTC-Impl ====\n" );
                                hm.del_.printAxioms( recursion_depth_ );

                                for ( int i = 0; i < recursion_depth_; ++i ) {
                                    System.out.print( "\t" );
                                }

                                System.out.print( "  ==\n" );
                                SparqlUpdaterImpl.printAxiomSet( hm.success_, recursion_depth_ );
                            }
                        }
                    }

                    // The next part is a little tricky, we need to find all combinations of implementations of different axioms to be deleted. All combinations form new implementations to be added to the candidates list.
                    // This requires a nested for loop of a size we don't know on compile-time.
                    List< Implementation > sim_combineds = new ArrayList< Implementation >();

                    if ( !ntc_impls.isEmpty() ) {
                        NestedFor.IAction testAction = new NestedFor.IAction() {
                            public void act(int[] indices) {
                                    Implementation sim_combined = new Implementation();

                                    for ( int d = 0; d < ntc_impls.size(); ++d ) {

                                        try {
                                            Implementation sim = ntc_impls.get( d ).get( indices[ d ] );
                                            sim_combined.del_.merge( sim.del_ );
                                            sim_combined.dbg_.merge( sim.dbg_ );
                                            sim_combined.success_.addAll( sim.success_ );
                                        }
                                        catch ( Exception e ) {
                                            SparqlUpdater.logger.warning( "Indices out of range in nested for" );
                                        }
                                    }

                                    sim_combineds.add( sim_combined );
                            }
                        };

                        NestedFor nf = new NestedFor(0, ntc_impls.get( ntc_impls.size() - 1 ).size(), testAction);
                        nf.nFor( ntc_impls.size() );
                    }

                    // We can then filter the resulting implementations w.r.t. minimal sets
                    for ( Implementation impl : sim_combineds ) {
                        Implementation tracker = new Implementation( hs, dbg );
                        tracker.success_.addAll( cascaded );
                        tracker.success_.addAll( impl.success_ );

                        // Add rigid deletions
                        tracker.success_.addAll( rigidRemoved( tracker ) );

                        boolean should_add = true;

                        // This iteratively removes all implementations being supersets of the current implementation, and ultimately
                        // flags the current implementation to be added if there is no other currently recorded implementation that is
                        // in fact a subset (only in that case we are minimal).
                        for ( Iterator< Implementation > iterator = best_implementations.iterator(); iterator.hasNext(); ) {
                            Implementation other = iterator.next();
                            boolean first_pass = false;

                            // Check if we are a subset
                            if ( other.success_.containsAll( tracker.success_ ) ) {
                                first_pass = true;
                            }

                            if ( tracker.success_.containsAll( other.success_ ) ) {
                                if ( first_pass ) {
                                    // Sets are equal. Don't add
                                    should_add = false;
                                }
                                else {
                                    // We are not minimal since the other is a subset of us
                                    should_add = false;
                                    break; // It's not possible for another implementation to be here that's not minimal, so we may stop.
                                }
                            }
                            // If the other contains us, and we don't contain it:
                            // The other is NOT minimal.
                            else if ( first_pass ) {
                                iterator.remove();
                            }
                        }

                        if ( should_add ) {
                            best_implementations.add( tracker );
                        }
                    }
                }

                manager.addAxioms( ontology, dbg.set() );

                if ( SparqlUpdater.verbose_level > 1 && SparqlUpdater.user_input ) {
                    System.out.println( "Press \"ENTER\" to continue..." );
                    scanner = new Scanner( System.in );
                    scanner.nextLine();
                }
            }
        }

        HittingSet< OWLAxiom > best_deletion = new HittingSet< OWLAxiom >();
        HittingSet< OWLAxiom > best_debug = new HittingSet< OWLAxiom >();
        ArrayList< Implementation > best_as_array = new ArrayList< Implementation >( best_implementations );

        if ( SparqlUpdater.benchmark && recursion_depth_ == 0 ) {
            if ( best_as_array.isEmpty() || ( best_as_array.size() == 1 && best_as_array.get( 0 ).del_.isEmpty() ) ) { // happens when axiom to be deleted does not exist in ontology
                stats.append( "-1|" ); // no hitting sets

                int count = ways_to_delete.containsKey( 0 ) ? ways_to_delete.get( 0 ) : 0;
                ways_to_delete.put( 0, count + 1 );
                count = assertions_to_delete.containsKey( 0 ) ? assertions_to_delete.get( 0 ) : 0;
                assertions_to_delete.put( 0, count + 1 );
            }
            else {
                stats.append( String.valueOf( best_as_array.size() ) );

                // There should be no debugging hitting set since we don't do insertions for benchmarks
                for ( Implementation impl : best_as_array ) {
                    stats.append( "|" + impl.success_.size() ); // cascaded deletions...
                    int count = assertions_to_delete.containsKey( impl.success_.size() ) ? assertions_to_delete.get( impl.success_.size() ) : 0;
                    assertions_to_delete.put( impl.success_.size(), count + 1 );
                }

                int count = ways_to_delete.containsKey( best_as_array.size() ) ? ways_to_delete.get( best_as_array.size() ) : 0;
                ways_to_delete.put( best_as_array.size(), count + 1 );
            }

            //return best_as_array;
            // Doesn't matter what is returned, won't be used. _stats_ matters and has been written to!
            //return new ArrayList< Implementation >();
        }

        //if ( SparqlUpdater.verbose_level > 0 && recursion_depth_ > 0 ) {
        if ( SparqlUpdater.verbose_level > 1 ) {
            for ( int i = 0; i < recursion_depth_; ++i ) {
                System.out.print( "\t" );
            }

            System.out.print( "Implementations:\n" );

            for ( Implementation impl_ : best_as_array ) {
                impl_.del_.printAxioms( recursion_depth_ );

                for ( int i = 0; i < recursion_depth_; ++i ) {
                    System.out.print( "\t" );
                }

                System.out.print( "  ==\n" );
                SparqlUpdaterImpl.printAxiomSet( impl_.success_, recursion_depth_ );

            }
        }

        return best_as_array;
    }

    /**
     * @brief Used for checking if a dependency (C,D,R) in Dep(K) for C(a) satisfies the criteria to be removed
     * @param manager The ontology manager for the input ontology
     * @param ontology The input ontology; either A' or A'\Re (see function below this one)
     * @param a The individual
     * @param D The class that C is dependent on
     * @param R The property w.r.t. which C is dependent on D
     * @param original_update The original update to performed by the entire program, used for extracting prefixes
     * @return True if there is an individual from D for which R(a,d) is entailed by the input ontology
     *
     * Criteria that can be evaluated with this function:
     *
     * 1. There exists an individual b so that (R,T,A') entails D(b) and (R,T,A') entails R(a,b) ----- depsat(A',D,R) == true
     * 2. There is no individual c so that (R,T, A'\Re) entails D(c) and (R,T,A'\Re) entails R(a,c) ------ depsat(A'\Re,D,R) == false
     */
    private static boolean depsat( OWLOntologyManager manager, OWLOntology ontology, OWLIndividual a, OWLClass D, OWLObjectProperty R, String original_update ) {
    // 1. construct D(d) where D(d)
        File output = null;

        try {
            output = File.createTempFile( "tmp", "owl" );
            IRI documentIRI2 = IRI.create( output );
            manager.saveOntology( ontology, new RDFXMLDocumentFormat(), documentIRI2 );
        }
        catch ( Exception e ) {
            throw new RuntimeException( e.getMessage() );
        }

		// Create a Jena ontology model backed by the Pellet reasoner; for running a SparqlDL construct query
		// (note, the Pellet reasoner is required)
		OntModel jena_m = ModelFactory.createOntologyModel( PelletReasonerFactory.THE_SPEC );

		// Then read the data from the file into the ontology model
		jena_m.read( output.getAbsolutePath() );

        // Build construct query as string
        int delete_index = original_update.toLowerCase().indexOf( "delete" );

        // Defensive programming
        if ( delete_index == -1 ) {
            output.delete(); // Deletes from file system
            throw new RuntimeException( "Constructing construct query failed. Could not find index for \"DELETE\" in original update string." );
        }

        // Construct construct (heh)
        String head = original_update.substring( 0, delete_index ); // Everything up to "DELETE"
        String construct = new StringBuilder()
                           .append( "CONSTRUCT { " )
                           .append( "?d a <" + D.getIRI() + "> }" )
                           .toString();

        String construct_rad = new StringBuilder()
                               .append( head )
                               .append( construct )
                               .append( "\n" + construct.replace( "CONSTRUCT", "WHERE" ) ).toString();

        if ( SparqlUpdater.verbose_level > 3 ) {
            System.out.println( construct_rad );
        }

        Query q = QueryFactory.create( construct_rad );

        // Create a SPARQL-DL query execution for the given query and ontology model
        QueryExecution qe = SparqlDLExecutionFactory.create( q, jena_m );

        // Defensive programming
        if ( !qe.getQuery().isConstructType() ) {
            output.delete(); // Deletes from file system
            throw new RuntimeException( "Constructed construct query for finding R(a, d) is not a valid construct query!" );
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

    // 2. Get DInd from graph
        Set< OWLIndividual > DInd = new HashSet< OWLIndividual >();

        // Iterate over all statements of the constructed RDF graph.
        StmtIterator stmts = model.listStatements();

        while ( stmts.hasNext() ) {
            Statement stmt = stmts.next();
            OWLAxiom axiom = AxiomConverter.convert( stmt, ontology );
            Resource s = stmt.getSubject();
            String subject_string = s.toString();
            OWLEntity subject = OntologyUtils.findEntity( subject_string, ontology );

            if ( subject == null ) {
                output.delete(); // Deletes from file system
                throw new RuntimeException( "Undefined entity: " + subject_string );
            }
            else if ( !subject.isOWLNamedIndividual() ) {
                output.delete(); // Deletes from file system
                throw new RuntimeException( "Not an individual: " + subject_string );
            }

            DInd.add( ( OWLIndividual ) subject );
        }

    // 3. Check if R(a, d) is entailed
        PelletReasoner reasoner = null;

        try {
            KBLoader kbloader = new OWLAPILoader();
            OWLAPILoader loader = ( OWLAPILoader ) kbloader;
            KnowledgeBase kb = kbloader.createKB( new String[] { output.getAbsolutePath() } );
            reasoner = loader.getReasoner();
        }
        catch ( Exception e ) {
            output.delete(); // Deletes from file system
            throw new RuntimeException( e.getMessage() + "====" + e.getCause().getMessage() );
        }

        output.delete(); // Deletes from file system

        EntailmentChecker checker = new EntailmentChecker( reasoner );

        for ( OWLIndividual d : DInd ) {
            OWLAxiom r_a_d = OWL.propertyAssertion( a, R, d ); // TODO ?

            if ( checker.isEntailed( new HashSet< OWLAxiom >( Arrays.asList( r_a_d ) ) ) ) {
                return true;
            }
        }

        return false;
    }

    /**
     * @brief An implementation of the Cascade_i operator
     * @param ontology An ontology (R, T, A') to perform the operation on
     * @param K The original ontology K = (R, T, A) that should be updated
     * @param Kmanager The ontology manager object for _original_ontology_
     * @param Del A deletion to be performed
     * @param Ai An insertion to be performed
     * @param Dbg The debugging step performed after deleting and inserting (in that order)
     * @param original_update The original update to performed by the entire program, used for extracting prefixes
     * @return All removed axioms PLUS cascaded deletions
     *
     * Cascading deletions denote repeated deletions caused by dependencies between deleted concepts w.r.t. roles.
     */
    private static Set< OWLAxiom > cascade( OWLOntology ontology, OWLOntology K, OWLOntologyManager Kmanager, HittingSet< OWLAxiom > Del, Set< OWLAxiom > Ai, HittingSet< OWLAxiom > Dbg, String original_update ) {
        // Calculate what's been deleted
        //Set< OWLAxiom > abox = ontology.aboxAxioms().collect( Collectors.toList() );
        //Set< OWLAxiom > original_abox = ontology.aboxAxioms().collect( Collectors.toList() );
        final OWLAnnotationProperty comment = Kmanager.getOWLDataFactory().getRDFSComment();
        //Set< OWLAxiom > new_abox = K.getABoxAxioms( Imports.INCLUDED );
        //Set< OWLAxiom > A = K.getABoxAxioms( Imports.INCLUDED );
        Set< OWLAxiom > K_expanded = new HashSet< OWLAxiom >( K.getABoxAxioms( Imports.INCLUDED ) );
        K_expanded.addAll( Ai );
        Set< OWLAxiom > new_abox = new HashSet< OWLAxiom >( K_expanded );
        Set< OWLAxiom > A = new HashSet< OWLAxiom >( K_expanded );
        Set< OWLAxiom > Re = new HashSet< OWLAxiom >( K_expanded );//K.getABoxAxioms( Imports.INCLUDED );
        //Re.addAll( Ai );
        Re.removeAll( ontology.getABoxAxioms( Imports.INCLUDED ) ); // TODO VERY INEFFICIENT, I am 100% sure this could be done way faster by not even looking at the ontology
        Set< OWLAxiom > Casc = null;

        do {
            Casc = new HashSet< OWLAxiom >(); // empty set

            for ( OWLAxiom Ca : A ) {
                if ( Ca.isOfType( AxiomType.CLASS_ASSERTION ) ) {
                    OWLClassAssertionAxiomImpl class_ass = ( OWLClassAssertionAxiomImpl ) Ca;
                    OWLClass C = class_ass.getClassExpression().asOWLClass();
                    OWLIndividual a = class_ass.getIndividual();

                    if ( SparqlUpdater.verbose_level > 3 ) {
                        System.out.println( "Class: " + C.toString() );
                        System.out.println( "Axiom: " + Ca.toString() );
                    }

                    // Get all comment annotations for this class and check for comments that say "rigid" (has to be modeled accordingly)
                    for ( OWLAnnotation anno : EntitySearcher.getAnnotations( C, K, comment ) ) {
                        OWLAnnotationValue val = anno.getValue();

                        if ( val instanceof OWLLiteral ) {
                            String literal = ( ( OWLLiteral ) val ).getLiteral();
                            int count_depend = StringUtils.countMatches( literal, "dependOn" );

                            if ( count_depend > 0 ) {
                                String[] split = literal.split( "\\s+" );

                                if ( split.length != 4 * count_depend ) { // needs to be e.g. "dependOn D w.r.t. R", always exactly 4 elements or e.g. 8 for two dependencies
                                    SparqlUpdater.logger.warning( "[WARNING] \"" + literal + "\" is not a valid dependency annotation" );
                                    continue;
                                }

                                for ( int i = 0; i < split.length; i += 4 ) {
                                    String dep_class = split[ i + 1 ];
                                    String dep_role = split[ i + 3 ];
                                    OWLClass D = null;
                                    OWLObjectProperty R = null;

                                    // Get actual class and role from ontology
                                    D = Kmanager.getOWLDataFactory().getOWLClass( IRI.create( C.getIRI().getNamespace() + dep_class ) );
                                    R = Kmanager.getOWLDataFactory().getOWLObjectProperty( IRI.create( C.getIRI().getNamespace() + dep_role ) );

                                    if ( !K.containsClassInSignature( D.getIRI() ) ) {
                                        SparqlUpdater.logger.warning( "[WARNING] \"" + dep_class + "\" in dependency annotation \"" + literal + "\" does not exist in the input ontology." );
                                        continue;
                                    }

                                    if ( !K.containsObjectPropertyInSignature( R.getIRI() ) ) {
                                        SparqlUpdater.logger.warning( "[WARNING] \"" + dep_role + "\" in dependency annotation \"" + literal + "\" does not exist in the input ontology." );
                                        continue;
                                    }

                                    if ( SparqlUpdater.verbose_level > 1 ) {
                                        System.out.println( C.getIRI().getFragment() + " commented dependent on " + D.getIRI().getFragment() + " w.r.t. role " + R.getIRI().getFragment() + "." );
                                    }

                                    OWLOntologyManager A__manager = null;
                                    OWLOntology A_ = null;
                                    OWLOntologyManager A_Re_manager = null;
                                    OWLOntology A_Re = null;

                                    try {
                                        A__manager = OWLManager.createOWLOntologyManager();
                                        A_ = A__manager.createOntology( IRI.create( "http://www.uni-koblenz.de/west/evowipe/A'.owl" ) );
                                        Set< OWLAxiom > to_add = new HashSet< OWLAxiom >( K.getAxioms() );

                                        // Remove ABox
                                        for ( Iterator< OWLAxiom > it = to_add.iterator(); it.hasNext(); ) {
                                            OWLAxiom ax = it.next();

                                            if ( ax.isOfType( AxiomType.ABoxAxiomTypes ) ) {
                                                it.remove();
                                            }
                                        }

                                        // Add everything except the ABox from the very original ontology
                                        A__manager.addAxioms( A_, to_add );

                                        // Add A', new ABox
                                        A__manager.addAxioms( A_, new_abox );

                                        A_Re_manager = OWLManager.createOWLOntologyManager();
                                        A_Re = A_Re_manager.createOntology( IRI.create( "http://www.uni-koblenz.de/west/evowipe/A'Re.owl" ) );

                                        // Add everything except the ABox from the very original ontology
                                        A_Re_manager.addAxioms( A_Re, to_add );

                                        // Add A' \ Re, new ABox
                                        Set< OWLAxiom > A_Re_ABox = new HashSet< OWLAxiom >( new_abox );
                                        A_Re_ABox.removeAll( Re );
                                        A_Re_manager.addAxioms( A_Re, A_Re_ABox );
                                    }
                                    catch ( OWLOntologyCreationException e ) {
                                        throw new RuntimeException( e.getMessage() );
                                    }

                                    boolean depsat1 = depsat( A__manager, A_, a, D, R, original_update );
                                    boolean depsat2 = depsat( A_Re_manager, A_Re, a, D, R, original_update );

                                    if ( SparqlUpdater.verbose_level > 2 ) {
                                        System.out.println( "deperfüllt(A',D,R): " + depsat1);
                                        System.out.println( "deperfüllt(A'\\Re,D,R): " + depsat2);
                                    }

                                    if ( depsat1 && !depsat2 ) {
                                        if ( SparqlUpdater.verbose_level > 2 ) {
                                            System.out.println( "Adding " + Ca.toString() + " to Casc.");
                                        }

                                        Casc.add( Ca );
                                    }
                                }
                            }
                        }
                    }
                }
            }

            new_abox.removeAll( Re );
            Re.addAll( Casc );

            if ( SparqlUpdater.verbose_level > 2 ) {
                System.out.println( "Re \\cup Casc: " + Re.toString());
            }
        }
        while ( !Casc.isEmpty() );

        // Re is now all we remove, including cascaded dependency deletions.

        return Re;
    }

    private HashSet< OWLAxiom > rigidRemoved( Implementation del ) {
        final OWLAnnotationProperty comment = manager_.getOWLDataFactory().getRDFSComment();
        HashSet< OWLAxiom > rigid_axioms = new HashSet< OWLAxiom >();
        HashSet< OWLAxiom > rigid_removed = new HashSet< OWLAxiom >();

        for ( OWLAxiom a : del.success_ ) { // TODO is success_ correct to use or del_?
            // This could only apply to class assertions.
            if ( a.isOfType( AxiomType.CLASS_ASSERTION ) ) {
                OWLClassAssertionAxiomImpl class_ass = ( OWLClassAssertionAxiomImpl ) a;
                OWLClass cl = class_ass.getClassExpression().asOWLClass();

                if ( SparqlUpdater.verbose_level > 3 ) {
                    System.out.println( "Class: " + cl.toString() );
                    System.out.println( "Axiom: " + a.toString() );
                }

                // Get all comment annotations for this class and check for comments that say "rigid" (has to be modeled accordingly)
                for ( OWLAnnotation anno : EntitySearcher.getAnnotations( cl, ontology_, comment ) ) {
                    OWLAnnotationValue val = anno.getValue();

                    if ( val instanceof OWLLiteral && ( ( OWLLiteral ) val ).getLiteral().equals( "rigid" ) ) {
                        if ( SparqlUpdater.verbose_level > 1 ) {
                            System.out.println( cl + " commented rigid." );
                        }

                        rigid_axioms.add( a ); // Assemble all class assertion axioms containing rigid concepts
                    }
                }
            }
        }

        //if ( SparqlUpdater.verbose_level >= 0 && rigid_axioms.size() > 0 ) {
        //    System.out.println( "Current hitting set: " );
        //    hs.printAxioms();
        //}

        for ( OWLAxiom a : rigid_axioms ) {
            // Defensive programming
            if ( !a.isOfType( AxiomType.CLASS_ASSERTION ) ) {
                throw new RuntimeException( "Rigid axiom is not of type class assertion!" );
            }

            OWLClassAssertionAxiomImpl class_ass = ( OWLClassAssertionAxiomImpl ) a;
            OWLIndividual ind = class_ass.getIndividual();
            String individual_iri = ind.toStringID();

            HashSet< OWLAxiom > additional_deletions = deleteIndividual( individual_iri, "" );
            rigid_removed.addAll( additional_deletions ); // add additional deletions to del (hitting set candidate corresponding to this list of rigid axioms)
        }

        return rigid_removed;
    }

    /**
     * @brief Completely remove an individual from the ontology.
     * @param individual_iri the specific individual identifier
     * @param previous when recursively calling this function, this is the IRI for the individual of the caller
     * @return a set of additional deletions to make in order to completely remove the individual from the ontology
     */
    private HashSet< OWLAxiom > deleteIndividual( String individual_iri, String previous ) {
        // Build construct query as string
        int delete_index = original_update_.toLowerCase().indexOf( "delete" );

        // Defensive programming
        if ( delete_index == -1 ) {
            throw new RuntimeException( "Constructing construct query failed. Could not find index for \"DELETE\" in original update string." );
        }

        // Construct construct (heh)
        String head = original_update_.substring( 0, delete_index ); // Everything up to "DELETE"
        String construct = new StringBuilder()
                           .append( "CONSTRUCT { " )
                           .append( "<" + individual_iri + "> ?R ?X .\n" )
                           .append( "?Y ?S <" + individual_iri + "> .\n" )
                           .append( "<" + individual_iri + "> a ?Z }" )
                           .toString();

        String construct_delete_individual = new StringBuilder()
                                             .append( head )
                                             .append( construct )
                                             .append( "\n" + construct.replace( "CONSTRUCT", "WHERE" ) ).toString();

        if ( SparqlUpdater.verbose_level > 2 ) {
            System.out.println( construct_delete_individual );
        }

        Query q = QueryFactory.create( construct_delete_individual );

        // Create a SPARQL-DL query execution for the given query and ontology model
        QueryExecution qe = SparqlDLExecutionFactory.create( q, jena_m_ );

        // Defensive programming
        if ( !qe.getQuery().isConstructType() ) {
            throw new RuntimeException( "Constructed construct query for deleting individual is not a valid construct query!" );
        }

        // Execute query
        Model model = qe.execConstruct();
        String syntax = "TURTLE"; // also try "N-TRIPLE" and "RDF/XML-ABBREV"
        StringWriter out = new StringWriter();
        model.write( out, syntax );

        // Iterate over all statements of the constructed RDF graph.
        // Add "translated" OWLAxioms to list.
        HashSet< OWLAxiom > additional_deletions = new HashSet< OWLAxiom >();
        StmtIterator stmts = model.listStatements();

        while ( stmts.hasNext() ) {
            Statement stmt = stmts.next();
            String property_string = stmt.getPredicate().getLocalName();
            String class_string = stmt.getObject().toString();

            // Need to also delete equal individuals
            if ( property_string.equals( "sameAs" ) ) {
                // Goes both ways because of the symmetry in our construct query, hence "a sameAs b" and "b sameAs a" will come up, disregard the second one
                if ( class_string.equals( previous ) || class_string.equals( individual_iri ) ) {
                    continue;
                }

                additional_deletions.addAll( deleteIndividual( class_string, individual_iri ) ); // RECURSIVE CALL
            }

            try {
                additional_deletions.add( AxiomConverter.convert( stmt, ontology_ ) );
            }
            catch ( RuntimeException e ) {
                //System.out.println( e.getMessage() );
                // TODO ARGH this is bad. Could be something not related to the axiom conversion. But introducing an AxiomConvertException didn't work for some reason.
            }
        }

        return additional_deletions;
    }
}
