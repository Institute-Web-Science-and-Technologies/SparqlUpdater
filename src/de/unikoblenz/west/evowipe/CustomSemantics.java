package de.unikoblenz.west.evowipe;

import java.util.Set;
import java.util.List;
import java.util.ArrayList;
import java.util.Scanner;
import java.util.Iterator;
import java.util.stream.Collectors;

import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.ImmutablePair;

import org.semanticweb.owlapi.model.OWLAxiom;
import com.clarkparsia.pellet.sparqldl.jena.SparqlDLExecutionFactory;
import com.hp.hpl.jena.ontology.OntModel;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.update.UpdateAction;

import java.util.HashSet;
import java.util.HashMap;
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
 * First, a deletion is chosen with a type of semantics for deletion. After performing the insertion on the resulting ontology, a debugging step is chosen (if necessary) using another kind of deletion-semantics.
 *
 */
public class CustomSemantics implements Semantics {
    private String ontology_path_;
    private String method_;
    private Semantics custom1_;
    private Semantics custom2_;

    /**
     * @brief Class constructor. Performs basic setup of member variables.
     * @param ontology_path the system file path to the knowledge base file.
     * @param method method to use for explanation (glass box/black box)
     * @param custom1 Semantics for choosing deletions
     * @param custom2 Semantics for choosing debuggings
     */
    public CustomSemantics( String ontology_path, String method, String custom1, String custom2 ) {
        ontology_path_ = ontology_path;
        method_ = method;

        if ( custom1.equals( "max" ) ) {
            custom1_ = new MaxichoiceSemantics();
        }
        else if ( custom1.equals( "meet" ) ) {
            custom1_ = new MeetSemantics();
        }
        else {
            throw new IllegalArgumentException( "Custom1 argument " + custom1 + " is not valid!" );
        }

        if ( custom2.equals( "max" ) ) {
            custom2_ = new MaxichoiceSemantics();
        }
        else if ( custom2.equals( "meet" ) ) {
            custom2_ = new MeetSemantics();
        }
        else {
            throw new IllegalArgumentException( "Custom2 argument " + custom2 + " is not valid!" );
        }
    }

    /**
     * @brief Applies custom semantics.
     *
     * In cases when there is more than one possible way to delete or debug, users must choose between all possibilities.
     *
     * @param delete_axioms hitting sets of axioms to be deleted
     * @param insert_axioms set of axioms to be inserted
     * @param stats, ways_to_delete, assertions_to_delete ONLY used in benchmark mode. Stores statistics for semantics
     * @return a list of implementations, for each of which the first element is the selected deletion, and the second element is the debugging step after the insertion.
     */
    @Override
    public List< Implementation > filter( Set< HittingSet< OWLAxiom > > delete_axioms, Set< OWLAxiom > insert_axioms, StringBuilder stats, HashMap< Integer, Integer > ways_to_delete, HashMap< Integer, Integer > assertions_to_delete ) {
        if ( SparqlUpdater.verbose_level > 0 ) {
            System.out.println( "========== CUSTOM SEMANTICS ==========" );
        }

        List< Implementation > impls = custom1_.filter( delete_axioms, insert_axioms, stats, ways_to_delete, assertions_to_delete );

        if ( SparqlUpdater.benchmark  || impls.isEmpty() ) {
            return impls;
        }

        // For each deletion (there are no debuggings yet), perform inserts and add debugging hitting sets if necessary
        // This may introduce new implementations if there are multiple ways to debug
        List< Implementation > new_implementations = new ArrayList< Implementation >();

        for ( Implementation impl : impls ) {
            HittingSet< OWLAxiom > hs = impl.del_;

            OWLOntology ontology = null;
            OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
            File file = new File( ontology_path_ );

            try {
                ontology = manager.loadOntologyFromOntologyDocument( file );
            }
            catch ( OWLOntologyCreationException e ) {
               throw new RuntimeException( "Could not create temporary OWL ontology: " + e );
            }

            if ( SparqlUpdater.verbose_level > 1 ) {
                System.out.println( "Current hitting set for deletion: " );
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
                throw new RuntimeException( e );
            }

            if ( SparqlUpdater.verbose_level > 2 ) {
                System.out.println( output.getAbsolutePath() );
            }

            InconsistencyJustificator ijust = new InconsistencyJustificator( output.getAbsolutePath(), 10000, "glass" );
            Set< Justification > justifications = ijust.computeJustifications(); // NOTE THAT THIS WILL NOT CONTAIN TBOX-ASSERTIONS (i.e. subClassOf, sameAs, ...)

            // Minimize this set of justifications, i.e. make it a set of root justifications.
            justifications = Justification.minimize( justifications );

            if ( SparqlUpdater.verbose_level > 2 ) {
                Justification.print( justifications );
            }

            // Compute minimal hitting sets of these root justifications
            SortedSet< WrappedSet< OWLAxiom > > wrapped_sets_of_axioms = new TreeSet< WrappedSet< OWLAxiom > >();

            for ( Justification justification : justifications ) {
                wrapped_sets_of_axioms.add( new WrappedSet< OWLAxiom >( justification ) );
            }

            Set< HittingSet< OWLAxiom > > minimal_hitting_sets = HittingSet.constructMinimalHittingSets( wrapped_sets_of_axioms );

            // Choose debugging step according to second semantics argument
            List< Implementation > dbg = custom2_.filter( minimal_hitting_sets, insert_axioms, null, null, null );

            output.delete(); // Deletes from file system

            if ( dbg.size() == 1 ) {
                impl.dbg_ = dbg.iterator().next().del_; // Careful, the deletion of this filter pass is the debugging hitting set! _dbg__ is always empty here for maxichoice and meet, and no other semantics are allowed.
            }
            else if ( dbg.size() > 1 ) {
                Iterator< Implementation > iterator = dbg.iterator();

                // Add first debugging set to current implementation
                Implementation first = iterator.next();
                impl.dbg_ = first.del_; // Careful, the deletion of this filter pass is the debugging hitting set! _dbg__ is always empty here for maxichoice and meet, and no other semantics are allowed.

                // All the others are new implementations:
                while ( iterator.hasNext() ) {
                    Implementation i = iterator.next();
                    new_implementations.add( new Implementation( hs, i.del_ ) ); // Careful, the deletion of this implementation is the debugging hitting set! _dbg__ is always empty here for maxichoice and meet, and no other semantics are allowed.
                }
            }
            // else, there's no debugging, so we can leave the empty debugging set already in the implementation. No new implementations added either.
        }

        impls.addAll( new_implementations );
        impls = impls.stream().distinct().collect( Collectors.toList() );

        return impls;
    }
}
