package de.unikoblenz.west.evowipe;

import java.util.Set;
import java.util.List;
import java.util.HashMap;
import java.util.ArrayList;
import java.util.Scanner;
import java.util.Iterator;

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
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLAnnotation;
import org.semanticweb.owlapi.model.OWLAnnotationProperty;
import org.semanticweb.owlapi.model.OWLAnnotationValue;
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
 * @brief Semantics trying to minimize deletion of rigid concept assertions
 */
public class RigidSemantics implements Semantics {
    private String original_update_;
    private String ontology_path_;
    private OWLOntology ontology_ = null;
    private OWLOntologyManager manager_ = null;
    private OntModel jena_m_;

    /**
     * @brief Class constructor. Performs basic setup of member variables.
     * @param ontology_path the system file path to the knowledge base file.
     * @param original_update the original update to be performed by the system
     * @throws RuntimeException if can't load ontology from file
     */
    public RigidSemantics( String ontology_path, String original_update ) {
        manager_ = OWLManager.createOWLOntologyManager();
        File file = new File( ontology_path );
        ontology_path_ = ontology_path;

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
    }

    /**
     * @brief Applies rigid semantics to hitting sets of axioms.
     * @param delete_axioms hitting sets of axioms to be deleted
     * @param insert_axioms set of axioms to be inserted
     * @param stats, ways_to_delete, assertions_to_delete ONLY used in benchmark mode. Stores statistics for semantics
     * @return a list of implementations, for each of which the first element is the selected deletion, and the second element is the debugging step after the insertion.
     */
    @Override
    public List< Implementation > filter( Set< HittingSet< OWLAxiom > > delete_axioms, Set< OWLAxiom > insert_axioms, StringBuilder stats, HashMap< Integer, Integer > ways_to_delete, HashMap< Integer, Integer > assertions_to_delete ) {
        if ( SparqlUpdater.verbose_level > 0 ) {
            System.out.println( "========== RIGID SEMANTICS ==========" );
        }

        if ( delete_axioms.isEmpty() ) {
            stats.append( "0|" ); // no hitting sets

            int count = ways_to_delete.containsKey( 0 ) ? ways_to_delete.get( 0 ) : 0;
            ways_to_delete.put( 0, count + 1 );
            count = assertions_to_delete.containsKey( 0 ) ? assertions_to_delete.get( 0 ) : 0;
            assertions_to_delete.put( 0, count + 1 );

            return new ArrayList< Implementation >();
        }

        final OWLAnnotationProperty comment = manager_.getOWLDataFactory().getRDFSComment();
        HashMap< Integer, HittingSet< OWLAxiom > > rigid_map = new HashMap< Integer, HittingSet< OWLAxiom > >();

        // Throw together deletion and debugging hitting sets (benchmark mode has no insertions, hence no debugging is performed; we will use this anyway and just set it to be the same as _delete_axioms_)
        ArrayList< HittingSet< OWLAxiom > > del_cup_dbg = new ArrayList< HittingSet< OWLAxiom > >();

        // Non-benchmark only:
        ArrayList< Pair< HittingSet< OWLAxiom >, HittingSet< OWLAxiom > > > implementations = new ArrayList< Pair< HittingSet< OWLAxiom >, HittingSet< OWLAxiom > > >();

        // We're looking for comments (i.e. annotations) that mark a concept as rigid
        for ( HittingSet< OWLAxiom > hs : delete_axioms ) {
            HashSet< OWLAxiom > rigid_axioms = new HashSet< OWLAxiom >();

            for ( OWLAxiom a : hs ) {
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

            if ( SparqlUpdater.verbose_level >= 0 && rigid_axioms.size() > 0 ) {
                System.out.println( "Current hitting set: " );
                hs.printAxioms();
            }

            for ( OWLAxiom a : rigid_axioms ) {
                // Defensive programming
                if ( !a.isOfType( AxiomType.CLASS_ASSERTION ) ) {
                    throw new RuntimeException( "Rigid axiom is not of type class assertion!" );
                }

                OWLClassAssertionAxiomImpl class_ass = ( OWLClassAssertionAxiomImpl ) a;
                OWLIndividual ind = class_ass.getIndividual();
                String individual_iri = ind.toStringID();

                HashSet< OWLAxiom > additional_deletions = deleteIndividual( individual_iri, "" );

                OWLClass cl = class_ass.getClassExpression().asOWLClass();
                String answer = null;

                if ( SparqlUpdater.verbose_level > 0 ) { // if 0, don't tell and don't ask, just perform the deletions.
                    System.out.println( "Because " + cl.toString() + " is rigid, and (possibly) because of owl:sameAs relations for individual " + individual_iri + ", I would like to also delete: ");
                    SparqlUpdaterImpl.printAxiomSet( additional_deletions );

                    if ( SparqlUpdater.user_input ) {
                        System.out.print( "Confirm additional deletions? (Y/N) " );
                        Scanner scanner = new Scanner( System.in );
                        answer = scanner.next();
                    }
                    else {
                        answer = "Y";
                    }
                }
                else {
                    answer = "Y"; // for benchmark mode (verbose -1), always add these deletions
                }

                if ( answer.equalsIgnoreCase( "Y" ) ) {
                    hs.merge( additional_deletions ); // add additional deletions to del (hitting set candidate corresponding to this list of rigid axioms)
                }
                else { // can't be benchmark mode, so can print
                    System.out.println( "Will not perform additional deletions." );
                }
            }

            if ( !SparqlUpdater.benchmark ) {
                // If no benchmarking, we can now perform debugging (benchmarking doesn't do insertions)
                // The goal of this code segment is simply to add necessary debugging sets to the already chosen candidates.
                OWLOntology ontology = null;
                OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
                File file = new File( ontology_path_ );

                try {
                    ontology = manager.loadOntologyFromOntologyDocument( file );
                }
                catch ( OWLOntologyCreationException e ) {
                   throw new RuntimeException( "Could not create temporary OWL ontology: " + e.getMessage() );
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

                if ( minimal_hitting_sets.isEmpty() ) {
                    del_cup_dbg.add( hs );
                }

                for ( HittingSet< OWLAxiom > dbg : minimal_hitting_sets ) {
                    if ( SparqlUpdater.verbose_level > 2 ) {
                        System.out.println( "=== DEBUGGING HITTING SET ===" );
                        dbg.printAxioms();
                    }

                    // Store all deletions and debugging deletions in one set
                    HittingSet< OWLAxiom > merged = new HittingSet< OWLAxiom >();
                    merged.merge( hs );
                    merged.merge( dbg );
                    del_cup_dbg.add( merged );

                    // Add hitting set and debugging set to the candidate implementations
                    implementations.add( new ImmutablePair< HittingSet< OWLAxiom >, HittingSet< OWLAxiom > >( hs, dbg ) );
                    // TODO; in theory, you'd have to recursively check for more rigid deletions that might've occurred during debugging.
                }
            }
        }

        // At this point, we've (optionally) deleted individuals that had their rigid class assertions removed, and performed debugging on the results after insertion (the latter only if we're not benchmarking, since benchmark mode has no insertions).
        // Now we have to find out which of the resulting implementations have deleted a minimal amount of rigid axioms.
        ArrayList< HashSet< OWLAxiom > > rigid_list = new ArrayList< HashSet< OWLAxiom  > >();

        if ( SparqlUpdater.benchmark ) {
            del_cup_dbg = new ArrayList< HittingSet< OWLAxiom > >( delete_axioms ); // _delete_axioms_ \cup empty set = _delete_axioms_
        }

        // We're looking for comments (i.e. annotations) that mark a concept as rigid
        for ( HittingSet< OWLAxiom > hs : del_cup_dbg ) {
            HashSet< OWLAxiom > rigid_axioms = new HashSet< OWLAxiom >();

            for ( OWLAxiom a : hs ) {
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

            rigid_list.add( rigid_axioms );
        }

        // Benchmark only:
        ArrayList< HittingSet< OWLAxiom > > candidates_bench = new ArrayList< HittingSet< OWLAxiom > >();

        // Non-benchmark only:
        ArrayList< Implementation > best_implementations = new ArrayList< Implementation >();

        int index = 0;

        // Now, for each possible rigid axiom that might be minimal w.r.t. subset relation, ...
        for ( HashSet< OWLAxiom > candidate : rigid_list ) {
            boolean is_minimal = true;

            // ...check if all others are not subsets
            for ( HashSet< OWLAxiom > r_axioms : rigid_list ) {
                if ( candidate.containsAll( r_axioms ) && !candidate.equals( r_axioms ) ) {
                    is_minimal = false;
                    break;
                }
            }

            // If we couldn't find another set that is a subset, we are minimal. Add the corresponding hitting set to the candidates list.
            if ( is_minimal ) {
                if ( SparqlUpdater.benchmark ) {
                    candidates_bench.add( del_cup_dbg.get( index++ ) );
                }
                else {
                    // This works because _del_cup_dbg_, _rigid_list_ and _implementations_ have the same size and added elements in the same order!
                    Pair< HittingSet< OWLAxiom >, HittingSet< OWLAxiom > > tmp = implementations.get( index++ );
                    best_implementations.add( new Implementation( tmp.getLeft(), tmp.getRight() ) );
                }
            }
        }

        if ( SparqlUpdater.benchmark ) {
            if ( candidates_bench.size() == 0 || ( candidates_bench.size() == 1 && candidates_bench.get( 0 ).isEmpty() ) ) {
                stats.append( "0|" ); // no hitting sets

                int count = ways_to_delete.containsKey( 0 ) ? ways_to_delete.get( 0 ) : 0;
                ways_to_delete.put( 0, count + 1 );
                count = assertions_to_delete.containsKey( 0 ) ? assertions_to_delete.get( 0 ) : 0;
                assertions_to_delete.put( 0, count + 1 );
            }
            else {
                stats.append( String.valueOf( candidates_bench.size() ) );

                for ( HittingSet< OWLAxiom > hs : candidates_bench ) {
                    stats.append( "|" + hs.size() );
                    int count = assertions_to_delete.containsKey( hs.size() ) ? assertions_to_delete.get( hs.size() ) : 0;
                    assertions_to_delete.put( hs.size(), count + 1 );
                }

                int count = ways_to_delete.containsKey( candidates_bench.size() ) ? ways_to_delete.get( candidates_bench.size() ) : 0;
                ways_to_delete.put( candidates_bench.size(), count + 1 );
            }

            // Doesn't matter what is returned, won't be used. _stats_ matters and has been written to!
            return new ArrayList< Implementation >();
        }

        return best_implementations;
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
