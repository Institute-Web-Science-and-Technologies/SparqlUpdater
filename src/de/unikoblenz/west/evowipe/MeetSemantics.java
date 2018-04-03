package de.unikoblenz.west.evowipe;

import java.util.Set;
import java.util.List;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.HashMap;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.ImmutablePair;

/**
 * @brief This semantics is rather pessimistic since it removes all assertions occurring in a deletion. Thus the resulting ABox implements the deletion while possessing minimal cardinality.
 *
 */
public class MeetSemantics implements Semantics {
    /**
     * @brief Applies the meet semantics to hitting sets of axioms.
     *
     * @param delete_axioms hitting sets of axioms to be deleted
     * @param insert_axioms set of axioms to be inserted (not used here)
     * @param stats, ways_to_delete, assertions_to_delete ONLY used in benchmark mode. Stores statistics for semantics
     * @return a list of implementations, for each of which the first element is the selected deletion, and the second element is the debugging step after the insertion (not used here).
     */
    @Override
    public List< Implementation > filter( Set< HittingSet< OWLAxiom > > delete_axioms, Set< OWLAxiom > insert_axioms, StringBuilder stats, HashMap< Integer, Integer > ways_to_delete, HashMap< Integer, Integer > assertions_to_delete ) {
        HittingSet< OWLAxiom > deletion = new HittingSet< OWLAxiom >();

        for ( HittingSet< OWLAxiom > hset : delete_axioms ) {
            deletion.merge( hset );
        }

        if ( SparqlUpdater.benchmark ) {
            if ( delete_axioms.isEmpty() ) {
                stats.append( "0|" ); // no hitting sets

                int count = ways_to_delete.containsKey( 0 ) ? ways_to_delete.get( 0 ) : 0;
                ways_to_delete.put( 0, count + 1 );

                count = assertions_to_delete.containsKey( 0 ) ? assertions_to_delete.get( 0 ) : 0;
                assertions_to_delete.put( 0, count + 1 );
            }
            else {
                stats.append( "1|" + deletion.size() ); // one hitting set with .size() axioms to be deleted

                int count = ways_to_delete.containsKey( 1 ) ? ways_to_delete.get( 1 ) : 0;
                ways_to_delete.put( 1, count + 1 );

                count = assertions_to_delete.containsKey( deletion.size() ) ? assertions_to_delete.get( deletion.size() ) : 0;
                assertions_to_delete.put( deletion.size(), count + 1 );
            }
        }

        List< Implementation > implementations = new ArrayList< Implementation >();

        if ( deletion.size() > 0 ) {
            // Debug is empty, and only one hitting set (all alternatives merged)
            implementations.add( new Implementation( deletion, new HittingSet< OWLAxiom >() ) );
        }

        // If deletion is empty, the list has size 0 (this is important for CustomSemantics to work properly)
        return implementations;
    }
}
