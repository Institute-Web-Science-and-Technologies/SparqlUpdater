package de.unikoblenz.west.evowipe;

import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Scanner;
import java.util.Set;
import java.util.TreeSet;
import java.util.HashMap;
import java.util.SortedSet;
import java.util.Iterator;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.ImmutablePair;

/**
 * @brief In maxichoice semantics, the deletion that's minimal w.r.t. subsets is chosen.
 */
public class MaxichoiceSemantics implements Semantics {
    /**
     * @brief Applies the maxichoice semantics to hitting sets of axioms.
     *
     * @param delete_axioms hitting sets of axioms to be deleted
     * @param insert_axioms set of axioms to be inserted (not used here)
     * @param stats, ways_to_delete, assertions_to_delete ONLY used in benchmark mode. Stores statistics for semantics
     * @return a list of implementations, for each of which the first element is the selected deletion, and the second element is the debugging step after the insertion (not used here).
     */
    @Override
    public List< Implementation > filter( Set< HittingSet< OWLAxiom > > delete_axioms, Set< OWLAxiom > insert_axioms, StringBuilder stats, HashMap< Integer, Integer > ways_to_delete, HashMap< Integer, Integer > assertions_to_delete ) {
        List< Implementation > best_implementations = new ArrayList< Implementation >();

        // Prevent logging one possibility if the hitting set is empty (for whatever reason)
        if ( !( delete_axioms.size() == 1 && delete_axioms.iterator().next().isEmpty() ) ) {

            // Since all hitting sets are per definition minimal, all we need to do is add one implementation for each. Debugging is performed in CustomSemantics for each resulting deletion.
            for ( HittingSet< OWLAxiom > hs : delete_axioms ) {
                best_implementations.add( new Implementation( hs, new HittingSet< OWLAxiom >() ) );
            }
        }

        // Gotta write benchmark results here as CustomSemantics only adds debugging for each implementation, which is irrelevant for benchmark mode
        if ( SparqlUpdater.benchmark ) {
            if ( best_implementations.isEmpty() ) {
                stats.append( "0|" ); // no hitting sets

                int count = ways_to_delete.containsKey( 0 ) ? ways_to_delete.get( 0 ) : 0;
                ways_to_delete.put( 0, count + 1 );

                count = assertions_to_delete.containsKey( 0 ) ? assertions_to_delete.get( 0 ) : 0;
                assertions_to_delete.put( 0, count + 1 );
            }
            else if ( best_implementations.size() == 1 ) {
                int size = best_implementations.get( 0 ).del_.size();

                if ( size > 0 ) {
                    stats.append( "1|" + size ); // one hitting set with .size() axioms to be deleted

                    int count = ways_to_delete.containsKey( 1 ) ? ways_to_delete.get( 1 ) : 0;
                    ways_to_delete.put( 1, count + 1 );

                    count = assertions_to_delete.containsKey( size ) ? assertions_to_delete.get( size ) : 0;
                    assertions_to_delete.put( size, count + 1 );
                }
                else {
                    stats.append( "0|" );

                    int count = ways_to_delete.containsKey( 0 ) ? ways_to_delete.get( 0 ) : 0;
                    ways_to_delete.put( 0, count + 1 );

                    count = assertions_to_delete.containsKey( 0 ) ? assertions_to_delete.get( 0 ) : 0;
                    assertions_to_delete.put( 0, count + 1 );
                }
            }
            else {
                stats.append( String.valueOf( best_implementations.size() ) );

                for ( Implementation i : best_implementations ) {
                    stats.append( "|" + i.del_.size() );
                    int count = assertions_to_delete.containsKey( i.del_.size() ) ? assertions_to_delete.get( i.del_.size() ) : 0;
                    assertions_to_delete.put( i.del_.size(), count + 1 );
                }

                int count = ways_to_delete.containsKey( best_implementations.size() ) ? ways_to_delete.get( best_implementations.size() ) : 0;
                ways_to_delete.put( best_implementations.size(), count + 1 );
            }
        }

        return best_implementations;
    }
}
