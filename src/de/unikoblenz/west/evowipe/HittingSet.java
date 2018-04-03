package de.unikoblenz.west.evowipe;

import java.io.IOException;
import java.io.StringWriter;
import java.util.Objects;
import java.util.Collections;
import java.util.Set;
import java.util.TreeSet;
import java.util.HashSet;
import java.util.SortedSet;
import java.util.Iterator;
import java.lang.IllegalStateException;

import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.util.SimpleShortFormProvider;
import org.semanticweb.owlapi.manchestersyntax.renderer.ManchesterOWLSyntaxObjectRenderer;

/**
 * @brief A class for a generalized hitting set
 *
 * A hitting set for S is a set H that has an intersection with each S_i in S.
 */
public class HittingSet< T > extends WrappedSet< T > {
    /**
     * @brief Default class constructor for the hitting set.
     */
    public HittingSet() {
    }

    /**
     * @brief Class constructor for the hitting set. Performs basic setup of member variables.
     * @param elements the elements contained within this hitting set
     */
    public HittingSet( Set< T > elements ) {
        super( elements );
    }

    /**
     * @brief Construct all minimal hitting sets regarding given input sets.
     *
     * A hitting set for S is a set H that has an intersection with each S_i in S.
     * If further no proper subset of H is a hitting set for S, H is called a minimal hitting set.
     *
     * @param S = {S_1, ... S_n} is a set of sets. It is required that its elements are sorted. In case of a _WrappedSet_, the sets are sorted based on their cardinality, which is significant for this algorithm to produce the correct result.
     * @return the set of all minimal hitting sets for S, denoted by HS(S).
     */
    public static < T > Set< HittingSet< T >> constructMinimalHittingSets( SortedSet< WrappedSet< T >> S ) {
        // Make a local copy of _S_ in order not to modify the original set passed to the function
        SortedSet< WrappedSet < T >> local_copy = new TreeSet< WrappedSet< T >> ();

        for ( WrappedSet< T > s_i : S ) {
            WrappedSet< T > new_s_i = new WrappedSet< T >( s_i );
            local_copy.add( new_s_i );
        }

        SortedSet< HittingSet< T >> minimal_hitting_sets = new TreeSet< HittingSet< T >>(); // Ordered output is prettier
        Set< T > hitting_base = new HashSet< T > (); // base for hitting set (construct hitting set from this using the class constructor), does not need to be sorted

        backtrackConstructMinimalHittingSets( hitting_base, minimal_hitting_sets, local_copy );

        return minimal_hitting_sets;
    }

    /**
     * @brief Recursive helper function for constructing all minimal hitting sets regarding given input sets.
     *
     * This method is used for backtracking purposes, and as such, takes as arguments TEMPORARY "states" of variables within the overall algorithm and refines them for a partial solution. All of the minimal hitting sets recursively constructed this way are effectively merged into one final output set containing all minimal hitting sets.
     *
     * @param hitting_base a current, non-final minimal hitting set that is being constructed by the algorithm. It is complete when the outer loop below exits, i.e. when the input set of sets is empty (note; it is naturally only empty FOR THIS BACKTRACKING ITERATION, not for all other backtracking processes). Once all recursive calls exit upon completing their respectively loops, we can assume that all minimal hitting sets have been computed.
     * @param minimal_hitting_sets the current, non-final "output" of the algorithm, containing all minimal hitting sets computed so far by various backtracking iterations.
     * @param S = {S_1, ... S_n} is a set of sets. It is required that its elements are sorted. In case of a _WrappedSet_, the sets are sorted based on their cardinality, which is mandatory for this algorithm to produce the correct result.
     * @throws IllegalStateException if step 3.4 produces empty sets
     */
    private static < T > void backtrackConstructMinimalHittingSets( Set< T > hitting_base, SortedSet< HittingSet< T >> minimal_hitting_sets, SortedSet< WrappedSet< T >> S ) throws IllegalStateException {
        // Repeat until the input is reduced to the empty set
        // Read these following comments after reading the rest of the code.
        // This "loop" is technically never really a loop; the looping behaviour comes from picking elements and sets and recursively calling this function, which starts a new iteration of the loop.
        // Thus, once we actually reach the end of the loop body, or otherwise stop picking new elements for backtracking, we have to do a "hard" exit from the entire function; otherwise we end up with an infinite recursion - since only the recursive calls will reduce the size of _S_.
        // After exiting the recursive calls, _S_ is the same size as before, and as such, never empty. I'm writing this up mostly for myself because I had a hard time understanding my own algorithm for a bit there.
        // We pick an element, start a new iteration of the loop, and once that has produced a valid hitting set, we backtrack and pick other elements, which will then result in more iterations, but once we stop backtracking, there are no more elements to start new iterations. In that case, we should immediately exit the function because only the actual backtracking processes which exit the loop normally, i.e. when _S_ is actually empty (for this particular construction of a partial solution), should actually execute the last line of code which adds final hitting sets, since the algorithm only specifies a hitting set to be complete when _S_ is empty - and therefore NOT when there are no more elements to backtrack.
        while ( !S.isEmpty()) {
            // 1. Add all units to the hitting set
            // Since _S_ is sorted, we can iterate over it and it will start with the sets containing the least elements; all we need to do is check if there is only one element (thus, there's no need to iterate over the entire set of sets, just until we reach one set with at least two elements).
            for ( WrappedSet< T > e : S ) {
                if ( e.size() > 1 ) {
                    break; // no more units after this because the set is sorted
                }

                hitting_base.add( e.first()); // add unit (the only element within the set)
            }

            // 2. Delete all sets from _S_ that have an intersection with the current hitting set
            // Java has ways to calculate intersections directly, such as Set.retainAll(), however, we don't actually need to calculate the intersection, just find out if it exists. That said, we can stop once we find one element present in both sets.
            for ( Iterator< WrappedSet< T >> it = S.iterator(); it.hasNext(); ) {
                WrappedSet< T > s_i = it.next();

                // TODO it would possibly be faster if we iterated over the smaller set; for now, just iterate over the current hitting set
                for ( T e : hitting_base ) {
                    // If there is an intersection, remove this set from the input
                    if ( s_i.contains( e )) {
                        it.remove();
                        break; // As explained above, we are done here
                    }
                }
            }

            // 3. CHOICE POINTS; backtrack if possible to attain all minimal hitting sets
            // CHOICE POINT 3.1 Choose a set from _S_ with minimal cardinality
            // Note that for the implementation, both choice points are effectively reduced to one recursive call, since choice point 3.2 results as a sub-problem of choice point 3.1 (choosing elements from the chosen set).
            if ( !S.isEmpty ()) { // defensive coding
                int min_size = S.iterator().next().size(); // first element in set is the smallest (order constraint of WrappedSet)

                for ( WrappedSet< T > smin : S ) {
                    // Don't choose sets that dont't actually have minimal cardinality
                    // Since we've gone through all sets with minimal cardinality, this process is finished.
                    // This does not formally "end" the algorithm, just one backtracking process. The actual algorithm for one partial solution is only finished - producing a minimal hitting set - upon reaching the empty set of inputs.
                    if ( smin.size() > min_size ) {
                        return; // Note that this should not add anything to the minimal hitting sets; otherwise we'd add preliminary, uncomplete solutions to the output; thus, we return instead of breaking the outer loop.
                        // See also the lengthy comment at the beginning of the function, right above the loop header.
                    }

                    // This set has minimal size
                    // CHOICE POINT 3.2 Choose an element from _smin_
                    // Which, since we use backtracking, will just go through all of them to construct all possible minimal hitting sets
                    for ( T e : smin ) {
                        //printD( "Chosen element: " + e.toString(), depth );
                        // 3.3 Add the element to the hitting set
                        // DO NOT use the current hitting base, because it should remain the same for other iterations of this loop (backtracking)
                        Set< T > new_hitting_base = new HashSet< T >( hitting_base );
                        new_hitting_base.add( e );

                        // 3.4 Delete all other elements in _smin_ from all sets in _S_
                        // Again, use a new set of sets specifically for this backtracking iteration
                        SortedSet< WrappedSet< T >> new_S = new TreeSet< WrappedSet< T >> ();

                        for ( WrappedSet< T > s_i : S ) {
                            // 3.5 Delete _smin_ from _S_
                            // (Just don't add it to the new copy - effectively "deletes" it for the backtracking process)
                            if ( s_i.equals( smin )) {
                                continue;
                            }

                            WrappedSet< T > new_s_i = new WrappedSet< T >( s_i );

                            for ( T others : smin ) {
                                if ( e.equals( others )) {
                                    continue;
                                }

                                new_s_i.remove( others );
                            }

                            if ( new_s_i.isEmpty()) {
                                throw new IllegalStateException( "Minimal hitting set construction: Step 3.4 should not produce empty sets" );
                            }

                            new_S.add( new_s_i );
                        }

                        // RECURSIVE CALL FOR CHOICE POINTS
                        backtrackConstructMinimalHittingSets( new_hitting_base, minimal_hitting_sets, new_S );

                        // Keep in mind that _hitting_base_ and _S_ have not been altered by the previous recursive call when we come back here!
                        // They have merely been used to construct a different solution.
                    }
                }

                // End of backtracking.
                // This does not formally "end" the algorithm, just one backtracking process. The actual algorithm for one partial solution is finished and produces a minimal hitting set only upon reaching the empty set of inputs.
                return; // Note that this should not add anything to the minimal hitting sets; otherwise we'd add preliminary, uncomplete solutions to the output; thus, we return instead of breaking the outer loop.
                // See also the lengthy comment at the beginning of the function, right above the loop header.
            }
        }

        // This minimal hitting set is finished; now, exit the function and if possible, backtrack to create all the other minimal hitting sets
        // This point will only be reached upon exiting the loop NORMALLY, i.e. when _S_ is eventually reduced to the empty set.
        // See also the lengthy comment at the beginning of the function, right above the loop header.
        minimal_hitting_sets.add( new HittingSet< T > ( hitting_base ) );
    }

    /**
     * @brief Print a hitting set of OWL assertions using a renderer.
     */
    @SuppressWarnings("unchecked")
    public void printAxioms() {
        for ( OWLAxiom a : ( Set< OWLAxiom > ) set_ ) {
            StringWriter writer = new StringWriter();
            ManchesterOWLSyntaxObjectRenderer renderer = new ManchesterOWLSyntaxObjectRenderer( writer, new SimpleShortFormProvider() );
            a.accept( renderer );
            System.out.println( "  " + writer.toString() );
        }
    }

    /**
     * @brief Print a hitting set of OWL assertions using a renderer.
     * @param indent How many leading tabs to add to each line
     */
    @SuppressWarnings("unchecked")
    public void printAxioms( int indent ) {
        for ( OWLAxiom a : ( Set< OWLAxiom > ) set_ ) {
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
