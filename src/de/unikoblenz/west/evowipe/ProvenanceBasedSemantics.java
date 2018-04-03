package de.unikoblenz.west.evowipe;

import java.lang.UnsupportedOperationException;
import java.util.Set;
import java.util.List;
import java.util.HashMap;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.apache.commons.lang3.tuple.Pair;

/**
 * @brief Semantics using provenance information to decide which assertions to delete by for example preferably deleting those assertions associated
 *        with a low credibility or an old time stamp.
 *
 */
public class ProvenanceBasedSemantics implements Semantics {
    /**
     * @brief Applies the priority/credibility based semantics to hitting sets of axioms.
     *
     * @param delete_axioms hitting sets of axioms to be deleted
     * @param insert_axioms set of axioms to be inserted
     * @param stats, ways_to_delete, assertions_to_delete ONLY used in benchmark mode. Stores statistics for semantics
     * @return a list of implementations, for each of which the first element is the selected deletion, and the second element is the debugging step after the insertion.
     */
    @Override
    public List< Implementation > filter( Set< HittingSet< OWLAxiom > > delete_axioms, Set< OWLAxiom > insert_axioms, StringBuilder stats, HashMap< Integer, Integer > ways_to_delete, HashMap< Integer, Integer > assertions_to_delete ) {
        throw new UnsupportedOperationException( "Priority/credibility based semantics are not implemented/supported!" );
    }
}
