package de.unikoblenz.west.evowipe;

import java.util.Set;
import java.util.List;
import java.util.HashMap;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.apache.commons.lang3.tuple.Pair;

/**
 * @brief Different semantics are used to choose among the possibilities to delete a set of assertions and/or to debug a knowledge base.
 *
 * Supported semantics (TODO update this list when new semantics are implemented) are:
 *     Maxichoice Semantics (deletion)
 *     Meet Semantics (deletion)
 *     Brave Semantics (insertion)
 *     Combinations of the above for deletion + debugging (i.e. insertion + deletion)
 *     Query-driven Update Semantics (insertion + deletion)
 *     Query-driven Update Semantics based on subset relation (insertion + deletion)
 *     Rigid Semantics (prefer deleting non-rigid concepts) (insertion + deletion)
 *     Dependency-Guided Semantics (insertion + deletion)
 */
public interface Semantics {
    /**
     * @brief Applies the semantics to hitting sets of axioms.
     * @param delete_axioms hitting set of axioms to be deleted
     * @param insert_axioms set of axioms to be inserted
     * @param stats, ways_to_delete, assertions_to_delete ONLY used in benchmark mode. Stores statistics for semantics
     * @return a list of implementations, for each of which the first element is the selected deletion, and the second element is the debugging step after the insertion.
     */
    public List< Implementation > filter( Set< HittingSet< OWLAxiom > > delete_axioms, Set< OWLAxiom > insert_axioms, StringBuilder stats, HashMap< Integer, Integer > ways_to_delete, HashMap< Integer, Integer > assertions_to_delete );
}
