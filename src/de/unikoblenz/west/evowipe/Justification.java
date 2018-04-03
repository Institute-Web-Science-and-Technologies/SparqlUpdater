package de.unikoblenz.west.evowipe;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collections;
import java.util.Set;
import java.util.TreeSet;
import java.util.Iterator;

import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.AxiomType;

import com.clarkparsia.owlapi.explanation.io.ExplanationRenderer;
import com.clarkparsia.owlapi.explanation.io.manchester.ManchesterSyntaxExplanationRenderer;

/**
 * @brief Wrapper class for justifications (which, at their core, are simply represented as sets of axioms)
 *
 * A justification for an ABox assertion 'a' in a knowledge base 'K' is a minimal subset of the Abox which together with the TBox implies 'a'.
 * Note: Pellet calls it an 'explanation', which means the same thing.
 */
//public class Justification implements Comparable< Justification > {
public class Justification extends WrappedSet< OWLAxiom > {
    /**
     * @brief Class constructor for the justification. Performs basic setup of member variables.
     * @param axiom_set this is basically an OWLAPI representation of a justification.
     */
    public Justification( Set< OWLAxiom > axiom_set ) {
        super( axiom_set );
    }

    /**
     * @brief Test whether this justification is a strict subset of another justification (remember that a justification is a set of assertions).
     *
     * Note that we require 'strictness' for this subset-relation, which is also commonly associated with the term "proper subset".
     * That is, the justifications may not be equal, i.e. the cardinality of their intersection is equal to the cardinality of 'this' justification if this method holds true.
     *
     * @param other the supposed superset justification.
     * @return true if all of the requirements explained above are met.
     */
    private boolean isStrictSubsetOf( Justification other ) {
        return other.set_.containsAll( this.set_ ) && other.set_.size() > this.set_.size(); // _this_ is added for clarity, not necessity
    }

    /**
     * @brief Minimize a set of justifications in order to gain 'root justification's.
     *
     * A set J contained in the set of all justifications for assertions 'a_i' in a knowledge base 'K' is a root justification for a set of ABox-assertions {a_1, ... a_n} iff there is no other such set 'J0' so that 'J0' is a strict subset of 'J'.
     * In other words, we have to minimize the set of all justifications to gain a set of root justifications.
     *
     * @param justifications the set of justifications to minimize.
     * @return a new set of justifications that contains only root justifications (see right above for a definition)
     *
     * TODO it may very well be possible to do this a lot more efficiently.
     */
    public static Set< Justification > minimize( Set< Justification > justifications ) {
        Set< Justification > root_justifications = new TreeSet < Justification > (); // order is important for hitting set computation -> use TreeSet!

        // General idea: For each justification, check if it is a strict superset of another justification.
        // If it is, it is called a 'derived justification', and as such, not a root justification, hence it shall be disregarded.
        Outer: for ( Justification justification0 : justifications ) {
            for ( Justification justification1 : justifications ) {
                // Disregard the outer iterator when it comes up
                if ( justification0 == justification1 ) {
                    continue;
                }

                // Now we're guaranteed to look at a justification that is not the same object.
                // Test for strict subsets; note that this test will check that the cardinality of the superset is larger than that of the subset to ensure the sets of assertions are not equal;
                // However, this is technically not necessary since we are operating on a set of justifications, thus each pair of justifications we encounter at this point will be different either in terms of size, or in terms of contents.
                // Therefore, a justification that contains all assertions from another justification must naturally contain more assertions in total, because the justifications would otherwise be equal, which in turn is not possible here.
                // Roles are naturally swapped here; the current justification is a strict superset of the other if the other is a strict subset of the former.
                if ( justification1.isStrictSubsetOf( justification0 )) {
                    // _justification0_ is not a root justification because there is another justification that is a strict subset of _justification0_.
                    // Thus, we wish to skip the rest of the loop and ESPECIALLY the last line of code before the next iteration of the outer loop starts.
                    continue Outer;
                }
                // else, continue the inner loop over all other justifications...
            }

            // ... and if no other justification is ever a strict subset of _justification0_, then the latter is a root justification.
            root_justifications.add ( justification0 );
        }

        return root_justifications;
    }

    /**
     * @brief Remove all TBox and RBox axioms
     */
    public void removeTBoxAndRBoxAxioms() {
        // JAVA 8:
        // justification.removeIf( ( OWLAxiom a ) -> { return a.isOfType( AxiomType.TBoxAndRBoxAxiomTypes ) } );
        //
        // JAVA < 8 (there is probably a better way even then):
        for ( Iterator< OWLAxiom > it = set_.iterator(); it.hasNext(); ) {
            OWLAxiom a = it.next();

            if ( a.isOfType( AxiomType.TBoxAndRBoxAxiomTypes ) ) {
                it.remove();
            }
        }
    }

    /**
     * @brief Print a set of justifications using a renderer.
     * @param justifications the set of justifications to render
     * @param axiom if given, the justified assertion
     */
    public static void print( Set< Justification > justifications, OWLAxiom axiom ) {
        ExplanationRenderer rend = new ManchesterSyntaxExplanationRenderer();
        PrintWriter pw = new PrintWriter( System.out );

        try {
            rend.startRendering( pw );

            for ( Justification justification : justifications ) {
                pw.flush();
                rend.render( axiom, Collections.singleton ( justification.set_ ));
            }

            rend.endRendering();
        }
        catch ( OWLException e ) {
            SparqlUpdater.logger.severe( "Error rendering justifications: " + e );
        }
        catch ( IOException e ) {
            SparqlUpdater.logger.severe( "Error rendering justifications: " + e );
        }
    }

    /**
     * @brief Print a set of justifications using a renderer.
     * @param justifications the set of justifications to render
     *
     * This version does not specify an assertion the justifications belong to; thus, no axiom will be printed, just the set  of justifications.
     */
    public static void print( Set< Justification > justifications ) {
        print( justifications, null );
    }
}
