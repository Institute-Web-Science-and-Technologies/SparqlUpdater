package de.unikoblenz.west.evowipe;

import org.semanticweb.owlapi.model.OWLAxiom;
import java.util.HashSet;
import java.util.Set;

/**
 * @brief An implementation for a Sparql-DL update
 */
public class Implementation {
    public HittingSet< OWLAxiom > del_;
    public HittingSet< OWLAxiom > dbg_;
    public Set< OWLAxiom > success_;

    /**
     * @brief Empty class constructor.
     */
    public Implementation() {
        del_ = new HittingSet< OWLAxiom >();
        dbg_ = new HittingSet< OWLAxiom >();
        success_ = new HashSet< OWLAxiom >();
    }

    /**
     * @brief Class constructor. Performs basic setup of member variables.
     * @param del a minimal hitting set for the deletion
     * @param dbg a minimal hitting set for the debugging step
     */
    public Implementation( HittingSet< OWLAxiom > del, HittingSet< OWLAxiom > dbg ) {
        del_ = del;
        dbg_ = dbg;
        success_ = new HashSet< OWLAxiom >();
    }

    @Override
    public boolean equals( Object obj ) {
        if ( obj == null ) {
            return false;
        }

        if ( !( obj instanceof Implementation )) {
            return false;
        }

        final Implementation other = ( Implementation ) obj;

        if ( !this.del_.equals( other.del_ ) ) {
            return false;
        }

        if ( !this.dbg_.equals( other.dbg_ ) ) {
            return false;
        }

        if ( !this.success_.equals( other.success_ ) ) {
            return false;
        }

        return true;
    }

    @Override
    public int hashCode() {
        return del_.hashCode() + dbg_.hashCode() + success_.hashCode();
    }
};
