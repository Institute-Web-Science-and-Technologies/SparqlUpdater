package de.unikoblenz.west.evowipe;

import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;
import java.util.Iterator;
import java.util.Collection;

/**
 * @brief A wrapper class for sets that ensures they are compared and ordered according to their cardinality.
 *
 * TODO possibly? generalize this for all kinds of sets
 */
public class WrappedSet< T > implements Comparable< WrappedSet< T >>, Iterable< T >  {
    protected Set< T > set_;

    /**
     * @brief Default class constructor for the wrapped set. Performs basic setup of member variables.
     */
    public WrappedSet() {
        set_ = new TreeSet< T >();
    }

    /**
     * @brief Alternative class constructor for the wrapped set. Copies an existing collection.
     * @param collection an arbitrary collection
     */
    public WrappedSet( Collection< T > collection ) {
        set_ = new TreeSet< T >( collection );
    }

    /**
     * @brief Alternative class constructor for the wrapped set. Copies another wrapped set.
     * @param set another wrapped set that should be the basis for _this_ wrapped set
     */
    public WrappedSet( WrappedSet< T > set ) {
        set_ = new TreeSet< T >( set.set_ );
    }

    /**
     * @return the set
     */
    public Set< T > set() {
        return set_;
    }

    /**
     * @return Return the very first element within the wrapped set.
     */
    public T first() {
        return set_.iterator().next();
    }
    
    /**
     * @return Returns the number of elements in this wrapped set (its cardinality).
     */
    public int size() {
        return set_.size();
    }

    /**
     * @return true if this wrapped set contains no elements
     */
    public boolean isEmpty() {
        return set_.isEmpty();
    }

    /**
     * @brief Returns true if this wrapped set contains the specified element. More formally, returns true if and only if this wrapped_set contains an element e such that (o==null ? e==null : o.equals(e)).
     * @return true if this set contains the specified element
     */
    public boolean contains( Object o ) {
        return set_.contains( o );
    }

    /**
     * @brief Removes the specified element from this wrapped set if it is present (optional operation).
     *
     * More formally, removes an element e such that (o==null ? e==null : o.equals(e)), if this wrapped set contains such an element. 
     *
     * @param o object to be removed from this wrapped set, if present
     * @return true if this wrapped set contained the specified element
     */
    public boolean remove( Object o ) {
        return set_.remove( o );
    }

    /**
     * @brief Merges another container with this set, adding all of the elements if they are not already present.
     * @param c collection containing elements to be added to this wrapped set
     */
    public void merge( Collection< T > c ) {
        set_.addAll( c );
    }

    /**
     * @brief Merges another wrapped set with this set, adding all of the elements if they are not already present.
     * @param other wrapped set containing elements to be added to this wrapped set
     */
    public void merge( WrappedSet< T > other ) {
        merge( other.set_ );
    }

    /**
     * @brief Returns an iterator over the elements in this wrapped set. The elements are returned in sorted, descending order.
     * @return an iterator over the elements in this set in descending order
     */
    @Override
    public Iterator< T > iterator() {
        return set_.iterator();
    }

    /**
     * @brief Returns a hash code value for the object. This method is supported for the benefit of hash tables such as those provided by HashMap.
     * @return a hash code value for this object. Check the java Object documentation for the general contract of "hashCode".
     */
    @Override
    public int hashCode() {
        int hash = 1;

        // Multiply hash values of all contained axioms
        for ( T e : set_ ) {
            hash *= Objects.hashCode( e );
        }

        return hash;
    }

    /**
     * @brief Indicates whether some other object is "equal to" this wrapped set.
     * @param other the reference object with which to compare.
     * @return true if this wrapped set is the same as the _other_ argument; false otherwise.
     */
    @SuppressWarnings("unchecked")
    @Override
    public boolean equals( Object other ) {
        // If the other object is not a wrapped set, it is naturally not equal
        if ( !( other instanceof WrappedSet )) {
            return false;
        }

        // The other object is a wrapped set, cast and compare fields
        WrappedSet< T > other_wrapped_set = ( WrappedSet< T > ) other;

        return set_.equals( other_wrapped_set.set_ );
    }

    /**
     * @brief Compares this wrapped set with the specified wrapped set for order.
     *
     * The accomplished order sorts sets in ascending order based on their sizes.
     *
     * @param other the wrapped set compared.
     * @return a negative integer, zero, or a positive integer as this wrapped set is less than, equal to, or greater than the specified wrapped set.
     */
    @SuppressWarnings("unchecked")
    @Override
    public int compareTo( WrappedSet< T > other ) {
        if ( set_.equals( other.set_ )) {
            return 0;
        }
        else {
            if ( set_.size() > other.set_.size()) {
                return 1;
            }
            else if ( set_.size() < other.set_.size()) {
                return -1;
            }
            else {
                // If the sets are not equal, but do not differ in size, we must decide a sorting order based on the contents of the respective sets.
                // "The implementor must ensure that sgn(compare(x, y)) == -sgn(compare(y, x)) for all x and y."
                // In this, we choose an element-wise comparison of individual elements, taking the result of the comparison between the first two elements that are not equal. This pair of elements must exist since otherwise, the sets would be equal.
                Iterator< T > me_it = set_.iterator();
                Iterator< T > other_it = other.set_.iterator();

                while ( me_it.hasNext()) {
                    T e1 = me_it.next();
                    T e2 = other_it.next();

                    int compare_elements = ( ( Comparable ) e1 ).compareTo( e2 );

                    if ( compare_elements != 0 ) {
                        return compare_elements;
                    }
                }
            }
        }

        throw new RuntimeException( "End of CompareTo method reached!" );
    }

    /**
     * @brief Print this wrapped set to standard output.
     *
     * Output is not very pretty.
     */
    public void print() {
        System.out.println( "{" );

        for ( T e : set_ ) {
            System.out.println( e.toString());
        }

        System.out.println( "}" );
    }

    /**
     * @return a string representation of the object.
     */
    @Override
    public String toString() {
        if ( set_.isEmpty() ) {
            return "{}";
        }

        String as_string = "{";
        Iterator it = set_.iterator();
        as_string += it.next().toString();

        while ( it.hasNext() ) {
            as_string += ", ";
            as_string += it.next().toString();
        }

        as_string += "}";

        return as_string;
    }
}
