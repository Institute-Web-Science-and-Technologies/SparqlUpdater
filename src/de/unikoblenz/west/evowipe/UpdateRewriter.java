package de.unikoblenz.west.evowipe;

import org.mindswap.pellet.jena.PelletReasonerFactory;
import com.clarkparsia.pellet.sparqldl.jena.SparqlDLExecutionFactory;
import com.hp.hpl.jena.ontology.OntModel;
import com.hp.hpl.jena.query.Query;
import com.hp.hpl.jena.query.QueryExecution;
import com.hp.hpl.jena.query.QueryFactory;
import com.hp.hpl.jena.rdf.model.ModelFactory;
// !!!! if you change the JENA version to 3 upwards, need to use these imports: !!!!
//import org.apache.jena.ontology.OntModel;
//import org.apache.jena.query.Query;
//import org.apache.jena.query.QueryExecution;
//import org.apache.jena.query.QueryFactory;
//import org.apache.jena.rdf.model.ModelFactory;

/**
 * @brief Rewrite a SPARQL-DL update briefly to construct a graph containing all assertions to be deleted.
 */
public class UpdateRewriter {
    private String ontology_;
    private String update_;
    private OntModel m_;

    /**
     * @brief Class constructor. Performs basic setup of member variables.
     * @param ontology_path the system file path to the knowledge base file.
     * @param update_as_string the update to perform; NOT the file path, but the actual update contents.
     */
	public UpdateRewriter( String ontology_path, String update_as_string ) {
        ontology_ = ontology_path;
        update_ = update_as_string;

		// First create a Jena ontology model backed by the Pellet reasoner
		// (note, the Pellet reasoner is required)
		m_ = ModelFactory.createOntologyModel( PelletReasonerFactory.THE_SPEC );

		// Then read the data from the file into the ontology model
		m_.read( ontology_ );

        if ( SparqlUpdater.verbose_level > 2 ) {
            System.out.println( "Update:" );
            System.out.println( update_ );
        }
	}

    /**
     * @brief Convert the update into a construct query and return it.
     * @param start_r String marking the beginning of what to remove
     * @param end_r String marking the end of what to remove
     * @param repl_caps what to replace with "CONSTRUCT"
     * @param repl what to replace with "construct"
     * @return a construct query constructing a graph containing all assertions to be deleted or inserted.
     */
	private QueryExecution makeSparqlDLQueryExecution( String start_r, String end_r, String repl_caps, String repl ) {
		// Replace respective terms with constructs 
		String query = update_.replaceAll( repl_caps, "CONSTRUCT" );

		// Remove opponent blocks (for delete, remove insert; for insert, remove delete)
        if ( SparqlUpdater.verbose_level > 2 ) {
            System.out.println( query );
        }

		int s_index = query.indexOf( start_r );
		int e_index = query.indexOf( end_r );
		StringBuffer tmp = new StringBuffer( query ); // replacing between indices does not work with strings for some reason...
		tmp.replace( s_index, e_index, "" ); // replace with nothing to remove it
		query = tmp.toString(); // convert back to string

        if ( SparqlUpdater.verbose_level > 2 ) {
            System.out.println( "Query for " + repl + ":" );
            System.out.println( query );
            System.out.println();
        }

		Query q = QueryFactory.create( query );

		// Create a SPARQL-DL query execution for the given query and ontology model
		QueryExecution qe = SparqlDLExecutionFactory.create( q, m_ );

        return qe;
    }

    /**
     * @brief Convert the update into a construct query and return it.
     * @return a construct query constructing a graph containing all assertions to be deleted.
     */
	public QueryExecution makeSparqlDLQueryExecutionDelete() {
        return makeSparqlDLQueryExecution( "INSERT", "WHERE", "DELETE", "delete" );
	}

    /**
     * @brief Convert the update into a construct query and return it.
     * @return a construct query constructing a graph containing all assertions to be inserted.
     */
	public QueryExecution makeSparqlDLQueryExecutionInsert() {
        return makeSparqlDLQueryExecution( "DELETE", "CONSTRUCT", "INSERT", "insert" );
	}
}
