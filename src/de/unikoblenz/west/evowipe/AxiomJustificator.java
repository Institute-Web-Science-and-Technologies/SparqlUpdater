package de.unikoblenz.west.evowipe;

import java.util.Set;
import java.util.TreeSet;
import java.util.Iterator;

import com.hp.hpl.jena.rdf.model.Statement;
// !!!! if you change the JENA version to 3 upwards, need to use this import: !!!!
//import org.apache.jena.rdf.model.Statement;

//import org.coode.owlapi.manchesterowlsyntax.ManchesterOWLSyntaxEditorParser;
import org.semanticweb.owlapi.util.mansyntax.ManchesterOWLSyntaxParser;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import com.clarkparsia.owlapi.explanation.GlassBoxExplanation;
import com.clarkparsia.owlapi.explanation.BlackBoxExplanation;
import com.clarkparsia.owlapi.explanation.HSTExplanationGenerator;
import com.clarkparsia.owlapi.explanation.MultipleExplanationGenerator;
import com.clarkparsia.owlapi.explanation.SatisfiabilityConverter;
import com.clarkparsia.owlapiv3.OWL;
import com.clarkparsia.owlapiv3.OntologyUtils;

import org.mindswap.pellet.KBLoader;
import org.mindswap.pellet.KnowledgeBase;
import com.clarkparsia.pellet.owlapiv3.OWLAPILoader;
import com.clarkparsia.pellet.owlapiv3.PelletReasoner;
import com.clarkparsia.pellet.owlapiv3.PelletReasonerFactory;

/**
 * @brief Calculate justifications for axioms in a knowledge base.
 *
 * This only handles instance-of and general property relations.
 * A justification for an ABox assertion 'a' in a knowledge base 'K' is a minimal subset of the Abox which together with the TBox implies 'a'.
 * Justifications are calculated through the Pellet reasoner. The class stores in itself subject, property and object of a general property relation and subject and class for an instance-of relation.
 */
public class AxiomJustificator extends Justificator {
    private OWLAxiom axiom_;

    /**
     * @brief Class constructor for the 'justificator'. Performs basic setup of member variables.
     * @param statement Jena statement to compute justifications for
     * @param ontology_path the system file path to the knowledge base file.
     * @param max_explanations the maximum number of justifications that should be computed
     * @param method method to use for explanation (glass box/black box)
     */
    public AxiomJustificator( Statement statement, String ontology_path, int max_explanations, String method ) {
        super( ontology_path, max_explanations, method );
        axiom_ = AxiomConverter.convert( statement, loader_.getOntology() );
    }

    /**
     * @brief Class constructor for the 'justificator'. Performs basic setup of member variables.
     * @param axiom axiom to compute justifications for
     * @param ontology_path the system file path to the knowledge base file.
     * @param max_explanations the maximum number of justifications that should be computed
     * @param method method to use for explanation (glass box/black box)
     */
    public AxiomJustificator( OWLAxiom axiom, String ontology_path, int max_explanations, String method ) {
        super( ontology_path, max_explanations, method );
        axiom_ = axiom;
    }

    /**
     * @return axiom_
     */
    public OWLAxiom getAxiom() {
        return axiom_;
    }

    /**
     * @brief Compute justifications for the predefined assertion.
     *
     * NOTE THAT THIS WILL NOT CONTAIN TBOX-ASSERTIONS (i.e. subClassOf, ...)
     * @return a set of justifications for the assertion (basically a set of wrappers around sets of OWL-Axioms)
     */
    @Override
    public Set< Justification > computeJustifications() {
        Set< Set< OWLAxiom > > justifications = null;

        try {
            justifications = explainAxiom( axiom_ );
        }
        catch ( OWLException e ) {
            throw new RuntimeException( e );
        }

        // We represent justifications as instances of a custom class outside of this function, which requires transitioning
        // This is done in order to hide usage of the OWLAPI in code that does not need to rely directly on it.
        Set< Justification > return_justifications = new TreeSet< Justification > (); // order is important for hitting set computation -> use TreeSet!

/* //TODO Use this if printing is not desired
        for ( Set< OWLAxiom > justification : justifications ) {
            // JAVA 8:
            // justification.removeIf( ( OWLAxiom a ) -> { return a.isOfType( AxiomType.TBoxAndRBoxAxiomTypes ) } );
            //
            // JAVA < 8 (there is probably a better way even then):
            for ( Iterator< OWLAxiom > it = justification.iterator(); it.hasNext(); ) {
                OWLAxiom a = it.next();

                if ( a.isOfType( AxiomType.TBoxAndRBoxAxiomTypes ) ) {
                    it.remove();
                }
            }

            return_justifications.add( new Justification( justification ) );
        }
*/
        for ( Set< OWLAxiom > justification : justifications ) {
            return_justifications.add( new Justification( justification ) );
        }

        //if ( SparqlUpdater.verbose_level > 0 ) {
            //Justification.print( return_justifications, axiom_ );
        //}

        // We only consider ABox axioms for deletion. Therefore, we remove TBox and RBox assertions.
        // TODO if printing is not desired, this loop can be combined with the one above and the method used here can be removed within the Justification class.
        for ( Justification justification : return_justifications ) {
            justification.removeTBoxAndRBoxAxioms();
        }

        return return_justifications;
    }
}
