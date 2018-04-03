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
 * @brief Calculate justifications/explanations in a knowledge base.
 *
 * This only handles instance-of and general property relations.
 * A justification for an ABox assertion 'a' in a knowledge base 'K' is a minimal subset of the Abox which together with the TBox implies 'a'.
 * Justifications are calculated through the Pellet reasoner.
 */
public abstract class Justificator {
    protected KBLoader kbloader_;
    protected SatisfiabilityConverter converter_;
    protected OWLAPILoader loader_;
    protected int max_explanations_;
    protected PelletReasoner reasoner_;
    protected String method_;

    /**
     * @brief Class constructor for the 'justificator'. Performs basic setup of member variables.
     * @param ontology_path the system file path to the knowledge base file.
     * @param max_explanations the maximum number of justifications that should be computed
     * @param method method to use for explanation (glass box/black box)
     */
    public Justificator( String ontology_path, int max_explanations, String method ) {
        GlassBoxExplanation.setup();

        max_explanations_ = max_explanations;
        kbloader_ = new OWLAPILoader();
        loader_ = ( OWLAPILoader ) kbloader_;
        KnowledgeBase kb = kbloader_.createKB( new String[] { ontology_path } );
        converter_ = new SatisfiabilityConverter( loader_.getManager().getOWLDataFactory() );
        reasoner_ = loader_.getReasoner();
        method_ = method;
    }

    /**
     * @return reasoner_
     */
    public PelletReasoner getReasoner() {
        return reasoner_;
    }

    /**
     * @brief Compute justifications.
     *
     * NOTE THAT THIS WILL NOT CONTAIN TBOX-ASSERTIONS (i.e. subClassOf, ...)
     * @return a set of justifications for an assertion (basically a set of wrappers around sets of OWL-Axioms)
     */
    abstract public Set< Justification > computeJustifications();

    /**
     * @brief Compute justifications for an assertion.
     *
     * Note that this is the actual place where justifications are computed. The above function calls this one, and does some distinguishing between what kind of axiom is present.
     * @param axiom the assertion to justify.
     * @return a set of sets of OWLAxioms, i.e. the justifications for _axiom_. Each justifications is itself a set of assertions.
     */
    protected Set< Set< OWLAxiom > > explainAxiom( OWLAxiom axiom ) throws OWLException {
        MultipleExplanationGenerator expGen = new HSTExplanationGenerator( method_.equals( "glass" ) ?
                                                                    new GlassBoxExplanation( reasoner_ ) :
                                                                    new BlackBoxExplanation( reasoner_.getRootOntology(),
                                                                            PelletReasonerFactory.getInstance(), reasoner_ ) );
        OWLClassExpression uclass = converter_.convert( axiom );
        Set< Set< OWLAxiom > > expls = expGen.getExplanations( uclass, max_explanations_ );

        if ( method_.equals( "glass" ) ) {
            for ( Iterator< Set< OWLAxiom > > it = expls.iterator(); it.hasNext(); ) {
                Set< OWLAxiom > axioms = it.next();
                OWLOntology debug_ontology = OWL.Ontology( axioms );
                PelletReasoner reasoner = ( ( PelletReasonerFactory ) ( expGen.getReasonerFactory() ) ).createNonBufferingReasoner( debug_ontology );
                boolean satisfiable = uclass.isOWLThing() ? reasoner.isConsistent() : reasoner.isSatisfiable( uclass );

                if ( satisfiable ) {
                    if ( SparqlUpdater.verbose_level > 1 ) {
                        SparqlUpdater.logger.warning( "[ SparQLUpdater ] Explanation incomplete: " + uclass );
                        SparqlUpdater.logger.warning( "[ SparQLUpdater ] in " + axioms );
                        SparqlUpdater.logger.warning( "[ SparQLUpdater ] Removing this explanation. As a result, you may be seeing less explanations than the given max argument even though more explanations exist." + axioms );
                    }

                    it.remove();
                }
            }
        }

        return expls;
    }
}
