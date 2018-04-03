package de.unikoblenz.west.evowipe;

// !!!! if you change the JENA version to 3 upwards, need to use these imports: !!!!
//import org.apache.jena.rdf.model.Statement;
//import org.apache.jena.rdf.model.RDFNode;
//import org.apache.jena.rdf.model.Resource;
//import org.apache.jena.rdf.model.Property;
import com.hp.hpl.jena.rdf.model.Statement;
import com.hp.hpl.jena.rdf.model.RDFNode;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.rdf.model.Property;

//import org.coode.owlapi.manchesterowlsyntax.ManchesterOWLSyntaxEditorParser;
import org.semanticweb.owlapi.util.mansyntax.ManchesterOWLSyntaxParser;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLProperty;
import org.semanticweb.owlapi.model.OWLOntology;

import com.clarkparsia.owlapiv3.OWL;
import com.clarkparsia.owlapiv3.OntologyUtils;

/**
 * @brief Convert between Jena statements and 'OWLAxiom's
 */
public class AxiomConverter {
    /**
     * @brief Class functionality
     * @param stmt the Jena statement to convert
     * @return the resulting OWLAxiom
     */
    public static OWLAxiom convert( Statement stmt, OWLOntology ontology ) {
        RDFNode object_or_class = stmt.getObject();
        Resource s = stmt.getSubject();
        Property p = stmt.getPredicate();
        String object_or_class_string = object_or_class.toString();
        String subject_string = s.toString();
        String property_string = p.getLocalName();
        OWLEntity subject;
        OWLEntity cla;
        OWLEntity property;
        OWLObject object;
        OWLAxiom axiom = null;

        if ( property_string.equals( "type" ) ) { // TODO not very robust. How to improve this?
            subject = OntologyUtils.findEntity( subject_string, ontology );
            cla = OntologyUtils.findEntity( object_or_class_string, ontology );

            if ( subject == null ) {
                throw new RuntimeException( "[ Converter ] Undefined entity: " + subject_string );
            }
            else if ( !subject.isOWLNamedIndividual()) {
                throw new RuntimeException( "[ Converter ] Not a defined individual: " + subject_string );
            }

            if ( cla == null ) {
                throw new RuntimeException( "[ Converter ] Undefined entity: " + object_or_class_string );
            }
            else if ( !cla.isOWLClass()) {
                throw new RuntimeException( "[ Converter ] Not a defined class: " + object_or_class_string );
            }

            if ( !( ( ( OWLClass ) cla ).isOWLThing() ) && subject.isOWLNamedIndividual() && cla.isOWLClass() ) {
                axiom = OWL.classAssertion( ( OWLIndividual ) subject, ( OWLClass ) cla );
            }
            else {
                throw new RuntimeException( "[ Converter ] Subject for instance-relation is not of type NamedIndividual or class is not of type OWLClass!" );
            }
        }
        else {
            subject = OntologyUtils.findEntity( subject_string, ontology );
            property = OntologyUtils.findEntity( property_string, ontology );

            if ( subject == null ) {
                throw new RuntimeException( "[ Converter ] Undefined entity: " + subject_string );
            }
            else if ( !subject.isOWLNamedIndividual() ) {
                throw new RuntimeException( "[ Converter ] Not an individual: " + subject_string );
            }

            if ( property == null ) {
                throw new RuntimeException( "[ Converter ] Undefined entity: " + property_string );
            }
            else if ( !property.isOWLObjectProperty() && !property.isOWLDataProperty() ) {
                throw new RuntimeException( "[ Converter ] Not a defined property: " + property_string );
            }

            if ( property.isOWLObjectProperty() ) {
                object = OntologyUtils.findEntity( object_or_class_string, ontology );

                if ( object == null ) {
                    throw new RuntimeException( "[ Converter ] Undefined entity: " + object_or_class_string );
                }
                else if ( !( object instanceof OWLIndividual )) {
                    throw new RuntimeException( "[ Converter ] Not a defined individual: " + object_or_class_string );
                }
            }
            else {
                    //ManchesterOWLSyntaxEditorParser parser = new ManchesterOWLSyntaxEditorParser( loader.getManager().getOWLDataFactory(), object_or_class );
                    ManchesterOWLSyntaxParser parser = OWLManager.createManchesterParser();
                    parser.setStringToParse( object_or_class_string );
                try {
                    object = parser.parseLiteral( null );
                    //object = parser.parseConstant();
                }
                catch ( Exception e ) {
                    throw new RuntimeException( "[ Converter ] Not a valid literal: " + object_or_class_string );
                }
            }

            if ( ( ( OWLProperty ) property ).isOWLObjectProperty() ) {
                axiom = OWL.propertyAssertion( ( OWLIndividual ) subject, ( OWLObjectProperty ) property, ( OWLIndividual ) object );
            }
            else {
                axiom = OWL.propertyAssertion( ( OWLIndividual ) subject, ( OWLDataProperty ) property, ( OWLLiteral ) object );
            }
        }

        return axiom;
    }
}
