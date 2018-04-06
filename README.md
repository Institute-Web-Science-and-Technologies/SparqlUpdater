# SparqlUpdater
An implementation of dependency-guide semantics and other semantics for SPARQL update.

##  Installation directive: ##

# Requirements/Dependencies #  
1. Operating system  
So far, the system has been used on Ubuntu 14.04.5 LTS exclusively. There has been no experience deploying it on different operating systems. Other Linux distributions should be fine. Windows should technically work just fine as well as long as there is a way to provide command line options.  

2. Java  
Naturally, Java 8 or higher is required to run or build the program.

3. Pellet  
The Pellet reasoner is absolutely required if you are trying to build the program from source code. Otherwise, it should not be a requirement.  https://github.com/stardog-union/pellet.  

4. Maven  
For anything else, there is an Apache Maven pom.xml configuration file provided in the repository that should automatically download any other required libraries. Keep in mind however that Pellet will have to be added externally to your local Maven configuration, and thus the pom.xml will likely need to be adjusted accordingly to reflect your installation.  

# Instructions #  
For simply running the distributed program, which should - in its basic form - just be a .jar file, you do not actually require anything else! However, keep in mind that not all ontology formats are supported; common OWL RDF should work fine for starters. If building from source, it is required to build Pellet first and foremost. In my case, the cloned Pellet directory then had a folder named ”dist/lib” which included .jar files for each Pellet module that I could import in Maven. The pom.xml reflects the local configuration on our system. This approach is somewhat clumsy. Pellet should also come with its own pom.xml files that could naturally be imported as well to build everything automatically along with our Sparql-Updater. There really are a variety of ways to do this. The important step remains importing the individual Pellet modules into Maven so that they can be used during the compilation process.  

## Usage ##

Please refer to the provided documentation PDF file. You can also get a help info text:  

```
foo@bar:<path−to−sparqlupdater−target−folder>$java −jar sparqlupdater−0.0.1.jar -h
```
