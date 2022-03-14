C/C++ parser for the CSP XML format version 3.0

(c) 2015 xcsp.org (contact <at> xcsp.org)<br />
(c) 2008 olivier.roussel at cril.univ-artois.fr


### Introduction
The files in this archive contains a C++ parser for the XML format of
CSP/WCSP instances named XCSP 3.0 (see http://xcsp.org). 

This parser uses the libxml2 library which must be installed on your
system

See http://xmlsoft.org/

This library is probably installed on most Linux platforms. Note that
you'll need both the libxml2 and the libxml2-devel packages to compile
your program.

The proposed parser reads the XML file in SAX mode. That means that
each time an XML tag is read, the libxml2 library calls a function of
the parser. In turn, the parser will decode the XML information and
call a function of the solver to transmit the informations that were
read.

The advantage of the SAX mode is that it doesn't use much memory. Its
drawback is that it forces to read the information in the order of
the XML file. In contrast, the DOM model would allow reading the
informations in any order but would require to store the whole XML
file in memory before the solver can grab any information.


Here's how the parser interfaces with the solver. The author of a
solver writes an interface (a set of functions) which are called by
the parser when it decodes a piece of information from the XML file
(this is a callback). These interface functions are in charge of
populating the data structures used by the solver. They don't have to
cope with the XML details (only the parser does). This is in fact an
instance of the Builder Design Pattern
(http://www.developer.com/design/article.php/1502691)

The programmer simply calls the parser with the file to read and with
a reference to the callback functions to use. The parser reads the
file, decodes the information and calls the callback functions that
create the solver data structures. Once the parser is done, the solver
can start its quest of a solution.

Let's take an example to give a clear idea of how it can work:

1. the solver calls the parser
2. the parser reads the XML file, chunk by chunk
3. when the parser reads the &lt;instance&gt; tag, it calls the solver callback's
function <code>beginInstance()</code>. When the parser reads the &lt;/instance&gt; tag,
it calls the function <code>endInstance()</code>.
4. It does the same calls for tags variables, constraints, group,
 slide, block and objectives. These functions are not essentials. Their original
 implementations are empty.
5. when the parser reads the &lt;var&gt; tag, the callback's function
<code>buildVariableInteger</code> is called (depending if the domain is a range or not).
You must override these two functions in order to create your own variables.
6. the same occurs for each type of constraint, with the dedicated
call to <code>buildConstraintXXX</code> where XXX is either Extension, Intension....
Note that all of these functions are surrounded and throw an exception if they
are not overriden.
7. Given an array of variables, a call to <code>buildVariableInteger</code> will occur
for each element of the array
8. Given a group of constraint, a call to the dedicated <code>builConstraintXXX</code> will occur for each arguments
of the group (the same occurs for slide).

###Requirements
 - libxml2
 - cmake >= 3.6
 - c++11 compiler
 
###Installation
open a console and type ````./build.sh````




