The Iowa Agda Library (IAL)
Aaron Stump

1. About the library

The goal is to provide a concrete library focused on verification
examples, as opposed to mathematics.  The library has a good number
of theorems for booleans, natural numbers, and lists.  It also has
trees, tries, vectors, and rudimentary IO.  A number of good ideas
come from Agda's standard library.

2. Using the library 

This library has been tested with Agda 2.5.4.  If you are
using an older version of Agda, try version 1.2:

https://svn.divms.uiowa.edu/repos/clc/projects/agda/ial-releases/1.2

Starting with Agda 2.5.1, to use the library you must add it to your
Agda libraries.  On linux, create the directory ~/.agda, and add a file
called "libraries" to it, containing the full path to the .agda-lib file
contained in this directory (for the IAL version 1.3).  Then create
a file called "defaults", and add the word "ial" to it (no quotes).
These steps tell Agda where the IAL library is, and that you want to
include it when opening .agda files in emacs (or with the command-line
tool).

In Agda, you can include the whole library by importing lib.agda.  

You can compile the whole library by running "make".

The library is set up so there are no name conflicts between modules
(except sometimes I have several versions of the same module, like
nat-division and nat-division-wf, and there might
be name conflicts in such cases).

3. Browsing the library

You can get some overview of what is in the library by following
imports from lib.agda (this is the main entry point for the library).

4. Credits

The library is mostly written by myself, but it also includes some
contributions from John Bodeen, Harley Eades, and undergraduates who
took my Programming Language Concepts class, Spring 2014 and 2015,
especially Tom Werner.

5. Releases

Recent releases of the IAL can be found here:

https://github.com/cedille/ial/releases

Older released versions of the library can be found at

https://svn.divms.uiowa.edu/repos/clc/projects/agda/ial-releases

The development version is at

https://github.com/cedille/ial

6. License

This library is currently provided under the MIT License, see LICENSE.txt.

7. Documentation

There is no formal documentation currently, besides comments in the files.

Much of the library is described in my book, "Verified Functional
Programming in Agda", published 2016 with ACM Books.

