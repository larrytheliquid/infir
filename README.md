Generic Lookup and Update for Infinitary Inductive-Recursive Types
==================================================================

Agda code for draft paper by Larry Diehl and Tim Sheard (submitted for consideration to [TyDe 2016](http://conf.researchr.org/track/icfp-2016/tyde-2016-papers)):

Draft
---------------

* [PDF version](https://dl.dropboxusercontent.com/u/31465260/drafts/infir.pdf)
* [Literate Agda version](paper/infir.tex)

You can build the paper in the `paper` directory with a command like:

`agda --latex-dir=. -i /PATH/TO/AGDA-STDLIB/src/ -i . --latex infir.lagda && pdflatex infir.texagda --latex-dir=. -i /PATH/TO/AGDA-STDLIB/src/ -i . --latex infir.lagda && pdflatex infir.tex`


Standalone code
---------------

* [Concrete large `Type` universe](src/Infir/ConcreteLarge.agda)
  * [Correctness proof](src/Infir/ConcreteLarge.agda#L82-L115)
* [Concrete small `Arith` universe](src/Infir/ConcreteSmall.agda)
  * [Correctness proof](src/Infir/ConcreteSmall.agda#L122-L155)
* [Generic open universe](src/Infir/GenericOpen.agda)
  * [Correctness proof](src/Infir/GenericOpen.agda#L160-L222)
* [Generic closed universe](src/Infir/GenericClosed.agda)
  * [Correctness proof](src/Infir/GenericOpen.agda#L196-L270)

Additionally, a [universe polymorphic version](src/Infir/GenericOpenHier.agda) of the generic open universe.

Notes
-----

The code is released under an [MIT license](src/LICENSE)
