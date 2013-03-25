########################################################################
# Phony targets are scoped, so you probably want to declare them first.
#

.PHONY : clean clean-subcode

frac2.subc.pdf : frac2.tex frac2.subc.tex cites.bib
	pdflatex -halt-on-error frac2.subc.tex
	bibtex frac2.subc
	pdflatex -halt-on-error frac2.subc.tex
	pdflatex -halt-on-error frac2.subc.tex

frac2.subc.tex : frac2.tex
	ruby ../subcode/subc.rb frac2.tex

frac.subc.pdf : frac.tex frac.subc.tex cites.bib
	pdflatex -halt-on-error frac.subc.tex
	bibtex frac.subc
	pdflatex -halt-on-error frac.subc.tex
	pdflatex -halt-on-error frac.subc.tex

frac.subc.tex : frac.tex
	ruby subcode/subc.rb frac.tex

r.subc.pdf : r.subc.tex cites.bib
	pdflatex -halt-on-error r.subc.tex
	bibtex r.subc
	pdflatex -halt-on-error r.subc.tex
	pdflatex -halt-on-error r.subc.tex

r.subc.tex : r.tex
	ruby subcode/subc.rb r.tex

talk.subc.pdf : talk.subc.tex 
	pdflatex talk.subc.tex

talk.subc.tex : talk.tex
	ruby subcode/subc.rb talk.tex

agda-sabry: VecSN.agda VecS.agda Homotopy.agda Pi.agda PiN.agda PiF.agda PiNF-syntax.agda PiNF-algebra.agda PiNF-semantics.agda Pi-abstract-machine.agda Pi-reasoning.agda oldPi.agda
	touch /u/sabry/.hyplan/pi
	/bin/rm -r /u/sabry/.hyplan/pi
	agda --html-dir=/u/sabry/.hyplan/pi --allow-unsolved-metas --html -i . -i /u/sabry/include/agda2/src VecSN.agda
	agda --html-dir=/u/sabry/.hyplan/pi --allow-unsolved-metas --html -i . -i /u/sabry/include/agda2/src VecS.agda
	agda --html-dir=/u/sabry/.hyplan/pi --allow-unsolved-metas --html -i . -i /u/sabry/include/agda2/src Homotopy.agda
	agda --html-dir=/u/sabry/.hyplan/pi --allow-unsolved-metas --html -i . -i /u/sabry/include/agda2/src Pi.agda
	agda --html-dir=/u/sabry/.hyplan/pi --allow-unsolved-metas --html -i . -i /u/sabry/include/agda2/src PiN.agda
	agda --html-dir=/u/sabry/.hyplan/pi --allow-unsolved-metas --html -i . -i /u/sabry/include/agda2/src PiF.agda
	agda --html-dir=/u/sabry/.hyplan/pi --allow-unsolved-metas --html -i . -i /u/sabry/include/agda2/src PiNF-syntax.agda
	agda --html-dir=/u/sabry/.hyplan/pi --allow-unsolved-metas --html -i . -i /u/sabry/include/agda2/src PiNF-algebra.agda
	agda --html-dir=/u/sabry/.hyplan/pi --allow-unsolved-metas --html -i . -i /u/sabry/include/agda2/src PiNF-semantics.agda
	agda --html-dir=/u/sabry/.hyplan/pi --allow-unsolved-metas --html -i . -i /u/sabry/include/agda2/src Pi-abstract-machine.agda
	agda --html-dir=/u/sabry/.hyplan/pi --allow-unsolved-metas --html -i . -i /u/sabry/include/agda2/src Pi-reasoning.agda
	agda --html-dir=/u/sabry/.hyplan/pi --allow-unsolved-metas --html -i . -i /u/sabry/include/agda2/src oldPi.agda

# Clean
clean: 
	rm *.subc.*
	rm .subcode_cache*

clean-subcode:
	rm .subcode_cache*

