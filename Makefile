########################################################################
# Phony targets are scoped, so you probably want to declare them first.
#

.PHONY : clean clean-subcode

# ICFP
rational.subc.pdf : rational.subc.tex cites.bib
	pdflatex -halt-on-error rational.subc.tex
	bibtex rational.subc

rational.subc.tex : rational.tex
	ruby subcode/subc.rb rational.tex

# Clean
clean: 
	rm *.subc.*
	rm .subcode_cache*

clean-subcode:
	rm .subcode_cache*

