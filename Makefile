########################################################################
# Phony targets are scoped, so you probably want to declare them first.
#

.PHONY : clean clean-subcode

# ICFP
dual.subc.pdf : dual.subc.tex cites.bib
	pdflatex -halt-on-error dual.subc.tex
	bibtex dual.subc

dual.subc.tex : dual.tex
	ruby subcode/subc.rb dual.tex

# Clean
clean: 
	rm *.subc.*
	rm .subcode_cache*

clean-subcode:
	rm .subcode_cache*

