########################################################################
# Phony targets are scoped, so you probably want to declare them first.
#

.PHONY : clean clean-subcode

# ICFP
rational_ext.subc.pdf : rational_ext.subc.tex cites.bib
	pdflatex -halt-on-error rational_ext.subc.tex
	bibtex rational_ext.subc
	pdflatex -halt-on-error rational_ext.subc.tex
	pdflatex -halt-on-error rational_ext.subc.tex

rational_ext.subc.tex : rational_ext.tex
	ruby subcode/subc.rb rational_ext.tex

# Clean
clean: 
	rm *.subc.*
	rm .subcode_cache*

clean-subcode:
	rm .subcode_cache*

