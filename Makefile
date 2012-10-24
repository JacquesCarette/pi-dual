########################################################################
# Phony targets are scoped, so you probably want to declare them first.
#

.PHONY : clean clean-subcode

# ICFP
r.subc.pdf : r.subc.tex cites.bib
	pdflatex -halt-on-error r.subc.tex
	bibtex r.subc
	pdflatex -halt-on-error r.subc.tex
	pdflatex -halt-on-error r.subc.tex

r.subc.tex : r.tex
	ruby subcode/subc.rb r.tex

# Clean
clean: 
	rm *.subc.*
	rm .subcode_cache*

clean-subcode:
	rm .subcode_cache*

