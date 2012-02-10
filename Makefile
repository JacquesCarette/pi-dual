########################################################################
# Phony targets are scoped, so you probably want to declare them first.
#

.PHONY : clean clean-subcode

# ICFP
p.subc.pdf : p.subc.tex cites.bib
	pdflatex -halt-on-error p.subc.tex
	bibtex p.subc

p.subc.tex : p.tex
	ruby subcode/subc.rb p.tex

# Clean
clean: 
	rm *.subc.*
	rm .subcode_cache*

clean-subcode:
	rm .subcode_cache*

