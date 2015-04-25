
all : p.pdf

p.pdf : latex/p.tex
	pdflatex latex/p.tex; bibtex p

latex/p.tex : p.lagda
	agda --allow-unsolved-metas --latex -i . -i $(AGDALIB) -i $(CATLIB) p.lagda


