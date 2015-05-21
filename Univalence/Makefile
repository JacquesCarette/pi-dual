
all : talk.pdf p.pdf

talk.pdf : latex/talk.tex
	pdflatex latex/talk.tex

latex/talk.tex : talk.lagda
	agda --allow-unsolved-metas --latex -i . -i $(AGDALIB) -i $(CATLIB) talk.lagda

p.pdf : latex/p.tex
	pdflatex latex/p.tex; bibtex p

latex/p.tex : p.lagda
	agda --allow-unsolved-metas --latex -i . -i $(AGDALIB) -i $(CATLIB) p.lagda


