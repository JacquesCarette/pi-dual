
all : ring.pdf

ring.pdf : latex/ring.tex
#	export TEXINPUTS=".//:" ; pdflatex latex/ring.tex
	pdflatex latex/ring.tex ; bibtex ring

latex/ring.tex : ring.lagda
	agda --allow-unsolved-metas --latex -i . -i $(AGDALIB) ring.lagda

