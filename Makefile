
all : ring.pdf

ring.pdf : latex/ring.tex
	pdflatex latex/ring.tex

latex/ring.tex : ring.lagda
	agda --allow-unsolved-metas --latex -i . -i /u/sabry/include/agda2/src ring.lagda

