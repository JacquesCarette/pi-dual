
all : p.pdf

p.pdf : latex/p.tex
	pdflatex latex/p.tex

latex/p.tex : p.lagda
	agda --allow-unsolved-metas --latex -i . -i /u/sabry/include/agda2/src p.lagda

