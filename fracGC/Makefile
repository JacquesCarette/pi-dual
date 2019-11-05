
all : p.pdf

p.pdf : latex/p.tex
	cd latex; xelatex p.tex; bibtex p
#	cd latex; lualatex p.tex; bibtex p

latex/p.tex : p.lagda
#	agda --allow-unsolved-metas --latex p.lagda
	agda --latex p.lagda


