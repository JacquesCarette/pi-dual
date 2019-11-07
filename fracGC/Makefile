
all : p.pdf

p.pdf : p.tex latex/PiFracDynCode.tex
	cd latex; xelatex p.tex; bibtex p

latex/PiFracDynCode.tex : PiFracDynCode.lagda
	agda --latex PiFracDynCode.lagda


