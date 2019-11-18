
all : p.pdf

p.pdf : p.tex latex/PiFracDynCode.tex
	xelatex p.tex; bibtex p; xelatex p.tex; xelatex p.tex; xelatex p.tex

latex/PiFracDynCode.tex : PiFracDynCode.lagda
	agda --latex PiFracDynCode.lagda


