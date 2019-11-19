
all : p.pdf

p.pdf : p.tex latex/PiFracDynCode.tex latex/BooleanCircuitsCode.tex
#	xelatex p.tex; bibtex p; xelatex p.tex; xelatex p.tex; xelatex p.tex
	xelatex p.tex; bibtex p

latex/PiFracDynCode.tex : PiFracDynCode.lagda
	agda --latex PiFracDynCode.lagda

latex/BooleanCircuitsCode.tex : BooleanCircuitsCode.lagda
	agda --latex BooleanCircuitsCode.lagda


