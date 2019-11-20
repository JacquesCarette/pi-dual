
all : p.pdf

p.pdf : p.tex latex/PiFracDynCode.tex latex/PiFracDynDefCode.tex latex/BooleanCircuitsCode.tex latex/PiPointedFracCode.tex latex/ExtractionCode.tex
#	xelatex p.tex; bibtex p; xelatex p.tex; xelatex p.tex; xelatex p.tex
#	xelatex p.tex; bibtex p
	latexmk -pdfxe p.tex

latex/PiFracDynCode.tex : PiFracDynCode.lagda
	agda --latex PiFracDynCode.lagda

latex/PiFracDynDefCode.tex : PiFracDynDefCode.lagda
	agda --latex PiFracDynDefCode.lagda

latex/BooleanCircuitsCode.tex : BooleanCircuitsCode.lagda
	agda --latex BooleanCircuitsCode.lagda

latex/PiPointedFracCode.tex : PiPointedFracCode.lagda
	agda --latex PiPointedFracCode.lagda

latex/ExtractionCode.tex : ExtractionCode.lagda
	agda --latex ExtractionCode.lagda
