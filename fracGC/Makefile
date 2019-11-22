
all : p.pdf

p.pdf : p.tex latex/PiFracDynCode.tex latex/PiFracDynDefCode.tex latex/BooleanCircuitsCode.tex \
	latex/PiPointedFracCode.tex latex/ExtractionCode.tex latex/PiMemSemCode.tex \
	latex/PiFracMemSemCode.tex latex/PiPointedFracTraceCode.tex latex/J.tex \
	idpic.tikz parity.tikz revrev.tikz trace1.tex
#	xelatex p.tex; bibtex p; xelatex p.tex; xelatex p.tex; xelatex p.tex
#	xelatex p.tex; bibtex p
	latexmk -pdfxe p.tex

latex/J.tex : J.lagda
	agda --latex J.lagda

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

latex/PiMemSemCode.tex : PiMemSemCode.lagda
	agda --latex PiMemSemCode.lagda

latex/PiFracMemSemCode.tex : PiFracMemSemCode.lagda
	agda --latex PiFracMemSemCode.lagda

latex/PiPointedFracTraceCode.tex : PiPointedFracTraceCode.lagda
	agda --latex PiPointedFracTraceCode.lagda
