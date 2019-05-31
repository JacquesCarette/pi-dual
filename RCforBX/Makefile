all: slides.pdf

slides.pdf : latex/slides.tex
	pdflatex latex/slides.tex
	bibtex RCforBX
	pdflatex latex/slides.tex
	pdflatex latex/slides.tex

RCforBX.pdf : latex/RCforBX.tex
	pdflatex latex/RCforBX.tex
	bibtex RCforBX
	pdflatex latex/RCforBX.tex
	pdflatex latex/RCforBX.tex

latex/RCforBX.tex : RCforBX.lagda
	agda --allow-unsolved-metas --latex -i . -i ../Univalence RCforBX.lagda

latex/slides.tex : slides.lagda
	agda --latex -i . -i ../Univalence slides.lagda
