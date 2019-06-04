all: slides.pdf

slides.pdf : latex/slides.tex latex/Equiv.tex
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

latex/Equiv.tex : ../Univalence/Equiv.lagda
	agda --latex -i . -i ../Univalence ../Univalence/Equiv.lagda
