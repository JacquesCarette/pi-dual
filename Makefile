
all : pearl.pdf

pearl.pdf : latex/pearl.tex
	pdflatex latex/pearl.tex

latex/pearl.tex : pearl.lagda
	agda --allow-unsolved-metas --latex -i . -i $(AGDALIB) pearl.lagda


