RCforBX.pdf : latex/RCforBX.tex
	pdflatex latex/RCforBX.tex
	bibtex RCforBX
	pdflatex latex/RCforBX.tex
	pdflatex latex/RCforBX.tex

latex/RCforBX.tex : RCforBX.lagda
	agda --allow-unsolved-metas --latex -i . RCforBX.lagda
