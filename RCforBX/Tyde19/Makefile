RCforBX.pdf : latex/RCforBX.tex
	latexmk -pdf RCforBX.tex

latex/RCforBX.tex : RCforBX.lagda
	agda --allow-unsolved-metas --latex-dir=. --latex -i . -i ../../Univalence RCforBX.lagda
