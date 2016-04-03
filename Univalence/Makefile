esop_slides.pdf : latex/esop_slides.tex esop_slides.lagda
	pdflatex latex/esop_slides.tex; bibtex esop_slides; pdflatex latex/esop_slides.tex; pdflatex latex/esop_slides.tex

latex/esop_slides.tex : esop_slides.lagda
	agda --allow-unsolved-metas --latex -i . -i $(AGDALIB) -i $(CATLIB) esop_slides.lagda

esop2.pdf : latex/esop2.tex
	pdflatex latex/esop2.tex; bibtex esop2; pdflatex latex/esop2.tex; pdflatex latex/esop2.tex

latex/esop2.tex : esop2.lagda
	agda --allow-unsolved-metas --latex -i . -i $(AGDALIB) -i $(CATLIB) esop2.lagda

esop.pdf : latex/esop.tex
	pdflatex latex/esop.tex; bibtex esop; pdflatex latex/esop.tex; pdflatex latex/esop.tex

latex/esop.tex : esop.lagda
	agda --allow-unsolved-metas --latex -i . -i $(AGDALIB) -i $(CATLIB) esop.lagda

talk.pdf : latex/talk.tex
	pdflatex latex/talk.tex

latex/talk.tex : talk.lagda
	agda --allow-unsolved-metas --latex -i . -i $(AGDALIB) -i $(CATLIB) talk.lagda

p.pdf : latex/p.tex
	pdflatex latex/p.tex; bibtex p

latex/p.tex : p.lagda
	agda --allow-unsolved-metas --latex -i . -i $(AGDALIB) -i $(CATLIB) p.lagda


