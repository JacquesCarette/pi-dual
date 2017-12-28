#!/bin/bash

while inotifywait -e close_write survey.tex; do
    pdflatex -halt-on-error survey.tex;
    bibtex survey.aux;
    pdflatex -halt-on-error survey.tex;
    pdflatex -halt-on-error survey.tex;
done
