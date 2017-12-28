#!/bin/bash

while inotifywait -e close_write survey.tex; do
    pdflatex survey.tex;
    bibtex survey.aux;
    pdflatex survey.tex;
    pdflatex survey.tex;
done
