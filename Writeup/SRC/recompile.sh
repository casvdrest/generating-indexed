lhs2TeX -o SRC.tex SRC.lhs 
bibtex SRC
pdflatex -shell-escape SRC.tex
