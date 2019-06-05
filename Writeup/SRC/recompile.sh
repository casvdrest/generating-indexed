lhs2TeX -o tyde.tex tyde.lagda --agda
bibtex tyde
pdflatex -shell-escape tyde.tex
