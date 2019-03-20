lhs2TeX -o proposal.tex proposal.lagda --agda
bibtex proposal
pdflatex -shell-escape proposal.tex
