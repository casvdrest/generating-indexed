
default:slides.pdf

verbose:slides.md
	pandoc -t beamer slides.md -o slides.pdf --slide-level=2 --latex-engine=xelatex --verbose --template include/beamer-template.tex


slides.pdf:slides.md
	pandoc -t beamer slides.md -o slides.pdf --slide-level=2 --latex-engine=xelatex --template include/beamer-template.tex


