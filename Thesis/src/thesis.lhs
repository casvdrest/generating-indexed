\documentclass[10pt,a4paper,msc,twosized=semi]{uustthesis}

\newcommand{\includeagda}[2]{\ExecuteMetaData[../src/chap0#1/latex/code.tex]{#2}}

%include polycode.fmt
%include greek.fmt
%include colorcode.fmt

%include src/hsformat.lhs

\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}
\usepackage{textcomp}

\title{Thesis title}

\author{C.R. van der Rest}

\supervisor{Dr. W.S. Swierstra \\ Dr. M.M.T. Chakravarty \\ Dr. A. Serrano Mena }

%include lhs2TeX.fmt
\begin{document}
\maketitle

%% Set up the front matter of our book
\frontmatter
\tableofcontents

\chapter{Declaration}
Thanks to family, supervisor, friends and hops!

\chapter{Abstract}
Abstract

%% Starts the mainmatter
\mainmatter

\chapter{Introduction}

\chapter{Background}

\chapter{Literature Review}

\chapter{A Combinator Library for Generators}
%include src/chap04/body.lhs

\chapter{Generic Generators for Regular types}
%include src/chap05/body.lhs

\chapter{Deriving Generators for Indexed Containers}\label{chap:derivingregular}

\chapter{Deriving Generators for Indexed Descriptions}

\chapter{Program Term Generation}

\chapter{Implementation in Haskell}

\chapter{Conclusion \& Further Work}

\appendix
\chapter{Some Formulas}

\backmatter
\listoffigures
\listoftables

\bibliographystyle{alpha}
\bibliography{references}

\end{document}


