\documentclass[10pt,a4paper,msc,twosized=semi]{uustthesis}

\usepackage{cleveref}
\usepackage{lipsum}
\usepackage{textgreek}

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
%include src/chap01.lhs

\chapter{Generator Definitions}

\chapter{Regular Datatypes}

\chapter{By the way ...}
%include src/chap03.lagda

\appendix
\chapter{Some Formulas}

\backmatter
\listoffigures
\listoftables

\bibliographystyle{alpha}
\bibliography{references}

\end{document}


