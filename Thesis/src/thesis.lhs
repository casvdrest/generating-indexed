\documentclass[10pt,a4paper,msc,twosized=semi]{uustthesis}

\usepackage{framed}
\usepackage{setspace}
\setstretch{1.15}

\renewcommand{\figurename}{Listing}
\renewcommand{\listfigurename}{Code listings}

%% Listings 
\newenvironment{listing}[2] %% #1 = caption #2 = label
{
    \begin{figure}[h]
      \label{#2}
      \begin{framed}
        \caption{#1}
}
{
      \end{framed}
    \end{figure}
}

%% Agda snippets 
\newcommand{\includeagda}[2]{\begin{spacing}{1}\ExecuteMetaData[../src/chap0#1/latex/code.tex]{#2}\end{spacing}}

%% Agda listings
\newcommand{\includeagdalisting}[4]{
  \begin{listing}{#3}{#4} 
    \includeagda{#1}{#2}
  \end{listing} 
}

%% Agda snippets (appendices)
\newcommand{\appincludeagda}[2]{\ExecuteMetaData[../src/app#1/latex/code.tex]{#2}}

%% Agda listings (appendices)
\newcommand{\appincludeagdalisting}[4]{
  \begin{listing}{#3}{#4} 
    \appincludeagda{#1}{#2}
  \end{listing}
}

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

\chapter{Deriving Generators for Indexed Containers}

\chapter{Deriving Generators for Indexed Descriptions}
%include src/chap07/body.lhs

\chapter{Program Term Generation}

\chapter{Implementation in Haskell}

\chapter{Conclusion \& Further Work}

\appendix
\chapter{Datatype Definitions}
%include src/appA/body.lhs

\backmatter
\listoffigures
\listoftables

\bibliographystyle{alpha}
\bibliography{references}

\end{document}


