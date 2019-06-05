\documentclass[a4paper,msc,twosized=semi]{uustthesis}

\usepackage{framed}
\usepackage{mdframed}
\usepackage{setspace}
% \usepackage{extsizes}

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
\newcommand{\includeagda}[2]{\vspace*{-0.35cm}\begin{center}\ExecuteMetaData[../src/chap0#1/latex/code.tex]{#2}\end{center}\vspace*{-0.35cm}}

%% Agda snippets, without removed spacing
\newcommand{\includeagdanv}[2]{\begin{center}\ExecuteMetaData[../src/chap0#1/latex/code.tex]{#2}\end{center}}

%% Agda snippets, not centered
\newcommand{\includeagdanc}[2]{\ExecuteMetaData[../src/chap0#1/latex/code.tex]{#2}\vspace*{-0.35cm}}

%% Agda listings
\newcommand{\includeagdalisting}[4]{
  \begin{listing}{#3}{#4} 
    \includeagdanc{#1}{#2}
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

\newmdenv[
  topline=false,
  bottomline=false,
  rightline=false,
  skipabove=\topsep,
  skipbelow=\topsep
]{siderules}

\newenvironment{example}[0] 
{
  \begin{siderules}
    \vspace{-0.5cm}
    \paragraph{\textbf{Example}}
}
{
  \end{siderules}
}

%include polycode.fmt
%include greek.fmt
%include colorcode.fmt

%include src/hsformat.lhs

\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}
\usepackage{textcomp}

%% Haskell snippet 
\newenvironment{myhaskell}
{
  \vspace{-0.35cm}
  \begin{center}
}
{
  \end{center}
  \vspace{-0.35cm}
}

%% Haskell snippet 
\newenvironment{myhaskellnv}
{
  \begin{center}
}
{
  \end{center}
}


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
%include src/chap02/body.lhs

\chapter{Literature Review}
%include src/chap03/body.lhs

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


