\documentclass[a4paper,msc,twosized=semi]{uustthesis}

\usepackage{framed}
\usepackage{mdframed}
\usepackage{setspace}
\usepackage{fontspec}
\usepackage{mathtools}


\newfontfamily{\agdafont}{DejaVu Sans Mono}[Scale=MatchLowercase]
\newfontfamily{\agdafontinline}{DejaVu Sans Mono}[Scale=MatchLowercase]
\renewcommand{\figurename}{Listing}
\renewcommand{\listfigurename}{Code listings}

\let\oldemph\emph
\renewcommand\emph[1]{{\large\oldemph{#1}}}

\definecolor{agdacolor}{rgb}{ 0.15 , 0 , 0.6 }

\newcommand{\agda}[1]{{\agdafontinline\color{agdacolor}#1}}

%% Listings 
\newenvironment{listing}[2] %% #1 = caption #2 = label
{
    \begin{figure}[h]
      \label{#2}
      \begin{mdframed}[linecolor=black!50]
        \caption{#1}
}
{
      \end{mdframed}
    \end{figure}
}
%% Agda snippets 
\newcommand{\includeagda}[2]{\vspace*{-0.25cm}\begin{center}{\fontsize{12}{14}\agdafont\ExecuteMetaData[../src/chap0#1/latex/code.tex]{#2}}\end{center}\vspace*{-0.25cm}}

%% Agda snippets, without removed spacing
\newcommand{\includeagdanv}[2]{\begin{center}{\fontsize{12}{14}\agdafont\ExecuteMetaData[../src/chap0#1/latex/code.tex]{#2}}\end{center}}

%% Agda snippets, not centered
\newcommand{\includeagdanc}[2]{{\fontsize{12}{14}\agdafont\ExecuteMetaData[../src/chap0#1/latex/code.tex]{#2}}\vspace*{-0.25cm}}

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
  skipbelow=\topsep, 
  linecolor=black!50
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

%format <$> = "\ {\color{gray}\mathbin{<\hspace{-1.6pt}\mathclap{\raisebox{0.1pt}{\scalebox{.8}{\$}}}\hspace{-1.6pt}>}}\ "
%format <*> = "\ {\color{gray}\mathbin{<\hspace{-1.1pt}\mathclap{\raisebox{0.1pt}{\scalebox{1.2}{$*$}}}\hspace{-1.1pt}>} }\ "
%format :*: = "\ {\color{gray}\mathbin{:\hspace{-0.3pt}\mathclap{\raisebox{0.1pt}{\scalebox{1.2}{$*$}}}\hspace{-0.3pt}:}}\ "
%format :+> = "\ {\color{gray}\mathbin{:\hspace{-0.1pt}\mathclap{\raisebox{0.1pt}{\scalebox{.9}{$+$}}}\hspace{-0.3pt}>}}\ "
%format :*:$ = "\ {\color{gray}\mathbin{:\hspace{-0.3pt}\mathclap{\raisebox{0.1pt}{\scalebox{1.2}{$*$}}}\hspace{-0.3pt}:}{\scalebox{1}{\$}}}\ "
%format :+>$ = "\ {\color{gray}\mathbin{:\hspace{-0.1pt}\mathclap{\raisebox{0.1pt}{\scalebox{.9}{$+$}}}\hspace{-0.3pt}>}{\scalebox{1}{\$}}}\ "
%format :::$ = "\ {\color{gray}\mathbin{:\hspace{-0.3pt}:\hspace{-0.3pt}:\hspace{-0.3pt}\hspace{-0.1pt}}{\scalebox{1}{\$}}}\ "
%format :-> = "\ {\color{gray}\mathbin{:\hspace{-0.1pt}\mathclap{\raisebox{0.1pt}{\scalebox{.9}{$-$}}}\hspace{-0.3pt}>}}\ "
%format :->$ = "\ {\color{gray}\mathbin{:\hspace{-0.1pt}\mathclap{\raisebox{0.1pt}{\scalebox{.9}{$-$}}}\hspace{-0.3pt}>}{\scalebox{1}{\$}}}\ "
%format . = "\ .\ "

\title{Generating Constrained Test Data using Datatype Generic Programming}

\author{C.R. van der Rest}

\supervisor{Dr. W.S. Swierstra \\ Dr. M.M.T. Chakravarty \\ Dr. A. Serrano Mena }

\setstretch{1.125}

%include lhs2TeX.fmt
\begin{document}
\maketitle


%% Set up the front matter of our book
\frontmatter
\tableofcontents

\chapter{Declaration}
Thanks to family, supervisor, friends and hops!
\\ \\
I declare that this thesis has been composed solely by myself and that it has not been
submitted, in whole or in part, in any previous application for a degree. Except where
stated otherwise by reference or acknowledgment, the work presented is entirely my
own.

\chapter{Abstract}
The generation of suitable test data is an essential part of \emph{property based testing}. Obtaining test data is simple enough when there are no additional constraints, however things become more complicated once we require data with a richer structure, for example well-formed programs when testing a compiler. We observe that we can often describe constrained data as an \emph{indexed family}. By generating values of an indexed family that describes a set of constrained test data, we simultaneously obtain a way to generate the constrained data itself. To achieve this goal, we consider three increasingly expressive type universes: \emph{regular types}, \emph{indexed containers} and \emph{indexed descriptions}. We show how generators can be derived from codes in these universes, and for \emph{regular types} and \emph{indexed descriptions} we show that these derived generators are \emph{complete}. We implement the generic generator for indexed descriptions in Haskell, and use this implementation to generate constrained test data, such as well-typed lambda terms. 

%% Starts the mainmatter
\mainmatter

\chapter{Introduction}
%include src/chap01/body.lhs

\chapter{Background \& Prerequisites}
%include src/chap023/body.lhs 

\part{Theoretical Model}

\chapter{Regular types}
%include src/chap05/body.lhs

\chapter{Indexed Containers}
%include src/chap06/body.lhs

\chapter{Indexed Descriptions}
%include src/chap07/body.lhs 

%% \chapter{A Combinator Library for Generators}
%% %include src/chap04/body.lhs

\part{Implementation}

\chapter{Generators for Indexed Descriptions in Haskell}
%include src/chap08/body.lhs

\chapter{Discussion}
%include src/chap09/body.lhs

%% \appendix
%% \chapter{Datatype Definitions}
%% %include src/appA/body.lhs

\backmatter
\listoffigures

\bibliographystyle{acm}
\bibliography{references}

\end{document}


