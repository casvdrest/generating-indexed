\documentclass[11pt]{article}

%include agda.fmt
%include polycode.fmt
%include greek.fmt

\usepackage[top=4cm,bottom=4cm,left=3cm,right=3cm]{geometry} 
\usepackage{fancyhdr}
\pagestyle{fancy}

\usepackage{textcomp}

\DeclareUnicodeCharacter{10218}{$\langle\langle$}
\DeclareUnicodeCharacter{10219}{$\rangle\rangle$}
\DeclareUnicodeCharacter{7522}{\textsubscript{i}}
\DeclareUnicodeCharacter{10631}{$\llparenthesis$}
\DeclareUnicodeCharacter{10632}{$\rrparenthesis$}

\renewcommand{\figurename}{Listing}
\usepackage[font=small,labelfont=bf]{caption}

\usepackage{cite}

\usepackage[T1]{fontenc}
\rhead{\leftmark}
\cfoot{\textsc{Utrecht University}}
\rfoot{\thepage}
% Quotes
\usepackage{epigraph}

\usepackage{geometry}

\usepackage{textgreek}

\usepackage{multicol}

% Math
\usepackage{amssymb}
\usepackage[inference, ligature]{semantic}
% Tables
\usepackage{amsmath}

% Colors
\usepackage{xcolor, color, colortbl}
\colorlet{gray}{gray!70}
\colorlet{green}{green!50}
\definecolor{darkblue}{HTML}{1D577A}
\definecolor{rred}{HTML}{C03425}
\definecolor{darkgreen}{HTML}{8BB523}
\definecolor{ppurple}{HTML}{6B1B7F}
\definecolor{pblack}{HTML}{000000}
\definecolor{darkyellow}{HTML}{C0B225}

% Links
\usepackage{hyperref}
\definecolor{linkcolour}{rgb}{0,0.2,0.6}
\hypersetup{colorlinks,breaklinks,urlcolor=linkcolour,linkcolor=linkcolour,citecolor=blue}

% Geometry
%\usepackage{titling}
%\setlength{\droptitle}{-7em}

\title{Program Term Generation Through Enumeration of Indexed Data Types (Thesis Proposal)}
\author{Cas van der Rest}
\date{\today}

\begin{document}

\maketitle

\tableofcontents 

\newpage

\section{Introduction}

A common way of asserting a program's correctness is by defining properties that should universally hold, and asserting these properties over a range of random inputs. This technique is commonly referred to as \textit{property based testing}, and generally consists of a two-step process. Defining properties that universially hold on all inputs, and defining \textit{generators} that sample random values from the space of possible inputs. \textit{QuickCheck} \cite{claessen2011quickcheck} is likely the most well known tool for performing property based tests on haskell programs. 

Although coming up with a set of properties that propertly captures a program's behavious might initially seem to be the most involved part of the process, defining suitable generators for complex input data is actually quite difficult as well. Questions such as how to handle datatypes that are inhabited by an infinite numer of values arise, or how to deal with constrained input data. The answers to these questions are reasonably well understood for \textit{Algebraic Data Types (ADT's)}, but no general solution exists when more complex input data is required. In particular, little is known about enumerating and generating inhabitants of \textit{Indexed Data Types}. 

The latter may be of interest when considering property based testing in the context of languages with a more elaborate type system than Haskell's, such as \textit{Agda} or \textit{Idris}. Since the techniques used in existing tools such as QuickCheck and SmallCheck for the most part only apply to regular data types, meaning that there is no canonical way of generating inhabitants for a large class of datatypes in these languages. 

Besides the obvious applications to property based testing in the context of dependently typed languages, a broader understanding of how we can generate inhabitants of indexed datatypes may prove useful in other areas as well. Since we can often capture a programming language's semantics as an indexed data type, efficient generation of inhabitants of such a datatype may prove useful for testing compiler infrastructure. 

\subsection{Problem Statement}

\subsection{Research Questions and Contributions}

What is the problem? Illustrate with an example. \cite{runciman2008smallcheck, altenkirch2003generic}

What is/are your research questions/contributions? \cite{claessen2011quickcheck}

\section{Background}

What is the existing technology and literature that I'll be
studying/using in my research \cite{denes2014quickchick, yorgey2010species, loh2011generic, norell2008dependently}

\subsection{Dependently Typed Programming \& Agda}

\subsubsection{Propositions as Types}

\subsubsection{Codata}

\subsection{Property Based Testing}

\subsubsection{Existing Libraries}

\subsubsection{Generating Test Data}

\subsection{Generic Programming \& Type Universes}

\subsubsection{Regular Datatypes}

\subsubsection{Ornaments}

\subsubsection{Functorial Species}

\subsubsection{Indexed Functors}

\subsection{Blockchain Semantics}

\subsubsection{BitML}

\subsubsection{UTXO \& Extended UTXO}

\begin{itemize}

\item
Libraries for property based testing (QuickCheck, (Lazy) SmallCheck, QuickChick, QuickSpec)

\item 
Type universes (ADT's, Ornaments) \cite{ko2016programming, dagand2017essence}

\item 
Generic programming techniques. (pattern functors, indexed functors, functorial species)

\item 
Techniques to generate complex or constrained data (Generating constrained random data with uniform distribution, Generators for inductive relations)

\item 
Techniques to speed up generation of data (Memoization, FEAT)

\item 
Formal specification of blockchain (bitml, (extended) UTxO ledger) \cite{zahnentferner2018chimeric, zahnentferner2018abstract}

\item 
Representing potentially infinite data in Agda (Colists, coinduction, sized types)

\end{itemize}

Below is a bit of Agda code: 

\begin{figure}[h] \hrulefill
\begin{code}
Γ-match : (τ : Ty) → ⟪ ωᵢ (λ Γ → Σ[ α ∈ Id ] Γ [ α ↦ τ ]) ⟫
Γ-match τ μ ∅ = uninhabited
Γ-match τ μ (α ↦ σ ∷ Γ) with τ ≟ σ
Γ-match τ μ (α ↦ τ ∷ Γ)  | yes refl   =  ⦇  (α , TOP)          ⦈
                                      ∥  ⦇  (Σ-map POP) (μ Γ)  ⦈
Γ-match τ μ (α ↦ σ ∷ Γ)  | no ¬p      =  ⦇  (Σ-map POP) (μ Γ)  ⦈
\end{code} 
\hrulefill
\caption{Definition of \textGamma-match}
\end{figure}

\begin{figure}[h] \hrulefill
\begin{code}
data Env : Set where
  ∅     : Env
  _↦_∷_ : Id → Ty → Env → Env
\end{code}

\begin{code}
data _[_↦_] : Env → Id → Ty → Set where
{-""-}
  TOP  :  ∀  {Γ α τ}
          →  (α ↦ τ ∷ Γ) [ α ↦ τ ] 
{-""-}
  POP  :  ∀  {Γ α β τ σ} → Γ [ α ↦ τ ]                            
          →  (β ↦ σ ∷ Γ) [ α ↦ τ ]
\end{code}
\hrulefill
\caption{Envirionment definition and membership in \textit{Agda}}
\end{figure}

\begin{figure}[h] 
\hrulefill

\begin{equation*}
  TOP\ \frac{}{(\textalpha \mapsto \texttau : \Gamma) [\textalpha \mapsto \texttau]} 
\quad\quad\quad 
  POP\ \frac{\Gamma[\textalpha \mapsto \texttau]}{(\textbeta \mapsto \textsigma : \Gamma) [ \textalpha \mapsto \texttau ] }
\end{equation*}

\begin{equation*}
  VAR\ \frac{\Gamma[\textalpha \mapsto \tau]}{\Gamma \vdash \textalpha : \tau}
\quad\quad\quad
  ABS\ \frac{\Gamma , \textalpha \mapsto \sigma \vdash t : \tau}{\Gamma \vdash \lambda \textalpha \rightarrow t : \sigma \rightarrow \tau}
\end{equation*}

\begin{equation*}
  APP\ \frac{\Gamma \vdash f : \sigma \rightarrow \tau \quad \Gamma \vdash x : \sigma}{\Gamma \vdash f x : \tau}
\quad\quad\quad 
  LET\ \frac{\Gamma \vdash e : \sigma \quad \Gamma , \textalpha \mapsto \sigma \vdash t : \tau}
            {\Gamma \vdash \texttt{ let } \textalpha := e \texttt{ in } t : \tau }
\end{equation*}

\hrulefill
\caption{Semantics of the \textit{Simply Typed Lambda Calculus}}
\end{figure}


\section{Preliminary results}

What examples can you handle already? \cite{lampropoulos2017generating}

What prototype have I built? \cite{duregaard2013feat, claessen2010quickspec}

How can I generalize these results? What problems have I identified or
do I expect? \cite{yakushev2009generic}

\section{Timetable and planning}

What will I do with the remainder of my thesis? \cite{claessen2015generating}

Give an approximate estimation/timetable for what you will do and when you will be done.

\newpage
\bibliography{references}{}
\bibliographystyle{plain}

\end{document}paramter