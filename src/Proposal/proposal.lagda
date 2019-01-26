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

\title{Program Term Generation Through Enumeration of Indexed datatypes (Thesis Proposal)}
\author{Cas van der Rest}
\date{\today}

\begin{document}

\maketitle

\tableofcontents 

\newpage

\section{Introduction}

A common way of asserting a program's correctness is by defining properties that should universally hold, and asserting these properties over a range of random inputs. This technique is commonly referred to as \textit{property based testing}, and generally consists of a two-step process. Defining properties that universially hold on all inputs, and defining \textit{generators} that sample random values from the space of possible inputs. \textit{QuickCheck} \cite{claessen2011quickcheck} is likely the most well known tool for performing property based tests on haskell programs. 

Although coming up with a set of properties that propertly captures a program's behavious might initially seem to be the most involved part of the process, defining suitable generators for complex input data is actually quite difficult as well. Questions such as how to handle datatypes that are inhabited by an infinite numer of values arise, or how to deal with constrained input data. The answers to these questions are reasonably well understood for \textit{Algebraic datatypes (ADT's)}, but no general solution exists when more complex input data is required. In particular, little is known about enumerating and generating inhabitants of \textit{Indexed datatypes}. 

The latter may be of interest when considering property based testing in the context of languages with a more elaborate type system than Haskell's, such as \textit{Agda} or \textit{Idris}. Since the techniques used in existing tools such as QuickCheck and SmallCheck for the most part only apply to regular datatypes, meaning that there is no canonical way of generating inhabitants for a large class of datatypes in these languages. 

Besides the obvious applications to property based testing in the context of dependently typed languages, a broader understanding of how we can generate inhabitants of indexed datatypes may prove useful in other areas as well. Since we can often capture a programming language's semantics as an indexed datatype, efficient generation of inhabitants of such a datatype may prove useful for testing compiler infrastructure. 

\subsection{Problem Statement}

\subsection{Research Questions and Contributions}

What is the problem? Illustrate with an example. \cite{runciman2008smallcheck, altenkirch2003generic}

What is/are your research questions/contributions? \cite{claessen2011quickcheck}

\section{Background}

What is the existing technology and literature that I'll be
studying/using in my research \cite{denes2014quickchick, yorgey2010species, loh2011generic, norell2008dependently}

\subsection{Dependently Typed Programming \& Agda}

\subsubsection{Dependent Type Theory}

Dependent type theory extends a type theory with the possiblity of defining types that depend on values. In addition to familiar constructs, such as the unit type ($\top$) and the empty type $\bot$, one can use so-called $\Pi$-types and $\Sigma$-types. $\Pi$-types capture the idea of dependent function types, that is, \textit{functions} whose output type may depent on the values of its input. Given some type $A$ and a family $P$ of types indexed by values of type $A$ (i.e. $P$ has type $A \rightarrow Type$), $\Pi$-types have the following definition: 

\begin{equation*}
\Pi_{(x : A)} P(x) \quad \equiv \quad (x : A) \rightarrow P(x) 
\end{equation*}

In a similar spirit, $\Sigma$-types are ordered \textit{pairs} of which the type of the second value may depend on te first value of the pair. 

\begin{equation*}
\Sigma_{(x : A)} P(x) \quad \equiv \quad (x : A) \times P(x) 
\end{equation*}

The Curry-Howard equivalence extends to $\Pi$- and $\Sigma$-types as well: they can be used to model universal and existential quantification. 

\subsubsection{Codata and Sized Types}

Agda requires all functions to be total, where total means that they should be defined on any possible input, and give a result in a finite amount of time. The latter means that Agda is equipped with a termination checker that tries to prove that functions terminate. It is implied by undecidability of the halting problem that such a checker cannot be both sound and complete. Agda's termination checker is sound, meaning that there are functions that terminate which get rejected. This means that we cannot represent infinite structures in the same way as in haskell. For example, we might use the following definition in Haskell: \textt{nats = 0 : map (+1) nats}. A similar definition in Agda will get rejected by the termination checker. 

\subsection{Property Based Testing}

\subsubsection{Existing Libraries}

\subsubsection{Generating Test Data}

\subsection{Generic Programming \& Type Universes}

If we desire to abstract over the structure of datatypes, we need a suitable type universe to do so. Many such universes have been developed and studied; this section discusses a few of them. 

\subsubsection{Regular Datatypes}

The term \textit{regular datatypes} is often used to refer to the class of datatypes that can be assembled using any combination of products, coproducts, unary constructors, constants (a position that is inhabited by a value of another type) and recursive positions. Roughly, this class consists of ADT's in haskell, though mutual recursion is not accounted for. 

Any value that lives in the induced by these combinators describes a regular datatype, and is generally referred to as a \textit{pattern functor}. We can define a datatype in agda that captures these values: 

\begin{code}
data Reg : Set →  Set where
    U    : Reg ⊥
    K    : (a : Set) → Reg a
    _⊕_  : ∀ {a : Set} → Reg a → Reg a → Reg a
    _⊗_  : ∀ {a : Set} → Reg a → Reg a → Reg a
    I    : Reg ⊥
\end{code}

Pattern functors, i.e. values of the $Reg$ datatype, can be interpreted as types. Inhabitants of the interpretation of a pattern functor correspond to the inhabitants of the type that is represented by said pattern functor. We use the following interpretation function: 

\begin{code}
⟦_⟧ : Reg → Set → Set
⟦ U            ⟧ r = ⊤
⟦ K a          ⟧ r = a
⟦ reg₁ ⊕ reg₂  ⟧ r = ⟦ reg₁ ⟧ r ⊎ ⟦ reg₂ ⟧ r
⟦ reg₁ ⊗ reg₂  ⟧ r = ⟦ reg₁ ⟧ r × ⟦ reg₂ ⟧ r 
⟦ I            ⟧ r = r
\end{code}

Notice that recursive positions are left explicit. This means that we require an appropriate fixed-point combinator to find a pattern functor's representation in \textbf{Set}. 

\begin{code}
data μ (f : Reg) : Set where
  `μ : ⟦ f ⟧ (μ f) → μ f
\end{code}

\paragraph{Example} Consider the pattern functor corresponding to the definition of $List$: 

\begin{code}
List' : Set → Set
List' a = μ (U ⊕ (K a ⊗ I))
\end{code}

Notice that this pattern functor denotes a choice between a unary constructor ($[]]$), and a constructor that takes a constant of type $a$ and a recursive positions as arguments ($::$). We can define conversion functions between the standard $List$ type, and the interpretation of our pattern functor: 

\begin{code}
fromList : ∀ {a : Set} → List a → List' a
fromList [] = `μ (inj₁ tt)
fromList (x ∷ xs) = `μ (inj₂ (x , fromList xs))
\end{code}

\begin{code}
toList : ∀ {a : Set} → List' a → List a
toList (`μ (inj₁ tt)) = []
toList (`μ (inj₂ (fst , snd))) = fst ∷ toList snd
\end{code}

With these definitions, it is now trivial to show that there is indeed an isomorphism between the two: 

\begin{code}
isoList₁ : ∀ {a : Set} {xs : List a} → toList (fromList xs) ≡ xs
isoList₁ {xs = []} = refl
isoList₁ {xs = x ∷ xs} = cong (_∷_ x) isoList₁
\end{code}

\begin{code}
isoList₂ : ∀ {a : Set} {xs : List' a} → fromList (toList xs) ≡ xs
isoList₂ {xs = `μ (inj₁ x)} = refl
isoList₂ {xs = `μ (inj₂ (fst , snd))} = cong (`μ ∘ inj₂ ∘ _,_ fst) isoList₂
\end{code}

Using such isomorphisms, we can automatically derive functionality for datatypes that can be captured using pattern functors. We will see an example of this in section \ref{preliminary}, where we will derive enumeration of inhabitants for arbitrary pattern functors. 

\subsubsection{Ornaments}

\textit{Ornaments} \cite{dagand2017essence} provide a type universe in which we can describe the structure of indexed datatypes in a very index-centric way. Indexed datatypes are described by \textit{Signatures}, consisting of three elements:

\begin{itemize}
\item 
A function $Op : I \rightarrow Set$, that relates indices to operations/constructors

\item 
A function $Ar : Op\ i \rightarrow Set$, that describes the arity (with respect to recursive positions) for an operation 

\item 
A typing discipline $Ty : Ar\ op \rightarrow I$, that describes indices for recursive positions. 

\end{itemize}

When combined into a single structure, we say that $\Sigma_D$ gives the signature of some indexed datatype $D : I \rightarrow Set$:  

\begin{equation*}
\Sigma_D(I)=
\begin{cases}
Op : I \rightarrow Set \\
Ar : Op\ i \rightarrow Set \\
Ty : Ar\ op \rightarrow I
\end{cases}
\end{equation*}

\paragraph{Example} Let us consider the signature for the $Vec$ type, given by $\Sigma_{Vec}(\mathbb{N})$. Recall the definition of the $Vec$ datatype in listing \ref{vecdef}. It has the following relation between index and operations: 

\begin{code}
Op-vec : ∀ {a : Set} → ℕ → Set
Op-vec zero = ⊤
Op-vec {a} (suc n) = a
\end{code} 

If the index is $zero$, we have only the unary constructor $[]$ at our disposal, hence \texttt{Op-vec zero = top}. If the index is $suc\ n$, the number of possible constructions for $Vec$ corresponds to the set of inhabitants of its element type, hence we say that \texttt{Op-vec (suc n) = a}. 

The $[]$ constructor has no recursive argument, so its arity is $\bot$. Similarly, $cons\ a$ takes one recursive argument, so its arity is $\top$:  

\begin{code}
Ar-vec : ∀ {a : Set} → (n : ℕ) → Op-vec {a} n → Set
Ar-vec zero tt = ⊥
Ar-vec (suc n) op = ⊤
\end{code} 

The definition of $::$ dictates that if the index is equal to $suc\ n$, the index of the recursive argument needs to be $n$. We interpret this as follows: if a vector has length (suc n), its tail has length n. This induces the following typing discipline for $Vec$: 

\begin{code}
Ty-vec : ∀ {a : Set} → (n : ℕ) → (op : Op-vec {a} n) → Ar-vec n op → ℕ
Ty-vec zero a ()
Ty-vec (suc n) a tt = n
\end{code} 

This defines the signature for $Vec$: $\Sigma_{Vec} \triangleq \texttt{Op-vec} \triangleleft^\texttt{Ty-vec} \texttt{Ar-vec}$. 

\begin{figure}[h] \hrulefill
\begin{code}
data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)
\end{code} 
\hrulefill
\caption{Definition of $Vec$}\label{vecdef}
\end{figure}

We can define signatures for non-indexed datatypes as well by choosing a trivial index, e.g. $I = \top$. This gives $\Sigma_{\mathbb{N}} \triangleq \texttt{Op-nat} \triangleleft^\texttt{Ty-nat} \texttt{Ar-nat}$ with the definitions given in listing \ref{signat-def}: 

\begin{figure} \hrulefill
\begin{code}
Op-nat : ⊤ → Set
Op-nat tt = ⊤ ⊎ ⊤
\end{code}
\begin{code}
Ar-nat : Op-nat tt → Set
Ar-nat (inj₁ x) = ⊥
Ar-nat (inj₂ y) = ⊤
\end{code}
\begin{code}
Ty-nat : (op : Op-nat tt) → Ar-nat op → ⊤
Ty-nat (inj₁ x) ()
Ty-nat (inj₂ y) tt = tt
\end{code}
\hrulefill
\caption{Signature definition for $\mathbb{N}$}\label{signat-def}
\end{figure}

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


\section{Preliminary results}\label{preliminary}

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