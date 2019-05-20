\documentclass[sigplan]{acmart}

\settopmatter{printacmref=false} % Removes citation information below abstract
\renewcommand\footnotetextcopyrightpermission[1]{} % removes footnote with conference information in first column
\pagestyle{plain} % removes running headers

%include agda.fmt
%include polycode.fmt
%include greek.fmt
%include colorcode.fmt

\usepackage{xcolor}
\newcommand\todo[1]{\textcolor{red}{\textbf{TODO:} #1}}


\usepackage{textcomp}

\DeclareUnicodeCharacter{10218}{$\langle\langle$}
\DeclareUnicodeCharacter{10219}{$\rangle\rangle$}
\DeclareUnicodeCharacter{7522}{\textsubscript{i}}
\DeclareUnicodeCharacter{7524}{\textsubscript{u}}
\DeclareUnicodeCharacter{8336}{\textsubscript{a}}
\DeclareUnicodeCharacter{8346}{\textsubscript{p}}
\DeclareUnicodeCharacter{10631}{$\llparenthesis$}
\DeclareUnicodeCharacter{10632}{$\rrparenthesis$}
\DeclareUnicodeCharacter{10627}{\{\!\{}
\DeclareUnicodeCharacter{10628}{\}\!\}}
\DeclareUnicodeCharacter{9656}{$\blacktriangleright$}
\DeclareUnicodeCharacter{9667}{$\triangleleft$}
\DeclareUnicodeCharacter{8347}{\textsubscript{s}}

\usepackage[font=small,labelfont=bf]{caption}

\usepackage{textgreek}

% Math
\usepackage{amssymb}
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

\setlength\mathindent{0.3cm}

\title{Generic Enumerators}
\author{Cas van der Rest}
\email{c.r.vanderrest@@students.uu.nl}
\affiliation{
\institution{Universiteit Utrecht}
}
\author{Wouter Swierstra}
\email{w.s.swierstra@@uu.nl}
\affiliation{
\institution{Universiteit Utrecht}
}
\author{Manuel Chakravarty}
\email{manuel.chakravarty@@iohk.io}
\affiliation{
\institution{...}
}


% Remove auto-generated ACM copyright notice
% \setcopyright{none}

\begin{document}

\maketitle

  \section*{Introduction} 

  Since the introduction of QuickCheck \cite{claessen2011quickcheck},
  \textit{property based testing} has proven to be effective for
  the discovery of bugs. However, defining the
  properties to test is only part of the story: it is equally
  important to \emph{generate} suitable test data. In particular,
  requiring random test data to satisfy arbitrary preconditions can
  lead to skewed distributions: for example, naively generating
  random sorted lists will rarely yield long lists. As a
  result, developers need to design custom generators carefully---but
  these generators can become arbitrarily complex. When testing a
  compiler, for example, it can be quite challenging to define a good
  generator that is guaranteed to produce well-formed programs. 
  \cite{palka2011testing, claessen2015generating}
  
  In this brief abstract we propose to address this problem using the
  observation that well-formed inputs can often be described by
  (indexed) inductive datatypes. By defining a \emph{generic}
  procedure for \emph{enumerating} indexed datatypes, we can obtain a
  way of safely generating precise test data. 

  \paragraph*{Defining generators}

  % Wouter: ik heb dit even in commentaar gezet -- hoewel
  % dit interessant is, zou ik me hier beperken tot
  % één interpretatie (lijsten) -- dat maakt het wat concreter.
  % Deze diepe(re) embedding is handig, maar voor nu een implementatie
  % detail.

  % We represent generators as a deep embedding of the combinators
  % exposed by the |Monad| and |Alternative| typeclasses, with
  % additional constructors for recursive positions, calls to other
  % generators and empty generators.

% \begin{code}
% data Gen : (a : Set) → Set where
%   Or    : ∀ {a}     → Gen a → Gen a → Gen a
%   Pure  : ∀ {a}    → a → Gen a
%   Bind  : ∀ {a b}  → Gen b → (b → Gen a) → Gen a In
%   None  : ∀ {a}    → Gen a
%   μ     : ∀ {a}    → Gen a
% \end{code}

% This results in a tree-like structure that can consequently be mapped
% to any desired interpretation.

  We will sketch how to define a generic enumerator for a collection
  of datatypes in several steps:
  \begin{itemize}
  \item We begin by defining some universe of types |U| together with
    its semantics of the form |⟦_⟧ : U → Set|;
  \item Next, we define a datatype generic function
    \begin{code}
    enumerate : (u : U) -> (n : ℕ) -> List ⟦ u ⟧
    \end{code}
    This function produces a list of elements,
    bounded by some size parameter |n|;
  \item Finally, we formulate the key \emph{completeness} property
    that we expect of our enumerators:
    \begin{code}
      ∀ u -> (x : ⟦ u ⟧) →
        Σ[ n ∈ ℕ ] (x ∈ enumerate u n)      
    \end{code}
    This property states that for each possible |x|,
    there is some size |n| such than |x| occurs in our enumeration.
  \end{itemize}

  We will now sketch three increasingly complex universes, together
  with their corresponding generic enumerations.
  
  \section*{Enumeration of regular types}

  One of the simplest universes that describes a wide class of
  algebraic datatypes is the \emph{universe of regular types}. This
  universe contains the unit type, empty type, constant types, and is
  closed under products and coproducts.

\begin{code}
  data Reg : Set where
    Z U I : Reg 
    _⊕_ _⊗_  : Reg → Reg → Reg
    K   : Set → Reg
\end{code}

  The associated semantics, |⟦_⟧ : Reg -> Set -> Set|, maps values of
  type |Reg| to their corresponding pattern functor. By taking the
  fixpoint of such a pattern functor, we have a uniform representation
  of a wide class of (recursive) algebraic datatypes:
  \begin{code}
    data Fix (c : Reg) : Set where
      In : ⟦ c ⟧ (Fix c) → Fix c
  \end{code}
  Examples of regular types and their respective codes include natural
  numbers (|U ⊕ I|) or lists  (|U ⊕ (K a ⊗ I)|).
 
  It is reasonably straightforward to define a generic enumeration function:
  \begin{code}
      enumerate : (c : Reg) -> (n : ℕ) -> List ⟦ Fix c ⟧  
  \end{code}
  For example, the enumeration of a coproduct of two codes is a fair merge of 
  the two recursive calls, and for products we enumerate all possible 
  combinations of values. 

  \section*{Enumeration of Indexed Containers}

  What happens when we consider \emph{indexed} datatypes? Initially,
  we will consider \textit{indexed containers}
  \cite{altenkirch2015indexed, dagand2017essence}, a subset of all
  possible indexed types that are defined by induction over the index
  type.

  Following the presentation in \cite{dagand2017essence}, we define indexed
  containers as a triple of \textit{operations},
  \textit{arities} and \textit{typing}:

\begin{code}
Op : i → Reg 
Ar : ∀ {x} → Fix (Op x) → Reg 
Ty : ∀ {x} {op : Fix (Op x)} → Fix (Ar op) → i 
\end{code}

  The set |Op i| describes the set of available operations at index |i|;
  |Ar op| the arities of each constructor; finally, |Ty ar| gives the
  index corresponding to the recursive subtree at arity |ar|. Signatures
  are interpreted as a function from index to dependent pair, with the
  first element of the pair denoting a choice of constructor, and the
  second element being a function that maps each recursive subtree to
  a value of the type that results from applying the recursive argument
  with the index given by the typing discipline for that arity. 
  
\begin{code}
⟦ Op ◃ Ar ∣ Ty ⟧ x = λ i → 
  Σ[ op ∈ Fix (Op i) ] (ar : Fix (Ar op)) → x (Ty ar)
\end{code}

  Interpretations of signatures live in |I → Set|, hence we
  also need adapt our fixpoint, |Fix|, accordingly. 
  
\paragraph{Examples}    
  Many familiar indexed datatypes can be described using the universe
  of indexed containers, such as finite types (|Fin|), well-scoped lambda 
  terms, or the type of vectors given below:

  \begin{code}
  Σ-vec a = 
    let  op-vec = (λ { zero → U ; (suc n) → K a }) 
         ar-vec = (λ { {zero} tt → Z ; {suc n} x → U })
         ty-vec = (λ { {suc n} {a} (In tt) → n })
    in  op-vec ◃ ar-vec ∣ ty-vec
  \end{code}

  Each index is associated with a unique operation. We map |suc n| to a 
  constant type in |op-vec|, since the |∷| constructor stores a value along 
  its recursive subtree. The empty vector, |[]|, has no recursive subtrees, 
  hence it arity is the empty type. Any non-empty vector has one subtree, so 
  we assign its arity to be the unit type. This single subtree has an index 
  that is one less than the original index, as described by |ty-vec|.  

  %\todo{Leg uit of haal weg -- anders voegt het weinig toe}

\paragraph*{Generic enumerators}
  In the definition of indexed containers, we carefully restricted the
  type of operations and arities to the universe of regular types. As a result,
  we can reuse the enumeration of regular types to write a generic enumerator 
  for indexed containers. The second component of a signature's interpretation is 
  a function type, so we require an enumerator for function types. Inspired by 
  SmallCheck \cite{runciman2008smallcheck} we can define such an enumerator: 

\begin{code}
cogenerate : 
  (ℕ → List a) → (c : Reg) → ℕ → List (⟦ c ⟧ → a)
\end{code}

  This allows us to define enumerators for both components of the dependent pair:

\begin{code}
enumOp  : ∀ i →  ℕ → List ⟦ Op i ⟧
enumAr  : ∀ i → (x : ⟦ Op i⟧) 
        → ℕ → List ⟦ (y : Ar x) → r (Ty y) ⟧ 
\end{code}

  We then sequence these operations using the monadic structure of
  lists:

\begin{code}
λ n → enumOp n >>= (λ op → op , enumAr n op)
\end{code}

  Intuitively, this defines the enumeration of a signature as the union
  of the enumerations of its constructors.
    
\section*{Indexed Descriptions}
  Not all indexed families may be readily described as indexed
  containers. Consider, for example, the type of binary trees indexed by
  their number of nodes:

\begin{code}
  data Tree (a : Set) : ℕ → Set where
      Leaf :  Tree a 0
      Node :  ∀ {n m} → Tree a n → a → Tree a m 
              → Tree a (suc (n + m))
\end{code}

Without introducing further equalities, it is hard to capture the
decomposition of the index |suc (n + m)| into two subtrees of size |n|
and |m|.

The universe of indexed descriptions, as defined in
\cite{dagand2013cosmology}, is capable of representing arbitrary
indexed families. This makes two key modifications to the universe of
regular types: firstly, recursive positions must store an additional 
field corresponding to their index. Secondly, a new combinator, |Σ| is 
added. 
  
\begin{code}
I    : (i : I) → IDesc I
`Σ   : (S : Set) → (T : S → IDesc I) → IDesc I
\end{code}

Their interpretation is rather straightforward. 
\begin{code}
⟦ I i     ⟧ r = r i
⟦ `Σ S T  ⟧ r = Σ[ s ∈ S ] ⟦ T s ⟧ r
\end{code}
With the added |`Σ| and |`var|, we can now describe the |Tree| datatype: 
\begin{code}
tree : Set → ℕ → IDesc ℕ
tree a zero     = `1
tree a (suc n)  = `Σ (Σ (ℕ × ℕ) λ { (n' , m') → n' + m' ≡ n })
    λ { ((n , m) , refl) → I n ⊗ K a ⊗ I m }
\end{code}
The dependency between the indices of the left- and right subtrees of
nodes is captured by having their description depend on a pair of
natural numbers together with a proof that they sum to the required
index.

\paragraph*{Enumerators for indexed descriptions}
Since the |IDesc| universe largely exposes the same combinators as the
universe of regular types, we only really need to define |enumerate|
for the |`Σ| combinator. This is straightforward once we can enumerate 
its first component. 

\begin{code}
enumerate : (δ : IDesc I) → ℕ → List ⟦ δ ⟧
enumerate (`Σ s g) = 
  λ n → gen n >>= (λ x → x , enumerate (g s) n)  
\end{code}

However, since |`Σ| may range over any type in |Set|, 
we have no generic procedure to obtain a suitable enumerator. 
This creates a separation between the parts of a datatype for which an 
enumerator can be assembled mechanically, and those parts for which this 
would be too difficult. 

In the case of the |Tree| datatype, we see that those elements that make 
it hard to generically enumerate inhabitants of this datatype emerge 
quite naturally; we merely need to supply a generator inverting addition:

\begin{code}
+⁻¹  : (n : ℕ) → ℕ 
     → List (Σ (ℕ × ℕ) λ {(n' , m') → n' + m' ≡ n }) 
\end{code}

|enumerate| needs nothing beyond |+⁻¹| in order to be able to enumerate 
inhabitants of |Tree|. 

  \todo{Dit
  is in zekere zin het meest interessante aan de hele abstract--leg
  dit beter uit: omdat je moet Sigmas toestaat over een arbitrary set
  (of is het niet beter om een expliciete constraint constructor toe
  te voegen?), kun je geen generieke generator geven. Dus verwacht je
  die van de gebruiker.}

\todo{Noem heel kort quickchick als alternatief}
  
\bibliographystyle{acm} % ACM-Reference-Format
\bibliography{references}
\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End: 


