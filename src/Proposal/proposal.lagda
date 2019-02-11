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

Agda requires all functions to be total, where total means that they should be defined on any possible input, and give a result in a finite amount of time. The latter means that Agda is equipped with a termination checker that tries to prove that functions terminate. It is implied by undecidability of the halting problem that such a checker cannot be both sound and complete. Agda's termination checker is sound, meaning that there are functions that terminate which get rejected. This means that we cannot represent infinite structures in the same way as in haskell. For example, we might use the following definition in Haskell: \texttt{nats = 0 : map (+1) nats}. A similar definition in Agda will get rejected by the termination checker. 

\subsection{Property Based Testing}

\subsubsection{Existing Libraries}

\subsubsection{Generating Test Data}

\subsection{Generic Programming \& Type Universes}

If we desire to abstract over the structure of datatypes, we need a suitable type universe to do so. Many such universes have been developed and studied; this section discusses a few of them. 

\subsubsection{Regular Datatypes}\label{patternfunctors}

The term \textit{regular datatypes} is often used to refer to the class of datatypes that can be assembled using any combination of products, coproducts, unary constructors, constants (a position that is inhabited by a value of another type) and recursive positions. 

Any value that lives in universe induced by these combinators describes a regular datatype, and is generally referred to as a \textit{pattern functor}. We can define a datatype in agda that captures these values: 

\begin{code}
data Reg : Set →  Set where
    U    : Reg ⊥
    K    : (a : Set) → Reg a
    _⊕_  : ∀ {a : Set} → Reg a → Reg a → Reg a
    _⊗_  : ∀ {a : Set} → Reg a → Reg a → Reg a
    I    : Reg ⊥
\end{code}

Pattern functors can be interpreted as types in such a way that inhabitants of the interpreted type correspond to inhabitants of the type that is represented by the functor.  

\begin{code}
⟦_⟧ : Reg → Set → Set
⟦ U            ⟧ r = ⊤
⟦ K a          ⟧ r = a
⟦ reg₁ ⊕ reg₂  ⟧ r = ⟦ reg₁ ⟧ r ⊎ ⟦ reg₂ ⟧ r
⟦ reg₁ ⊗ reg₂  ⟧ r = ⟦ reg₁ ⟧ r × ⟦ reg₂ ⟧ r 
⟦ I            ⟧ r = r
\end{code}

Notice that recursive positions are left explicit. This means that we require an appropriate fixed-point combinator: 

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

Using such isomorphisms, we can automatically derive functionality for datatypes that can be captured using pattern functors. We will see an example of this in section \ref{derivegen}, where we will derive enumeration of inhabitants for arbitrary pattern functors. 

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

\subsection{Enumeration of Agda Types}

We look at how to enumerate various datatypes in Agda, starting with simple examples such as $\mathbb{N}$ or $Bool$, and progressively working towards more complex data. The first question we encounter is what the result of an enumeration should be. The ovious answer is that $enumerate a$ should return something of type $List a$, containing all possible values of type $a$. This is however not possible, as $List$ in Agda can only represent a finite list, and many datatypes, such as $\mathbb{N}$ have an infinite number of inhabitants. To solve this, we may either use the $Codata$ functionality from the standard library, or index our result with some kind of metric that limits the number of solutions to a finite set. The latter approach is what is used by both \textit{SmallCheck}\cite{} and \textit{LeanCheck}\cite{}, enumerating values up to a certain depth or size. 

We admit the same approach as the SmallCheck library, defining an enumerator/generator to be a function of type $\mathbb{N} \rightarrow List\ a$, where input argument signifies the maximum depth. By working with $List$, ensuring termination becomes a lot easier, since it is by definition a finite structure. Furthermore, proving properties about generators becomes more straightforward, as we can simply prove the desired properties about the $List$ type, and lift the result to our generator type. 

\subsubsection{Basic Combinators}

We can define a few basic combinators to allow composition of generators. 

\paragraph{Constants} Generators can yield a constant value, e.g. $true$ for the $Bool$ type. Unary constructors have a recursive depth of zero, so we simply return a singleton list: 

\begin{code}
𝔾-pure : ∀ {a : Set} {n : ℕ} → a → 𝔾 a n
𝔾-pure x _ = [ x ]
\end{code}

\paragraph{Application} Many datatypes are constructed by applying a constructor to a value of another datatype. An example is the $just$ constructor that takes a value of type $a$ and yields a value of type $Maybe a$. We can achieve this by lifting the familiar $map$ function for lists to the generator type: 

\begin{code}
𝔾-map : ∀ {a b : Set} {n : ℕ} → (a → b) → 𝔾 a n → 𝔾 b n
𝔾-map f x n = map f (x n)
\end{code}

\paragraph{Product} When a constructor takes two or more values (e.g. $\_,\_$), enumerating all values that can be constructed using that constructor comes down to enumerating all possible combinations of its input values, and applying the constructor. Again, we can do this by defining the canonical cartesian product on lists, and lifing it to the generator type: 

\begin{code}
list-ap : ∀ {ℓ} {a b : Set ℓ} → List (a → b) → List a → List b
list-ap fs xs = concatMap (λ f → map f xs) fs
\end{code}
\begin{code}
𝔾-ap : ∀ {a b : Set} → 𝔾 (a → b) → 𝔾 a → 𝔾 b
𝔾-ap f x n = list-ap (f n) (x n)
\end{code}

Note that in addition to $\mathbb{G}-ap$, one also needs $\mathbb{G}-map$ to construct values using constructors with arity greater than one. Assuming $f$ generates values of type $a$, and $g$ generates values of type $b$, we can generate values of type $a \times b$ using the following snippet:

\begin{code}
pair : ∀ {a b : Set} → 𝔾 a → 𝔾 b → 𝔾 (a × b)
pair f g = 𝔾-ap (𝔾-map _,_ f) g
\end{code}

Notice that $\mathbb{G}-map$, $\mathbb{G}-pure$ and $\mathbb{G}-ap$ make $\mathbb{G}$ an instance of both $Functor$ and $Applicative$, allowing us to use Agda's \textit{idiom brackets} to define generators. This allows us to write 

\begin{code}
pair : ∀ {a b : Set} {n : ℕ} → 𝔾 a n → 𝔾 b n →  𝔾 (a × b) n
pair f g = ⦇ f , g ⦈
\end{code}

instead. 

\paragraph{Choice} Choice between generators can be defined by first defining a \textit{merge} function on lists 

\begin{code}
merge : ∀ {ℓ} {a : Set ℓ} → List a → List a → List a
merge  []        ys  =  ys
merge  (x ∷ xs)  ys  =  x ∷ merge ys xs
\end{code}

and lifting it to the generator type: 

\begin{code}
_∥_ : ∀ {a : Set} {n : ℕ} → 𝔾 a n → 𝔾 a n → 𝔾 a n
x ∥ y = λ n → merge (x n) (y n)
\end{code}

Allowing for choice between constructors to be denoted in a very natural way: 

\begin{code}
bool : 𝔾 Bool
bool  =  ⦇ true  ⦈
      ∥  ⦇ false ⦈
\end{code}

\paragraph{Recursion} Simply using implicit recursion is the most natural way for defining generators for recursive datatypes. However, the following definition that generates inhabitants of $\mathbb{N}$ gets rejected by the termination checker: 

\begin{code}
nats : 𝔾 ℕ
nats  =  ⦇ zero      ⦈
      ∥  ⦇ suc nats  ⦈
\end{code}

Though the above code does terminate, the termination checker cannot see this. Since the input depth is threaded through the applicative combinators, it is not immediately clear that the depth parameter decreases with the recursive call. We solve this by making recursive positions explicit:

\begin{code}
nat : 𝔾 ℕ → 𝔾 ℕ
nat μ  =  ⦇ zero   ⦈
       ∥  ⦇ suc μ  ⦈
\end{code}

and defining an appropriate fixed-point combinator: 

\begin{code}
fix : ∀ {a : Set} → (𝔾 a → 𝔾 a) → 𝔾 a
fix f 0        =  []
fix f (suc n)  =  f (fix f) n
\end{code}

This definition of $fix$ gets rejected by the termination checker as well. We will see later how we can fix this. However, it should be apparent that it is terminating under the assumption that $f$ is well-behaved, i.e. it applies the $n$ supplied by $fix$ to its recursive positions. 

\subsubsection{Indexed Types}

Indexed types can be generated as well. Indexed generators can simply be defined as a $\Pi$-type, where the generated type depends on some input index: 

\begin{code}
𝔾ᵢ : ∀ {i : Set} → (i → Set) → Set
𝔾ᵢ {i = i} a = (x : i) → 𝔾 (a x)
\end{code}

The previously defined combinators can then be easily lifted to work with indexed types: 

\begin{code}
_∥ᵢ_ : ∀ {i : Set} {a : i → Set} → 𝔾ᵢ a → 𝔾ᵢ a → 𝔾ᵢ a 
(f ∥ᵢ g) i = f i ∥ g i
\end{code}

Throughout the code, a subscript $i$ is used to indicate that we deal with indexed types. 

\subsubsection{Guarantueeing Termination}

We can prove termination for our fixed-point combinator if we somehow enforce that its input function is well behaved. Consider the following example of a generator that does not terminate under our fixed-point combinator: 

\begin{code}
bad : 𝔾 ℕ → 𝔾 ℕ 
bad μ _ = map suc (μ 1)
\end{code}

Clearly, the base case of $fix$ is never reached. We can solve this by indexing generators with a natural number, and requiring generators to be called with their index, yielding the following alternative definition for $\mathbb{G}$: 

\begin{code}
𝔾 : Set → ℕ → Set 
𝔾 a m = (p : Σ[ n ∈ ℕ ] n ≡ m) → List a
\end{code}

We then use the following type for recursive generators: 

\begin{code}
⟪_⟫ : (ℕ → Set) → Set
⟪ a ⟫ = ∀ {n : ℕ} → a n → a n
\end{code}

Meaning that the resulting generator can only apply \textit{its own input number} to recursive positions. If we now decrease the index explicitly in the fixed-point combinator, the termination checker is able to see that $fix$ allways terminates.

\begin{code}
fix : ∀ {a : Set} → (n : ℕ) → ⟪ 𝔾 a ⟫ → 𝔾 a n
fix zero     f  (.0 , refl)      = []
fix (suc n)  f  (.suc n , refl)  = f {n} (fix n f) (n , refl)
\end{code}

Let us reconsider the previous counterexapmle: 

\begin{code}
bad : ⟪ 𝔾 ℕ ⟫
bad μ n = map suc (μ (1 , {!!}))
\end{code}

It is impossible to complete this definition when applying any other value than $n$ to the recursive position. 

\subsubsection{Deriving Enumeration for Regular Types}\label{derivegen}

One may have noticed that the way in which generators are defined is structurally \textit{very} similar to how one would define the corresponding datatypes in Haskell. This similarity is intentional, and serves to illustrate that the definition of many generators is completely mechanical with respect to the structure of the underlying datatype. 

If we consider the universe of regular datatypes described in section \ref{patternfunctors}, we see that there is a clear correspondence between our generator combinators, and the constructors of the $Reg$ datatype. We can utilize this correspondence to automatically derive generators for datatypes, given an isomorphism with the fixed-point of some pattern functor. 

\paragraph{Generating pattern functors} Recall that by fixing the interpretation of some value $f$ of type $Reg$, we get a type whose inhabitants correspond to the inhabitants of the type that is represented by $f$. If we thus construct a generator that produces all inhabitants of this type, we have a generator that is isomorphic to a complete generator for the type represented by $f$. Doing this generically amounts to constructing a function of the following type: 

\begin{code}
deriveGen : (f : Reg) → ⟪ 𝔾 (μ f) ⟫
deriveGen = {!!}
\end{code}

Intuitively, this definition is easily completed by pattern matching on $f$, and returning the appropriate combinator. However, due to the intertwined usage of two fixed-point combinators to deal with recursion, there are quite a few subtleties that need to be taken into account. 

We simplify the definition slightly by expanding the generator type: $\mu$ has one constructor, with one argument, so we replace $\mu\ f$ by its constructor's argument: $\llbracket f \rrbracket\ (\mu\ f)$. 

Let us now consider the branch of $deriveGen$ that deals with coproducts. We would like to simply write the following:

\begin{code}
deriveGen (f₁ ⊕ f₂) μ = ⦇ inj₁ (deriveGen f₁ μ) ⦈ ∥ ⦇ inj₂ (deriveGen f₂ μ) ⦈
\end{code}

This definition is incorrect, however. The recursive call $deriveGen\ f_1$ yields a generator of type $\langle\langle\ \mathbb{G}\ (\llbracket\ f_1\ \rrbracket\ (\mu\ f_1))\ \rangle\rangle$, meaning that two things go wrong: The recursive argument $\mu$ we apply to the recursive call has the wrong type, and recursive positions in $f_1$ refer to values of type $\mu\ f_1$ instead of $\mu\ (f_1 \oplus f_2)$. A similar problem occurs when attempting to define a suitable definition for products. 

We solve this issue by \textit{remembering} the top-level pattern functor for which we are deriving a generator when entering recursive calls to $deriveGen$. This can be done by having the recursive argument be a generator for the interpretation of this top-level pattern functor: 

\begin{code}
deriveGen : ∀ {n : ℕ} → (f g : Reg) → 𝔾 (⟦ g ⟧ (μ g)) n → 𝔾 (⟦ f ⟧ (μ g)) n
\end{code}

By using the type signature defined above instead, the previously shown defintion for the coproduct branch is accepted. 

In most cases, the initial call to $deriveGen$ will have the same value for $f$ and $g$. Observe that $\forall f \in Reg\ .\ deriveGen\ f\ f : \mathbb{G}\ (\llbracket\ f\ \rrbracket\ (\mu\ f))\ n \rightarrow \mathbb{G}\ (\llbracket\ f\ \rrbracket\ (\mu\ f))\ n$, thus we can use $fix$ to obtain a genrator that generates values of type $\llbracket\ f\ \rrbracket\ (\mu\ f))$. 

\paragraph{Deriving generators from isomorphism} We use the following record to witness an isomorphism betwen type $a$ and $b$: 

\begin{code}
record _≅_ (a b : Set) : Set where
  field
    from  : a → b
    to    : b → a
    iso₁  : ∀ {x : a} → to (from x) ≡ x
    iso₂  : ∀ {y : b} → from (to y) ≡ y
\end{code}

The functions $from$ and $to$ allow for conversion between $a$ and $b$, while $iso_1$ and $iso_2$ assert that these conversion functions do indeed form a bijection between values of type $a$ and type $b$. Given an isomorphism $a \cong b$, a generator $\mathbb{G}\ a\ n$ can easily be converted to a generator $\mathbb{G}\ b\ n$ by using $\llparenthesis\ \texttt{\_$\cong$\_}.to\ gen\ \rrparenthesis$. 

We can say that some type $a$ is \texttt{Regular} if there exists some value $f$ of type $Reg$ such that $a$ is isomorphic to $\mu\ f$. We capture this notion using the following record: 

\begin{code}
record Regular (a : Set) : Set where
  field
    W : Σ[ f ∈ Reg ] (a ≅ μ f)
\end{code}

Given a value of type $Regular\ a$, we can now derive a generator for $a$ by deriving a generator for $f$, and traveling through the isomorphism by applying the aforementioned conversion. 

\subsection{Proving Correctness of Generators}

Since generators are essentially an embellishment of the $List$ monad, we can reasonably expect them to behave according to our expectations. However, it would be better to prove that generators behave as intended. Before we can start reasoning about generators, we need to formulate our properties of interest:

\paragraph{Productivity} We say that a generator $g$ \textit{produces} some value $x$ if there exists some $n \in \mathbb{N}$ such that $x$ is an element of $g n$. We denote this by $g \leadsto x$. Below is the Agda formulation for this property: 

\begin{code}
_↝_ : ∀ {a : Set} → (∀ {n : ℕ} → 𝔾 a n) → a → Set
f ↝ x = ∃[ n ] (x ∈ f (n , refl))
\end{code}

\paragraph{Completeness} A generator $g : \mathbb{G}\ a\ n$ is complete when for all $x : a$, $g \leadsto x$. Informally, this means that a complete generator will eventually produce any inhabitant of the type it generates, provided it is given a large enough depth bound. We can formulate this in Adga as follows: 

\begin{code}
Complete : ∀ {a : Set} → (∀ {n : ℕ} → 𝔾 a n) → Set
Complete {a} f = ∀ {x : a} → f ↝ x
\end{code}

\paragraph{Equivalence} Informally, two generators of type $\mathbb{G}\ a\ n$ can be considered equivalent if they produce the same elements. We formulate this as a bi-implication between productivity proofs, i.e. for all $x : a$, $g_1 \leadsto x$ if and only if $g_2 \leadsto x$. In Agda: 

\begin{code}
_∼_ : ∀ {a} (g₁ g₂ : ∀ {n} → 𝔾 a n) → Set
g₁  ∼  g₂ = (∀ {x} → g₁ ↝ x → g₂ ↝ x) × (∀ {x} → g₂ ↝ x → g₁ ↝ x)
\end{code}

Notice that equivalence follows trivially from completeness, i.e. if two generators produce the same type, and they are both complete, then they are equivalent: 

\begin{code}
Complete→eq :  ∀ {a} {g₁ g₂ : ∀ {n} → 𝔾 a n}
               → Complete g₁ → Complete g₂
               → g₁ ∼ g₂
Complete→eq p₁ p₂ = (λ _ → p₂) , (λ _ → p₁)
\end{code}

\subsubsection{Combinator Correctness}

A natural starting point is to prove that properties are preserved by combinators. This section is by no means intended to exhaustively enumerate all possible combinations of combinators and properties and prove them correct, but rather serves to illustrate the general structure which can be used to construct such proofs. 

We take productivity of choice as an example, hence our goal is to show that if, for some generator $g_1 : \mathbb{G}\ a\ n$ and $x : a$, $g_1 \leadsto x$, then for all generators $g_2$ we have that $(g_1 \parallel g_2) \leadsto x$. Since the $\parallel$-combinator is defined in terms of $merge$, we first prove a similar property over the $merge$ function. 

\begin{code}
merge-complete-left :  ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x : a}
                       → x ∈ xs
                       → x ∈ merge xs ys
merge-complete-left (here)                   = here
merge-complete-left {xs = _ ∷ xs} (there p)  = 
  merge-cong {xs = xs} (merge-complete-left p)
\end{code}

\textit{merge-cong} is a lemma stating that if $y \in merge\ xs\ ys$, then $y \in merge\ (x :: xs)\ ys$; its definition is omitted for conciseness. Armed with the above lemma that asserts left-completeness of the $merge$ function, we can set out to prove left-completeness for the $\parallel$-combinator. The key insight here is that the depth bound at which $x$ occurs does not change, thus we can sipmly reuse it, and lift the above lemma to the generator type: 

\begin{code}
∥-complete-left :  ∀ {a : Set} {x : a} {f g : ∀ {n : ℕ} → 𝔾 a n}
                   → f ↝ x
                   → (f ∥ g) ↝ x
∥-complete-left (n , p) = n , merge-complete-left p
\end{code}

We can construct a similar proof for products by first proving similar properties about lists, and lifting them to the generator type. Proofs about the productivity of combinators can, in a similar fashion, consequently be lifted to reason about completeness. This allows us to show that, for example, if the two operands of a choice are both complete, then the resulting generator is complete as well. 

\subsubsection{Correctness of Derived Generators}

\subsection{Generalization to Indexed Types}

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