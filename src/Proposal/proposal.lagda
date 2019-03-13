\documentclass[acmsmall]{acmart}

\settopmatter{printacmref=false} % Removes citation information below abstract
\renewcommand\footnotetextcopyrightpermission[1]{} % removes footnote with conference information in first column
\pagestyle{plain} % removes running headers

%include agda.fmt
%include polycode.fmt
%include greek.fmt
%include colorcode.fmt

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

\setlength\mathindent{1cm}

\title{Program Term Generation Through Enumeration of Indexed datatypes (Thesis Proposal)}
\author{Cas van der Rest}
\date{\today}

% Remove auto-generated ACM copyright notice
\setcopyright{none}

\begin{document}

\maketitle

  \section{Introduction}\label{introduction}

    A common way of asserting a program's correctness is by defining properties that should universally hold, and asserting these properties over a range of random inputs. This technique is commonly referred to as \textit{property based testing}, and generally consists of a two-step process. Defining properties that universally hold on all inputs, and defining \textit{generators} that sample random values from the space of possible inputs. \textit{QuickCheck} \cite{claessen2011quickcheck} is likely the most well known tool for performing property based tests on Haskell programs. 

    Although coming up with a set of properties that properly captures a program's behavior might initially seem to be the most involved part of the process, defining suitable generators for complex input data is actually quite difficult as well. Questions such as how to handle datatypes that are inhabited by an infinite number of values arise, or how to deal with constrained input data. The answers to these questions are reasonably well understood for \textit{Algebraic datatypes (ADT's)}, but no general solution exists when more complex input data is required. In particular, little is known about enumerating and generating inhabitants of \textit{Indexed datatypes}. 

  \subsection{Problem Statement}

    Let us consider an example property in the context of QuickCheck: 

\begin{code}
reverse_preserves_length :: [a] -> Bool 
reverse_preserves_length xs = length xs == length (reverse xs)
\end{code}

    We can \textit{check} this property by taking a collection of lists, and asserting that |reverse_preserves_length| is |true| on all test inputs. Note that any inhabitant of the type |[a]| can be used test data for |reverse_preserves_length|. However, a problem occurs when we want to test a conditional property: 

\begin{code}
insert_preserves_sorted :: Int -> [Int] -> Property 
insert_preserves_sorted x xs = (sorted xs) ==> sorted (insert' x xs)
\end{code}

    If we invoke QuickCheck on (\texttt{quickCheck insert\_preserves\_sorted}), we get the following output: 

\begin{verbatim}
Test.QuickCheck> quickCheck prop_insertPreservesSorted 
*** Gave up! Passed only 70 tests; 1000 discarded tests.
\end{verbatim}

    In essence, two things go wrong here. The obvious problem is that QuickCheck is unable to generate a sufficient amount of relevant testcases due to the sparseness of the precondition. The second and perhaps more subtle problem is that the generated test data for which the precondition holds almost exclusively consists of small values (that is, lists of $0$, $1$ or $2$ elements). These problems make testing both inefficient (in terms of computational power required), as well as ineffective. Obviously, things will only get worse once we require more complex test data. 

    Data invariants, such as sortedness, can often be represented as an indexed datatype: 

\begin{code}
data Sorted {ℓ} : List ℕ → Set ℓ where
  nil    :  Sorted []
  single :  ∀ {n : ℕ} → Sorted (n ∷ [])
  step   :  ∀ {n m : ℕ} {xs : List ℕ} → n ≤ m 
            → Sorted {ℓ} (m ∷ xs) → Sorted {ℓ} (n ∷ m ∷ xs)
\end{code}

    This means we can generate test data for properties with a precondition by generating values of a suitable indexed datatype. Or in this case, enumerating all indices for which the datatype is inhabited. A good understanding of how to generate inhabitants of indexed datatypes might aid in the generation of many types of complex test data, such as well-typed program terms. 

  \subsection{Research Questions and Contributions}

    The general aim of this thesis is to work towards an answer to the following question:

    \begin{center}
    \textit{How can we generically enumerate and/or sample values of indexed datatypes?}
    \end{center}

    Obviously, this is quite a broad question, and as such answering it in its entirety is not realistic. Some subproblems worth considering are:

    \begin{itemize}

    \item
    We know that enumeration and sampling is possible for regular datatypes. QuickCheck \cite{claessen2011quickcheck} and SmallCheck \cite{runciman2008smallcheck} do this to generically derive test data generators. However, the question remains for which universes of indexed datatypes we can do the same. 

    \item 
    For more complex datatypes (such as ASTs or lambda terms), the number of values grows \textit{extremely} fast with their size: there are only a few lambda terms (up to \textalpha-equivalence) with depth $1$ or $2$, but for depth $50$ there are a little under $10^{66}$ \cite{grygiel2013counting} distinct terms. How can we efficiently sample or enumerate larger values of such datatypes? Can we apply techniques such memoization to extend our reach?

    \item 
    How can insights gained into the enumeration and sampling of indexed datatypes aid in efficient generation of program terms?

    \item 
    What guarantees about enumeration or sampling can we give? Can we exhaustively enumerate all datatypes, or are there some classes for which this is not possible (if not, why)?

    \end{itemize}

    \paragraph{Intended research contributions} automatic derivation of generators for at least a subset of indexed datatypes and an implementation in Haskell showing how such derivations can be applied to practical problems. 

  \subsection{Methodology}

    We use the programming language/proof assistant Agda \cite{norell2008dependently} as our vehicle of choice, with the intention to eventually backport our development to Haskell in order to be able to investigate the practical applications of our insights in the context of program term generation. 

  \section{Background}

  In this section we discuss relevant existing work and background information about Agda, property based testing, test data generation and datatype generic programming. 

  \subsection{Dependent Types}

    Dependent type theory allows the definition of types that depend on values. In addition to familiar constructs, such as the unit type ($\top$) and the empty type $\bot$, one can use so-called $\Pi$-types and $\Sigma$-types. $\Pi$-types capture the idea of dependent function types, that is, \textit{functions} whose output type may depend on the values of its input. Given some type $A$ and a family $P$ of types indexed by values of type $A$ (i.e. $P$ has type $A \rightarrow Type$), $\Pi$-types have the following definition: 

\begin{equation*}
\Pi_{(x : A)} P(x) \equiv (x : A) \rightarrow P(x) 
\end{equation*}

    In a similar spirit, $\Sigma$-types are ordered \textit{pairs} of which the type of the second value may depend on te first value of the pair. 

\begin{equation*}
\Sigma_{(x : A)} P(x) \equiv (x : A) \times P(x) 
\end{equation*}

    The Curry-Howard equivalence extends to $\Pi$- and $\Sigma$-types as well: they can be used to model universal and existential quantification \cite{wadler2015propositions}. 

  \subsection{Agda}

    Agda is a programming language based on Martin L{\"o}f type theory \cite{norell2008dependently}. Its syntax is broadly similar to Haskell's, though Agda's type system is more elaborate in the sense that types may depend on term level values. Agda is also a proof assistant, using the Curry-Howard equivalence to express propositions as types. 

  \subsubsection{Codata and Sized Types}\label{codata}

    All definitions in Agda are required to be \textit{total}, meaning that they must be defined on all possible inputs, and give a result in finite time. The Halting problem states that it is impossible to define a general procedure that decides the termination condition for all functions, so to ensure that only terminating definitions are accepted Agda's termination checker uses a sound approximation. A logical consequence is that there are Agda programs that terminate, but are rejected by the termination checker. This means that we cannot work with infinite data in the same way as in the same way as in Haskell, which does not care about termination. For example, the following definition is perfectly fine in Haskell: 

\begin{code}
nats :: [Int]
nats = 0 : map (+1) nats
\end{code}

    meanwhile, an equivalent definition in Agda gets rejected by the Termination checker: 

\begin{code}
nats : List ℕ
nats = 0 ∷ map suc nats
\end{code}

    This is no surprise, as the termination checker will reject any recursive calls where there is not at least one argument that is strictly smaller. However, in both Agda and Haskell, an expression such as |take 10 nats| evaluates to $[0,1, \ldots , 9]$ in finite time. 

    We can prevent the termination checker from flagging these kind of operations by making the lazy semantics explicit, using \textit{codata} and {sized types}. Codata is a general term for possible inifinite data, often described by a co-recursive definition. Sized types extend the space of function definitions that are recognized by the termination checker as terminating by tracking information about the size of values in types \cite{abel2010miniagda}. In the case of lists, this means that we explicitly specify that the recursive argument to the |_∷_| constructor is a \textit{Thunk}, which should only be evaluated when needed: 

\begin{code}
data Colist {a} (A : Set a) (i : Size) : Set a where
  []  : Colist A i
  _∷_ : A → Thunk (Colist A) i → Colist A i
\end{code}

    We can now define |nats| in Agda by wrapping the recursive call in a thunk: 

\begin{code}
nats : ∀ {i : Size} → Colist ℕ i
nats = 0 ∷ λ where .force → map suc nats
\end{code}

    Since colists are possible infinite structures, there are some functions we can define on lists, but not on colists. An example of this is a function calculating the length of a colist: 

\begin{code}
length : ∀ {a : Set} → Colist a ∞ →  ℕ
length [] = 0
length (x ∷ xs) = suc (length' (xs .force))
\end{code}

    In this case |length| is not accepted by the termination checker because the input colist is indexed with size |∞|, meaning that there is no finite upper bound on its size. Hence, there is no guarantee that our function terminates when inductively defined on the input colist.
    
    There are some cases in which we can convince the termination checker that our definition is terminating by using sized types. Consider the folowing example of a function that increments every element in a list of naturals with its position: 

\begin{code}
incpos : List ℕ → List ℕ
incpos [] = []
incpos (x ∷ xs) = x ∷ incpos (map suc xs)
\end{code}

    The recursive call to |incpos| gets flagged by the termination checker; we know that |map| does not alter the length of a list, but the termination checker cannot see this. For all it knows |map| equals |const [ 1 ]|, which would make |incpos| non-terminating. The size-preserving property of |map| is not reflected in its type. 

    We can define an alternative version of the |List| datatype indexed with |Size|, which tracks the depth of a value in its type. 

\begin{code}
data List (a : Set) : Size → Set where
  []  : ∀ {i} → List' a i
  _∷_ : ∀ {i} → a → List' a i → List' a (↑ i)
\end{code}

    Here |↑ i| means that the depth of a value constructed using the $::$ constructor is one deeper than its recursive argument. Incidently, the recursive depth of a list is equal to its size (or length), but this is not necessarily the case. By indexing values of |List| with their size, we can define a version of |map| which reflects in its type that the size of the input argument is preserved: 

\begin{code}
map : ∀ {i} {a b : Set} → (a → b) → List a i → List b i
\end{code}

    Using this definition of |map|, the definition of |incpos| is no longer rejected by the termination checker. 

  \subsection{Property Based Testing}

    \textit{Property Based Testing} aims to assert properties that universally hold for our programs by parameterizing tests over values and checking them against a collection of test values. Libraries for property based testing often include some kind of mechanism to automatically generate collections of test values. Existing tools take different approaches towards generation of test data: \textit{QuickCheck} \cite{claessen2011quickcheck} randomly generates values within the test domain, while \textit{SmallCheck} \cite{runciman2008smallcheck} and \textit{LeanCheck} \cite{matela2017tools} exhaustively enumerate all values in the test domain up to a certain point. 

  \subsubsection{Existing Libraries}

    Many libraries exist for property based testing. This section briefly discusses some of them. 

    \paragraph{QuickCheck} Published in 2000 by Claessen \& Hughes \cite{claessen2011quickcheck}, QuickCheck implements property based testing for Haskell. As mentioned before, test values are generated by sampling randomly from the domain of test values. QuickCheck supplies the typeclass \texttt{Arbitrary}, whose instances are those types for which random values can be generated. A property of type |a -> Bool| can be tested if |a| is an instance of \texttt{Arbitrary}. Instances for most common Haskell types are supplied by the library. 

    If a property fails on a testcase, QuickCheck supplies a counterexample. Consider the following faulty definition of |reverse|: 

\begin{code}
reverse :: Eq a => [a] -> [a]
reverse []      =  []
reverse (x:xs)  =  nub ((reverse xs) ++ [x, x])
\end{code}

    If we now test our function by calling |quickCheck reverse_preserves_length|, we get the following output: 

\begin{verbatim}
Test.QuickCheck> quickCheck reverse_preserves_length 
*** Failed! Falsifiable (after 8 tests and 2 shrinks):    
[7,7]
\end{verbatim}

    We see that a counterexample was found after 8 tests \textit{and 2 shrinks}. Due to the random nature of the tested values, the counterexamples that falsify a property are almost never minimal counterexamples. QuickCheck takes a counterexample and applies some function that produces a collection of values that are smaller than the original counterexample, and attempts to falsify the property using one of the smaller values. By repeatedly \textit{Shrinking} a counterexample, QuickCheck is able to find much smaller counterexamples, which are in general of much more use to the programmer. 

    Perhaps somewhat surprising is that QuickCheck is also able randomly generate values for function types by modifying the seed of the random generator (which is used to generate the function's output) based on it's input. 

    \paragraph{(Lazy) SmallCheck} Contrary to QuickCheck, SmallCheck \cite{runciman2008smallcheck} takes an \textit{enumerative} approach to the generation of test data. While the approach to formulation and testing of properties is largely similar to QuickCheck's, test values are not generated at random, but rather exhaustively enumerated up to a certain \textit{depth}. Zero-arity constructors have depth $0$, while the depth of any positive arity constructor is one greather than the maximum depth of its arguments.  The motivation for this is the \textit{small scope hypothesis}: if a program is incorrect, it will almost allways fail on some small input \cite{andoni2003evaluating}. 

    In addition to SmallCheck, there is also \textit{Lazy} SmallCheck. In many cases, the value of a property is determined only by part of the input. Additionally, Haskell's lazy semantics allow for functions to be defined on partial inputs. The prime example of this is a property \texttt{sorted :: Ord a => [a] -> Bool} that returns \texttt{false} when presented with \texttt{1:0:$\bot$}. It is not necessary to evaluate $\bot$ to determine that the input list is not ordered. 

    Partial values represent an entire class of values. That is, \texttt{1:0:$\bot$} can be viewed as a representation of the set of lists that have prefix \texttt{[1, 0]}. By checking properties on partial values, it is possible to falsify a property for an entire class of values in one go, in some cases greatly reducing the amount of testcases needed. 

    \paragraph{LeanCheck} Where SmallCheck uses a value's \textit{depth} to bound the number of test values, LeanCheck uses a value's \textit{size} \cite{matela2017tools}, where size is defined as the number of construction applications of positive arity.

    Both SmallCheck and LeanCheck contain functionality to enumerate functions similar to QuickCheck's \texttt{Coarbitrary}. 

    \paragraph{Hegdgehog} Hedgehog \cite{hedgehog} is a framework similar to QuickCheck, that aims to be a more modern alternative. It includes support for monadic effects in generators and concurrent checking of properties.

    \paragraph{Feat} A downside to both SmallCheck and LeanCheck is that they do not provide an efficient way to generate or sample large test values. QuickCheck has no problem with either, but QuickCheck generators are often more tedious to write compared to their SmallCheck counterpart. Feat \cite{duregaard2013feat} aims to fill this gap by providing a way to efficiently enumerate algebraic types, employing memoization techniques to efficiently find the $n^{th}$ element of an enumeration. 

    \paragraph{QuickChick} QuickChick is a QuickCheck clone for the proof assistant Coq \cite{denes2014quickchick}. The fact that Coq is a proof assistant enables the user to reason about the testing framework itself \cite{paraskevopoulou2015foundational}. This allows one, for example, to prove that generators adhere to some distribution.  

  \subsubsection{Generating Constrained Test Data}\label{genconstrainedtd}

    Defining a suitable generation of test data for property based testing is notoriously difficult in many cases, independent of whether we choose to sample from or enumerate the space of test values. Writing generators for mutually recursive datatypes with a suitable distribution is especially challenging. 
    
    We run into prolems when we desire to generate test data for properties with a precondition. If a property's precondition is satisfied by few input values, it becomes unpractical to test such a property by simply generating random input data. Few testcases will be relevant (meaning they satisfy the precondition), and the testcases that do are often trivial cases. The usual solution to this problem is to define a custom test data generator that only produces data that satisfies the precondition. In some cases, such as the |insert_preserves_sorted| from section \ref{introduction}, a suitable generator is not too hard to define: 

\begin{code}
gen_sorted :: Gen [Int]
gen_sorted = arbitrary >>= return . diff
  where  diff :: [Int] -> [Int]
         diff []      = [] 
         diff (x:xs)  = x:map (+x) (diff xs) 
\end{code}

    However, for more complex preconditions defining suitable generators is all but trivial. 

  \subsubsection{Automatic Generation of Specifications}

    A surprising application of property based testing is the automatic generation of program specifications, proposed by Claessen et al. \cite{claessen2010quickspec} with the tool \textit{QuickSpec}. QuickSpec automatically generates a set of candidate formal specifications given a list of pure functions, specifically in the form of algebraic equations. Random property based testing is then used to falsify specifications. In the end, the user is presented with a set of equations for which no counterexample was found. 

  \subsection{Techniques for Generating Test Data}

    This section discusses some existing work regarding the generation of test data satisfying invariants, such as well-formed $\lambda$-terms. 

  \subsubsection{Lambda Terms} 

    A problem often considered in literature is the generation of (well-typed) lambda terms \cite{palka2011testing, grygiel2013counting, claessen2015generating}. Good generation of arbitrary program terms is especially interesting in the context of testing compiler infrastructure, and lambda terms provide a natural first step towards that goal. 

    Claessen and Duregaard \cite{claessen2015generating} adapt the techniques described by Duregaard \cite{duregaard2013feat} to allow efficient generation of constrained data. They use a variation on rejection sampling, where the space of values is gradually refined by rejecting classes of values through partial evaluation (similar to SmallCheck \cite{runciman2008smallcheck}) until a value satisfying the imposed constrained is found. 

    An alternative approach centered around the semantics of the simply typed lambda calculus is described by Pa{\l}ka et al. \cite{palka2011testing}. Contrary to the work done by Claessen and Duregaard \cite{claessen2015generating}, where typechecking is viewed as a black box, they utilize definition of the typing rules to devise an algorithm for generation of random lambda terms. The basic approach is to take some input type, and randomly select an inference rule from the set of rules that could have been applied to arrive at the goal type. Obviously, such a procedure does not guarantee termination, as repeated application of the function application rule will lead to an arbitrarily large goal type. As such, the algorithm requires a maximum search depth and backtracking in order to guarantee that a suitable term will eventually be generated, though it is not guaranteed that such a term exists if a bound on term size is enforced \cite{moczurad2000statistical}. 

    Wang \cite{wang2005generating} considers the problem of generating closed untyped lambda terms. 

  \subsubsection{Inductive Relations in Coq}

    An approach to generation of constrained test data for Coq's QuickChick was proposed by Lampropoulos et al. \cite{lampropoulos2017generating} in their 2017 paper \textit{Generating Good Generators for Inductive Relations}. They observe a common pattern where the required test data is of a simple type, but constrained by some precondition. The precondition is then given by some inductive dependent relation indexed by said simple type. The |Sorted| datatype shown in section \ref{introduction} is a good example of this

    They derive generators for such datatypes by abstracting over dependent inductive relations indexed by simple types. For every constructor, the resulting type uses a set of expressions as indices, that may depend on the constructor's arguments and universally quantified variables. These expressions induce a set of unification constraints that apply when using that particular constructor. These unification constraints are then used when constructing generators to ensure that only values for which the dependent inductive relation is inhabited are generated. 

  \subsection{Generic Programming \& Type Universes}

    Datatype generic programming concerns techniques that allow for the definition of functions by inducting on the \textit{structure} of a datatype. Many approaches towards this goal have been developed, some more expressive than others. This section discusses a few of them.  

  \subsubsection{SOP (Sum of Products)}\label{sop}

    On of the more simple representations is the so called \textit{Sum of Products} view \cite{de2014true}, where datatypes are respresented as a choice between an arbitrary amount of constructors, each of which can have any arity. This view corresponds to how datatypes are defined in Haskell. As we will see (for example in section \ref{patternfunctors}), other universes too employ sum and product combinators to describe the structure of datatypes, though they do not necessarily enforce the representation to be in disjunctive normal form. 

    Sum of Products, in its simplest form, cannot represent mutually recursive families of datatypes. An extension that allows this has been developed in \cite{miraldo2018sums}. 

  \subsubsection{Regular Datatypes}\label{patternfunctors}

    The term \textit{regular datatypes} is often used to refer to the class of datatypes that can be assembled using any combination of products, coproducts, unary constructors, constants (a position that is inhabited by a value of another type) and recursive positions. Any value that lives in universe induced by these combinators (a \textit{code}) represents a regular datatype. We can define a datatype in Agda that captures these values: 

\begin{code}
data Reg : Set where
    U   : Reg 
    _⊕_ : Reg → Reg → Reg
    _⊗_ : Reg → Reg → Reg
    I   : Reg
    K   : Set → Reg
\end{code}

    Codes can be interpreted as types in such a way that inhabitants of the interpretation correspond to inhabitants of the type that is represented by the code. 

\begin{code}
⟦_⟧ : Reg → Set → Set
⟦ U            ⟧ r = ⊤
⟦ K a          ⟧ r = a
⟦ reg₁ ⊕ reg₂  ⟧ r = ⟦ reg₁ ⟧ r ⊎ ⟦ reg₂ ⟧ r
⟦ reg₁ ⊗ reg₂  ⟧ r = ⟦ reg₁ ⟧ r × ⟦ reg₂ ⟧ r 
⟦ I            ⟧ r = r
\end{code}

The interpretation of a code is a function with type |Set → Set|, called a \textit{pattern functor}, whose input argument is the type of recursive positions. By using an appropriate fixed-point combinator, we can fix a pattern functor to obtain a type that is isomorphic with the type that is represented by the code. 

\begin{code}
data μ (f : Reg) : Set where
  `μ : ⟦ f ⟧ (μ f) → μ f
\end{code}

    \paragraph{Example} Consider (the fixed point of) a pattern functor corresponding to the definition of $List$: 

\begin{code}
List' : Set → Set
List' a = μ (U ⊕ (K a ⊗ I))
\end{code}

    Notice that this pattern functor denotes a choice between a unary constructor ($[]$), and a constructor that takes a constant of type $a$ and a recursive positions as arguments ($::$). We can define conversion functions between the standard $List$ type, and the interpretation of our pattern functor: 

\begin{code}
fromList : ∀ {a : Set} → List a → List' a
fromList []        = `μ (inj₁ tt)
fromList (x ∷ xs)  = `μ (inj₂ (x , fromList xs))
\end{code}

\begin{code}
toList : ∀ {a : Set} → List' a → List a
toList (`μ (inj₁ tt))           = []
toList (`μ (inj₂ (fst , snd)))  = fst ∷ toList snd
\end{code}

    Using such isomorphisms, we can derive functionality for regular datatypes. We will see an example of this in section \ref{derivegen}, where we will derive enumeration of inhabitants for all regular datatypes. 

    Similar to the pure Sum of Products representation, extensions to this universe have been developed that allow for the encoding of mutually recursive structures \cite{yakushev2009generic}. 

  \subsubsection{Multisorted Signatures}\label{ornaments}

    \textit{Signatures} \cite{dagand2017essence, ko2016programming} provide a type universe in which we can describe the structure of indexed datatypes in a very index-centric way. Indexed datatypes are described by \textit{Signatures}, consisting of three elements:

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
Ar : \forall\ \{i\} \rightarrow Op\ i \rightarrow Set \\
Ty : \forall\ \{i\}\ \{op\} \rightarrow Ar\ op \rightarrow I
\end{cases}
\end{equation*}

    \paragraph{Example} Let us consider the signature for the $Vec$ type, denoted by $\Sigma_{Vec}(\mathbb{N})$. Recall the definition of the $Vec$ datatype: 

\begin{code}
data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)
\end{code} 

    It has the following relation between indices and operations (available constructors): 

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

  \subsubsection{Combinatorial Species}
  
    \textit{Combinatorial species} \cite{yorgey2010species} were originally developed as a mathematical framework, but can also be used as an alternative way of looking at datatypes. A \textit{species} can, in terms of functional programming, be thought of as a type constructor with one polymorphic argument. Haskell's ADTs (or regular types in general) can be described by defining familiar combinators for species, such as sum and product. 

  \subsubsection{Indexed Functors}

    The most notable downside to the encoding described in section \ref{patternfunctors} is the lack of ability to encode mutually recursive datatypes. This makes generic operations on regular types of limited use in the context of program term generation, as abstract syntax trees often make heavy use of mutual recursion. 

    Löh and Magalhães \cite{loh2011generic} describe a universe that allows for these kind of mutual recursive structures to be encoded. Codes are indexed with an input and output type (both in |Set|), and are interpreted as a function between indexed functors. That is, a code of type |I ▸ O| gets interpreted as a function of type |(I → Set) → O → Set|. Compared to \ref{patternfunctors}, a number of combinators are added to the universe, such as a construct for dependent pairs or isomorphisms. 

  \section{Preliminary results}\label{preliminary}

    This section discusses the progress made in the Agda development accompanying this proposal. The main contribution of this development is a set of proven complete combinators that can be used to assemble generators for regular types, as well as a proven complete derivation mechanism that automatically constructs generators for all types for which an isomorphism exists to some pattern functor. 

    These isomorphisms are included for a number of common types, together with proofs asserting equivalence between manually defined and derived generators for these types. 

  \subsection{Enumerating Regular Types in Agda}

    We look at how to enumerate various datatypes in Agda, starting with simple examples such as $\mathbb{N}$ or $Bool$, and progressively working towards more complex data. The first question we encounter is what the result of an enumeration should be. The obvious answer is that |enumerate a| should return something of type |List a|, containing all possible values of type |a|. This is however not possible, as |List| in Agda can only represent a finite list, and many datatypes, such as $\mathbb{N}$ have an infinite number of inhabitants. To solve this, we may either use the |Codata| functionality from the standard library (see \ref{codata}), or index our result with some kind of metric that limits the number of solutions to a finite set. The latter approach is what is used by both \textit{SmallCheck}\cite{runciman2008smallcheck} and \textit{LeanCheck}\cite{matela2017tools}, enumerating values up to a given depth or size. 

    We use the same approach as the SmallCheck library, defining an enumerator/generator to be a function of type |ℕ → List a|, where input argument signifies the maximum depth. By working with |List|, ensuring termination becomes a lot easier, since it is by definition a finite structure. Furthermore, proving properties about generators becomes more straightforward compared to |Colist|, as we can simply prove the desired properties about the $List$ type, and lift the result to our generator type. 

    This motivates the following definition for |𝔾 a|, representing a generator that produces elements of type |a|: 

\begin{code}
𝔾 : Set → Set
𝔾 a = ℕ → List a
\end{code}

    An example generator for the |Bool| type could be: 

\begin{code}
bool : 𝔾 Bool
bool _ = false ∷ true ∷ []
\end{code}

  \subsubsection{Basic Combinators}

    We can define a few basic combinators to allow composition of generators. The goal eventually is to choose our combinators such that generator definitions bear a close resemblance to a datatype's \textit{structure}.  

    \paragraph{Constants} Generators can yield a constant value, e.g. |true| for the |Bool| type. |𝔾-pure| lifts a constant value to the |𝔾| type.  Unary constructors have a recursive depth of zero, so we simply return a singleton list, independent of the input depth bound.  

\begin{code}
𝔾-pure : ∀ {a : Set} {n : ℕ} → a → 𝔾 a n
𝔾-pure x _ = [ x ]
\end{code}

    \paragraph{Constructor application} Many datatypes are constructed by applying a constructor to a value of another datatype. An example is the |just| constructor that takes a value of type |a| and yields a value of type |Maybe a|. We can achieve this by lifting the familiar |map| function for lists to the generator type: 

\begin{code}
𝔾-map : ∀ {a b : Set} {n : ℕ} → (a → b) → 𝔾 a n → 𝔾 b n
𝔾-map f x n = map f (x n)
\end{code}

    \paragraph{Product} When a constructor takes two or more values (e.g. |_,_|), enumerating all values that can be constructed using that constructor comes down to enumerating all possible combinations of its input values, and applying the constructor. Again, we can do this by defining the canonical cartesian product on lists, and lifting it to the generator type: 

\begin{code}
list-ap : ∀ {ℓ} {a b : Set ℓ} → List (a → b) → List a → List b
list-ap fs xs = concatMap (λ f → map f xs) fst

𝔾-ap : ∀ {a b : Set} → 𝔾 (a → b) → 𝔾 a → 𝔾 b
𝔾-ap f x n = list-ap (f n) (x n)
\end{code}

    Note that in addition to |𝔾-ap|, one also needs |𝔾-map| to construct values using constructors with arity greater than one. Assuming $f$ generates values of type |a|, and $g$ generates values of type |b|, we can generate values of type |a × b| using the following snippet:

\begin{code}
pair : ∀ {a b : Set} → 𝔾 a → 𝔾 b → 𝔾 (a × b)
pair f g = 𝔾-ap (𝔾-map _,_ f) g
\end{code}

    Notice that |𝔾-map|, |𝔾-pure| and |𝔾-ap| make |𝔾| an instance of both $Functor$ and $Applicative$, allowing us to use Agda's \textit{idiom brackets} to define generators. This allows us to write 

\begin{code}
pair : ∀ {a b : Set} → 𝔾 a → 𝔾 b →  𝔾 (a × b)
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

    We can now write a generator for the |Bool| type using only our combinators:

\begin{code}
bool : 𝔾 Bool
bool  =  ⦇ true  ⦈
      ∥  ⦇ false ⦈
\end{code}

    \paragraph{Recursion} Simply using implicit recursion seems to be the most obvious choice for defining recursive generators. However, the following definition that generates inhabitants of $\mathbb{N}$ gets rejected by the termination checker: 

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

    and defining a fixed-point combinator: 

\begin{code}
fix : ∀ {a : Set} → (𝔾 a → 𝔾 a) → 𝔾 a
fix f 0        =  []
fix f (suc n)  =  f (fix f) n
\end{code}

    This definition of |fix| gets rejected by the termination checker. We will see later how we can resolve this. However, it should be apparent that it is terminating under the assumption that $f$ is well-behaved, i.e. it applies the $n$ supplied by |fix| to its recursive positions. 

  \subsubsection{Indexed Types}\label{genindex}

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

  \subsubsection{Guaranteeing Termination}

    We can prove termination for our fixed-point combinator if we somehow enforce that its input function is well behaved. Consider the following example of a generator which leads to nontermination when we take its fixpoint: 

\begin{code}
bad : 𝔾 ℕ → 𝔾 ℕ 
bad μ _ = map suc (μ 1)
\end{code}

     Since $\mu$ is allways called with $1$, we never reach the branch |fix f 0 = []| when applying |bad| to |fix|, leading to an infinite chain of calls to fix. We can resolve this by indexing generators with a natural number, and requiring that the input depth bound to a generator is allways the number it is indexed with. This yields the following alternative definition for $\mathbb{G}$: 

\begin{code}
𝔾 : Set → ℕ → Set 
𝔾 a m = (p : Σ[ n ∈ ℕ ] n ≡ m) → List a
\end{code}

    Notice that in addition to a natural number as input, a proof that the input bound is equal to the generator's index is required. We then use the following type synonym for recursive generators: 

\begin{code}
⟪_⟫ : (ℕ → Set) → Set
⟪ a ⟫ = ∀ {n : ℕ} → a n → a n
\end{code}

     This definition requires that the recursive positions in a generator are allways called with the same depth bound as the generator itself. If we redefine |bad| using this new type for recursive generators, the type signature enforces that the input argument $\mu$ is called with depth bound $n$: 

\begin{code}
bad : ⟪ 𝔾 ℕ ⟫
bad μ n = map suc (μ (1 , {!!}))
\end{code}

    We cannot complete the above definition of |bad| since there exists no proof that |n ≡ 1|. 
     
    If we now decrease the index explicitly in the fixed-point combinator, the termination checker is able to see that $fix$ allways terminates: 

\begin{code}
fix : ∀ {a : Set} → (n : ℕ) → ⟪ 𝔾 a ⟫ → 𝔾 a n
fix zero     f  (.0 , refl)      = []
fix (suc n)  f  (.suc n , refl)  = f {n} (fix n f) (n , refl)
\end{code}

  \subsubsection{Deriving Enumeration for Regular Types}\label{derivegen}

    Generator definitions are very similar to how one would define the corresponding datatypes in Haskell. This similarity is intentional, and serves to illustrate that the definition of many generators is completely mechanical with respect to the structure of the underlying datatype. 

    If we consider the universe of regular datatypes described in section \ref{patternfunctors}, we see that there is a clear correspondence between our generator combinators, and the constructors of the $Reg$ datatype. We can utilize this correspondence to automatically derive generators for datatypes, given that there exists some isomorphism between said datatype and the fixed point of a pattern functor.  

    \paragraph{Generating pattern functors} Recall that by fixing the interpretation of some value $f$ of type $Reg$, we get a type whose inhabitants correspond to the inhabitants of the type that is represented by $f$. If we thus construct a generator that produces all inhabitants of the fixed pattern functor, we can create a generator for the type represended by $f$. Hence we aim to construct the following function:  

\begin{code}
deriveGen : (f : Reg) → ⟪ 𝔾 (μ f) ⟫
deriveGen = {!!}
\end{code}

    Intuitively, this definition is easily completed by pattern matching on $f$, and returning the appropriate combinator (recursing where necessary). However, due to the intertwined usage of two fixed-point combinators to deal with recursion, there are quite a few subtleties that need to be taken into account.  

    We simplify things slightly by expanding the generator type: $\mu$ has one constructor, with one argument, so we replace $\mu\ f$ by its constructor's argument: $\llbracket f \rrbracket\ (\mu\ f)$. 

    Let us now consider the branch of $deriveGen$ that deals with coproducts. We would like to simply write the following:

\begin{code}
deriveGen (f₁ ⊕ f₂) μ = ⦇ inj₁ (deriveGen f₁ μ) ⦈ ∥ ⦇ inj₂ (deriveGen f₂ μ) ⦈
\end{code}

    This definition is incorrect, however. The recursive call $deriveGen\ f_1$ yields a generator of type $\langle\langle\ \mathbb{G}\ (\llbracket\ f_1\ \rrbracket\ (\mu\ f_1))\ \rangle\rangle$ rather than |⟪ 𝔾 (⟦ f₁ ⟧ (μ (f₁ ⊕ f₂)) ⟫|. This means that two things go wrong: The recursive argument $\mu$ we apply to the recursive call has the wrong type, and recursive positions in $f_1$ refer to values of type $\mu\ f_1$ instead of $\mu\ (f_1 \oplus f_2)$. This prevents us from unifying the results of recursive calls using the |∥| combinator. A similar problem occurs when attempting to define a suitable definition for products. 

    We solve this issue by \textit{recording} the top-level pattern functor for which we are deriving a generator when entering recursive calls to $deriveGen$. This can be done by having the recursive argument be a generator for the interpretation of this top-level pattern functor: 

\begin{code}
deriveGen : ∀ {n : ℕ} → (f g : Reg) → 𝔾 (⟦ g ⟧ (μ g)) n → 𝔾 (⟦ f ⟧ (μ g)) n
\end{code}

    By using the type signature defined above instead, the previously shown defintion for the coproduct branch is accepted. 

    In most cases, the initial call to $deriveGen$ will have the same value for $f$ and $g$, which means that we can use $fix$ to obtain a generator that generates values of type $\llbracket\ f\ \rrbracket\ (\mu\ f))$. 

    \paragraph{Deriving for the |K|-combinator} Since we can refer to arbitrary values of |Set| using the |K|-combinator, there is no general procedure to construct generators of type |𝔾 (⟦ K a ⟧ (μ g))| for any |a| and |g|. At first glance, there are two ways to resolve this issue: 

    \begin{enumerate}
    \item
    Restrict the set of types to which we can refer using |K| to those types for which we can automatically derive a generator (i.e. the regular types). 

    \item 
    Somehow require the programmer to supply generators for all occurrences of |K| in the pattern functor, and use those generators
    \end{enumerate}

    The first approach has as a downside that it limits the expressiveness of derived generators, and excludes references to non-regular types, hence we choose to require the user to supply a suitable set of generators that can be used whenever we encounter a value constructed using |K|. 

    Since it is likely that we will need to record other information about |K| constructors beyond generators at some point, we use a separate metadata structure that records whatever auxiliary information necessary. This metadata structure is indexed by some value of the |Reg| datatype. Values of this type have the exact same structure as their index, with the relevant data stored at the |K| leaves: 

\begin{code}
data RegInfo (P : Set → Set) : Reg → Set where
    U~    :  RegInfo P U
    _⊕~_  :  ∀ {f₁ f₂ : Reg}
             → RegInfo P f₁ → RegInfo P f₂
             → RegInfo P (f₁ ⊕ f₂)
    _⊗~_  :  ∀ {f₁ f₂ : Reg}
             → RegInfo P f₁ → RegInfo P f₂
             → RegInfo P (f₁ ⊗ f₂)
    I~    :  RegInfo P I
    K~    :  ∀ {a : Set} → P a → RegInfo P (K a)
\end{code}

    This means that |deriveGen| gets an additional parameter of type |RegInfo (λ a → ⟪ 𝔾 a ⟫) f|, where |f| is the pattern functor we are \textit{currently} deriving a generator for (so not the top level pattern functor): 

\begin{code}
deriveGen :  ∀ {f g : Reg} {n : ℕ} → RegInfo (λ a → ⟪ 𝔾 a ⟫) f
             → 𝔾 (⟦ g ⟧ (μ g)) n → 𝔾 (⟦ f ⟧ (μ g)) n
\end{code}

    In the |K| branch of |deriveGen|, we can then simply return the generator that is recorded in the metadata structure: 

\begin{code}
deriveGen {K a} {g} {n} (K~ x) rec = ⟨ x ⟩
\end{code}

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

    Given a value of type $Regular\ a$, we can now derive a generator for $a$ by deriving a generator for $f$, and traveling through the isomorphism by applying the aforementioned conversion: 

\begin{code}
isoGen :  ∀ {n : ℕ} → (a : Set) → ⦃ p : Regular a ⦄ 
          → RegInfo (λ a → ⟪ 𝔾 a ⟫) (getPf p) → 𝔾 a n
\end{code}

  \subsection{Proving Generator Correctness}

    We would like to prove that our generators behave as intended. Most notably, we are interested in a proof of their \textit{completeness}, i.e. a generator produces all elements of a certain type. We show that completeness is preserved by our combinators, and that the derived generators for regular types are complete. 
    
  \subsubsection{Generator Properties}

    Before we set out to prove that our generators are complete, we need to establish what exactly completeness means in our context. 

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
Complete→eq :  ∀ {a} {g₁ g₂} → Complete g₁ → Complete g₂ → g₁ ∼ g₂
\end{code}

  \subsubsection{Combinator Completeness}

    We show here how to prove completeness for the |_∥_| combinator, but proofs for other combinators follow a similar structure. Our goal is to show that if, for some generator $g_1 : \mathbb{G}\ a\ n$ and $x : a$, $g_1 \leadsto x$, then for all generators $g_2$ we have that $(g_1 \parallel g_2) \leadsto x$. Since the $\parallel$-combinator is defined in terms of $merge$, we first prove a similar property over the $merge$ function by inducting over |x ∈ xs|. 

\begin{code}
merge-complete-left :  ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x : a}
                       → x ∈ xs → x ∈ merge xs ys
\end{code}

    With the above lemma that asserts left-completeness of the $merge$ function, we can set out to prove left-completeness for the $\parallel$-combinator. The key insight here is that the depth bound at which $x$ occurs does not change, thus we can simply reuse it, and lift the above lemma to the generator type: 

\begin{code}
∥-complete-left :  ∀ {a : Set} {x : a} {f g : ∀ {n : ℕ} → 𝔾 a n}
                   → f ↝ x → (f ∥ g) ↝ x
∥-complete-left (n , p) = n , merge-complete-left p
\end{code}

    Proofs about the productivity of combinators can, in a similar fashion, be lifted to reason about completeness. This allows us to show that if the two operands of a choice are both complete, then the resulting generator is complete as well: 

\begin{code}
∥-Complete :  ∀ {a b : Set} {f : ∀ {n : ℕ} → 𝔾 a n} {g : ∀ {n : ℕ} → 𝔾 b n}
              → Complete f → Complete g
              → Complete (⦇ inj₁ f ⦈ ∥ ⦇ inj₂ g ⦈)
\end{code}

    The definition simply invokes |∥-complete-left|, though there is an intermediate step where we show that mapping |inj₁| or |inj₂| over a generator preserves its completeness. 

    \paragraph{Depth monotonicity} Contrary to coproducts, the depth bound at which values occur in the production of a generator is not preserved by products. If a value |x| occurs at depth $n$, it is by no means guaranteed that |(x , y)| occurs at depth $n$ for any value |y|. This poses the following problem: suppose |f ↝ x| and |g ↝ y|, what depth do we chose when we aim to show that |⦇ f , g ⦈ ↝ (x , y)|? 

    We might say that the lowest depth that at which the product generator produces the pair |(x , y)| is equal to |max (depth (f ↝ x)) (depth (g ↝ y))|. However, this includes the implicit assumption that if a generator produces a value at depth $n$, it will also produce this value at depth $m$ for any $m \geq n$. This property follows automatically from the intended meaning of the term \textit{depth bound}, but is in no way enforced in Agda. This means that we cannot complete the proof for product generators without adding the following postulate:

\begin{code}
postulate depth-monotone :
            ∀ {a : Set} {x : a} {n m : ℕ} {g₁ : ∀ {n : ℕ} → 𝔾 a n}
            → n ≤ m → x ∈ g₁ (n , refl) → x ∈ g₁ (m , refl)  
\end{code}

    Of course, adding such a postulate is dangerous, since it assumes depth monotonicity for \textit{any} inhabitant of the generator type, while the generator type itself in no way enforces that its inhabitants are actually depth monotone. A better solution would be to make the completeness proof for product generators depend on the depth monotonicity of its operands, shifting the responsibility to the programmer defining the generator. Additionally, we aim to provide proofs that our combinators preserve monotonicity. 

  \subsubsection{Correctness of Derived Generators}

    When assembling a completeness proof for derived generators, the question arises which metadata structure to use to deal with |K|-combinators; we need both a generator of the type referred to by the |K| leave, as well as a proof that it is correct. The natural choice for metadata is then a dependent pair with a generator and a completeness proof: |Σ[ gen ∈ ⟪ 𝔾 a ⟫ ] Complete ⟨ gen ⟩|. 

    \paragraph{Proving completeness for the |K|-combinator} Consider the result type of our completeness proof: 

\begin{code}
Complete ⟨ deriveGen {f = f} {g = f} {!!} ⟩
\end{code}

    The metadata structure that is required by |deriveGen| is different from the structure that the completeness proof gets as its input. This means that we require a mapping function that can be used to transform metadata structures:

\begin{code}
map-reginfo :  ∀ {f : Reg} {P Q : Set → Set} 
               → (∀ {a : Set} → P a → Q a) → RegInfo P f → RegInfo Q f
\end{code}

    In this case, we simply need to extract the first element of the dependent pair, resulting in the following result type for our completeness proof: 

\begin{code}
Complete ⟨ deriveGen {f = f} {g = f} (map-reginfo proj₁ info) ⟩
\end{code}

    where |info| refers to the metadata structure that was provided. 

    \paragraph{Assembling the proof} When attempting to assemble the final proof, we encounter much of the same problems as with the definition of |deriveGen|. Especially in the case of products and coproducts, we would like to recurse on the left- and right subtree before combining the result into the desired proof. This is again problematic, since the proofs resulting from the recursive calls will have the wrong type. To solve this, we use an auxiliary lemma that establishes a productivity proof for |deriveGen|, where we keep track both of the top level pattern functor for which we are deriving the proof, as well as the top level metadata structure (which is needed for the |I|-combinator). The general pattern is similar to that used in the definition of |deriveGen|. 

\subsubsection{Equivalence with manually defined generators}

    With a completeness proof for derived generators at hand, we can prove that generators derived from pattern functors are equivalent to their manually defined counterparts. Consider the following generator that generates values of the |Maybe| type: 

\begin{code}
maybe : ∀ {a : Set} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 (Maybe a) ⟫
maybe a _  =  ⦇ nothing    ⦈
           ∥  ⦇ just ⟨ a ⟩ ⦈
\end{code}

    Given a proven complete generator for elements of type |a|, we can construct a proof that |maybe| is a complete generator. Assuming an instance argument is in scope of type |Regular (Maybe a)|, we can derive a generator for the |Maybe| type as well: 

\begin{code}
maybe' : ∀ {n : ℕ} → (a : Set) → ⟪ 𝔾 a ⟫ → 𝔾 (Maybe a) n
maybe' a gen = isoGen (Maybe a) (K~ gen ⊕~ U~)
\end{code}

    We can prove the completeness of this derived generator using our completeness proof for |deriveGen|. The key observation is that completeness is preserved if we apply a bijective function to the outputs of a generator. Given that such a proof, equivalence between the manual and derived generator for the |maybe| type now trivially follows from their respective completeness. 

  \subsection{Generation for Indexed Datatypes}

    Although having a well understood and proven set of definitions for the enumeration of regular types is useful, we would like to achieve something similar for indexed datatypes. As described in section \ref{genindex}, our existing set of combinators can be easily adapted to work with indexed datatypes, meaning that generators for indexed types can be defined in a very natural way. For example, for the |Fin| datatype: 

\begin{code}
fin : ⟪ 𝔾ᵢ Fin ⟫
fin _ zero     = uninhabited
fin μ (suc n)  =  ⦇ zero      ⦈
               ∥  ⦇ suc (μ n) ⦈
\end{code}

    Here, |uninhabited| denotes that a type is uninhabited for a certain index, and is simply defined as |const []|. Note that |uninhabited| should be used with care, since it has the potential to be a source of inefficiency!

    Although the current set of combinators can be used to manually assemble generators for some indexed datatypes, we still lack a generic procedure to derive generators for indexed datatypes as well as suitable combinators to capture more intricate dependencies between indices.  

  \section{Timetable and planning}

    In the remainder of this thesis, we aim to address the following topics: 

    \begin{enumerate}
    \item
    Generic derivation of generators for multisorted signatures. 

    \item
    Enumeration for datatypes beyond multisorted signatures
    
    \item 
    A port to Haskell of (part of) our work. 
    \end{enumerate}

    The remainder of this section contains a little bit of elaboration on each of these topics, identifying challenges and possible approaches, as well as (first) steps required. It is important to note that there is little use in starting on the latter two topics before we have finished generic generators for multisorted signatures.
  \subsection{Generic Generation for Multisorted Signatures}

    We intend to apply the approach used for generic derivation of generators for regular types to multisorted signatures. That is, automatically derive a generator from a signature that generates values of the fixed point of its interpretation and using a suitable isomorphism to obtain values of the desired type. 

    Given a family of types |x : i → Set| The interpretation function described by Dagand \cite{dagand2017essence} interprets signatures as a function from index to a dependent pair (e.g. a $\Sigma$-type) consisting of a choice of constructor and a $\Pi$-type describing a mapping between arity and an element of |x| indexed with whatever is returned by the signature's typing discipline: 

\begin{code}
⟦_⟧ : ∀ {i : Set} → Sig i → (x : i → Set) → (i → Set)
⟦ Op ◃ Ar ∣ Ty ⟧ x = λ i → Σ[ op ∈ ⟦ Op i ⟧ᵤ ] Π[ ⟦ Ar op ⟧ᵤ ] x ∘ Ty
\end{code}

    This means that, if we desire to generically derive a generator for a signature's interpretation, we need a way to generate both $\Sigma$- and $\Pi$-types. A generic generator for $\Sigma$-types can be obtained by adapting a generator for pairs to deal with the dependencies between elements. $\Pi$-types, however, are a little more complicated, as we do not have any functionality for dealing with the generation of function types yet. 
    
    We identify the following steps necessary in order to achieve generic generation for multisorted signatures: 

    \begin{enumerate}

      \item
      Defining suitable combinators to deal with the enumeration of function types, similar to SmallCheck's \cite{runciman2008smallcheck} \textit{CoSerial} typeclass. 

      \item
      Extending generators for pairs and function types to generators for $\Sigma$- and $\Pi$-types. The |Applicative| class is probably not expressive enough for this, since it does not allow for dependencies between the different parameters of a construction. For example, in the generator for pairs (|⦇ x , y ⦈|), |x| and |y| are generated independently, while in a $\Sigma$-type the type of y would depend on the generated value for |x|. The |Monad| class is expressive enough to capture such dependencies.

      \item
      Defining suitable isomorphisms between datatypes and the fixed point of some signature. For the most part this step is relatively trivial, though some challenge arises from the fact that the interpretation of signatures contains a function type.  

      \item 
      Formalizing completeness for function types. This step is necessary if we desire to eventually prove completeness for the generators derived from signatures. However, it may be challenging to do so, as it requires that we prove that any arbitrary function occurs in an enumeration.  

      \item 
      Automatically deriving generation for the inhabitants of a signature's fixed point. This should be rather straightforward given that we can generate $\Sigma$-types and $\Pi$-types. 

      \item
      Formalizing completeness for said derivation, and extending it to generators derived from an isomorphism. This step completely depends on whether we succeed in formalizing completeness for function types. 
    \end{enumerate}

  \subsection{Beyond Multisorted Signatures}

    Not all indexed datatypes can be described as a signature. In particular, constructors are used with arity greater than 1 with dependencies between the indices of recursive calls are problematic. For example, consider the following datatype definition for binary trees indexed with their size: 

\begin{code}
data Tree : ℕ → Set where
    leaf : Tree zero
    node : ∀ {n m : ℕ} → Tree n → Tree m  → Tree (suc (n + m))
\end{code}

    When attempting to define a signature for this type, we cannot define a suitable typing discipline: 

\begin{code}
Ty-Tree : (n : ℕ) → (op : ⟦ Op-Tree n ⟧ᵤ) → ⟦ Ar-Tree n op ⟧ᵤ → ℕ
Ty-Tree zero tt ()
Ty-Tree (suc n) tt (inj₁ x) = {!!}
Ty-Tree (suc n) tt (inj₂ y) = {!!}
\end{code}

    The definition of |Tree| requires that the sum of the last two branches is equal to |n|, but since they are independently determined, there is no way to enforce this requirement. In general this means that we cannot capture any datatype that has a constructor with recursive positions whose indices in some way depend on each other as a signature. 

    Another problem is that |_+_| is surjective on $\mathbb{N}$, so the indices of the recursive positions are not uniquely determined by the index of the result type. Multisorted signatures are only equipped to return a single index for their recursive positions.

    These limitations mean, for example, that we cannot describe the simply typed lambda calculus as a signature, since similar dependencies occur when constructing a typing judgement for function application. 

    In case of the |Tree| datatype, we can define a generator if we have a way to invert |_+_| (That is, for all |n|, find all pairs of numbers such that they sum to |n|) combined with an appropriate $Monad$ instance for |𝔾|. 

    Solving this problem generically will probably be too difficult, as it essentially equates to synthesizing proofs for arbitrary theorems (which is a hard problem \cite{cook1971complexity} ). However, the |Tree| example points us to a hybrid solution, where \textit{most} of the generator can be mechanically defined based on the datatype definition, but input from the programmer is required to supply a suitable strategy to deal with the more difficult parts of generation (in this case, inversion of the |_+_| function). 

    Hence a good approach may be to establish the common paterns that emerge when defining example generators for more complex datatypes (we have already done so for the simply typed lambda calculus and regular expressions) and trying to find out which part of the generator follow mechanically from the definition of the datatype, and which parts require more thought from the programmer. 

  \subsection{Haskell Implementation}

    Implementing (part of) our work in Haskell gives us opportunity to work on a few more practical aspects: 

    \begin{enumerate}
      \item 
      Developing a framework for generation and sampling of values of some Generic Algebraic Datatypes \cite{hinze2003fun} based on our Agda development. Though generically enumerating all inhabitants of a GADT is probably a too difficult, we may be able to do so for at least the subset of GADTs that can be described as a multisorted signature. Additionally some work has been done on generic programming for datatypes beyond regular ADTs in Haskell \cite{magalhaes2011generic, serrano2018generic}, which might be useful for our purposes. 

      \item 
      Integration with our findings into existing testing facilities for Haskell, such as QuickCheck or SmallCheck, allowing for a wider range of test data to be automatically generated in these frameworks. 

      \item 
      Applying memoization techniques in order to achieve efficient sampling and/or generation of complex data. Memoization in the context of functional languages has been studied extensively \cite{brown2007monadic, swadi2006monadic} and has shown to be effective in the context of data generation \cite{duregaard2013feat}, and it might prove effective for improving performance in our case. 
    \end{enumerate}

    Additionally, porting our work to Haskell allows for experimentation with the generation of realistic abstract syntax datatypes. 
\bibliographystyle{acm} % ACM-Reference-Format
\bibliography{references}
\end{document}