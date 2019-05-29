\section{Dependent Types}

    Dependent type theory allows the definition of types that depend 
    on values. In addition to familiar constructs, such as the unit 
    type ($\top$) and the empty type $\bot$, one can use so-called 
    $\Pi$-types and $\Sigma$-types. $\Pi$-types capture the idea of 
    dependent function types, that is, \textit{functions} whose output 
    type may depend on the values of its input. Given some type $A$ 
    and a family $P$ of types indexed by values of type $A$ (i.e. $P$ 
    has type $A \rightarrow Type$), $\Pi$-types have the following 
    definition: 

\begin{equation*}
\Pi_{(x : A)} P(x) \equiv (x : A) \rightarrow P(x) 
\end{equation*}

    In a similar spirit, $\Sigma$-types are ordered \textit{pairs} of 
    which the type of the second value may depend on te first value of 
    the pair. 

\begin{equation*}
\Sigma_{(x : A)} P(x) \equiv (x : A) \times P(x) 
\end{equation*}

    The Curry-Howard equivalence extends to $\Pi$- and $\Sigma$-types 
    as well: they can be used to model universal and existential 
    quantification \cite{wadler2015propositions}. 

  \subsection{Agda}

    Agda is a programming language based on Martin L{\"o}f type theory 
    \cite{norell2008dependently}. Its syntax is broadly similar to Haskell's, 
    though Agda's type system is more elaborate in the sense that types 
    may depend on term level values. Agda is also a proof assistant, 
    using the Curry-Howard equivalence to express propositions as 
    types. 

  \subsubsection{Codata and Sized Types}\label{codata}

    All definitions in Agda are required to be \textit{total}, meaning 
    that they must be defined on all possible inputs, and give a result 
    in finite time. The Halting problem states that it is impossible to 
    define a general procedure that decides the termination condition 
    for all functions, so to ensure that only terminating definitions 
    are accepted Agda's termination checker uses a sound approximation. 
    A logical consequence is that there are Agda programs that terminate, 
    but are rejected by the termination checker. This means that we cannot 
    work with infinite data in the same way as in the same way as in 
    Haskell, which does not care about termination. For  example, the 
    following definition is perfectly fine in Haskell: 

\begin{code}
nats :: [Int]
nats = 0 : map (+1) nats
\end{code}

    meanwhile, an equivalent definition in Agda gets rejected by the Termination 
    checker: 

\includeagda{2}{natsnonterminating}

    This is no surprise, as the termination checker will reject any 
    recursive calls where there is not at least one argument that is 
    strictly smaller. However, in both Agda and Haskell, an expression 
    such as |take 10 nats| evaluates to $[0,1, \ldots , 9]$ in finite 
    time. 

    We can prevent the termination checker from flagging these kind 
    of operations by making the lazy semantics explicit, using 
    \textit{codata} and {sized types}. Codata is a general term for 
    possible inifinite data, often described by a co-recursive definition. 
    Sized types extend the space of function definitions that are recognized 
    by the termination checker as terminating by tracking information about 
    the size of values in types \cite{abel2010miniagda}. In the case of lists, 
    this means that we explicitly specify that the recursive argument to the 
    |_∷_| constructor is a \textit{Thunk}, which should only be evaluated 
    when needed: 

\includeagda{2}{colist}

    We can now define |nats| in Agda by wrapping the recursive call in a thunk: 

\includeagda{2}{terminating}

    Since colists are possible infinite structures, there are some functions we can 
    define on lists, but not on colists. An example of this is a function calculating 
    the length of a colist: 

\begin{code}
length : ∀ {a : Set} → Colist a ∞ →  ℕ
length [] = 0
length (x ∷ xs) = suc (length' (xs .force))
\end{code}

    In this case |length| is not accepted by the termination checker because the input 
    colist is indexed with size |∞|, meaning that there is no finite upper bound on its 
    size. Hence, there is no guarantee that our function terminates when inductively 
    defined on the input colist.
    
    There are some cases in which we can convince the termination checker that our 
    definition is terminating by using sized types. Consider the folowing example of a 
    function that increments every element in a list of naturals with its position: 

\begin{code}
incpos : List ℕ → List ℕ
incpos [] = []
incpos (x ∷ xs) = x ∷ incpos (map suc xs)
\end{code}

    The recursive call to |incpos| gets flagged by the termination checker; we know that 
    |map| does not alter the length of a list, but the termination checker cannot see this. 
    For all it knows |map| equals |const [ 1 ]|, which would make |incpos| non-terminating. 
    The size-preserving property of |map| is not reflected in its type. 

    We can define an alternative version of the |List| datatype indexed with |Size|, which 
    tracks the depth of a value in its type. 

\begin{code}
data List (a : Set) : Size → Set where
  []  : ∀ {i} → List' a i
  _∷_ : ∀ {i} → a → List' a i → List' a (↑ i)
\end{code}

    Here |↑ i| means that the depth of a value constructed using the $::$ constructor is one 
    deeper than its recursive argument. Incidently, the recursive depth of a list is equal 
    to its size (or length), but this is not necessarily the case. By indexing values of 
    |List| with their size, we can define a version of |map| which reflects in its type that 
    the size of the input argument is preserved: 

\begin{code}
map : ∀ {i} {a b : Set} → (a → b) → List a i → List b i
\end{code}

    Using this definition of |map|, the definition of |incpos| is no longer rejected by the 
    termination checker. 

\section{Generic Programming and Type Universes}

  In \emph{Datatype generic programming}, we define functionality not for individual types, 
  but rather by induction on \emph{structure} of types. This means that generic functions 
  will not take values of a particular type as input, but a \emph{code} that describes the 
  structure of a type. Haskell's |deriving| mechanism is a prime example of this mechanism. 
  Anytime we add |deriving Eq| to a datatype definition, GHC will, in the background, convert 
  our datatype to a structural representation, and use a \emph{generic equality} to create 
  an instance of the |Eq| typeclass for our type. 

\subsection{Design Pattern}

  Datatype generic programming often follows a common design pattern that is 
  independent of the structural representation of types involved. In general 
  we follow the following steps: 

  \begin{enumerate}
    \item
      First, we define a datatype |𝓤| representing the structure of types, 
      often called a \emph{Universe}. 
    \item 
      Next, we define a semantics |⟦_⟧ : 𝓤 → K| that associates codes in |𝓤| 
      with an appropriate value of kind |K|. In practice this is often a functorial 
      representation of kind |Set → Set|.
    \item 
      Finally, we (often) define a fixed point combinator of type |(u : 𝓤) → Set| 
      that calculates the fixpoint of |⟦ u ⟧|. 
  \end{enumerate}

  This imposes the implicit requirement that if we want to represent some type 
  |T| with a code |u : 𝓤|, the fixpoint of |u| should be isomorphic to |T|. 

  Given these ingredients we have everything we need at hand to write generic 
  functions. Section $3$ of Ulf Norell's \emph{Dependently Typed Programming 
  in Agda} \cite{norell2008dependently} contains an in depth explanation of 
  how this can be done in Agda. We will only give a rough sketch of the most 
  common design pattern here. In general, a datatype generic function is supplied
  with a code |u : 𝓤|, and returns a function whose type is dependent on the 
  code it was supplied with. In the case of a generic decidable equality, we 
  might use the following type signature. 

\includeagda{2}{eqdef}

  If we now define |≟| by induction over |u|, we have a decision procedure 
  for decidable equality that may act on values on any type, provided their 
  structure can be described as a code in |𝓤|. 

\subsection{Example Universes}

  There exist many different type universes. We will give a short overview of 
  the universes used in this thesis here; they will be explained in more detail 
  later on when we define generic generators for them. The literature review in 
  \cref{sec:lituniverses} contains a brief discussion of type universes beyond 
  those used we used for generic enumeration. 

  \paragraph{Regular Types} 
    Although the universe of regular types is arguably 
    one of the simplest type universes, it can describe a wide variaty of 
    recursive algebraic datatypes \texttt{[citation]}, roughly corresponding to 
    the algebraic types in Haskell98. Examples of regular types are 
    \emph{natural numbers}, \emph{lists} and \emph{binary trees}. 

    Regular types are insufficient once we want to have a generic representation 
    of mutually recursive or indexed datatypes. 

  \paragraph{Indexed Containers}
    The universe of \emph{Indexed Containers} \cite{altenkirch2015indexed} 
    provides a generic representation of large class indexed datatypes by 
    induction on the index type. Datatypes we can describe using this universe 
    include |Fin| (\cref{lst:deffin}), |Vec| (\cref{lst:defvec}) and closed 
    lambda terms (\cref{lst:defwellscoped}).

  \paragraph{Indexed Descriptions}
    Using the universe of \emph{Indexed Descriptions} \cite{dagand2013cosmology}
    we can represent arbitrary indexed datatypes. This allows us to describe 
    datatypes that are beyond what can be described using indexed containers, 
    that is, datatypes with recursive subtrees that are interdependent or whose 
    recursive subtrees have indices that cannot be uniquely determined from the 
    index of a value. 

\section{Universe Polymorphism}

  Contrary to Haskell, Agda does not have separate notions for \emph{types}, 
  \emph{kinds} and \emph{sorts}. Instead it provides an infinite hierarchy of 
  type universes, where level is a member of the next, i.e. |Set n : Set (n+1)|. 
  Agda uses this construction in favor of simply declaring |Set : Set| to avoid 
  the construction of contradictory statements through Russel's paradox. 

  This implies that every construction in Agda that ranges over some |Set n| can 
  only be used for values that are in |Set n|. It is not possible to define, for 
  example, a |List| datatype that may contain both \emph{values} and \emph{types}
   for this reason. 

   We can work around this limitation by defining a \emph{universe polymorphic} 
   construction for lists: 

\includeagda{2}{upolylist}

  Allowing us to capture lists of types (such as |ℕ ∷ Bool ∷ []|) and lists of 
  values (such as |1 ∷ 2 ∷ []|) using a single datatype. 

  Agda allows for the programmer to declare that |Set : Set| using the |{-# 
  OPTIONS --type-in-type #-}| pragma. Throughout the development accompanying 
  this thesis, we will refrain from using this pragma wherever possible. However,
   since the universe polymorphic version of an Agda construction is often more 
  difficult to read, we will include all code examples in this thesis in their 
  non-polymorphic form. 
