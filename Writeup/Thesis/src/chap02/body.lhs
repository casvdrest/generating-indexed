In this section, we will briefly discuss some of the relevant theoretical background 
for this thesis. We assume the reader to be familiar with the general concepts of both 
Haskell and Agda, as well as functional programming in general. We shortly touch upon 
the following subjects:

\begin{itemize}
  \item
  \emph{Type theory} and its relationship with \emph{classical logic} through the 
  \emph{Curry-Howard correspondence}

  \item 
  Some of the more advanced features of the programming language \emph{Agda}, which we 
  use for the formalization of our ideas: \emph{Codata}, \emph{Sized Types} and \emph
  {Universe Polymorphism}. 

  \item 
  \emph{Datatype generic programming} using \emph{type universes} and the design 
  patterns associated with datatype generic programming.  
\end{itemize}

  We present this section as a courtesy to those readers who might not be familiar 
  with these topics; anyone experienced in these areas should feel free to skip ahead. 

\section{Type Theory}

  \emph{Type theory} is the mathematical foundation that underlies the \emph{type 
  systems} of many modern programming languages. In type theory, we reason about \emph\
  {terms} and their \emph{types}. We briefly introduce some basic concepts, and show 
  how they relate to our proofs in Agda. 

  \subsection{Intuitionistic Type Theory}

  In Intuitionistic type theory consists of terms, types and judgements $a : A$ 
  stating that terms have a certain type. Generally we have the following two finite 
  constructions: $\mathbb{0}$ or the \emph{empty type}, containing no terms, and 
  $\mathbb{1}$ or the \emph{unit type} which contains exactly $1$ term. Additionally,
  the \emph{equality type}, $=$, captures the notion of equality for both terms and 
  types. The equalit type is constructed from \emph{reflexivity}, i.e. it is 
  inhabited by one term $refl$ of the type $a = a$. 

  Types may be combined using three constructions. The \emph{function type}, $a 
  \rightarrow b$ is inhabited by functions that take an element of type $a$ as input 
  and produce something of type $b$. The \emph{sum type}, $a + b$ creates a type that 
  is inhabited by \emph{either} a value of type $a$ \emph{or} a 
  value of type $b$. The \emph{product type}, $a * b$, is inhabited by a pair of 
  values, one of type $a$ and one of type $b$. In terms of set theory, these 
  operations correspond respectively to functions, \emph{cartesian product} and \emph
  {tagged union}. 

  \subsection{The Curry-Howard Equivalence}

  The \emph{Curry-Howard equivalence} establishes an isomorphism between \emph
  {propositions and types} and \emph{proofs and terms} \cite{wadler2015propositions}. 
  This means that for any type there is a corresponding proposition, and any term 
  inhabiting this type corresponds to a proof of the associated proposition. Types and 
  propositions are generally connected using the mapping shown in \cref{tbl:chiso}.

\begin{table}[h]\label{tbl:chiso}
\begin{center}\begin{framed}
\begin{tabular}{ll}
\multicolumn{1}{c}{\textbf{Classical Logic}} & \textbf{Type Theory} \\ \hline \hline
False                                        & $\bot$               \\
True                                         & $\top$               \\
$P \vee Q$                                   & $P + Q$              \\
$P \wedge Q$                                 & $P * Q$              \\
$p \Rightarrow Q$                            & $P \rightarrow Q$                       
\end{tabular}
\caption{Correspondence between classical logic and type theory}
\end{framed}\end{center}
\end{table}

  \begin{example}

    We can model the proposition $P \wedge (Q \vee R) \Rightarrow (P \wedge Q) \vee (P 
    \wedge R)$ as a function with the following type: 

\includeagdanv{2}{tautologytype}

    We can then prove that this implication holds on any proposition by supplying a 
    definition that inhabits the above type: 

\includeagda{2}{tautologydef}

  \end{example}

  In general, we may prove any proposition that captured as a type by writing a 
  programin that inhabits that type. Allmost all constructs are readily translatable 
  from proposition logic, except boolean negation, for which there is no corresponding 
  construction in type theory. Instead, we model negation using functions to the empty 
  type $\bot$. That is, we can prove a property $P$ to be false by writing a function \
  $P \rightarrow \bot$. This essentially says that $P$ is true, we can derive a \
  contradiction, hence it must be false. Alowing us to prove many properties including negation. 
  
  \begin{example}

    For example, we might prove that a property 
    cannot be both true and false, i.e. $\forall\ P\ .\ \neg(P \wedge \neg P)$: 

\includeagdanv{2}{notpandnotp}

  \end{example}

  However, there are properties of classical logic which do not carry over well 
  through the Curry-Howard isomorphism. A good example of this is the \emph{law of 
  excluded middle}, which cannot be proven in type theory: 

\includeagda{2}{excludedmiddle}

  This implies that type theory is incomplete as a proof system, in the sense that 
  there exist properties wich we cannot prove, nor disprove. 

\subsection{Dependent Types}

  Dependent type theory allows the definition of types that depend on values. In 
  addition to the constructs introduced above, one can use so-called $\Pi$-types and 
  $\Sigma$-types. 
  $\Pi$-types capture the idea of \emph{dependent function types}, that is, functions 
  whose output type may depend on the values of its input. Given some type $A$ and a 
  family $P$ of types indexed by values of type $A$ (i.e. $P$ has type $A \rightarrow 
  Type$), $\Pi$-types have the following form: 

\begin{equation*}
\Pi_{(x : A)} P(x) \equiv (x : A) \rightarrow P(x) 
\end{equation*}

  In a similar spirit, $\Sigma$-types are ordered \textit{pairs} of which the type
  of the second value may depend on te first value of the pair:

\begin{equation*}
\Sigma_{(x : A)} P(x) \equiv (x : A) \times P(x) 
\end{equation*}

  The Curry-Howard equivalence extends to $\Pi$- and $\Sigma$-types as well: they 
  can be used to model universal and existential quantification \cite
  {wadler2015propositions} (\cref{chisodependent}).

\begin{table}[h]\label{tbl:chisodependent}
\begin{center}\begin{framed}
\begin{tabular}{ll}
\multicolumn{1}{c}{\textbf{Classical Logic}} & \textbf{Type Theory}    \\ \hline \hline
$\exists\ x\ .\ P\ x$                        & $\Sigma_{(x : A)} P(x)$ \\
$\forall\ x\ .\ P\ x$                        & $\Pi_{(x : A)} P(x)$                    
\end{tabular}
\caption{Correspondence between quantifiers in classical logic and type theory}
\end{framed}\end{center}
\end{table}

  \begin{example} 
  
    we might capture the relation between universal and negated existential 
    quantification ($\forall\ x\ .\ \neg P\ x \Rightarrow \neg \exists\ x\ .\ P\ x$) 
    as follows: 

\includeagdanv{2}{forallnottonotexists} 

  \end{example}

  The correspondence between dependent pairs and existential quantification quite \
  beautifullly illustrates the constructive nature of proofs in type theory; we prove 
  any existential property by presenting a term together with a proof that the 
  required property holds for that term. 

\section{Agda}

  Agda is a programming language based on Intuitionistic type theory\cite
  {norell2008dependently}. Its syntax is broadly similar to Haskell's, though Agda's 
  type system is arguably more expressive, since types may depend on term level 
  values. 

  Due to the aforementioned correspondence between types and propositions, any Agda 
  program we write is simultaneously a proof of the proposition associated with its 
  type. Through this mechanism, Agda serves a dual purpose as a proof assistent. 

\subsection{Codata and Sized Types}\label{codata}

  All definitions in Agda are required to be \textit{total}, meaning that they must be 
  defined on all possible inputs, produce a result in finite time. To enforce this 
  requirement, Agda needs to check whether the definitions we provide are terminating. 
  As stated by the \emph{Halting Problem}, it is not possible to define a general 
  procedure to perform this check. Instead, Agda uses a \emph{sound approximation}, in 
  which it requires at least one argument of any recursive call to be \emph
  {syntactically smaller} than its corresponding function argument. A consequence of 
  this approach is that there are Agda programs that terminate, but are rejected by 
  the termination checker. This means that we cannot work with infinite data in the 
  same way as in the same way as in Haskell, which does not care about termination. 
  
  \begin{example}

    The following definition is perfectly fine in Haskell: 

\begin{myhaskellnv}
\begin{code}
nats :: [Int]
nats = 0 : map (+1) nats
\end{code}
\end{myhaskellnv}

    Meanwhile, an equivalent definition in Agda gets rejected by the Termination 
    checker. The recursive call to |nats| has no arguments, so none are structurally 
    smaller, thus the termination checker flags this call.  

\includeagda{2}{natsnonterminating}

  \end{example}

  However, as long as we use |nats| sensibly, there does not need to be a problem. 
  Nonterminating programs only arise with improper use of such a definition, for 
  example by calculating the length of |nats|. We can prevent the termination 
  checker from flagging these kind of operations by making the lazy semantics 
  explicit, using \textit{codata} and {sized types}. Codata is a general term for 
  possible inifinite data, often described by a co-recursive definition. Sized types 
  extend the space of function definitions that are recognized by the termination 
  checker as terminating by tracking information about the size of values in types 
  \cite{abel2010miniagda}. In the case of lists, this means that we explicitly 
  specify that the recursive argument to the |_∷_| constructor is a \textit{Thunk}, 
  which should only be evaluated when needed: 

\includeagda{2}{colist}

  We can now define |nats| in Agda by wrapping the recursive call in a thunk, 
  explicitly marking that it is not to be evaluated until needed.  

\includeagda{2}{natsterminating}

  Since colists are possible infinite structures, there are some functions we can 
  define on lists, but not on colists. 
    
  \begin{example} Consider a function that attempts to calculate the length of a |Colist|: 

\includeagdanv{2}{lengthdef}

    In this case |length| is not accepted by the termination checker because the input 
    colist is indexed with size |∞|, meaning that there is no finite upper bound on 
    its size. Hence, there is no guarantee that our function terminates when 
    inductively defined on the input colist. 

  \end{example}
  
  There are some cases in which we can convince the termination checker that our definition is terminating by using sized types. Consider the folowing function that increments every element in a list of naturals with its position: 

\includeagda{2}{incposdef}

  The recursive call to |incpos| gets flagged by the termination checker; we know 
  that |map| does not alter the length of a list, but the termination checker cannot 
  see this. For all it knows |map| equals |const [ 1 ]|, which would make |incpos| 
  non-terminating. The size-preserving property of |map| is not reflected in its 
  type. To mitigate this issue, we can define an alternative version of the |List| 
  datatype indexed with |Size|, which tracks the depth of a value in its type. 

\includeagda{2}{sizedlistdef}

  Here |↑ i| means that the depth of a value constructed using the $::$ constructor 
  is one deeper than its recursive argument. Incidently, the recursive depth of a 
  list is equal to its size (or length), but this is not necessarily the case. By 
  indexing values of |List| with their size, we can define a version of |map| which 
  reflects in its type that the size of the input argument is preserved: 

\includeagda{2}{sizedmapdef}

  Using this definition of |map|, the definition of |incpos| is no longer rejected 
  by the termination checker. 

\subsection{Universe Polymorphism}

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
  values (such as |1 ∷ 2 ∷ []|) using a single datatype. Agda allows for the 
  programmer to declare that |Set : Set| using the |{-# OPTIONS --type-in-type #-}| 
  pragma. Throughout the development accompanying this thesis, we will refrain from 
  using this pragma wherever possible. The examples included in this thesis are often 
  not universe-polymorphic, since the universe level variables required often pollute 
  the code, and obfuscate the concept we are trying to convey. 

\section{Generic Programming and Type Universes}

  In \emph{Datatype generic programming}, we define functionality not for individual 
  types, but rather by induction on \emph{structure} of types. This means that generic 
  functions will not take values of a particular type as input, but a \emph{code} that 
  describes the structure of a type. Haskell's |deriving| mechanism is a prime example 
  of this mechanism. Anytime we add |deriving Eq| to a datatype definition, GHC will, 
  in the background, convert our datatype to a structural representation, and use a 
  \emph{generic equality} to create 
  an instance of the |Eq| typeclass for our type. 

\subsection{Design Pattern}\label{sec:tudesignpattern}

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
  code it was supplied with. 
  
  \begin{example}

    Suppose we are defining a generic procedure for decidable equality. We might use the following type signature for such a procedure:

\includeagdanv{2}{eqdef}

    If we now define |≟| by induction over |u|, we have a decision procedure 
    for decidable equality that may act on values on any type, provided their 
    structure can be described as a code in |𝓤|. 

  \end{example}

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
    \emph{natural numbers}, \emph{lists} and \emph{binary trees}. Regular types are 
    insufficient once we want to have a generic representation of mutually recursive 
    or indexed datatypes. 

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
