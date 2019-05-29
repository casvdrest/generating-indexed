
  A large class of recursive algebraic data types can be described with 
  the universe of \emph{regular types}. In this section we lay out this 
  universe, together with its semantics, and describe how we may define 
  functions over regular types by induction over their codes. We will 
  then show how this allows us to derive from a code a generic generator 
  that produces all values of a regular type.

\section{The universe of regular types}

  Though the exact definition may vary across sources, the universe of 
  regular types is generally regarded to consist of the \emph{empty type} 
  (or $\mathbb{0}$), the unit type (or $\mathbb{1}$) and constants types. 
  It is closed under both products and coproducts. We can define a datatype 
  for this universe in Agda as shown in lising \ref{lst:regular}

\includeagdalisting{5}{regular}{The universe of regular types}{lst:regular}

  The semantics associated with the |Reg| datatype map a code to a functorial 
  representation of a datatype, commonly known as its \emph{pattern functor}. 
  The datatype that is represented by a code is isomorphic to the least 
  fixpoint of its pattern functor. 

\includeagda{5}{regularsemantics}

  \paragraph{Example} The type of natural numbers (see listing \ref{lst:defnat}) 
  exposes two constructors: the nullary constructor |zero|, and the unary 
  constructor |suc| that takes one recursive argument. We may thus view this 
  type as a coproduct (i.e. choice) of either a \emph{unit type} or a 
  \emph{recursive subtree}: 

\includeagda{5}{natregular}

  We convince ourselves that |ℕ'| is indeed equivalent to |ℕ| by defining 
  conversion functions, and showing their composition is extensionally equal to 
  the identity function. 

\includeagda{5}{natiso} 

  We may then say that a type is regular if we can provide a proof that it is 
  isomorphic to the fixpoint of some |c| of type |Reg|. We use a record to capture this 
  notion, consisting of a code and an value that witnesses the isomorphism.

\includeagda{5}{regularrecord}

\subsection{Non-regular data types}

  Although there are many algebraic datatypes that can be described in the universe 
  of regular types, some cannot. Perhaps the most obvious limitation the is lack of 
  ability to caputure data families indexed with values. The regular univeres 
  imposes the implicit restriction that a datatype is uniform in the sens that all 
  recursive subtrees are of the same type. Indexed families, however, allow for 
  recursive subtrees to have a structure that is different from the structure of the 
  datatype they are a part of. 

  Furethermore, any family of mutually recursive datatypes cannot be described as a 
  regular type; again, this is a result of the restriction that recursive positions 
  allways refer to a datatype with the same structure. 

\section{Generic Generators for regular types}

  We can derive generators for all regular types by induction over their associated 
  codes. Furthermore, we will show in section \cref{regularproof} that, once interpreted 
  as enumerators, these generators are complete; i.e. any value will eventually show 
  up in the enumerator, provided we supply a sufficiently large size parameter.  

\subsection{Defining functions over codes}

  Defining functions over codes is quite subtle, as we need to account for the code 
  referred to by recursive positions \cite{norell2008dependently}. Simply put, we 
  cannot work with values of type |Fix c|, since this implicitly imposes the 
  restriction that any |I| in |c| refers to |Fix c|. However, as we descent into 
  recursive calls, the code we are working with changes, and with it the type 
  associated with recursive positions. For example, the |I| in (|U ⊕ I|) refers 
  to values of type |Fix (U ⊕ I)|, not |Fix I|. 

  This can be resolved by observing that |⟦ c' ⟧ (Fix c) ≅ Fix c| for any code |c|
  and |c'|, so long |c| and |c'| are equal. By inducting over |c'|, we may recursively
  define functionality over codes without altering the semantics of recursive positions. 

\subsection{Composing generic generators}

\section{Enumerators for regular types}

\subsection{A generic enumerator}

\subsection{Proving completeness}\label{sec:regularproof}
