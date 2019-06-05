
  A large class of recursive algebraic data types can be described with the universe 
  of \emph{regular types}. In this section we lay out this universe, together with its 
  semantics, and describe how we may define functions over regular types by induction 
  over their codes. We will then show how this allows us to derive from a code a 
  generic generator that produces all values of a regular type. We sketch how we can 
  prove that these generators are indeed complete. 

\section{The universe of regular types}

  Though the exact definition may vary across sources, the universe of regular types 
  is generally regarded to consist of the \emph{empty type} (or $\mathbb{0}$), the 
  unit type (or $\mathbb{1}$) and constants types. It is closed under both products 
  and coproducts \footnote{This roughly corresponds to datatypes in Haskell 98}. We 
  can define a datatype for this universe in Agda as shown in lising \ref{lst:regular}

\includeagdalisting{5}{regular}{The universe of regular types}{lst:regular}

  The semantics associated with the |Reg| datatype, as shown in listing \ref
  {lst:regsem}, map a code to a functorial representation of a datatype, commonly 
  known as its \emph{pattern functor}. The datatype that is represented by a code is 
  isomorphic to the least fixpoint of its pattern functor. 

\includeagdalisting{5}{regularsemantics}{Semantics of the universe of regular types}{lst:regsem}

  \begin{example}

    The type of natural numbers (see listing \ref{lst:defnat}) 
    exposes two constructors: the nullary constructor |zero|, and the unary constructor |suc| that takes one recursive argument. We may thus view this type as a coproduct (i.e. choice) of either a \emph{unit type} or a \emph{recursive subtree}: 

\includeagdanv{5}{natregular}

    We convince ourselves that |ℕ'| is indeed equivalent to |ℕ| by defining conversion 
    functions, and showing their composition is extensionally equal to the identity 
    function, shown in listing \ref{lst:natiso}. 

  \end{example}

\includeagdalisting{5}{natiso}{Isomorphism between |ℕ| and |ℕ'|}{lst:natiso}

  We may then say that a type is regular if we can provide a proof that it is 
  isomorphic to the fixpoint of some |c| of type |Reg|. We use a record to capture 
  this notion, consisting of a code and an value that witnesses the isomorphism.

\includeagda{5}{regularrecord}

  By instantiating |Regular| for a type, we may use any generic functionality that is defined over regular types. 

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
  codes. Furthermore, we will show in section \cref{regularproof} that, once 
  interpreted as enumerators, these generators are complete; i.e. any value will eventually show up in the enumerator, provided we supply a sufficiently large size parameter.  

\subsection{Defining functions over codes}

  If we apply the approach described in \cref{sec:tudesignpattern} without care, we run into problems. Simply put, we cannot work with values of type |Fix c|, since this implicitly imposes the restriction that any |I| in |c| refers to |Fix c|. However, as we descent into recursive calls, the code we are working with changes, and with it the type associated with recursive positions. For example: the |I| in (|U ⊕ I|) refers to values of type |Fix (U ⊕ I)|, not |Fix I|. We need to make a distinction between the code we are currently working on, and the code that recursive positions refer to. For this reason, we cannot define the generic generator, |deriveGen|, with the following type signature: 

\includeagda{5}{genericgen}

  If we observe that |⟦ c ⟧ (Fix c) ≃ Fix c|, we may alter the type signature of |deriveGen| slightly, such that it takes two input codes instead of one

\includeagda{5}{genericgen2}

  This allows us to induct over the first input code, while still being able to have recursive positions reference the correct \emph{top-level code}. Notice that the first and second type parameter of |Gen| are different. This is intensional, as we would otherwise not be able to use the $\mu$ constructor to mark recursive positions.  

\subsection{Composing generic generators}

  Now that we have the correct type for |deriveGen| in place, we can start defining it. Starting with the cases for |Z| and |U|: 

\includeagda{5}{genericgenZU}

  Both cases are trivial. In case of the |Z| combinator, we yield a generator that produces no elements. As for the |U| combinator, |⟦ U ⟧ (Fix c')| equals |⊤|, so we need to return a generator that produces all inhabitants of |⊤|. This is simply done by lifting the single value |tt| into the generator type. 

  In case of the |I| combinator, we cannot simply use the $\mu$ constructor right away. In this context, $\mu$ has the type |Gen (⟦ c' ⟧ (Fix c')) ( ⟦ c' ⟧ (Fix c'))|. However, since |⟦ I ⟧ (Fix c)| equals |Fix c|, the types do not lign up. We need to map the |In| constructor over $\mu$ to fix this: 

\includeagda{5}{genericgenI}

  Moving on to products and coproducts: with the correct type for |deriveGen| in place, we can define their generators quite easily by recursing on the left and right subcodes, and combining their results using the appropriate generator combinators: 

\includeagda{5}{genericgenPCOP}

  Since the the |Regular| record expects an isomorphism with |Fix c|, we still need to wrap the resulting generator in the |In| constructor: 

\includeagda{5}{genericgenFinal}

  The elements produced by |genericGen| can now readily be transformed into the required datatype through an appropriate isomorphism. 

  \begin{example}

    We derive a generator for natural numbers by invoking |genericGen| on the appropriate code |U ⊕ I|, and applying the isomorphism defined in listing \ref{natiso} to its results: 

\includeagdanv{5}{genericgenNat}

  \end{example}

  In general, we can derive a generator for any type |A|, as long as there is an instance argument of the type |Regular A| in scope: 

\includeagda{5}{isogen}

\section{Enumerators for regular types}

  We can define enumerators for regular types, and prove that these enumerators are \emph{complete}, in the sense that they will allways \emph{eventually} produce any arbitrary elementof the type they range over. We show how to arrive at such an enumerator, and how to assemble the completeness proof. 

\subsection{A generic enumerator}

  Since we define enumerators as functions |ℕ → List A|, we can look at Haskell's standard library for inspiration, specifically the implementations of the |Applicative| and |Alternative| typeclasses. 

\subsection{Proving completeness}\label{sec:regularproof}
