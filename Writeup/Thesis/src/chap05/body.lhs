
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
  isomorphic to the least fixpoint of its pattern functor. We fix pattern functors 
  using the following fixpoint combinator: 

\includeagda{5}{regularfix}

\includeagdalisting{5}{regularsemantics}{Semantics of the universe of regular types}
{lst:regsem}

  \begin{example}

    The type of natural numbers (see listing \ref{lst:defnat}) 
    exposes two constructors: the nullary constructor |zero|, and the unary 
    constructor |suc| that takes one recursive argument. We may thus view this type as 
    a coproduct (i.e. choice) of either a \emph{unit type} or a \emph{recursive 
    subtree}: 

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
  interpreted as enumerators, these generators are complete; i.e. any value will 
  eventually show up in the enumerator, provided we supply a sufficiently large size 
  parameter.  

\subsection{Defining functions over codes}

  If we apply the approach described in \cref{sec:tudesignpattern} without care, we 
  run into problems. Simply put, we cannot work with values of type |Fix c|, since 
  this implicitly imposes the restriction that any |I| in |c| refers to |Fix c|. 
  However, as we descent into recursive calls, the code we are working with changes, 
  and with it the type associated with recursive positions. For example: the |I| in (|
  U ⊕ I|) refers to values of type |Fix (U ⊕ I)|, not |Fix I|. We need to make a 
  distinction between the code we are currently working on, and the code that 
  recursive positions refer to. For this reason, we cannot define the generic 
  generator, |deriveGen|, with the following type signature: 

\includeagda{5}{genericgen}

  If we observe that |⟦ c ⟧ (Fix c) ≃ Fix c|, we may alter the type signature of |
  deriveGen| slightly, such that it takes two input codes instead of one

\includeagda{5}{genericgen2}

  This allows us to induct over the first input code, while still being able to have 
  recursive positions reference the correct \emph{top-level code}. Notice that the 
  first and second type parameter of |Gen| are different. This is intensional, as we 
  would otherwise not be able to use the $\mu$ constructor to mark recursive 
  positions.  

\subsection{Composing generic generators}

  Now that we have the correct type for |deriveGen| in place, we can start defining 
  it. Starting with the cases for |Z| and |U|: 

\includeagda{5}{genericgenZU}

  Both cases are trivial. In case of the |Z| combinator, we yield a generator that 
  produces no elements. As for the |U| combinator, |⟦ U ⟧ (Fix c')| equals |⊤|, so we 
  need to return a generator that produces all inhabitants of |⊤|. This is simply done 
  by lifting the single value |tt| into the generator type. 

  In case of the |I| combinator, we cannot simply use the $\mu$ constructor right 
  away. In this context, $\mu$ has the type |Gen (⟦ c' ⟧ (Fix c')) ( ⟦ c' ⟧ (Fix c'))|
  . However, since |⟦ I ⟧ (Fix c)| equals |Fix c|, the types do not lign up. We need 
  to map the |In| constructor over $\mu$ to fix this: 

\includeagda{5}{genericgenI}

  Moving on to products and coproducts: with the correct type for |deriveGen| in place,
   we can define their generators quite easily by recursing on the left and right 
   subcodes, and combining their results using the appropriate generator combinators: 

\includeagda{5}{genericgenPCOP}

  Although defining |deriveGen| constitutes most of the work, we are not quite there 
  yet. Since the the |Regular| record expects an isomorphism with |Fix c|, we still 
  need to wrap the resulting generator in the |In| constructor: 

\includeagda{5}{genericgenFinal}

  The elements produced by |genericGen| can now readily be transformed into the 
  required datatype through an appropriate isomorphism. 

  \begin{example}

    We derive a generator for natural numbers by invoking |genericGen| on the 
    appropriate code |U ⊕ I|, and applying the isomorphism defined in listing \ref
    {natiso} to its results: 

\includeagdanv{5}{genericgenNat}

  \end{example}

  In general, we can derive a generator for any type |A|, as long as there is an 
  instance argument of the type |Regular A| in scope: 

\includeagda{5}{isogen}

\section{Constant Types}

  In some cases, we describe datatypes as a compositions of other datatypes. An 
  example of this would be lists of numbers, |List ℕ|. Our current universe definition 
  is not expressive enough to do this. 
  
  \begin{example}

    Given the code representing natural numbers (|U ⊕ I|) and lists (|U ⊕ (C ⊗ I)|, 
    where |C| is a code representing the type of elements in the list), we might be 
    tempted to try and replace |C| with the code for natural numbers in the code for 
    lists: 

  \includeagdanv{5}{natlist}

    This code does not describe lists of natural numbers. The problem here is that the 
    two recursive positions refer to the \emph{same} code, which is incorrect. We need 
    the first |I| to refer to the code of natural numbers, and the second |I| to refer 
    to the entire code. 

  \end{example}

\subsection{Definition and Semantics}

  In order to be able to refer to other recursive datatypes, the universe of regular 
  types often includes a constructor marking \emph{constant types}: 

\includeagda{5}{constantdef}

  The |K| constructor takes one parameter of type |Set|, marking the type it 
  references. The semantics of |K| is simply the type it carries: 

\includeagda{5}{constantsemantics}

  \begin{example}
    
    Given the addition of |K|, we can now define a code that represents lists of 
    natural numbers: 

\includeagdanv{5}{natlist2}

    With the property that |listℕ ≃ List ℕ|. 

  \end{example}

\subsection{Generic Generators for Constant Typse}

  When attempting to define |deriveGen| on |K s|, we run into a problem. We need to 
  return a generator that produces values of type |s|, but we have no information 
  about |s| whatsoever, apart from knowing that it lies in |Set|. This is a problem, 
  since we cannot derive generators for arbitrary values in |Set|. This leaves us with 
  two options: either we restrict the types that |K| may carry to those types for 
  which we can generically derive a generator, or we require the programmer to supply 
  a generator for every constant type in a code. We choose the latter, since it has 
  the advantage that we can generate a larger set of types. 

  We have the programmer supply the necessary generators by defining a \emph{metadata} 
  structure, indexed by a code, that carries additional information for every |K| 
  constructor used. We then parameterize |deriveGen| with a metadata structure, 
  indexed by the code we are inducting over. The definition of the metadata structure 
  is shown in listing \ref{lst:mdstructure}. 

\includeagdalisting{5}{mdstructure}{Metadata structure carrying additional information 
for constant types}{lst:mdstructure}

  We then adapt the type of |deriveGen| to accept a parameter containing the required 
  metadata structure: 

\includeagda{5}{derivegenKTy} 

  We then define |deriveGen| as follows for constant types. All cases for existing 
  constructors remain the same. 

\includeagda{5}{derivegenKCase}

\section{Complete Enumerators For Regular Types}

  By applying the |toList| interpretation shown in listing \ref{lst:tolist} to our 
  generic generator for regular types we obtain a complete enumeration for regular 
  types. Obviously, this relies on the programmer to supply complete generators for 
  all constant types referred to by a code. 

  We formulate the desired completeness property as follows: \textit{for every code c 
  and value x it holds that there is an n such that x occurs at depth n in the 
  enumeration derived from c}. In Agda, this amounts to proving the following 
  statement: 

\includeagda{5}{genericgencomplete}

  Just as was the case with deriving generators for codes, we need to take into the 
  account the difference between the code we are currently working with, and the top 
  level code. To this end, we alter the previous statement slightly. 

\includeagda{5}{derivegencomplete}

  If we invoke this lemma with two equal codes, we may leverage the fact that |In| is 
  bijective to obtain a proof that |genericGen| is complete too. The key observation 
  here is that mapping a bijective function over a complete generator results in 
  another complete generator. 

  The completeness proof roughly follows the following steps: 

  \begin{itemize}

    \item 
      First, we prove completeness for individual generator combinators 

    \item 
      Next, we assemble a suitable metadata structure to carry the required proofs 
      for constant types in the code. 

    \item 
      Finally, we assemble the individual components into a proof of the statement 
      above. 

  \end{itemize}

\subsection{Combinator Correctness}

  We start our proof by asserting that the used combinators are indeed complete. That 
  is, we show for every constructor of |Reg| that the generator we return in |
  deriveGen| produces all elements of the interpretation of that constructor. In the 
  case of |Z| and |U|, this is easy. 

\includeagda{5}{derivegencompleteZU}

  The semantics of |Z| is the empty type, so any generator producing values of type |⊥|
   is trivially complete. Similarly, in the case of |U| we simply need to show that 
   interpreting |pure tt| returns a list containing |tt|. 

  Things become a bit more interesting once we move to products and coproducts. In the 
  case of coproducts, we know the following equality to hold, by definition of both |
  toList| and |deriveGen|: 

\includeagda{5}{tolistcopeq}

  Basically, this equality unfolds the |toList| function one step. Notice how the 
  generators on the left hand side of the equation are \emph{almost} the same as the 
  recursive calls we make. This means that we can prove completeness for coproducts by 
  proving the following lemmas, where we obtain the required completeness proofs by 
  recursing on the left and right subcodes of the coproduct. 

\includeagda{5}{mergecomplete}

  Similarly, by unfolding the toList function one step in the case of products, we get 
  the following equality:

\includeagda{5}{tolistpeq}

  We can prove the right hand side of this equality by proving the following lemma 
  about the applicative instance of lists:

\includeagda{5}{apcomplete}

  Again, the preconditions of this lemma can be obtained by recursing on the left and 
  right subcodes of the product. 

\subsection{Completeness for Constant Types}

  Since our completeness proof relies on completeness of the generators for constant 
  types, we need the programmer to supply a proof that the supplied generators are 
  indeed complete. To this end, we add a metadata parameter to the type of |deriveGen|
  -|complete|, with the following type: 

\includeagda{5}{proofinfotype}

  In order to be able to use the completeness proof from the metadata structure in the 
  |K| branch of |deriveGen|-|Complete|, we need to be able to express the relationship 
  between the metadata structure used in the proof, and the metadata structure used by 
  |deriveGen|. To do this, we need a way to transform the type of information that is 
  carried by a value of type |KInfo|: 

\includeagda{5}{kinfomap}

  Given the definition of |KInfo|-|map|, we can take the first projection of the 
  metadata input to |deriveGen|-|Complete|, and use the resulting structure as input 
  to |deriveGen|: 

\includeagda{5}{proofinfotype}

  This amounts to the following final type for |deriveGen|-|Complete|, where |◂ m| = |
  KInfo|-|map proj₁ m|:  

\includeagda{5}{derivegenwithmd}

  Now, with this explicit relation between the completeness proofs and the generators 
  given to |deriveGen|, we can simply retrun the proof contained in the metadata of 
  the |K| branch. 
  
\subsection{Generator Monotonicity}

  The lemma |×|-|complete| is not enough to prove completeness in the case of 
  products. We make two recursive calls, that both return a dependent pair with a 
  depth value, and a proof that a value occurs in the enumeration at that depth. 
  However, we need to return just such a dependent pair stating that a pair of both 
  values does occur in the enumeration at a certain depth. The question is what depth 
  to use. The logical choice would be to take the maximum of both dephts. This comes 
  with the problem that we can only combine completeness proofs when they have the 
  same depth value. 

  For this reason, we need a way to transform a proof that some value |x| occurs in 
  the enumeration at depth |n| into a proof that |x| occurs in the enumeration at 
  depth |m|, given that $n \leq m$. In other words, the set of values that occurs in 
  an enumeration monotoneously increases with the enumeration depth. To finish our 
  completeness proof, this means that we require a proof of the following lemma: 

\includeagda{5}{derivegenmonotone}

  We can complete a proof of this lemma by using the same approach as for the 
  completeness proof. 

\subsection{Final Proof Sketch}

  By bringing all these elements together, we can prove that |deriveGen| is complete 
  for any code |c|, given that the programmer is able to provide a suitable 
  metadatastructure. We can transform this proof into a proof that |isoGen| returns a 
  complete generator by observing that any isomorphism |A ≃ B| establishes a bijection 
  between the types |A| and |B|. Hence, if we apply such an isomorphism to the 
  elements produced by a generator, completeness is preserved. 

  We have the required isomorphism readily at our disposal in |isoGen|, since it is 
  contained in the instance argument |Regular a|. This allows us to have |isoGen| 
  return a completeness proof for the generator it derives: 

\includeagda{5}{isogenproven}

  With which we have shown that if a type is regular, we can derive a complete 
  generator producing elements of that type. 
