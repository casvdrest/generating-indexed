
  We can describe a large class of recursive algebraic data types as a \emph{regular types}. 
  In this section we describe this universe together with its 
  semantics, and demonstrate how we may define generators for regular types by 
  induction over their codes. We will then prove that these derived generators 
  satisfy our completeness property. 

\section{Universe definition}

  Though the exact definition may vary across sources, the universe of regular types 
  is generally regarded to consist of the \emph{empty type} (containing \emph{no} 
  inhabitants), the unit type (containing exactly \emph{one} inhabitant) and constants 
  types (which simply refer to another type). Regular types are closed under both \emph
  {products} (representing pairing of types) and \emph{coproducts} (representing a 
  choice between types). Listing \ref{lst:regular} shows the Agda datatype that we use 
  to represent codes in this universe, with the associated semantics of type \agda{Reg → 
  Set → Set} being shown in listing \ref{lst:regsem}.

\includeagdalisting{5}{regular}{The universe of regular types}{lst:regular}

  The semantics map a code to a functorial representation of the datatype described by 
  that code, commonly known as its \emph{pattern functor}. The datatype that is 
  represented by a code is isomorphic to the least fixpoint of its pattern functor. We 
  find this fixpoint with the following fixpoint operation:

\includeagda{5}{regularfix}

\includeagdalisting{5}{regularsemantics}{Semantics of the universe of regular types}
{lst:regsem}

  \begin{example}

    Let us consider the type of natural numbers: 

\includeagda{3}{defnat}

    \agda{Nat} exposes two constructors: the nullary constructor \agda{zero}, and the unary 
    constructor \agda{suc} that takes one recursive argument. We can view this type then 
    as a coproduct (or choice) between a unit type, representing \agda{zero}, and a 
    recursive position, representing the recursive argument of the \agda{suc} constructor. 

\includeagdanv{5}{natregular}

    We convince ourselves that \agda{ℕ'} is indeed equivalent to \agda{ℕ} by defining an 
    isomorphism of type \agda{ℕ ≃ ℕ'}. 
  \end{example}

  In general, we say that a type is regular if and only if we can provide a proof that 
  it is isomorphic to the fixpoint of some code \agda{c} of type \agda{Reg}. We use a record to 
  capture this notion, which holds a code and an value that witnesses the 
  isomorphism between the fixpoint of this code and the regular type \agda{A}.

\includeagda{5}{regularrecord}

  By instantiating \agda{Regular} for a type \agda{A}, we may use any generic functionality by leveraging 
  the isomorphism stored with the record \agda{Regular A}.

\section{Deriving generators}\label{sec:genericgenreg}

  We can derive generators for all regular types at once by induction over their associated 
  codes. In \cref{sec:regularproof} we will prove that the generators we 
  derive from codes satisfy our completeness property under the enumerative interpretation we defined in 
  \cref{sec:generators}. 

\subsection{Performing induction over codes}

  In our initial approach, we might be to try to define a generator that produces values 
  of type \agda{Fix c}. Unfortunately, this will not work. By choosing \agda{Fix c} as the type of elements 
  generated, we implicitly imposes the restriction that any \agda{I} in \agda{c} refers to \agda{Fix 
  c}. This restriction is problematic in some cases, specifically when encountering a 
  product or coproduct. In that case, we destruct a code \agda{c} into two smaller codes \agda{c₁} and \agda{c₂}. Calling 
  our deriving function on these codes will yield two generators, one producing values 
  of type \agda{Fix c₁} and the other producing values of type \agda{Fix c₂}. It is then not 
  possible to combine these generators into a single generator producing values of 
  type \agda{Fix c}: the recursive positions in the subgenerators refer to different types!

  To remedy this, we make a distinction between the code we are doing induction over, \agda{
  c}, and the code which describes the type that recursive positions in \agda{c} refer to, \agda{
  c'}. Furthermore, we do not produce elements of type \agda{Fix c}, but rather of type \agda{⟦ 
  c ⟧ (Fix c')} (i.e. values of the type given by the semantics of \agda{c}, but recursive 
  positions refer to the type described by \agda{c'}). When calling our derivation function 
  with two equal codes, the values produced will be isomorphic to \agda{Fix c}! This results 
  in the following type signature of our generator deriving function: 

\includeagda{5}{genericgen2}

  This step allows us to perform induction over the first input code, 
  while still being able to have recursive positions refer to the correct \emph
  {top-level code}. The first and second type parameter (respectively describing the 
  type we are generating, and the type of recursive positions) of \agda{Gen} are
  consequently distinct, with the second type parameter being isomorphic to \agda{Fix c'}.  

\subsection{Composing generic generators}

  Now that we have the correct type for \agda{deriveGen} in place, we can begin to define it 
  We do this on a case by case basis, describing how to derive generators for each 
  of the constructors of the \agda{Reg} datatype. 

\subsubsection{The empty (Z) and unit (U) type}

  We start with the generic generators for the \agda{Z} and \agda{U} constructors. Recall
  that the generators we derive from these constructors should produce \emph{all}
  inhabitants of the type given by their semantics. 

\includeagda{5}{genericgenZU}

  In case of both \agda{Z} and \agda{U} this requirement is trivially fulfilled. For the \agda{Z} combinator, we yield a 
  generator that produces no elements, since its semantics is the empty type (\agda{⊥}). As 
  for the \agda{U} combinator, \agda{⟦ U ⟧ (Fix c')} equals the unit type (\agda{⊤}), so we need to 
  return a generator that produces all inhabitants of \agda{⊤}, which is only the value \agda{tt}. 
  We get a generator that does this by lifting \agda{tt} into the generator type. 

\subsubsection{Recursive positions (I)}

  We mark a recursive position in a generator with the $\mu$ constructor. However, 
  given the previously defined type signature for \agda{deriveGen}, $\mu$ is a generator 
  that produces elements of type \agda{⟦ c' ⟧ (Fix c')}. We require that the generator 
  derived from the \agda{I} constructor produces elements of type \agda{⟦ I ⟧ (Fix c')}, which 
  by definition of \agda{⟦\_⟧} equals \agda{Fix c'}. This means that we need to apply the 
  fixpoint wrapper \agda{In} over the elements produced by $\mu$:

\includeagda{5}{genericgenI}

\subsubsection{Products (\agda{⊗}) and coproducts (\agda{⊕})}

  For products and coproducts, we can quite easily define their generators by 
  recursing on the left and right subcodes now that we have the correct type for \agda{
  deriveGen} in place. We then only need to combine these generators in an appropriate 
  way. We do this respectively building a product type out of the elements produced by 
  the subgenerators and by marking a choice between the generators derived from the 
  subcodes. 

\includeagda{5}{genericgenPCOP}

  Of course, the exact way in which the elements of subgenerators are combined still 
  depends on how we interpret the abstract generator type; here we only describe these 
  operations in terms of the functions exposed by |Applicative| and |Alternative|.

\subsubsection{Wrapping up}

  We have defined a function that derives generators from codes in the 
  universe of regular types (barring constant types, with with we will deal in \cref
  {sec:constanttypes}). We need to take one final step before we can use \agda{deriveGen} for 
  all regular types. Any vallue \agda{Regular A} holds an isomorphism \agda{A ≃ Fix c}, so we need 
  to wrap the resulting generator in the \agda{In} constructor, which we can only do if \agda{
  deriveGen} is called \emph{with two equal codes}. We use the following function to 
  perform this initial call to \agda{deriveGen}, and to wrap the values produced by the 
  resulting generator in the fixpoint operation: 

\includeagda{5}{genericgenFinal}

  The elements produced by \agda{genericGen} can now readily be transformed into the 
  required datatype through an appropriate isomorphism. 

  \begin{example}

    We derive a generator for natural numbers by invoking \agda{genericGen} on the 
    appropriate code \agda{U ⊕ I}, and applying an isomorphism of type \agda{ℕ ≃ ℕ'} to 
    the resulting generator:

\includeagdanv{5}{genericgenNat}

  \end{example}

  We use the following function to define a generator for any type \agda{A} for which there 
  is an instance argument \agda{Regular A} in scope:

\includeagda{5}{isogen}

\section{Constant types}\label{sec:constanttypes}

  Constant types present a bit of a challenge, since the code \agda{K s} can carry any type in \agda{Set}. 
  This means that we know nothing about the type \agda{s} whatsoever. Since we have no general 
  procedure for deriving generators for arbitrary types in \agda{Set}, we need to either 
  restrict \agda{s} to a set of types for which we \emph{can} derive generators (e.g. regular types), or have the user 
  supply generators for all constant types in a code. We choose the latter approach in order to retain the flexibility 
  that comes with the ability to refer to arbitrary types.

\subsection{Metadata structure}

  We have the programmer supply the necessary generators by defining a \emph{metadata} 
  structure, indexed by a code, that carries additional information for every \agda{K} 
  constructor used. We parameterize \agda{deriveGen} with a metadata structure that is
  indexed by the code we are inducting over, carrying generators for every 
  constant type used in said code. The definition of this metadata structure is shown 
  in listing \ref{lst:mdstructure}. 

\includeagdalisting{5}{mdstructure}{Metadata structure carrying additional information 
for constant types}{lst:mdstructure}

  We purposefully keep the type of information stored for constant types abstract, as 
  we will need to record information beyond generators when proving completeness for 
  the generators produced by \agda{deriveGen}. 

\subsection{Deriving a generator for constant types}

  Given the definition of the metadata structure, we augment \agda{deriveGen} with an extra 
  parameter that stores generators for every constant type in a code: 

\includeagda{5}{derivegenKTy} 

  We then define \agda{deriveGen} as follows for constant types:

\includeagda{5}{derivegenKCase}

  All cases for existing constructors remain the same, except for the fact that the metadata parameter 
  distributes over recursive calls in the case of products and coproducts. 
  
  With this, we have completed the definition of \agda{deriveGen}. 

\section{Proving completeness}\label{sec:regularproof}

  We set out to prove that the derived generators satisfy our completeness property.
  Obviously, this relies on the generators supplied by the programmer being complete 
  as well. 

  We start the proof by instantiating the completeness property formulated in listing \ref
  {lst:abstractgen} with \agda{deriveGen} to obtain the definition of the theorem that 
  we will prove:

\includeagda{5}{derivegencomplete}

  We explicitly distinguish the codes \agda{c} and \agda{c'} to (again) be able to construct the 
  proof by performing induction over the input code \agda{c}. The reasoning behind this is very 
  much the same as the reasoning behind the definition of \agda{deriveGen} itself. If we 
  invoke this lemma with two equal codes, we may utilize the fact that \agda{In} is 
  bijective to obtain a proof that \agda{genericGen} is complete too. The key observation 
  here is that mapping a bijective function over a complete generator results in 
  another complete generator. We do not show this proof here explicitly, but we have constructed
  a proof of the following statement in the Agda development:

\includeagda{5}{genericgencomplete}

  Which we need to generalize the proof to all types which are isomorphic to some code \agda{c : Reg}. 

\subsection{Proof structure}

  The completeness proof roughly follows the following steps: 

  \begin{itemize}

    \item 
      First, we prove completeness for the individual constructors of the \agda{Reg} type. 

    \item 
      Next, we assemble a suitable metadata structure to carry the required proofs 
      for constant types in this code. 

    \item 
      Finally, we generalize the proof over our generic generator to a proof that 
      ranges over all types \agda{A} that are isomorphic to the fixpoint of some code
      \agda{c : Reg}. 

  \end{itemize}

\subsection{Combinator correctness}

  We start our proof by asserting that the generators derived from the individual constructors 
  of the \agda{Reg} datatype are complete. That is, we show that for every constructor of \agda{Reg} the derived generator 
  produces all values of the type given by the semantics of that constructor. 
  
\subsubsection{Empty (Z) and unit (U) types}

  In the case of \agda{Z} and \agda{U}, completing the completeness proof is relatively easy:

\includeagda{5}{derivegencompleteZU}

  The semantics of \agda{Z} is the empty type, so any generator producing values of type \agda{⊥}
   is trivially complete: we simply close this branch with an absurd pattern. In the 
   case of \agda{U} we simply need to show that interpreting \agda{pure tt} returns a list 
   containing \agda{tt}, which we can do by returning a trivial proof that \agda{tt} is an 
   element of the singleton list \agda{[ tt ]}. 

\subsubsection{Recursive positions (I)}

  The proof that a recursive position $\mu$ is interpreted to a complete enumeration 
  is simply the induction hypothesis, which states that \agda{deriveGen c' c'} is complete. A subtlety 
  here is that we \emph{must} pattern match on \agda{In x}, otherwise Agda's termination 
  checker will flag the recursive call. 

\includeagda{5}{derivegencompleteI}

  We can complete this definition by proving a lemma that asserts that mapping \agda{In} 
  over a generator preserves completeness: 

\includeagda{5}{derivegencompleteIlemma}

\subsubsection{Products and coproducts}

  Things become a bit more interesting once we move to products and coproducts, since 
  this requires us to prove that the way in which we combine subgenerators satisfies completeness 
  under our enumerative interpretation. In both cases, this proof follows a similar 
  structure: 

  \begin{enumerate}
    \item 
      Obtain completeness proofs for the subgenerators with recursive calls to \agda{
      deriveGen-Complete}
    \item 
      Construct a lemma that asserts that the enumerative interpretation of generators 
      preserves completeness
    \item 
      Invoke this lemma to complete the definition
  \end{enumerate}
  
  \paragraph{Coproducts} To find out what lemma we need to prove completeness for the 
  generators derived from coproducts, we observe the following equality by unfolding 
  the defintions of \agda{enumerate} and \agda{deriveGen}: 

\includeagda{5}{tolistcopeq}

  The generators on the right hand side of the equation are virtually the same as the 
  recursive calls we make, modulo the \agda{inj₁} and \agda{inj₂} constructors we map over them to unify 
  their result types. We can obtain a proof of completeness for the right hand side of this equality 
  by proving the following two lemmas about the \agda{merge} function we use to combine the 
  results of the subgenerators of a coproduct. 

\includeagda{5}{mergecomplete}

  Proofs for these lemmas can readily be extended to a proof that if the left and 
  right subgenerator are complete under the enumerative interpretation, then the 
  interpretation of their coproduct (which is a call to \agda{merge}), is also complete, 
  simply by pairing them with the depth value returned by the recursive call. 
  
  \paragraph{Products} Similarly, by unfolding \agda{enumerate} one step in the 
  case of products, we get the following equality:

\includeagda{5}{enumeratepeq}

  We can prove completeness for the right hand side of this equality by proving the following lemma 
  about the applicative instance of lists:

\includeagda{5}{apcomplete}

  We can again extend this lemma to a proof that the enumerative interpretation of 
  product types is completeness preserving. In \cref{sec:monotonicity} we describe in 
  more detail how an appropriate depth value can be obtained. 

\subsection{Completeness for constant types}

  Since our completeness proof relies on completeness of the supplied generators for constant 
  types, we need the programmer to supply a completness proof for the generators 
  stored in the provided metadata structure. To this end, we 
  parameterize the completeness proof over a metadata structure that carries 
  both generators for all constant types in a code, and a proof that these generators are 
  complete. We express the relation between generator and proof with a dependent 
  pair, using the following type synonym to describe the type of this metadata parameter:

\includeagda{5}{proofinfotype}

  In order to be able to use the completeness proof from the metadata structure in the 
  \agda{K} branch of \agda{deriveGen-Complete}, we need to be able to express the relationship 
  between the metadata structure used in the proof, and the metadata structure used by 
  \agda{deriveGen}. To do this, we need a way to transform the \emph{type} of information that is 
  carried by a metadata structure. This will allow us to map a metadata structure 
  containing generators and proofs to a metadata structure containing only generators. 

\includeagda{5}{kinfomap}

  We only present the case for constant types; in all other cases we simply distribute the mapping 
  operation over all recursive positions. Given a definition of \agda{KInfo-map}, we can take the first projection of the 
  metadata input to \agda{deriveGen-Complete}, and use the resulting metadata structure as input 
  to \agda{deriveGen}. We define a type synonym to describe this mapping operation:

\includeagda{5}{mdtransform}

  Which results in the following final type of \agda{deriveGen-Complete}. 

\includeagda{5}{derivegenwithmd}

  By expressing the relation between the metadata structure supplied to the proof 
  and the metadata structure supplied to \agda{deriveGen} explicitly in the proof's type 
  signature, Agda is able to infer that the completeness proofs range over the 
  generators that were supplied to \agda{deriveGen}. This allows us to complete the 
  proof for constant types simply by returning the proof that is stored in the 
  metadata structure. 
  
\subsection{Generator monotonicity}\label{sec:monotonicity}

  There is one crucial detail we ignored when describing how to prove completeness for 
  generators derived from product types. Since existential quantification is modelled 
  in type theory as a dependent pair, we have to explicitly supply the depth at which 
  an element occurs in an enumeration when proving completeness. A problem, however arises 
  when choosing a depth value for generators derived from 
  product types. We combine values of both subgenerators in a pair, so at what depth 
  does this pair occur in the enumeration of the combined generator? Generally, we say 
  that the recursive depth of a pair is the maximum of the depth of its components. 
  Suppose the first component occurs at depth $n$, and the second at depth $m$. The 
  depth of the pair is then \agda{max n m}. However, the second components  of the returned 
  completeness proofs respectively have the type \agda{x ∈ enumerate ... n} and \agda{x ∈ 
  enumerate ... m}. In order to unify their types, we need a lemma that transforms a 
  proof that some value \agda{x} occurs in the enumeration at depth \agda{k} into a proof that \agda{
  x} occurs in the enumeration at 
  depth \agda{k'}, given that $k \leq k'$. In other words, the set of values that occurs in 
  an enumeration monotonously increases with the enumeration depth. We thus require a 
  proof of the following lemma in order to finish the completeness proof: 

\includeagda{5}{derivegenmonotone}

  We do not show the definition of this proof here, but it can be completed using the 
  exact same proof structure we used for the completeness proof. 

\subsection{Extending completeness to all regular types}

  By bringing all these elements together, we can prove that \agda{deriveGen} is complete 
  for any code \agda{c}, given that the programmer is able to provide a suitable 
  metadatastructure. We can transform this proof into a proof that \agda{isoGen} returns a 
  complete generator by observing that any isomorphism \agda{A ≃ B} establishes a bijection 
  between the types \agda{A} and \agda{B}. Hence, if we apply such an isomorphism to the 
  elements produced by a generator, completeness is preserved. 

  We have the required isomorphism readily at our disposal in \agda{isoGen}, since it is 
  contained in the instance argument \agda{Regular a}. This allows us to have \agda{isoGen} 
  return a completeness proof for the generator it derives: 

\includeagda{5}{isogenproven}

  With which we have shown that if a type is regular, we can derive a complete 
  generator producing elements of that type. 

\section*{Conclusion}

  In this chapter, we have shown how generators can be derived from codes in the 
  universe of regular types. While this is not necessarily a new result (e.g. 
  SmallCheck does this as well), we have also proven that these generators are 
  complete under an enumerative interpretation, meaning that they are guaranteed to 
  produce every inhabitant of the type they range over at some point. 

  Futhermore, the work done to establish this generic generator and the accompanying 
  proof provides a solid basis for extending this result to generic generators for 
  more expressive type universes. As we will see in the upcoming chapters, the 
  approach described in this chapter is to a large extent applicable to other type 
  universes as well. 

  Although we can describe many familiar datatypes with a code in the universe of 
  regular types, there are some limitations. Most notably, we cannot describe any 
  family of mutually recursive types. The way the universe is set up includes the 
  implicit assumption that all occurrences of \agda{I} reference the same type. If we 
  attempt to describe a datatype that is a composite of more than one recursive 
  algebraic datatype, such as for example the type of \emph{rose trees}: 

\includeagda{5}{defrose}

  The other obvious shortcoming is that this universe only allows us to describe 
  non-indexed datatypes. In the following chapters we will consider two type 
  universes that \emph{can} do this. 