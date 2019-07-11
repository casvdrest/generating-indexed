\ref
To be able to represent arbitrary indexed families, we use the universe of \emph
{Indexed Descriptinos}, as proposed by Dagand \cite{dagand2013cosmology} in his PhD 
thesis. We structure this chapter in the same way as the previous two chapter, by 
first giving the definition and semantics of the universe, before showing how a 
generator can be derived from codes in this universe and proving that these generators 
are complete under our enumerative interpretation. 

\section{Universe Definition}\label{sec:idescdesc}

  We first give the definition of the universe, together with its semantics and 
  fixpoint operation, before considering well-typed lambda terms as an example to 
  demonstrate how we might model a more complex datatype in this universe and to show its
  we can capture datatypes that cannot be described as a regular type or indexed 
  container. 

\subsection{Definition \& Semantics}\label{sec:idescdef}

  Where indexed containers can be viewed as an extension to W-types, indexed 
  description take the universe of regular types as a basis and extend it to be able 
  to deal with more complex datatypes. 

\begin{enumerate}
  \item 
  A type parameter \agda{I : Set}, describing the type of indices.

  \item 
  A generalized coproduct, \agda{`σ}, that denotes choice between $n$ constructors, 
  in favor of the \agda{\_⊕\_} constructor. 

  \item 
  A combinator, \agda{`Σ}, denoting dependent pairs. 

  \item 
  Recursive positions, \agda{`var}, storing the index of recursive values. 
\end{enumerate}

  This amounts to the Agda datatype describing indexed descriptions shown in listing 
  \ref{lst:idesc}. Types are not described by a value of type \agda{IDesc I}, but rather as 
  a function from index to description, \agda{I → IDesc I}. 

\includeagdalisting{7}{idesc}{The Universe of indexed descriptions}{lst:idesc}

  We retain the product of two descriptions as a first order construct of the universe 
  while including a generalized notion for coproducts, which does not present a choice 
  between 2, but rather any possible number of operations. The \agda{Sl} datatype is used 
  to select these operations, and is isomorphic to \agda{Fin}. We will require a lot of 
  pattern matches this datatype to build descriptions, and by using \agda{Sl} over \agda{Fin} we 
  end up with slightly more succinct descriptions. The definition of \agda{Sl} is included 
  below: 

\includeagda{7}{sl}

  The semantics associated with the \agda{IDesc} universe is mostly the same as the 
  semantics of the universe of regular types, the key difference being is that we do 
  not map codes to a functor \agda{Set → Set}, but rather to a function of type \agda{I → (I → 
  Set) → Set}. The semantics is shown in listing \ref{lst:idescsem}.

\includeagdalisting{7}{idescsem}{Semantics of the IDesc universe}{lst:idescsem}

  The universe does not contain a separate constructor representing the empty type, 
  since we can simply encode it as a coproduct of zero constructors: \agda{`σ 0 λ()}.

  We calculate the fixpoint of a description's semantics using the following fixpoint 
  operation: 

\includeagda{7}{idescfix}

  \begin{example}
    We can describe the \agda{Fin} datatype as follows using a code in the universe of 
    indexed descriptions: 

\includeagdanv{7}{idescfin}

    If the index is \agda{zero}, there are no inhabitants, so we return a coproduct of zero 
    choices. Otherwise, we may choose between two constructors: \agda{zero} or \agda{suc}. 
    Notice that we describe the datatype by induction on the index type. This is not 
    required, although convenient in this case. A different, but equally valid 
    description exists, in which we use the \agda{`Σ} constructor to explicitly 
    enforce the constraint that the index \agda{n} is the successor of some \agda{n'}. 
    
\includeagdanv{7}{idescfin2}
    
    We then have that \agda{Fix finD n} is isomorphic to \agda{Fin n}. 

  \end{example}

  We capture the notion of datatypes that can be described in the universe of indexed 
  descriptions by again constructing a record that stores a description and a proof 
  that said description is isomorphic to the type we are describing: 

\includeagda{7}{describe}

  This allows us to use Agda's instance arguments to define functionality generically. 

\subsection{Exmample: describing well typed lambda terms}

  To demonstrate the expressiveness of the \agda{IDesc} universe, and to show how one might 
  model a more complex datatype, we consider simply typed lambda terms as an example. 
  We model the simply typed lambda calculus in Agda according to the representation 
  used in Philip Wadler and Wen Kokke's PLFA \cite{wadler2019plfa}. 

\subsubsection{Modelling SLC in Agda}

  Wadler and Kokke use a representation using De Bruijn indices \cite{de1972lambda}, 
  which represents variables as a natural denoting the number of lambda abstractions 
  between the variable and the binder it refers to. Using De Bruijn indices has the 
  clear advantage that $\alpha$-equivalent terms have the same representation. Listing 
  \ref{lst:lambdadatatypes} contains the datatype definitions for raw terms, types and 
  contexts. Raw terms represent untyped lambda terms. Types can be either the ground 
  type \agda{`τ}, or a function type \agda{σ `→ τ}. Since we are using De Bruijn 
  indices, we do not need to store variable names in the context, only types. Hence 
  the \agda{Ctx} type is isomorphic to \agda{List Ty}. 

\includeagdalisting{7}{lambdadatatypes}{Datatypes for raw terms, types and contexts}
{lst:lambdadatatypes}

  We write $\Gamma \ni \tau$ to signify that a variable with type $\tau$ is bound in 
  context $\Gamma$. Context membership is described by the following inference rules: 

\begin{equation*}
\texttt{[Top]}
  \frac{}{\Gamma , \tau \ni \alpha : \tau} \quad 
\texttt{[Pop]}
  \frac{\Gamma \ni \tau}{\Gamma , \sigma \ni \alpha : \tau}
\end{equation*}

  We describe these inference rules in Agda using an inductive datatype, shown in 
  listing \ref{lst:ctxmem}, indexed with a type and a context, whose inhabitants 
  correspond to all proofs that a context \agda{Γ} contains a variable of type 
  \agda{τ}. 

\includeagdalisting{7}{ctxmembership}{Context membership in Agda}{lst:ctxmem}

  We write $\Gamma \vdash t : \tau$ to express a typing judgement stating that term 
  $t$ has type $\tau$ when evaluated under context $\Gamma$. The following inference 
  rules determine when a term is type correct: 


\begin{equation*}
\texttt{[Var]}
  \frac{\Gamma \ni \alpha : \tau}{\Gamma \vdash \alpha : \tau} \quad 
\texttt{[Abs]}
  \frac{\Gamma , \alpha : \sigma \vdash t : \tau}{\Gamma \vdash \lambda\ \alpha\ .\ t 
  : \sigma \rightarrow \tau} \quad
\texttt{[App]}
  \frac{\Gamma \vdash t1 : \sigma \rightarrow \tau \quad \Gamma \vdash t2 : \sigma}
  {\Gamma \vdash t_1\ t_2 : \tau}
\end{equation*} 

  We model these inference rules in Agda using a binary relation between contexts and 
  types whose inhabitants correspond to all terms that have a given type under a given 
  context (listing \ref{lst:wflambda})

\includeagdalisting{7}{typejudgement}{Well-typed lambda terms as a binary relation}
{lst:wflambda}

  Given an inhabitant of type \agda{Γ ⊢ τ} , we can write a 
  function \agda{toTerm} that transforms the typing judgement to its corresponding untyped 
  term, which simply \emph{erases} the indices of a proof with type \agda{Γ ⊢ τ} to 
  obtain an untyped term. 

\includeagda{7}{toterm}

  The term returned by \agda{toTerm} will has type \agda{τ} under context \agda{Γ}. 

\subsubsection{An indexed description for well-typed terms}

  In \cref{sec:idescdef}, we saw that we can describe the \agda{Fin} both by induction on 
  the index, as well as by adding explicit constraints. Similarly, we can choose to 
  define a description for well-typed terms in two ways: either by induction on the 
  type of the terms we are describing, or by including an explicit constraint that the 
  index type is a function type for the description of the abstraction rule. In either 
  case, we start by defining descriptions for each of the three possible constructors 
  (listing \ref{lst:sltcconstructordesc}). 

\includeagdalisting{7}{sltcconstructordesc}{Descriptions for the constructors of the 
simply typed lambda calculus}{lst:sltcconstructordesc}

  Given the descriptions for the individual constructors, we can assemble a 
  description for the entire datatype by pattern matchin on the index type, and 
  returning for each branch a coproduct of the descriptions of all constructors that 
  could have been used to create a value with that particular index (listing \ref
  {lst:slcdescinductive}). 

\includeagdalisting{7}{slcdescinductive}{Inductive description of the simply typed 
lambda calculus}{lst:slcdescinductive}

  Alternatively, we can describe the simply typed lambda calculus as a coproduct of 
  the descriptions of all its constructors, and adding an explicit constraint in the 
  case of the abstraction rule that requires a proof that the index type is a function 
  type (listing \ref{lst:slcdescconstrained}). 
  
\includeagdalisting{7}{slcdescconstrained}{Description of the simply typed lambda 
calculus with explicit constraints}{lst:slcdescconstrained}
  
  To convince ourselves that these descriptions do indeed describe the same type, we 
  can show that their fixpoints are isomorphic: 

\includeagda{7}{desciso}

  Given an isomorphism between the fixpoints of two descriptions, we can prove that 
  they are both isomorphic to the target type by establishing an isomorphism between 
  the fixpoint of one of them and the type we are describing. For example, we might 
  prove the following isomorphism: 

\includeagda{7}{constrainediso}

  Using the transitivity of isomorphisms, we can show that the inductive description 
  also describes well typed terms. 

  Both variations are equally valid descriptions of the simply typed lambda calculus 
  (they are isomorphic), but depending on the situation one might prefer one over the 
  other. A downside to defining descriptions by induction over the index type is that 
  we often end up with at least some code duplication, making them unnecessarily 
  verbose. Descriptions with explicit constraints do not have this downside. We could 
  even substitute \agda{varDesc}, \agda{absDesc} and \agda{appDesc} for their respective definitions, 
  since they are only referred to once. This often results in descriptions that are 
  much more succinct, but arguably less straightforward. 

  When looking ahead to the derivation of generators from descriptions, we see that 
  using a description with explicit constraints has the side effect that we delay the 
  point at which we find out that a certain constructor could not have been used to 
  construct a value with a particular index. In the case of inductive descriptions, we 
  find out this fact relatively early, since the set of available operations 
  explicitly depends on the index, so this set will never include descriptions that 
  could not have been used in the first place. Contrary, when using a description that 
  explicitly includes constraints, we only find that a particular constructor could 
  not have been used when we fail to synthesize the required equality proof. In the 
  end this means that the choice of descriptions style comes down to a tradeof between 
  brevity and efficiency. Throughout the remainder of this thesis, we will stick with 
  the inductive style of defining descriptions. 

\section{Deriving generators}

  The process of deriving a generator for indexed descriptions is mostly the same as 
  for regular types. There are a few subtle differences, which we will outline in this 
  section. We define a function \agda{IDesc-gen} that derives a generator from an indexed 
  description. Let us first look at its type signature: 

\includeagda{7}{idescgen}

  We take a value of type \agda{IDesc I} (the description we are inducting over) and a 
  function \agda{I → IDesc I} (describing the type for which we are deriving a generator) 
  as input. We return an \emph{indexed} generator, which produces values of the type 
  dictated by the semantics of the input description. We build this generator by 
  defining it for the various constructors of the \agda{IDesc} type. 

\subsection{Unit, product and recursive positions}
  
  The definition for \agda{`var}, \agda{`1} and \agda{`×} can be readily transferred from the 
  definition of \agda{deriveGen}. Their definition is included below: 

\includeagda{7}{idescgentrivial}
  
\subsection{Generalized coproduct}

  The generic generators for the generalized coproduct are slightly more involved, since we have to return a generator that produces dependent pairs. This is tricky, because the applicative combinators are not expressive enough to capture the dependency between the generated \emph{value} of the first element, and the \emph{type} of the second element. This means that we have to utilize the monadic structure of the generator type in order to be able to capture this dependency. 

\includeagda{7}{idescgencop}

  Here we assume that \agda{Sl-gen : (n : ℕ) → Genᵢ (Sl n) Sl n} is in scope, producing 
  values of the selector type. We capture the dependency between the generated first 
  element of the pair, and the type of the second element using the monadic bind of 
  the generator type, similar to when we were defining a generator for the universe of 
  indexed containers. The definition is pretty straightforward, although we need to 
  pass around some metavariables in order to convince Agda that everything is in 
  order. 

\subsection{Dependent pairs}

  We can reuse this exact same structure when defining a generator for \agda{`Σ}, 
  however since the type of its first element is chosen by the user, we cannot define 
  a generator for it in adavance, as we did for the selector type. We use the same 
  approach using a metadata structure as for regular types to have the programmer pass 
  appropriate generators as input to \agda{IDesc-gen}. We define this metadata structure as 
  a datatype \agda{data IDescM {I} (P : Set → Set) : IDesc I → Set}. Its constructors are 
  largely equivalent to the metadata structure used for regular types (\cref
  {sec:genericgenreg}), with the key difference being that we now require the 
  programmer to store a piece of data depending on the type of the first element of a \agda{`Σ}:

\includeagda{7}{idescmsigma}

  The constructor of the \agda{IDescM} type associated with the generalized coproduct 
  follows the same structure as \agda{`Σ$sim$}, but without a value argument, and with \agda{S} 
  instantiated to the selector type. 

  If we now assume that \agda{IDesc-gen} is parameterized over a metadata structure 
  containing generators for the first argument of the \agda{`Σ} constructor, we can 
  define a generator for its interpretation: 

\includeagda{7}{idescgensigma}

  By using an instance of \agda{Describe}, we may use the isomorphism stored within to 
  convert the values generated by \agda{IDesc-gen} to the type we are describing. 
 
\subsection{Example: deriving a generator for well-typed lambda terms}

  Let us look at an example in which we use \agda{deriveGen} to derive a generator in order 
  to get a feel for how the generic mechanism defined in this section works out when 
  we actually try to use it. We will use the inductive description of well-typed terms 
  to derive a generator from. 

  Looking at the description, we see that we use the \agda{`Σ} combinator to build 
  dependent pairs that have either a proof that some \agda{τ} is an element of a context 
  \agda{Γ}, or a type as their first element. This means that we require generators 
  that produce elements of type \agda{Γ ∋ τ } and \agda{Ty}: 

\includeagda{7}{genelem}

  How we obtain these generators is entirely up to us. We can use any of the generic 
  derivation mechanisms described throughout this thesis, or manually define them 
  according to our needs. The latter has the advantage that it lets us guide the 
  generation process somewhat. In the case of lambda terms, we need to choose a new 
  type $\sigma$ when using the application rule. It might be beneficial to, for 
  example, write a generator that will first produce a list of types that can be found 
  in the context, and only later will exhaustively enumerate the space of all types. 

  Given that the required generators are in scope, we define a metadata structure 
  indexed by the inductive description of well-typed lambda terms, shown in listing 
  \ref{lst:wtmeta}. The structure of this metadata structure is entirely dependent on 
  how we defined the description in the first place. We only really have a choice for 
  the first element of \agda{`Σ$sim$}. 

\includeagdalisting{7}{wtmeta}{Metadata structure for the inductive description of 
well-type lambda terms}{lst:wtmeta}

  The metadata structure for well-typed terms quite neatly demonstrates how our 
  approach separates the parts of generation that can be done mechanically from the 
  parts for which a little help from the programmer is required. Furthermore, after 
  creating this separation we leave the programmer with complete freedom over how they 
  provide the necessary generator, allowing them to choose whatever approach best 
  suits their needs. 

\section{Proving completeness}

  We aim to prove the same completeness property for generators derived from indexed 
  descriptions as we did for generators derived from regular types. Since both 
  universes and the functions that we use to derive generators from their inhabitants 
  share quite a few structural similarities, so do their respective completeness 
  proofs. This means that we can recycle a considerable portion of the completeness 
  proof that we wrote for regular types. 

  Let us first look at the exact property we aim to prove. Since we deal with indexed 
  generators, the desired completeness property changes slightly. In natural language, 
  we might say that our goal is to prove that \emph{for every index \agda{i} and value \agda{x} 
  of type \agda{P i}, there is a depth such that \agda{x} occurs in the enumeration we derive 
  from the code describing \agda{P}}. In Agda we formalize this property as follows: 

\includeagda{7}{completeness}

  Which is essentially the same property we used for regular types, adapted for usage 
  with indexed types. To be able to inductively define the completeness proof, we use 
  a slight variation on this property that distinguishes between the generator we are 
  inducting over, and the generator describing recursive positions: 

\includeagda{7}{productivity}

  In general, the second property is equivalent to the first if the two supplied 
  generators are the same. We then define the following completeness lemma for the 
  generators derived from indexed descriptions: 

\includeagda{7}{idesccompletetype}

  We will show how to define a proof for this lemma by considering the various 
  constructors of the \agda{IDesc} type. 

\subsection{Unit, product and recursive positions}

  The completeness proofs for \agda{`var}, \agda{`1} and \agda{`×} can again be transplanted almost 
  without changes from the proof for regular types:  

\includeagda{7}{idesccompletetrivial}

  Where we assume that a proofs of the following lemmas is in scope: 

\includeagda{7}{incompletetype}

  We will not go into how we can prove these lemmas, as we already discussed this when 
  describing the completeness proof for regular types. 
  
\subsection{Generalized coproducts and dependent pairs}
  
\includeagdalisting{7}{bindcomplete}{Completeness for the bind operator}
{lst:bindcomplete}

  Since the generators for \agda{`Σ} and \agda{`σ} are assembled using \emph{monadic 
  bind}, we need to prove that this operation is completeness preserving. Defining 
  what completeness even means for \agda{>>=} is very difficult in itself, but since both 
  usages in \agda{IDesc-gen} follow the same structure, we can get away with proving a 
  completeness property over our specific use of the bind operator. The lemma we use 
  is shown in listing \ref{lst:bindcomplete}. 

  With this lemma, and an appropriate metadata parameter supplied to our completeness 
  proof, we can fill in the cases for the generalized coproduct and dependent pairs, 
  assuming that a completeness proof for the generator producing values of the 
  selector type is in scope. 

\subsection{Wrapping up the proof}

  It is worth noting that, since the universe of indexed descriptions exposes a 
  product combinator, we require a proof of \emph{monotonicity} for generators derived 
  using \agda{IDesc-gen} as well. We will not go into how to assemble this proof here 
  (since its structure is essentially the same as the monotonicity proof for regular 
  types), but it is obviously not possible to assemble this proof without proving the 
  monotonicity property over our bind operation first. 

\section*{Conclusion}

  In this chapter, we have shown how we can extend the generic derivation mechanism we 
  used for regular types and indexed containers can be extended to a more expressive 
  universe that is able to represent arbitrary indexed families. Furthermore, we have 
  proved that the generators we derive from codes in this universe satisfy our 
  completeness property. We demonstrated that this generic approach is powerful enough 
  to generate well-typed lambda terms, relying on the programmer to supply guidance 
  for those parts of the datatype that are too difficult to handle generically. 

  Given the fact that we have developed a mechanism to find inhabitants of arbitrary 
  indexed families, we may view this result though the Curry-Howard correspondence, 
  which implies that we have simultaneously obtained a mechanism is able to synthesize 
  proofs of propositions in arbitrary formal systems. If we place our work in the 
  context of proof search, we find that we can alternatively view our work as an 
  implementation of \emph{backward-chaining proof search} \cite{miller1991uniform} 
  parameterized over a formal system and whose proofs are correct by construction, 
  enforced by Agda's type system. In this context, our completeness property implies 
  that, if we enumerate these proofs, we will eventually find \emph{all} proofs of a 
  property, given enough time and memory. Consequently, if a theorem has a proof in a 
  given formal system, we are guaranteed to find one in finite time. It is important 
  to recognize that, although our approach offers a great deal of flexibility, it is 
  not very efficient. Eventually, we exhaustively enumerate all possible proof chains 
  that could have led to our goal type, meaning that the practical applications of 
  this work are most likely limited until we further optimizations have been 
  implemented. 