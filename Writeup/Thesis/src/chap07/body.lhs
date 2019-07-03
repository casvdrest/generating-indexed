
We use the generic description for indexed datatypes proposed by Dagand \cite{dagand2013cosmology} in his PhD thesis. First, we give the definition and semantics of this universe, before showing how a generator can be derived from codes in this universe. Finally, we prove that the enumerations resulting from these generators are complete. 

\section{Universe Description}\label{sec:idescdesc}

\subsection{Definition}\label{sec:idescdef}

  Indexed descriptions are not much unlike the codes used to describe regular types (that is, the |Reg| datatype), with the differences being: 

\begin{enumerate}
  \item 
  A type parameter |I : Set|, describing the type of indices.

  \item 
  A generalized coproduct, |`|$\sigma$, that denotes choice between $n$ constructors, in favor of the |⊕| combinator. 

  \item 
  A combinator, |`|$\Sigma$, denoting dependent pairs. 

  \item 
  Recursive positions, |`var|, storing the index of recursive values. 
\end{enumerate}

  This amounts to the Agda datatype describing indexed descriptions shown in listing \ref{lst:idesc}. 

\includeagdalisting{7}{idesc}{The Universe of indexed descriptions}{lst:idesc}

  Notice how we retain the regular product of codes as a first-order construct in our universe. The |Sl| datatype is used to select the right branch from the generic coproduct, and is isomorphic to the |Fin| datatype. 

\includeagda{7}{sl}

  The semantics associated with the |IDesc| universe is largely the same as the semantics of the universe of regular types. The key difference is that we do not map codes to a functor |Set → Set|, but rather to |IDesc I → (I → Set) → Set|. The semantics is shown in listing \ref{lst:idescsem}.

\includeagdalisting{7}{idescsem}{Semantics of the IDesc universe}{lst:idescsem}

  We do not require a separate constructor representing the empty type, as we can encode it as a coproduct over zero constructors: |`|$\sigma$ |0| $\lambda$ |()|. 

  We calculate the fixpoint of interpreted codes using the following fixpoint combinator: 

\includeagda{7}{idescfix}

  \begin{example}
    We can describe the |Fin| datatype, listing \ref{lst:deffin}, as follows using a code in the universe of indexed descriptions: 

\includeagdanv{7}{idescfin}

    If the index is |zero|, there are no inhabitants, so we return a coproduct of zero choices. Otherwise, we may choose between two constructors: |zero| or |suc|. Notice that we describe the datatype by induction on the index type. This is not required, althoug convenient in this case. A different, but equally valid description exists, in which we use the |`|$\Sigma$ constructor to explicitly enforce the constraint that the index |n| is the successor of some |n'|. 
    
\includeagdanv{7}{idescfin2}
    
    Listing \ref{lst:finiso} establishes that the fixpoint of |finD| is indeed isomorphic to |Fin|. 

  \end{example}

\includeagdalisting{7}{idescfiniso}{Isomorphism between |Fix finD| and |Fin|}{lst:finiso}

  We generalize the notion of datatypes that can be described in the universe of indexed descriptions by again constructing a record that stores a description and a proof that said description is isomorphic to the type we are describing: 

\includeagda{7}{describe}

\subsection{Exmample: describing well typed lambda terms}

  To demonstrate the expressiveness of the |IDesc| universe, and to show how one might model a more complex datatype, we consider simply typed lambda terms as an example. We model the simply typed lambda calculus in Agda according to the representation used in Philip Wadler and Wen Kokke's PLFA \cite{wadler2019plfa}. 

\subsubsection{Modelling SLC in Agda}

  Wadler and Kokke use a representation using De Bruijn indices \cite{de1972lambda}, which represents variables as a natural denoting the number of lambda abstractions between the variable and the binder it refers to. Using De Bruijn indices has the clear advantage that $\alpha$-equivalent terms have the same representation. Listing \ref{lst:lambdadatatypes} contains the datatype definitions for raw terms, types and contexts. Raw terms represent untyped lambda terms. Types can be either the ground type |`|$\tau$, or a function type $sigma$|`->|$\tau$. Since we are using De Bruijn indices, we do not need to store variable names in the context, only types. Hence the |Ctx| type is isomorphic to |List Ty|. 

\includeagdalisting{7}{lambdadatatypes}{Datatypes for raw terms, types and contexts}{lst:lambdadatatypes}

  We write $\Gamma \ni \tau$ to signify that a variable with type $\tau$ is bound in context $\Gamma$. Context membership is described by the following inference rules: 

\begin{equation*}
\texttt{[Top]}
  \frac{}{\Gamma , \tau \ni \alpha : \tau} \quad 
\texttt{[Pop]}
  \frac{\Gamma \ni \tau}{\Gamma , \sigma \ni \alpha : \tau}
\end{equation*}

  We describe these inference rules in Agda using an inductive datatype, shown in listing \ref{lst:ctxmem}, indexed with a type and a context, whose inhabitants correspond to all proofs that a context $\Gamma$ contains a variable of type $\tau$. 

\includeagdalisting{7}{ctxmembership}{Context membership in Agda}{lst:ctxmem}

  We write $\Gamma \vdash t : \tau$ to express a typing judgement stating that term $t$ has type $\tau$ when evaluated under context $\Gamma$. The following inference rules determine when a term is type correct: 

\begin{equation*}
\texttt{[Var]}
  \frac{\Gamma \ni \alpha : \tau}{\Gamma \vdash \alpha : \tau} \quad 
\texttt{[Abs]}
  \frac{\Gamma , \alpha : \sigma \vdash t : \tau}{\Gamma \vdash \lambda\ \alpha\ .\ t : \sigma \rightarrow \tau} \quad
\texttt{[App]}
  \frac{\Gamma \vdash t1 : \sigma \rightarrow \tau \quad \Gamma \vdash t2 : \sigma}{\Gamma \vdash t_1\ t_2 : \tau}
\end{equation*} 

  We model these inference rules in Agda using a binary relation between contexts and types whose inhabitants correspond to all terms that have a given type under a given context (listing \ref{lst:wflambda})

\includeagdalisting{7}{typejudgement}{Well-typed lambda terms as a binary relation}{lst:wflambda}

  Given an inhabitant $\Gamma$ |⊢| $\tau$ of this relationship, we can write a function |toTerm| that transforms the typing judgement to its corresponding untyped term, which simply \emph{erases} the indices of a proof $\Gamma \vdash \tau$ to obtain an untyped term. 

\includeagda{7}{toterm}

  The term returned by |toTerm| will has type $\tau$ under context $\Gamma$. 

\subsubsection{Describing well typed terms}

  In \cref{sec:idescdef}, we saw that we can describe the |Fin| both by induction on the index, as well as by adding explicit constraints. Similarly, we can choose to define a description for well-typed terms in two ways: either by induction on the type of the terms we are describing, or by including an explicit constraint that the index type is a function type for the description of the abstraction rule. In either case, we start by defining descriptions for each of the three possible constructors (listing \ref{lst:sltcconstructordesc}). 

\includeagdalisting{7}{sltcconstructordesc}{Descriptions for the constructors of the simply typed lambda calculus}{lst:sltcconstructordesc}

  Given the descriptions for the individual constructors, we can assemble a description for the entire datatype by pattern matchin on the index type, and returning for each branch a coproduct of the descriptions of all constructors that could have been used to create a value with that particular index (listing \ref{lst:slcdescinductive}). 

\includeagdalisting{7}{slcdescinductive}{Inductive description of the simply typed lambda calculus}{lst:slcdescinductive}

  Alternatively, we can describe the simply typed lambda calculus as a coproduct of the descriptions of all its constructors, and adding an explicit constraint in the case of the abstraction rule that requires a proof that the index type is a function type (listing \ref{lst:slcdescconstrained}). 
  
\includeagdalisting{7}{slcdescconstrained}{Description of the simply typed lambda calculus with explicit constraints}{lst:slcdescconstrained}
  
  To convince ourselves that these descriptions do indeed describe the same type, we can show that their fixpoints are isomorphic: 

\includeagda{7}{desciso}

  Given an isomorphism between the fixpoints of two descriptions, we can prove that they are both isomorphic to the target type by establishing an isomorphism between the fixpoint of one of them and the type we are describing. For example, we might prove the following isomorphism: 

\includeagda{7}{constrainediso}

  Using the transitivity of |_≃_|, we can show that the inductive description also describes well typed terms. 

  Both variations are equally valid descriptions of the simply typed lambda calculus (they are isomorphic), but depending on the situation one might prefer one over the other. A downside to defining descriptions by induction over the index type is that we often end up with at least some code duplication, making them unnecessarily verbose. Descriptions with explicit constraints do not have this downside. We could even substitute |varDesc|, |absDesc| and |appDesc| for their respective definitions, since they are only referred to once. This often results in descriptions that are much more succinct, but arguably less straightforward. 

  When looking ahead to the derivation of generators from descriptions, we see that using a description with explicit constraints has the side effect that we delay the point at which we find out that a certain constructor could not have been used to construct a value with a particular index. In the case of inductive descriptions, we find out this fact relatively early, since the set of available operations explicitly depends on the index, so this set will never include descriptions that could not have been used in the first place. Contrary, when using a description that explicitly includes constraints, we only find that a particular constructor could not have been used when we fail to synthesize the required equality proof. In the end this means that the choice of descriptions style comes down to a tradeof between brevity and efficiency. Throughout the remainder of this thesis, we will stick with the inductive style of defining descriptions. 

\section{Generic Generators for Indexed Descriptions}

  The process of deriving a generator for indexed descriptions is mostly the same as for regular types. There are a few subtle differences, which we will outline in this section. We define a function |IDesc-gen| that derives a generator from an indexed description. Let us first look at its type signature: 

\includeagda{7}{idescgen}

  We take a value of type |IDesc I| (the description we are inducting over) and a function |I -> IDesc I| (describing the type for which we are deriving a generator) as input. We return an \emph{indexed} generator, which produces values of the type dictated by the semantics of the input description. The definition for |`var|, |`1| and |`×| can be readily transferred from the definition of |deriveGen|. The generic generators for the generalized coproduct and the |`Sigma| constructor are slightly more involved, since the both have to produce dependent pairs. Since the generalized coproduct is a particular instantiation of |`Sigma|, we will consider it first. 

\includeagda{7}{idescgencop}

  Here we assume that |Sl|-|gen : (n : ℕ) → Genᵢ (Sl n) Sl n| is in scope, producing values of the selector type. We capture the dependency between the generated first element of the pair, and the type of the second element using the monadic bind of the generator type, similar to when we were defining a generator for the universe of indexed containers. The definition is pretty straightforward, although we need to pass around some metavariables in order to convince Agda that everything is in order. 

  We can reuse this exact same structure when defining a generator for |`Sigma|, however since the type of its first element is chosen by the user, we cannot define a generator for it in adavance, as we did for the selector type. We use the same approach using a metadata structure as for regular types to have the programmer pass appropriate generators as input to |IDesc-gen|. We define this metadata structure as a datatype |data IDescM {I} (P : Set → Set) : IDesc I → Set|. Its constructors are largely equivalent to the metadata structure used for regular types (\cref{sec:genericgenreg}), with the key difference being that we now require the programmer to store a piece of data depending on the type of the first element of a |`Sigma|: 

\includeagda{7}{idescmsigma}

  The constructor of the |IDescM| type associated with the generalized coproduct follows the same structure as |`Sigma~|, but without a value argument, and with |S| instantiated to the selector type. 

  If we now assume that |IDesc-gen| is parameterized over a metadata structure containing generators for the first argument of the |`Sigma| constructor, we can define a generator for its interpretation: 

\includeagda{7}{idescgensigma}

  By using an instance of |Describe|, we may use the isomorphism stored within to convert the values generated by |IDesc-gen| to the type we are describing. 
 
\section{Completeness Proof for Enumerators Derived From Indexed Descriptions}

  We aim to prove the same completeness property for generators derived from indexed descriptions as we did for generators derived from regular types. Since both universes and the functions that we use to derive generators from their inhabitants are structurally quite similar, so are their completeness proofs. This means that we can recycle a considerable portion of the proof for regular types. 

  Let us first look at the exact property we aim to prove. Since we deal with indexed generators, the desired completeness property changes slightly. In natural language, we might say that our goal is to prove that \emph{for every index |i| and value |x| of type |P i|, there is a depth such that |x| occurs in the enumeration we derive from the code describing |P|}. In Agda we formalize this property as follows: 

\includeagda{7}{completeness}

  Which is essentially the same property we used for regular types, adapted for usage with indexed types. The completeness proofs for |`var|, |`1| and |`×| can be transplanted from the proof for regular types with only a few minor changes. However, generators for |`sigma| and |`Sigma| are assembled using \emph{monadic bind}, for which we have not yet proven that it satisfies our notion of completeness. Defining what completeness even means for |>>=| is very difficult in itself, but luckily since both usages in |IDesc-gen| follow the same structure, we only have to prove a completeness property over our specific use of the bind operator. We replace |Complete| with a slight variation that makes the value |x| we are quantifying over explicit in the type. 

\includeagdalisting{7}{bindcomplete}{Completeness for the bind operator}{lst:bindcomplete}

   Given that the proof is supplied with a metadata structure that provides generators with completeness proofs for all |`Sigma| in a description, and that we have a completeness proof over the generator for the selection type in scope, we can complete the proof for the case of |`sigma| and |`Sigma| with a call to |bind-Complete|. 

  It is worth noting that, since the universe of indexed descriptions exposes a product combinator, we require a proof of \emph{monotonicity} for generators derived using |IDesc-gen| as well. We will not go into how to assemble this proof here (since its structure is essentially the same as the monotonicity proof for regular types), but it is obviously not possible to assemble this proof without proving the monotonicity property over our bind operation first. 

