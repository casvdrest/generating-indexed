
We use the generic description for indexed datatypes proposed by Dagand \cite{dagand2013cosmology} in his PhD thesis. First, we give the definition and semantics of this universe, before showing how a generator can be derived from codes in this universe. Finally, we prove that the enumerations resulting from these generators are complete. 

\section{Universe Description}

  

\subsection{Definition}\label{sec:idescdef}

  Indexed descriptions are not much unlike the codes used to describe regular types (that is, the |Reg| datatype), with the differences being: 

\begin{enumerate}
  \item 
  A type parameter |I : Set|, describing the type of indices.

  \item 
  A generalized coproduct, |`|$\sigma$, that denotes choice between $n$ constructors, in favor of the |⊕| combinator. 

  \item 
  A combinator denoting dependent pairs. 

  \item 
  Recursive positions storing the index of recursive values. 
\end{enumerate}

  This amounts to the Agda datatype describing indexed descriptions shown in listing \ref{lst:idesc}. 

\includeagdalisting{7}{idesc}{The Universe of indexed descriptions}{lst:idesc}

  Notice how we retain the regular product of codes as a first order construct in our universe. The |Sl| datatype is used to select the right branch from the generic coproduct, and is isomorphic to the |Fin| datatype. 

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

\subsection{Exmample: describing well typed lambda terms}

  To demonstrate the expressiveness of the |IDesc| universe, and to show how one might model a more complex datatype, we consider simply typed lambda terms as an example. We assume raw terms as described in listing \ref{lst:defrawterm}. We type terms using the universe described in listing \ref{lst:defstype}. 

\subsubsection{Modelling SLC in Agda}

  We write $\Gamma \ni \alpha : \tau$ to signify that $\alpha$ has type $\tau$ in $\Gamma$. Context membership is described by the following inference rules: 

\begin{equation*}
\texttt{[Top]}
  \frac{}{\Gamma , \alpha : \tau \ni \alpha : \tau} \quad 
\texttt{[Pop]}
  \frac{\Gamma \ni \alpha : \tau}{\Gamma , \beta : \sigma \ni \alpha : \tau}
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

  We model these inference rules in Agda using a two way relation between contexts and types whose inhabitants correspond to all terms that have a given type under a given context (listing \ref{lst:wflambda})

\includeagdalisting{7}{typejudgement}{Well-typed lambda terms as a two way relation}{lst:wflambda}

  Given an inhabitant $\Gamma$ |⊢| $\tau$ of this relationship, we can write a function |toTerm| that transforms the typing judgement to its corresponding untyped term. 

\includeagda{7}{toterm}

  The term returned by |toTerm| will has type $\tau$ under context $\Gamma$. 

\subsubsection{Describing well typed terms}

  In \cref{sec:idescdef}, we saw that we can describe the |Fin| both by induction on the index, as well as by adding explicit constraints. Similarly, we can choose to define a description in two ways: either by induction on the type of the terms we are describing, or by including an explicit constraint that the index type is a function type for the description of the abstraction rule. If we consider a description for lambda terms using induction on the index (listing \ref{slcdescinductive}), we see that it has a downside. The same constructor may yield a value with different index patterns. 

\includeagdalisting{7}{slcdescinductive}{A description for well typed terms using induction on the index type}{lst:slcdescinductive}

  For example, the application rule may yield both a function type as well as a ground type, we need to include a description for this constructor in both branches when pattern matching on the input type. If we compare the inductive description to a version that explicitly includes a constraint that the input type is a function type in case of the description for the abstraction rule, we end up with a much more succinct description. 

  However, using such a description comes at a price. The descriptions used will become more complex, hence their interpretation will too. Additionally, we delay the point at which it becomes apparent that a constructor could not have been used to create a value with the input index. This makes the generators for indexed descriptions, which we will derive in the next section, potentially more computationally intensive to run when derived from a description that uses explicit constraints, compared to an equivalent description that is defined by induction on the index. 

\includeagdalisting{7}{slcdescconstrained}{A description for well typed terms using explicit constraints}{lst:slcdescconstrained} 

  To convince ourselves that these descriptions do indeed describe the same type, we can show that their fixpoints are isomorphic: 

\includeagda{7}{desciso}

  Given an isomorphism between the fixpoints of two descriptions, we can prove that they are both isomorphic to the target type by establishing an isomorphism between the fixpoint of one of them and the type we are describing. For example, we might prove the following isomorphism: 

\includeagda{7}{constrainediso}

  Using the transitivity of |_≃_|, we can show that the inductive description also describes well typed terms. 

\section{Generic Generators for Indexed Descriptions}



\section{Completeness Proof for Generators Derived From Indexed Descriptions}