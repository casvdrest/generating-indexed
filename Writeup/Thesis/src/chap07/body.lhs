\section{Universe Description}

  We utilize the generic description for indexed datatypes proposed by Dagand \cite{dagand2013cosmology} in his PhD thesis.

\subsection{Definition}

  Indexed descriptions are not much unlike the codes used to describe regular types (that is, the |Reg| datatype), with the differences being: 

\begin{enumerate}
  \item 
  A type parameter |I : Set|, describing the type of indices.

  \item 
  A generalized coproduct, |`|$\sigma$, that denotes choice between $n$ constructors, in favor of the |⊕| combinator. 

  \item 
  Recursive positions storing the index of recursive values

  \item 
  Addition of a combinator to encode $\Sigma$ types which is a generalization of the |K| combinator. 
\end{enumerate}

  This amounts to the definition of indexed descriptions described in listing \ref{lst:idesc}. 

\includeagdalisting{7}{idesc}{The Universe of indexed descriptions}{lst:idesc}\

The |Sl| datatype is used to select the right branch from the generic coproduct, and is isomorphic to the |Fin| datatype. 

\includeagda{7}{sl}

\subsection{Examples}

\section{Generic Generators for Indexed Descriptions}