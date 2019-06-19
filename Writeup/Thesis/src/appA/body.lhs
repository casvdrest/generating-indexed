
\section{Natural numbers}

\begin{listing}{Definition of natural numbers in Haskell and Agda}{lst:defnat}

  \begin{code}
    data Nat  =  Zero 
              |  Suc N
  \end{code}

  \dotfill

  \appincludeagda{A}{nat}

\end{listing}

\section{Finite Sets}

\begin{listing}{Definition of finite sets in Agda}{lst:deffin}

  \appincludeagda{A}{fin}

\end{listing}
\newpage
\section{Vectors}

\begin{listing}{Definition of vectors (size-indexed listst) in Agda}{lst:defvec}

  \appincludeagda{A}{vec}

\end{listing}

\section{Simple Types}

\begin{listing}{Definition of simple types in Haskell and Agda}{lst:defstype}

  \begin{code}
  data Type  =  T 
             |  Type :->: Type 
  \end{code}

  \dotfill

  \appincludeagda{A}{simpletypes}

\end{listing}

\section{Contexts}

\begin{listing}{Definition of contexts in Haskell and Agda}{lst:defcontext}

  \begin{code}
  data Ctx  =  Empty 
            |  Cons Id Type Ctx
  \end{code}

  \dotfill

  \appincludeagda{A}{context}

\end{listing}
\newpage
\section{Raw Lambda Terms}

\begin{listing}{Definition of raw lambda terms in Haskell and Agda}{lst:defrawterm}

  \begin{code}
  data RT  =  Var Id 
           |  Abs Id RT 
           |  App RT RT
  \end{code}

  \dotfill

  \appincludeagda{A}{rawterm}

\end{listing}

\section{Lists}

\begin{listing}{Definition lists and Agda}{lst:deflist}

  \appincludeagda{A}{list}

\end{listing}

\section{Well-scoped Lambda Terms}

\begin{listing}{Definition well-scoped lambda terms in Agda}{lst:defwellscoped}

  \appincludeagda{A}{wellscoped}

\end{listing}