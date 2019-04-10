
\section{Testing Fonts}
\label{sec:testing}

\subsection{Code Blocks}

  Below is the factorial function written in Haskell~\cite{ghcUsersGuide} and a paragraph of lorem ipsum:

\begin{code}
fat :: Int -> Int
fat 0  = 1
fat n  = n * fat (n-1)

class SomeClass2 r where
  method :: forall x . MyMethodType x -> r
\end{code}

\lipsum[1]

\subsection{Math Fonts}

  Below is some math to display our math font:
\begin{align}
CIF: \hspace*{5mm}F_0^j(a) = \frac{1}{2\pi \iota} \oint_{\gamma} \frac{F_0^j(z)}{z - a} dz
\label{eq:ref}
\end{align}

  And we will even reference \Cref{eq:ref} and \Cref{eq:euler} to see
how references and figures look like. For the sake of testing \Cref{sec:testing}.

\begin{figure}
\begin{equation*}
e^{i*\pi} + 1 \equiv 0
\end{equation*}
\caption{Euler's Equation}
\label{eq:euler}
\end{figure}

\subsection{Latex Font Face}

\begin{table}\centering
\begin{tabular}{@@{}lll@@{}}\toprule
             & Plain Text                  & With Faces           \\ \midrule
  bold face  & Stay bold, pony boy!        & \textbf{Stay bold, pony boy!} \\
  italic     & Just like the tower of piza & \textit{Just like the tower of piza} \\
  small caps & This is In Camel Case       & \textsc{This Is In Camel Case}  \\
  typewriter & Some text here              & \texttt{Some text here} \\
\bottomrule
\end{tabular}
\caption{Some Table}
\end{table}

\paragraph{Combos} 
  \begin{enumerate}
    \item \textbf{\textit{Boldface and italic}}
    \item \textbf{\texttt{Boldface and typewriter}}
  \end{enumerate}

\section{Testing Page Layouts}

\lipsum[1-10]