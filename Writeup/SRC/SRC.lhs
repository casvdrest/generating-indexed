\documentclass[acmsmall, nonacm]{acmart}

\settopmatter{printacmref=false} % Removes citation information below abstract
\renewcommand\footnotetextcopyrightpermission[1]{} % removes footnote with conference information in first column
\pagestyle{plain} % removes running headers

%include polycode.fmt
%include greek.fmt
%include colorcode.fmt
%include hsformat.lhs

% \usepackage{xcolor}
\usepackage{multicol}
\newcommand\todo[1]{\textcolor{red}{\textbf{TODO:} #1}}

\usepackage{textcomp}

\DeclareUnicodeCharacter{10218}{$\langle\langle$}
\DeclareUnicodeCharacter{10219}{$\rangle\rangle$}
\DeclareUnicodeCharacter{7522}{\textsubscript{i}}
\DeclareUnicodeCharacter{7524}{\textsubscript{u}}
\DeclareUnicodeCharacter{8336}{\textsubscript{a}}
\DeclareUnicodeCharacter{8346}{\textsubscript{p}}
\DeclareUnicodeCharacter{10631}{$\llparenthesis$}
\DeclareUnicodeCharacter{10632}{$\rrparenthesis$}
\DeclareUnicodeCharacter{10627}{\{\!\{}
\DeclareUnicodeCharacter{10628}{\}\!\}}
\DeclareUnicodeCharacter{9656}{$\blacktriangleright$}
\DeclareUnicodeCharacter{9667}{$\triangleleft$}
\DeclareUnicodeCharacter{8347}{\textsubscript{s}}
\DeclareUnicodeCharacter{2200}{\ensuremath{\forall}}
\DeclareUnicodeCharacter{220B}{\ensuremath{\ni}}
\DeclareUnicodeCharacter{22A2}{\ensuremath{\vdash}}

\usepackage[font=small,labelfont=bf]{caption}

\usepackage{textgreek}

% Math
\usepackage{amssymb}
\usepackage{mathtools}
% Tables
\usepackage{amsmath}

% Colors
%% \usepackage{xcolor, color, colortbl}
%% \colorlet{gray}{gray!70}
%% \colorlet{green}{green!50}
%% \definecolor{darkblue}{HTML}{1D577A}
%% \definecolor{rred}{HTML}{C03425}
%% \definecolor{darkgreen}{HTML}{8BB523}
%% \definecolor{ppurple}{HTML}{6B1B7F}
%% \definecolor{pblack}{HTML}{000000}
%% \definecolor{darkyellow}{HTML}{C0B225}

% Links
\usepackage{hyperref}
\definecolor{linkcolour}{rgb}{0,0.2,0.6}
\hypersetup{colorlinks,breaklinks,urlcolor=linkcolour,linkcolor=linkcolour,citecolor=blue}

\setlength\mathindent{0.6cm}

\title{Synthesizing Well-Formed Programs using Datatype Generic Programming}

\author{Cas van der Rest}
\email{c.r.vanderrest@@students.uu.nl}
\affiliation{
\institution{Utrecht University}
\country{The Netherlands}
}

\begin{abstract}
\textbf{Advisor:} Wouter Swierstra 
\textbf{Category:} Graduate (Master)
\textbf{ACM student member number:} 2709516
\end{abstract}

\begin{document}

\maketitle

  \section*{Introduction}

  Test programs are invaluable when testing a compiler. However, synthesizing constrained test data such as well-formed programs is a difficult problem, which has been the subject of extensive research. For example: Claessen and Duregaard \cite{claessen2015generating} generate constrained data using an iterative process in which they refine the search space in each step. Lampropoulos et al. define an abstraction over inductive relations in Coq, and describe how generators may be defined for these abstractions. They create an extension to QuickChick \cite{denes2014quickchick} implementing these ideas. Pa{\l}ka et al. \cite{palka2011testing} generate well-typed lambda terms by reverse engineering a proof tree, given a goal type and context.

  We take a novel approach by considering the more general problem of synthesizing values of \emph{arbitrary indexed datatypes}, and generating values that inhabit indexed datatypes describing well-formedness. We use Dagand's universe of \emph{Indexed Descriptions} \cite{dagand2013cosmology} to represent indexed datatypes in a generic fashion. Given a description in this universe, we can derive a generator that produces values isomorphic to the type it represents. We have constructed a Haskell Library that implements this approach, where the user only needs to supply a description of a type describing well-formedness, and a conversion function that transforms generated values into the desired non-indexed datatype. We show how well-typed lambda terms can be generated using this technique. Additionally, we assert correctness of our work through a formalization in Agda. Both are available on Github \cite{github}.

  \vspace{-0.1cm}
  \section*{The universe of indexed descriptions}

  \emph{Indexed descriptions} \cite{dagand2013cosmology} are perhaps best viewed as an extension to the universe of regular types. The key modifications include: 

  \begin{itemize}
    \item 
      Types are described by a function |I -> Description|, mapping indices to descriptions.

    \item 
      Recursive positions store the index of the recursive subtree at that position.

    \item 
      An extra constructor |Sigma : (S : *) -> (S -> Description) -> Description| is added. The interpretation of |Sigma S P| is a \emph{dependent pair} with type |((s : S) , interpret . P)|. 
  \end{itemize}

   We describe indexed descriptions using a GADT \cite{hinze2003fun} with two type parameters: one denoting the associated non-indexed datatype, and the other the index type. The constructors for unit types, empty types, recursive positions, products and coproducts closely follow the definition of regular types, with the exception of |Var|, which stores an index value.

\begin{code}
 data IDesc (a :: *) (i :: *) where
    One    ::                             IDesc a i
    Empty  ::                             IDesc a i
    Var    :: i                       ->  IDesc a i
    (:*:)  :: IDesc a i -> IDesc a i  ->  IDesc a i
    (:+:)  :: IDesc a i -> IDesc a i  ->  IDesc a i
\end{code}

  We can then define a \emph{type family} |Interpret (d :: IDesc a i) :: *| that describes the semantics of a description. |E| is a datatype with no constructors representing the \emph{empty type} ($\bot$).

\begin{code}
type instance Interpret One                   = ()
type instance Interpret Empty                 = E
type instance Interpret (Var _ :: IDesc a i)  = a
type instance Interpret (dl :*: dr)           = (Interpret dl , Interpret dr)
type instance Interpret (dl :+: dr)           = Either (Interpret dl) (Interpret dr)         
\end{code}

  Dagand originally defines this universe in a dependently typed setting. Since we choose to use Haskell for our implementation, we need to adapt the original definition slightly, choosing a more restrictive form of the |Sigma| constructor. We do this based on the observation that in most practical use cases of |Sigma|, only the indices of recursive positions depend on the choice for the first element. Since the interpretation of |Var| is independent of the recursive index stored, so is the interpretation of the entire description. Consequently, we can describe this class of functions using a single description with a function |s -> i| as its index type:

\begin{code}
Sigma :: Proxy s -> IDesc a (s -> i) -> IDesc a i
\end{code}

  This allows us to interpret a |Sigma| as a regular pair, instead of a dependent pair. 

\begin{code}
type instance Interpret (Sigma s d) = (UnProxy s, Interpret d)
\end{code}

  Here, |UnProxy| maps a value of type |Proxy a| to the type it carries. 

\vspace{-0.1cm}
\section*{Deriving generators}

  Assuming some generator type |G a|, our goal is to define a function of type |IDesc a i -> G a| that returns a generator derived from its input description. However, we need a way to describe (at the type level) the dependency between the input description and the type of values generated. It is not possible to encode this relation directly in Haskell's type system, but we can simulate it using \emph{singleton types} \cite{eisenberg2013dependently}. Singleton types bridge the gap between values at the term level and their promoted counterparts, by defining an indexed type that is inhabited by exactly one value for every value of the index type. We define a typeclass |Singleton a| with an associated type |Sing :: a -> *|, to capture this notion. We make |IDesc a i| an instance of |Singleton| by defining the type |SingIDesc (d :: IDesc a i)|:

\begin{code}
data SingIDesc (d :: IDesc a i) where 
  SOne    ::                                  SingIDesc One
  SEmpty  ::                                  SingIDesc Empty 
  SVar    :: i                            ->  SingIDesc (Var i')  
  (:*:$)  :: SingIDesc l  -> SingIDesc r  ->  SingIDesc (l :*: r)
  (:+:$)  :: SingIDesc l  -> SingIDesc r  ->  SingIDesc (l :+: r)
  SSigma  :: Proxy s -> SingIDesc d      ->  SingIDesc (Sigma (Proxy :: Proxy s) d)  
\end{code}

    This enables us to write a function |deriveGen :: Sing d -> G (Interpret d)|, which returns a generator whose output type depends on the provided description. We sketch the definition of |deriveGen|, under the assumption that |G| is an instance of both |Monad| and |Alternative|.

\begin{code}
deriveGen SOne          = pure ()
deriveGen SEmpty        = empty 
deriveGen (l :*:$ r)    = (,) <$> deriveGen l <*> deriveGen r 
deriveGen (l :+:$ r)    = Left <$> deriveGen l <|> Right <$> derivegen r
\end{code}

  In the case of the |Sigma| constructor, we need a way to generate values of the first element type. Since we do not have a general procedure to derive genrators for arbitrary types of kind |*|, we add this generator as a precondition to |deriveGen|. This can be achieved in various ways (e.g. by using typeclasses), so for now we simply assume that a generator |genS :: G s|, supplied by the programmer, is in scope. If we now define a type family |Expand| that transforms descriptions |IDesc a (s -> i)| into functions |s -> IDesc a i|:

\begin{code}
type family Expand (d :: IDesc a (s -> i)) (x :: s) :: IDesc a i
\end{code}

  and a function |expand| that describes this operation at the term level

\begin{code}
expand :: forall (d :: IDesc a (s -> i)) . Singleton s => Sing d -> Sing s -> SingIDesc (Expand d s)
\end{code}

  we can define a generator for the |Sigma| constructor by utilizing the monadic structure of |G|:
\begin{code}
  deriveGen (SSigma s P) = genS >>= \x -> deriveGen (expand f x) >>= \y -> (x , y)
\end{code}

completing our definition of |deriveGen|.

\vspace{-0.15cm}
\section*{Generating Lambda Terms}

We use the datatype |Term = TVar Nat || TAbs Term || TApp Term Term| to represent raw terms, and a subset of the representation used in Philip Wadler and Wen Kokke's PLFA \cite{wadler2019plfa} to describe well-formedness, restricting ourselves to the constructors for variables, abstraction and application. Let $\Gamma$ range over contexts and $\tau$ over types. A valid judgement of the form $\Gamma \vdash \tau$ can be constructed using one of the following constructors:

\vspace{-0.1cm}
\begin{equation*}
\texttt{[Var]}\frac{\Gamma \ni \tau}{\Gamma \vdash \tau} \quad 
\texttt{[Abs]}\frac{\Gamma , \sigma \vdash \tau}{\Gamma \vdash \sigma \rightarrow \tau} \quad 
\texttt{[App]}\frac{\Gamma \vdash \sigma \rightarrow \tau \quad \Gamma \vdash \sigma}{\Gamma \vdash \tau}
\end{equation*}

  \vspace{0.2cm}
  We use a type family |SLTCDesc (i :: (Ctx , Type))| to describe these judgements as a code in the universe of indexed descriptions. We do this by induction over the goal type, return a coproduct of the descriptions corresponding to the constructors that could have been used to arrive at a judgement with that type.

\begin{code}
type VarDesc = Sigma (P CtxPos) One
type AppDesc = Sigma (P Type) (Var I :*: Var I) 

type family SLTCDesc (i :: (Ctx , Type)) :: IDesc Term (Ctx , Type)
type instance SLTCDesc (ctx , T)            = VarDesc :+: AppDesc
type instance SLTCDesc (ctx , (t1 :-> t2))  = VarDesc :+: Var ((t1:ctx),t2) :+: AppDesc 
\end{code}

  Given a context |ctx| and a type |ty|, |Interpret (SLTCDesc (ctx , ty))| is isomorphic to the typing judgement $\texttt{ctx} \vdash \texttt{ty}$, its inhabitants corresponding to raw terms that have type \texttt{ty} under context \texttt{ctx}. Next, we define an appropriate singleton value |sltcDesc :: Sing i -> Sing (SLTCDesc i)| to connect the term and type level, along with a conversion function |toTerm :: Sing i -> Interpret (SLTCDesc i) -> Term| that transforms judgements into terms. Both definitions follow naturally once the type family that describes the inductive relation is in place. By passing the singleton description |sltcDesc| to |deriveGen|, and applying |toTerm| to the generated values, we have obtained a generator that produces well-typed lambda terms. 

\vspace{-0.1cm}
\section*{Conclusion \& Future work}

  We have shown that we can use the techniques described in this abstract to generate well-typed lambda terms, while being reasonably confident that the results are correct. Although a lot is left to be desired in terms of usability and efficiency, we could theoretically synthesize terms of any programming language whose well-formedness can be described using an indexed datatype. Still, there are many possible avenues for further exploration, such as more efficient generation using memoization techniques as used in FEAT \cite{duregaard2013feat}, property based testing for GADT's, and generation of data whose well-formedness is described by a \emph{mutually recursive} datatypes \cite{miraldo2018sums, yakushev2009generic}. 
  
\bibliographystyle{acm} % ACM-Reference-Format 
\bibliography{references}
\end{document}


