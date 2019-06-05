\section{The Type of Generators}

  We have not yet specified what it is exactly that we mean when we talk about \textit{generators}. In the context of property based testing, it makes sense to think of generators as entities that produce values of a certain type; the machinery that is responsible for supplying suitable test values. As we saw in section \cref{sec:literature}, this can mean different things depending on the library that you are using. \textit{SmallCheck} and \textit{LeanCheck} generators are functions that take a size parameter as input and produce an exhaustive list of all values that are smaller than the generator's input, while \textit{QuickCheck} generators randomly sample values of the desired type. Though various libraries use different terminology to refer to the mechanisms used to produce test values, we will use \textit{generator} as an umbrella term to refer to the test data producing parts of existing libraries. 

  \subsection{Examples in Existing Libraries}
  
   When comparing generator definitions across libraries, we see that their definition is often more determined by the structure of the datatype they ought to produce values of than the type of the generator itself. Let us consider the |Nat| datatype (definition \ref{defnat}). In QuickCheck, we could define a generator for the |Nat| datatype as follows: 

\begin{code}
  genNat :: Gen Nat 
  genNat = oneof [  pure Zero , Suc <$> genNat ]
\end{code}

  QuickCheck includes many combinators to finetune the distribution of values of the generated type, which are omitted in this case since they do not structurally alter the generator. Compare the above generator to its SmallCheck equivalent: 

\begin{code}
instance Serial m Nat where
  series = cons0 Zero  \/  Cons1 Suc
\end{code}

  Both generator definitions have a strikingly similar structure, marking a choice between the two available constructors (|Zero| and |Suc|) and employing a appropriate combinators to produce values for said constructors. Despite this structural similarity, the underlying types of the respective generators are wildly different, with |genNat| being an |IO| operation that samples random values and the |Serial| instance being a function taking a depth and producing all values up to that depth. 

\subsection{Separating Structure and Interpretation}

  The previous example suggests that there is a case to be made for separating a generators structure from the format in which test values are presented. Additionally, by having a single datatype representing a generator's structure, we shift the burden of proving termination from a generator's definition to its interpretation, which in Agda is a considerable advantage. In practice this means that we define some datatype |Gen a| that marks the structure of a generator, and a function |interpret : Gen a -> T a| that maps an input structure to some |T a|, where |T| which actually produces test values. In our case, we will almost exclusively consider an interpretation of generators to functions of type |ℕ → List a|, but we could have chosen |T| to by any other type of collection of values of type |a|. An implication of this separation is that, given suitable interpretation functions, a user only has to define a single generator in order to be able to employ different strategies for generating test values, potentially allowing for both random and enumerative testing to be combined into a single framework. 

  This approach means that generator combinators are not functions that operate on a a generator's result, such as merging two streams of values, but rather a constructor of some abstract generator type; |Gen| in our case. This datatype represents generators in a tree-like structure, not unlike the more familiar abstract syntax trees used to represent parsed programs. 

\subsection{The |Gen| Datatype}

  We define the datatype of generators, |Gen a t|, to be a family of types indexed by two types \footnote{The listed definition will not be accepted by Agda due to inconsistencies in the universe levels. This is also the case for many code examples to come. To keep things readable, we will not concern ourselves with universe levels throughout this thesis.}. One signifying the type of values that are produced by the generator, and one specifying the type of values produced by recursive positions. 

\includeagdalisting{4}{gendef}{Definition of the |Gen| datatype}{lst:gendef}

  \textit{Closed} generators are then generators produce that produce the values of the same type as their recursive positions: 

\includeagda{4}{gdef}

  The |Pure| and |Ap| constructors make |Gen| an instance of |Applicative|, meaning that we can (given a fancy operator for denoting choice) denote generators in way that is very similar to their definition: 

\includeagda{4}{gennat}

  This serves to emphasize that the structure of generators can, in the case of simpler datatypes, be mechanically derived from the structure of a datatype. We will see how this can be done in chapter \cref{chap:derivingregular}. 

  The question remains how to deal with constructors that refer to \textit{other} types. For example, consider the type of lists (definition \ref{deflist}). We can define an appropriate generator following the structure of the datatype definition: 

\includeagda{4}{listgenhole}

  It is however not immediately clear what value to supply to the remaining interaction point. If we inspect its goal type we see that we should supply a value of type |Gen a (List a)|: a generator producing values of type |a|, with recursive positions producing values of type |List a|. This makes little sense, as we would rather be able to invoke other \textit{closed generators} from within a generator. To do so, we add another constructor to the |Gen| datatype, that signifies the invokation of a closed generator for another datatype: 

\includeagda{4}{calldef}

  Using this definition of |Call|, we can complete the previous definition for |list|: 

\includeagda{4}{listgen}

\subsection{Generator Interpretations}

  We can view a generator's interpretation as any function mapping generators to some type, where the output type is parameterized by the type of values produced by a generator: 

\includeagda{4}{intdef}

  From this definition of |Interpretation|, we can define concrete interpretations. For example, if we want to behave our generators similar to SmallCheck's |Series|, we might define the following concrete instantiation of the |Interpretation| type: 

\includeagda{4}{scdef}

  We can then define a generator's behiour by supplying a definition that inhabits the |GenAsList| type: 

\includeagda{4}{scint}

  The goal type of the open interaction point is then $\mathbb{N}$| → List a|. We will see in \cref{sec:enuminterpretation} how we can flesh out this particular interpretation. We could however have chosen any other result type, depending on what suits our particular needs. An alternative would be to interpret generators as a |Colist|, omitting the depth bound altogether:

\includeagda{4}{intcolist}

\section{Generalization to Indexed Datatypes}

  A first approximation towards a generalization of the |Gen| type to indexed types might be to simply lift the existing definition from |Set| to |I → Set|. 

\includeagda{4}{liftgen}

  However, by doing so we implicitly impose the constraint that the recursive positions of a value have the same index as the recursive positions within it. Consider, for example, the |Fin| type (definition \ref{findef}). If we attempt to define a generator using the lifted type, we run into a problem. 

\includeagda{4}{finhole}

  Any attempt to fill the open interaction point with the |μ| constructor fails, as it expects a value of |Gen (Fin n) (Fin suc n)|, but |μ| requires both its type parameters to be equal. We can circumvent this issue by using direct recursion. 

\includeagda{4}{findirect}

  It is however clear that this approach becomes a problem once we attempt to define generators for datatypes with recursive positions which have indices that are not structurally smaller than the index they target. To overcome these limitations we resolve to a separate deep embedding of generators for indexed types. 

\includeagdalisting{4}{genidef}{Definitiong of the |Genᵢ| datatype}{lst:genidef}

  And consequently the type of closed indexed generators. 

\includeagda{4}{gidef}

  Notice how the |Apᵢ| constructor allows for its second argument to have a different index. The reason for this becomes clear when we 

  With the same combinators as used for the |Gen| type, we can now define a generator for the |Fin| type. 

\includeagda{4}{genfin}

  Now defining generators for datatypes with recursive positions whose indices are not structurally smaller than the index of the datatype itself can be done without complaints from the termination checker, such as well-scoped $\lambda$-terms (definition \ref{defwellscoped}). 

\includeagda{4}{wellscoped}

  It is important to note that it is not possible to call indexed generators from simple generators and vice versa with this setup. We can allow this by either parameterizing the |Call| and |iCall| constructors with the datatype they refer to, or by adding extra constructors to the |Gen| and |Genᵢ| datatypes, making them mutually recursive. 

\section{Interpreting Generators as Enumerations}\label{sec:enuminterpretation}

  We will now consider an example interpretation of generators where we map values of the |Gen| or |Genᵢ| datatypes to functions of type $\mathbb{N}$| → List a|. The constructors of both datatypes mimic the combinators used Haskell's |Applicative| and |Alternative| typeclasses, so we can use the |List| instances of these typeclasses for guidance when defining an enumerative interpretation.  

\includeagdalisting{4}{tolist}{Interpretation of the |Gen| datatype as an enumeration}{lst:tolist}

  Similarly, we can define such an interpretation for the |Genᵢ| datatype similar to listing \ref{lst:tolist} with the only difference being the appropriate indices getting passed to recursive calls. Notice how our generator's behaviour - most notably the intended semantics of the input depth bound - is entirely encoded within the definition of the interpretation. In this case by decrementing |n| anytime a recursive position is encountered.  

\section{Properties for Enumerations}

\section{Generating Function Types}

\section{Monadic Generators}

  There are some cases in which the applicative combinators are not expressive enough to capture the desired generator. For example, if we were to define a construction for generation of $\Sigma$ types, we encounter some problems. 

\includeagda{4}{sigmagenhole}

  We can extend the |Gen| datatype with a |Bind| operation that mimics the monadic bind operator (|>>=|) to allow for such dependencies to exist between generated values.

\includeagda{4}{sigmagen}