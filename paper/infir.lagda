\documentclass[preprint]{sigplanconf}

\usepackage{amsmath}
\usepackage{lipsum}

\usepackage{amsfonts,amssymb,textgreek,stmaryrd}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}

\usepackage[references]{agda}

\DeclareUnicodeCharacter{8759}{\ensuremath{::}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\cL}{{\cal L}}

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}
%% \setlength{\mathindent}{\parindent}

\conferenceinfo{CONF 'yy}{Month d--d, 20yy, City, ST, Country}
\copyrightyear{20yy}
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm}
\copyrightdoi{nnnnnnn.nnnnnnn}

% Uncomment the publication rights you want to use.
%\publicationrights{transferred}
%\publicationrights{licensed}     % this is the default
%\publicationrights{author-pays}

\titlebanner{DRAFT}        % These are ignored unless
%% \preprintfooter{short description of paper}   % 'preprint' option specified.

\title{Programming with Infinitary Inductive-Recursive Types}
\subtitle{Preconditions with computational content}

\authorinfo{Larry Diehl}
           {Portland State University}
           {ldiehl@cs.pdx.edu}
           
\authorinfo{Tim Sheard}
           {Portland State University}
           {sheard@cs.pdx.edu}

\maketitle

\begin{abstract}
\lipsum[3]
\end{abstract}

\category{D.3}{Software}{Programming Languages}.

\keywords
Dependent types; induction-recursion; generic programming.

\section{Introduction}

%% modeling univeres, modeling arithmetic summations and products,
%% modeling file formats

\AgdaHide{
\begin{code}
module _ where
open import Data.Nat
\end{code}}

Infinitary inductive-recursive (InfIR) types are commonly used in dependently
typed programs to model type-theoretic universes. For example,
consider the model below of the universe of natural numbers and
dependent functions.

\begin{code}
mutual
  data Type : Set where
    `ℕ : Type
    `Π : (A : Type) (B : ⟦ A ⟧ → Type) → Type
  
  ⟦_⟧ : Type → Set
  ⟦ `ℕ ⟧ = ℕ
  ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
\end{code}

\AgdaHide{
\begin{code}
_`→_ : (A B : Type) → Type
A `→ B = `Π A (λ _ → B)
\end{code}}

\noindent
This \AgdaDatatype{Type} is \emph{infinitary} because the
\AgdaInductiveConstructor{`Π} constructor's second inductive argument
(\AgdaBound{B}) is a function (hence \AgdaDatatype{Type}s can branch infinitely).
Additionally, it is \emph{inductive-recursive} because it
is mutually defined with a
function (\AgdaFunction{⟦\_⟧}) operating over it.

Once you have defined a model, it is also common to provide a few
examples of values that inhabit it.
For example, below (\AgdaFunction{NumFun}) is a function \AgdaDatatype{Type}
that takes a natural number \AgdaBound{n} as input, then asks you
to construct a natural number from \AgdaBound{n} additional natural
number arguments.

\begin{code}
NumArgs : ℕ → Type
NumArgs zero = `ℕ
NumArgs (suc n) = `ℕ `→ NumArgs n

NumFun : Type
NumFun = `Π `ℕ (λ n → NumArgs n)
\end{code}

While defining models and example values using infinitary
inductive-recursive types is common, writing inductively defined
\textit{functions} over them is not!

Why isn't there much existing work on programming functions with
infinitary inductive-recursive functions? They contain inherently
complex properties that make programmers rather avoid thinking about
dealing with them, so there simply aren't many examples for
programmers to base their programs off. Their infinitary nature makes them
\emph{higher-order} datatypes, rather than simpler first-order
datatypes. Their inductive-recursive nature means you need to deal
with dependencies between arguments and mutual functions too.

Functional programming languages typically package useful datatypes
(like \AgdaDatatype{List}s and \AgdaDatatype{Vec}tors) with useful operations
(like \AgdaFunction{lookup}, \AgdaFunction{update} and
\AgdaDatatype{Zipper} navigation) in their standard
libraries. Additionally, \emph{generic} implementations of such operations
may exist as libraries for any other user-defined datatypes.

Our \emph{primary contribution} is to show how to write analogues of common
functional operations using common universe models of infinitary
inductive-recursive types, and then show how to turn such operations
over specific datatypes into generic operations over any user-defined
datatype. More specifically, our contributions are:

\begin{itemize}
\item Concrete and generic open universe index InfIR types (\AgdaDatatype{Path}).
\item Concrete and generic open universe
  \AgdaFunction{lookup} and \AgdaFunction{update} functions for
  InfIR types.
\item Correctness proofs of \AgdaFunction{lookup} and
  \AgdaFunction{update} with respect to each other.
\item Concrete and generic open universe \AgdaDatatype{Zipper} InfIR types.
\item Concrete and generic open universe \AgdaDatatype{Zipper}
  operations for InfIR types.
\item Concrete, generic open universe, and generic \emph{closed} universe \AgdaFunction{show}
  functions for InfIR types. 
\item A model of a closed universe of InfIR types. The generic closed universe
  \AgdaFunction{show} function is another example of a
  concrete InfIR function, where the closed universe type is itself InfIR.
\end{itemize}

Finally, we hope that seeing examples of writing both specific and generic
functions using infinitary inductive-recursive types will help future
dependently functional programmers with writing their own functions
over this class of datatypes.

%% trouble: non-heterogeneous answers
%% either make the return type heterogeneous, or add
%% a heterogeneous argument

\section{The problem}

Before describing why writing functions over InfIR types is difficult,
we first consider writing analogous functions over simpler
datatypes. Thereafter we point out what becomes difficult in the
InfIR scenario, and describe a general methodology of writing
total functions in a dependently typed language, which can be applied
to successfully write InfIR functions. 

\subsection{Background}

Instead of diving directly into the complexity of writing functions
like \AgdaFunction{lookup} for the InfIR universe \AgdaDatatype{Type},
let us first consider writing \AgdaFunction{lookup} for a binary
\AgdaDatatype{Tree}.

\begin{code}
data Tree : Set where
  leaf : Tree
  branch : (A B : Tree) → Tree
\end{code}

Our \AgdaDatatype{Tree} stores no additional data in nodes, can have
binary \AgdaInductiveConstructor{branch}es, and ends with a
\AgdaInductiveConstructor{leaf}. It is easy to work with because it is
first-order, has no dependencies between arguments, and not mutually
defined functions.

If we want to \AgdaFunction{lookup}
a particular
sub\AgdaDatatype{Tree}, we must first have a way to describe a
\AgdaDatatype{Path} that indexes into our original tree.
\footnote{
  For lists, \texttt{lookup} refers to finding data in a list,
  whereas \texttt{drop} refers to finding sublists. Nevertheless, in
  this paper we refer to our generalization of ``drop'' to tree types
  as \AgdaFunction{lookup} because we never define a ``lookup''
  function for non-inductive elements of a type.
}

\begin{code}
data Path : Tree → Set where
  here : ∀{A} → Path A
  there₁ : ∀{A B}
    → Path A
    → Path (branch A B)
  there₂ : ∀{A B}
    → Path B
    → Path (branch A B)
\end{code}

The \AgdaInductiveConstructor{here} constructor indicates that we have
arrived at the subtree we would like to visit. The
\AgdaInductiveConstructor{there₁} constructor tells us to take a left
turn at a \AgdaInductiveConstructor{branch}, while
\AgdaInductiveConstructor{there₂} tells us to take a right turn.

Once we have defined \AgdaDatatype{Path}s into a \AgdaDatatype{Tree},
it is straightforward to defined \AgdaFunction{lookup} by following
the \AgdaDatatype{Path} until we arrive at the type appearing
\AgdaInductiveConstructor{here}.

\begin{code}
lookup : (A : Tree) → Path A → Tree
lookup A here = A
lookup (branch A B) (there₁ i) = lookup A i
lookup (branch A B) (there₂ i) = lookup B i
\end{code}


\subsection{Writing total functions}

Once we move from a finitary non-dependent type like
\AgdaDatatype{Tree} to a InfIR type like
\AgdaDatatype{Type}, it is not obvious how to write a function like
\AgdaFunction{lookup}. Looking up something in the
left side (domain) of a \AgdaInductiveConstructor{`Π} is easy, but
looking up something in the right side (codomain) requires entering a
function space.

One solution is to disallow right-side lookups of
\AgdaInductiveConstructor{`Π}s, but that is rather limiting. Figuring
out how to write functions like \AgdaFunction{lookup}, and more
complicated functions, for InfIR types is the subject of this
paper. Before we show the solution, let us first consider a general
methodology for turning a would-be partial function into a total
function. For example, say we wanted to write a total version of the
typically partial \AgdaFunction{head} function.

\AgdaHide{
\begin{code}
open import Data.Unit
open import Data.Maybe
open import Data.List
\end{code}}

\begin{code}
postulate head : {A : Set} → List A → A
\end{code}

We have 2 options to make this function total. We can either:

\begin{enumerate}
\item Change the domain, for example by requiring an extra default argument.
\item Change the codomain, for example by returning a
  \AgdaDatatype{Maybe} result.
\end{enumerate}

\begin{code}
head₁ : {A : Set} → List A → A → A
head₁ [] y = y
head₁ (x ∷ xs) y = x

head₂ : {A : Set} → List A → Maybe A
head₂ [] = nothing
head₂ (x ∷ xs) = just x
\end{code}

Both options give us something to do when we apply
\AgdaFunction{head} to an empty list, either get an extra argument to
return, or to bail on the computation with
\AgdaInductiveConstructor{nothing}.
However, these options are rather extreme as they require changing our
intended type signature of \AgdaFunction{head} for \emph{all} possible
lists. The precision of dependent types allows us to instead
conditionally ask for an extra argument, or return
\AgdaInductiveConstructor{nothing} of computational value, only if the
input list is empty!

\begin{code}
HeadDom : {A : Set} → List A → Set
HeadDom {A = A} [] = A
HeadDom (x ∷ xs) = ⊤

head₃ : {A : Set} (xs : List A) → HeadDom xs → A
head₃ [] y = y
head₃ (x ∷ xs) tt = x
\end{code}

\begin{code}
HeadCod : {A : Set} → List A → Set
HeadCod [] = ⊤
HeadCod {A = A} (x ∷ xs) = A

head₄ : {A : Set} (xs : List A) → HeadCod xs
head₄ [] = tt
head₄ (x ∷ xs) = x
\end{code}

\acks

Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}

% The bibliography should be embedded for final submission.

\begin{thebibliography}{}
\softraggedright

\bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
P. Q. Smith, and X. Y. Jones. ...reference text...

\end{thebibliography}


\end{document}
