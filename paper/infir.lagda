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

\newcommand{\refsec}[1]{Section \ref{sec:#1}}

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
%% \subtitle{Preconditions with computational content}

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
module InfIR where
open import Data.Unit
open import Data.Nat
open import Data.Maybe
open import Data.List
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
\label{sec:problem:background}

Instead of diving directly into the complexity of writing functions
like \AgdaFunction{lookup} for the InfIR universe \AgdaDatatype{Type},
let us first consider writing \AgdaFunction{lookup} for a binary
\AgdaDatatype{Tree}.

\AgdaHide{
\begin{code}
module Tree where
\end{code}}

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
\label{sec:problem:total}

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

First, let's use dependent types to conditonally change the domain. We
will ask for an extra argument of type \AgdaBound{A} if the
\AgdaDatatype{List} is empty. Otherwise, we will ask for an extra
argument of type unit (\AgdaDatatype{⊤}), which is isomorphic to not
asking for anything extra at all. Below, \AgdaFunction{HeadDom} is
type of the extra argument, which is dependent on the input
\AgdaBound{xs} of type \AgdaDatatype{List}.

\begin{code}
HeadDom : {A : Set} → List A → Set
HeadDom {A = A} [] = A
HeadDom (x ∷ xs) = ⊤

head₃ : {A : Set} (xs : List A) → HeadDom xs → A
head₃ [] y = y
head₃ (x ∷ xs) tt = x
\end{code}

Second, let's use dependent types to conditonally change the
codomain. \AgdaFunction{HeadCod} computes our new return type,
conditionally dependent on the input list. If the input list is empty,
our \AgdaFunction{head₄} function returns a value of type unit (\AgdaDatatype{⊤}). If
it is non-empty, it returns an \AgdaBound{A}. Note that returning a
value of \AgdaDatatype{⊤} is returning nothing of computational
significance. Hence, it is like \AgdaFunction{head₄} is not defined
for empty lists.

\begin{code}
HeadCod : {A : Set} → List A → Set
HeadCod [] = ⊤
HeadCod {A = A} (x ∷ xs) = A

head₄ : {A : Set} (xs : List A) → HeadCod xs
head₄ [] = tt
head₄ (x ∷ xs) = x
\end{code}

So far we have seen how to take a partial function and make it total,
both with and without the extra precision afforded to us by dependent
types.

At this point we would like to emphasize that the extra argument
\AgdaFunction{HeadDom} in \AgdaFunction{head₃} is not merely a
precondition, but rather extra computational content that is required
from the user applying the function to complete the cases that would
normally make it a partial function.
To see the difference, consider a total version of a function that looks up
\AgdaFunction{elem}ents of a \AgdaDatatype{List},
once given a natural number (\AgdaDatatype{ℕ}) index.

\begin{code}
postulate
  elem : {A : Set} (xs : List A) (n : ℕ)
    → length xs < n → A
\end{code}

Because the natural number \AgdaBound{n} may index outside the bounds
of the list \AgdaBound{xs}, we need an extra argument serving as a
precondition. If this precondition is satisfied, it computes to the unit
type (\AgdaDatatype{⊤}),
but if it fails it computes to the empty type (\AgdaDatatype{⊥}). So,
in the failure case the precondition (\AgdaDatatype{⊥}) is
unsatisfiable, whereas the failure case of \AgdaFunction{HeadDom} is
the extra argument \AgdaBound{A} needed to complete the otherwise
partial function.

The rest of this paper expands on the ideas of this section by
defining functions like \AgdaFunction{HeadDom} that non-trivially
compute extra arguments. These dependent extra arguments
are the key to writing functions over InfIR datatypes.

\section{InfIR \AgdaFunction{lookup} \& \AgdaFunction{update}}

\refsec{problem:background} reviewed how to
\AgdaFunction{lookup} a sub\AgdaDatatype{Tree} pointed to by a
particular \AgdaDatatype{Path}. In this section we define the
corresponding datatypes and functions for InfIR
\AgdaDatatype{Type}s.

\subsection{\AgdaDatatype{Path}s}

Let's reconsider what it means to be a \AgdaDatatype{Path}. When
traversing a \AgdaDatatype{Tree}, you can always go left or right at a
\AgdaInductiveConstructor{branch}. When traversing a
\AgdaDatatype{Type}, it you can immediately go to the left of a
\AgdaInductiveConstructor{`Π}, but going right requires first knowing
which element \AgdaBound{a} of the type family \AgdaBound{B a} to
continue traversing under.

\begin{code}
data Path : Type → Set where
  here : {A : Type} → Path A
  there₁ : {A : Type} {B : ⟦ A ⟧ → Type}
    (i : Path A)
    → Path (`Π A B)
  there₂ : {A : Type} {B : ⟦ A ⟧ → Type}
    (f : (a : ⟦ A ⟧) → Path (B a))
    → Path (`Π A B)
\end{code}

Above, \AgdaInductiveConstructor{there₂} represents going right
into the codomain of \AgdaInductiveConstructor{`Π}, but only once the
user tells you which \AgdaBound{a} to use. In a sense, going right is
like asking for a continuation that tells you where else to go once
you have been given \AgdaBound{a}. Also note that because the argument
\AgdaBound{f} of \AgdaInductiveConstructor{there₂} is a function that
returns a \AgdaDatatype{Path}, the \AgdaDatatype{Path} datatype is
infinitary (just like the \AgdaDatatype{Type} it indexes).



\begin{code}
Lookup : (A : Type) → Path A → Set
Lookup A here = Type
Lookup (`Π A B) (there₁ i) = Lookup A i
Lookup (`Π A B) (there₂ f) = (a : ⟦ A ⟧) → Lookup (B a) (f a)
\end{code}

\begin{code}
lookup : (A : Type) (i : Path A) → Lookup A i
lookup A here = A
lookup (`Π A B) (there₁ i) = lookup A i
lookup (`Π A B) (there₂ f) = λ a → lookup (B a) (f a)
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
