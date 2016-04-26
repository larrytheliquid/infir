\documentclass[preprint]{sigplanconf}

\usepackage{amsmath}
\usepackage{lipsum}
\usepackage{todonotes}

\usepackage{amsfonts,amssymb,textgreek,stmaryrd}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}


\usepackage[references]{agda}

\DeclareUnicodeCharacter{8759}{\ensuremath{::}}
\DeclareUnicodeCharacter{10218}{\guillemotleft}
\DeclareUnicodeCharacter{10219}{\guillemotright}

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
\label{sec:intro}

\AgdaHide{
\begin{code}
module InfIR where
open import Level using ( _⊔_ )
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat hiding ( _⊔_ )
open import Data.Fin hiding ( lift ; _<_ )
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality

postulate magic : ∀{ℓ} {A : Set ℓ} → A
  
module Intro where
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
  NumFun = `Π `ℕ NumArgs
\end{code}

While defining models and example values using infinitary
inductive-recursive types is common, writing inductively defined
\textit{functions} over them is not!

Why isn't there much existing work on programming functions with
infinitary inductive-recursive functions? They contain inherently
complex properties that make programmers rather avoid thinking about
dealing with them, so there simply aren't many examples for
programmers to base their programs off. Their infinitary nature makes them
\emph{higher-order datatypes}, rather than simpler first-order
datatypes. Their inductive-recursive nature means you need to deal
with \emph{dependencies} between arguments and \emph{mutual functions} too.

Functional programming languages typically package useful datatypes
(like \AgdaDatatype{List}s and \AgdaDatatype{Vec}tors) with useful operations
(like \AgdaFunction{lookup}, \AgdaFunction{drop} and
\AgdaFunction{update}) in their standard
libraries. Additionally, \emph{generic} implementations of such operations
may exist as libraries for any other user-defined datatypes.

Our \emph{primary contribution} is to show how to write analogues of common
functional operations defined over infinitary
inductive-recursive types (such as \AgdaDatatype{Type} universes), and then show how to turn such operations
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

\section{The problem}
\label{sec:problem}

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
first-order, has no dependencies between arguments, and has no mutually
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

\subsection{Writing type-changing functions}
\label{sec:problem:typechanging}

\AgdaHide{
\begin{code}
module List where
\end{code}}

Now let's consider writing a total \AgdaFunction{lookup} function for
polymorphic \AgdaDatatype{List}s instead of the binary
\AgdaDatatype{Tree}s above. Below is the \AgdaDatatype{List} and its
\AgdaDatatype{Path}.

\begin{code}
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A

  data Path {A : Set} : List A → Set where
    here : ∀{xs} → Path xs
    there₁ : ∀{x xs} → Path (cons x xs)
    there₂ : ∀{x xs}
      → Path xs
      → Path (cons x xs)
\end{code}

The \AgdaInductiveConstructor{here} and
\AgdaInductiveConstructor{there₂} constructors are analogous to those
for \AgdaDatatype{Tree} \AgdaDatatype{Path}s. However,
\AgdaInductiveConstructor{there₁} points to a non-inductive
\AgdaBound{A} value, the first argument to
\AgdaInductiveConstructor{cons}, whereas this pointed to an inductive
subtree in the \AgdaDatatype{Tree} scenario.

In the non-dependent Haskell~\cite{TODO} language there are two
distinct \AgdaFunction{lookup}-like functions for lists.

\begin{verbatim}
  drop :: Int -> [a] -> [a]
  (!!) :: [a] -> Int -> a
\end{verbatim}

The first (\texttt{drop}) looks up inductive sublists, and the second
\texttt{(!!)} looks up non-inductive \texttt{a} values.
A depedently typed language like Agda allows us to a write a single
function that may return a \AgdaDatatype{List} or an \AgdaBound{A},
depending on what the input \AgdaDatatype{Path} points to.

\begin{code}
  Lookup : {A : Set} (xs : List A) → Path xs → Set
  Lookup {A = A} xs here = List A
  Lookup {A = A} (cons x xs) there₁ = A
  Lookup (cons x xs) (there₂ i) = Lookup xs i

  lookup : {A : Set} (xs : List A) (i : Path xs) → Lookup xs i
  lookup xs here = xs
  lookup (cons x xs) there₁ = x
  lookup (cons x xs) (there₂ i) = lookup xs i
\end{code}

The \AgdaFunction{Lookup} function \textit{computes} the return type
of \AgdaFunction{lookup}, allowing \AgdaFunction{lookup} to return
either a \AgdaDatatype{List} or an \AgdaBound{A} (the base cases of
\AgdaFunction{Lookup}). I will refer to functions like
\AgdaFunction{Lookup} as \textit{computational types}.


\subsection{Writing total functions}
\label{sec:problem:total}

Once we move from finitary non-dependent types like
\AgdaDatatype{Tree} and \AgdaDatatype{List} to an InfIR type like
\AgdaDatatype{Type}, it is no longer obvious how to write a function like
\AgdaFunction{lookup}. Looking up something in the
left side (domain) of a \AgdaInductiveConstructor{`Π} is easy, but
looking up something in the right side (codomain) requires entering a
function space.

Figuring out how to write functions like \AgdaFunction{lookup}, and more
complicated functions, for InfIR types is the subject of this
paper. The solution (given in the next section) involves a more
complicated version of the computational type \AgdaFunction{Lookup} above. 
But, let us first consider a general
methodology for turning a would-be partial function into a total
function. For example, say we wanted to write a total version of the
typically partial \AgdaFunction{head} function.

\AgdaHide{
\begin{code}
  length : {A : Set} → List A → ℕ
  length nil = zero
  length (cons x xs) = suc (length xs)
\end{code}}


\begin{code}
  head : {A : Set} → List A → A
\end{code}

\AgdaHide{
\begin{code}
  head = magic
\end{code}}

We have 2 options to make this function total. We can either:

\begin{enumerate}
\item Change the domain, for example by requiring an extra default argument.
\item Change the codomain, for example by returning a
  \AgdaDatatype{Maybe} result.
\end{enumerate}

\begin{code}
  head₁ : {A : Set} → List A → A → A
  head₁ nil y = y
  head₁ (cons x xs) y = x
  
  head₂ : {A : Set} → List A → Maybe A
  head₂ nil = nothing
  head₂ (cons x xs) = just x
\end{code}

Both options give us something to do when we apply
\AgdaFunction{head} to an empty list: either get an extra argument to
return, or we simly return
\AgdaInductiveConstructor{nothing}.
However, these options are rather extreme as they require changing our
intended type signature of \AgdaFunction{head} for \emph{all} possible
lists. The precision of dependent types allows us to instead
conditionally ask for an extra argument, or return
\AgdaInductiveConstructor{nothing} of computational value, only if the
input list is empty!

First, let's use dependent types to conditonally change the domain. We
ask for an extra argument of type \AgdaBound{A} if the
\AgdaDatatype{List} is empty. Otherwise, we ask for an extra
argument of type unit (\AgdaDatatype{⊤}), which is isomorphic to not
asking for anything extra at all. Below, \AgdaFunction{HeadDom} is
type of the extra argument, which is dependent on the input
\AgdaBound{xs} of type \AgdaDatatype{List}.

\begin{code}
  HeadDom : {A : Set} → List A → Set
  HeadDom {A = A} nil = A
  HeadDom (cons x xs) = ⊤
  
  head₃ : {A : Set} (xs : List A) → HeadDom xs → A
  head₃ nil y = y
  head₃ (cons x xs) tt = x
\end{code}

Second, let's use dependent types to conditonally change the
codomain. \AgdaFunction{HeadCod} computes our new return type,
conditionally dependent on the input list. If the input list is empty,
our \AgdaFunction{head₄} function returns a value of type unit (\AgdaDatatype{⊤}). If
it is non-empty, it returns an \AgdaBound{A}. Note that returning a
value of \AgdaDatatype{⊤} is returning nothing of computational
significance. Hence, it is as if \AgdaFunction{head₄} is not defined
for empty lists.

\begin{code}
  HeadCod : {A : Set} → List A → Set
  HeadCod nil = ⊤
  HeadCod {A = A} (cons x xs) = A
  
  head₄ : {A : Set} (xs : List A) → HeadCod xs
  head₄ nil = tt
  head₄ (cons x xs) = x
\end{code}

So far we have seen how to take a partial function and make it total,
both with and without the extra precision afforded to us by dependent
types. Note that \AgdaFunction{HeadCod} is a computational type like
\AgdaFunction{Lookup}. We will refer to functions like
\AgdaFunction{HeadDom} as \textit{computational arguments}.
\footnote{It is
possible to write dependently typed functions using either a
computational argument or a computational type. Picking which
technique to use is a matter of preference, and determines whether the
arguments or the return type is statically known.}

Finally, we would like to emphasize that the extra argument
\AgdaFunction{HeadDom} in \AgdaFunction{head₃} is not merely a
precondition, but rather extra computational content that is required
from the user applying the function to complete the cases that would
normally make it a partial function.
To see the difference, consider a total version of a function that looks up
\AgdaFunction{elem}ents of a \AgdaDatatype{List},
once given a natural number (\AgdaDatatype{ℕ}) index.

\begin{code}
  elem : {A : Set} (xs : List A) (n : ℕ) → length xs < n → A
\end{code}

\AgdaHide{
\begin{code}
  elem = magic
\end{code}}

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

\section{Large InfIR \AgdaDatatype{Type}}
\label{sec:concretelarge}

\AgdaHide{
\begin{code}
module ConcreteLarge where
\end{code}}

\refsec{problem} reviews how to
\AgdaFunction{lookup} sub\AgdaDatatype{Tree}s, sub\AgdaDatatype{List}s,
and subelements pointed to by \AgdaDatatype{Path}s. In this section we
define the corresponding datatypes and functions for InfIR
\AgdaDatatype{Type}s.

\subsection{\AgdaDatatype{Type}}

The InfIR \AgdaDatatype{Type} used in this section is another
type universe, similar to the one in \refsec{intro}. The
\AgdaDatatype{Type} universe is still closed under functions, but now
the base types are parameters instead of being hardcoded to
\AgdaDatatype{ℕ}.

\begin{code}
  mutual
    data Type : Set₁ where
      `Base : Set → Type
      `Π : (A : Type) (B : ⟦ A ⟧ → Type) → Type
  
    ⟦_⟧ : Type → Set
    ⟦ `Base A ⟧ = A
    ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
\end{code}

\subsection{\AgdaDatatype{Path}}

Let's reconsider what it means to be a \AgdaDatatype{Path}.
You can still point to a recursive \AgdaDatatype{Type} using
\AgdaInductiveConstructor{here}. Now you can also point to a
non-recursive \AgdaBound{A} of type \AgdaDatatype{Set} using
\AgdaInductiveConstructor{thereBase}.

When traversing a \AgdaDatatype{Tree}, you can always go left or right at a
\AgdaInductiveConstructor{branch}. When traversing a
\AgdaDatatype{Type}, you can immediately go to the left of a
\AgdaInductiveConstructor{`Π}, but going right requires first knowing
which element \AgdaBound{a} of the type family \AgdaBound{B a} to
continue traversing under.

\begin{code}
  data Path : Type → Set₁ where
    here : {A : Type} → Path A
    thereBase : {A : Set} → Path (`Base A)
    thereΠ₁ : {A : Type} {B : ⟦ A ⟧ → Type}
      (i : Path A)
      → Path (`Π A B)
    thereΠ₂ : {A : Type} {B : ⟦ A ⟧ → Type}
      (f : (a : ⟦ A ⟧) → Path (B a))
      → Path (`Π A B)
\end{code}

Above, \AgdaInductiveConstructor{thereΠ₂} represents going right
into the codomain of \AgdaInductiveConstructor{`Π}, but only once the
user tells you which \AgdaBound{a} to use. In a sense, going right is
like asking for a continuation that tells you where else to go once
you have been given \AgdaBound{a}. Also note that because the argument
\AgdaBound{f} of \AgdaInductiveConstructor{thereΠ₂} is a function that
returns a \AgdaDatatype{Path}, the \AgdaDatatype{Path} datatype is
infinitary (just like the \AgdaDatatype{Type} it indexes).

\subsection{\AgdaFunction{lookup}}

We were able to write a total function to \AgdaFunction{lookup} any
sub\AgdaDatatype{Tree}, but \AgdaFunction{lookup}ing up a
sub\AgdaDatatype{Type} is not always possible. Using our methodology
from \refsec{problem:total}, we can make \AgdaFunction{lookup} for
\AgdaDatatype{Type}s total by choosing to change the codomain,
depending on the input \AgdaDatatype{Type} and \AgdaDatatype{Path}.
\AgdaFunction{Lookup} computes the codomain of
\AgdaFunction{lookup}, asking for a \AgdaDatatype{Type} or \AgdaDatatype{Set} in the base
cases, or a continuation when looking to the right of a
\AgdaInductiveConstructor{`Π}.

\begin{code}
  Lookup : (A : Type) → Path A → Set₁
  Lookup A here = Type
  Lookup (`Base A) thereBase = Set
  Lookup (`Π A B) (thereΠ₁ i) = Lookup A i
  Lookup (`Π A B) (thereΠ₂ f) = (a : ⟦ A ⟧) → Lookup (B a) (f a)
\end{code}

Finally, we can write \AgdaFunction{lookup} in terms of
\AgdaDatatype{Path} and \AgdaFunction{Lookup}. Notice that users
applying our \AgdaFunction{lookup} function need to supply
extra \AgdaBound{a} arguments exactly when they go to the right of a
\AgdaInductiveConstructor{`Π}. Thus, our definition can expect an
extra argument \AgdaBound{a} in the
\AgdaInductiveConstructor{thereΠ₂} case.

\begin{code}
  lookup : (A : Type) (i : Path A) → Lookup A i
  lookup A here = A
  lookup (`Base A) thereBase = A
  lookup (`Π A B) (thereΠ₁ i) = lookup A i
  lookup (`Π A B) (thereΠ₂ f) = λ a → lookup (B a) (f a)
\end{code}

\subsection{\AgdaFunction{update}}

Now we will write an \AgdaFunction{update} function for
\AgdaDatatype{Type}s. After supplying a \AgdaDatatype{Path} and a
substitute \AgdaDatatype{Type}, \AgdaFunction{update} should return
the original \AgdaDatatype{Type} but with the substitute replacing
what the \AgdaDatatype{Path} pointed to. To make updating the InfIR
\AgdaDatatype{Type}
more convenient, the type of the substitute will actually be
\AgdaDatatype{Maybe Type}, where \AgdaInductiveConstructor{nothing}
causes an identity update.
You might expect to write a function like:

\begin{code}
  updateNaive :
    (A : Type) (i : Path A) (X : Maybe Type) → Type
\end{code}

\AgdaHide{
\begin{code}
  updateNaive = magic
\end{code}}

\noindent
Above \AgdaBound{X} is the intended \AgdaDatatype{Type} to
\AgdaDatatype{Maybe} substitute at position \AgdaBound{i}.
In order to write a total version of
\AgdaFunction{updateNaive}, we need to change the domain by
asking for an \AgdaBound{a} whenever we update within the codomain of
a \AgdaInductiveConstructor{`Π}.

We call the type of the substitute
\AgdaFunction{Update}, which asks for a \AgdaDatatype{Maybe Type} or a
\AgdaDatatype{Maybe Set} in the base cases (\AgdaInductiveConstructor{here}
and \AgdaInductiveConstructor{thereBase} respectively), and a continuation in the
\AgdaInductiveConstructor{thereΠ₂} case. However, updating an element to
the left of a \AgdaInductiveConstructor{`Π} is also
problematic. We would like to keep the old
\AgdaInductiveConstructor{`Π} codomain \AgdaBound{B} unchanged, but it
still expects an \AgdaBound{a} of the original type
\AgdaFunction{⟦} \AgdaBound{A} \AgdaFunction{⟧}. Therefore, the
\AgdaInductiveConstructor{thereΠ₁} case must
ask for an additional function \AgdaBound{f} that maps newly
updated \AgdaBound{a}'s to their original type.

\todo[inline]{Give an example of the domain type changing and being translated}

\begin{code}
  Update : (A : Type) → Path A → Set₁
  update : (A : Type) (i : Path A) (X : Update A i) → Type
  
  Update A here = Maybe Type
  Update (`Base A) thereBase = Maybe Set
  Update (`Π A B) (thereΠ₁ i) =
    Σ (Update A i) (λ X → ⟦ update A i X ⟧ → ⟦ A ⟧)
  Update (`Π A B) (thereΠ₂ f) =
    (a : ⟦ A ⟧) → Update (B a) (f a)
  
  update A here X = maybe id A X
  update (`Base A) thereBase X = maybe `Base (`Base A) X
  update (`Π A B) (thereΠ₁ i) (X , f) =
    `Π (update A i X) (λ a → B (f a))
  update (`Π A B) (thereΠ₂ f) h =
    `Π A (λ a → update (B a) (f a) (h a))
\end{code}

Notice that we must define \AgdaFunction{Update} and
\AgdaFunction{update} mutually, because the translation
function (the codomain of
\AgdaDatatype{Σ} in the \AgdaInductiveConstructor{thereΠ₁} case of
\AgdaFunction{Update}) must refer to \AgdaFunction{update} in its
domain. Although the \AgdaInductiveConstructor{thereΠ₁} case of
\AgdaFunction{update} only updates the domain of
\AgdaInductiveConstructor{`Π}, the type family \AgdaBound{B} in the
codomain expects an \AgdaBound{a} of type
\AgdaFunction{⟦} \AgdaBound{A} \AgdaFunction{⟧}, so we use the
translation function \AgdaBound{f} to map back to \AgdaBound{a}'s
original type.

The base cases (\AgdaInductiveConstructor{here} and
\AgdaInductiveConstructor{thereBase}) of \AgdaFunction{update}
perform updates using the
subsitute \AgdaBound{X} (where \AgdaInductiveConstructor{nothing}
results in an identity update). The \AgdaInductiveConstructor{thereΠ₂}
case of \AgdaFunction{update} leaves the domain of
\AgdaInductiveConstructor{`Π} unchanged, and recursively updates the
codmain using the substitute continuation \AgdaBound{h}.

Note that
we could have defined \AgdaFunction{Update} as an inductive type,
rather than a computational type. If we had done so,
then it would be an InfIR type with \AgdaFunction{update} as its
mutually defined function!


\section{Small InfIR \AgdaDatatype{Arith}}
\label{sec:concretesmall}

\AgdaHide{
\begin{code}
module ConcreteSmall where
\end{code}}

\refsec{concretelarge} shows how to define
\AgdaFunction{lookup} and \AgdaFunction{update} for the large InfIR
\AgdaDatatype{Type}. \AgdaDatatype{Type} is called \textit{large}
because the codomain of its IR function \AgdaFunction{⟦\_⟧} has type
\AgdaDatatype{Set}. In this section we adapt our work to a
small InfIR type called \AgdaDatatype{Arith} (it is called
\textit{small} because the codomain of its IR function is \textit{not}
\AgdaDatatype{Set}), which is structurally similar to
\AgdaDatatype{Type}.

\subsection{\AgdaDatatype{Arith}}

The InfIR \AgdaDatatype{Arith} used in this section is structurally
similar to \AgdaDatatype{Type} from \refsec{intro}. One difference is
that the base constructor (\AgdaInductiveConstructor{`Num}), contains
a \AgdaDatatype{ℕ}atural number (rather than a \AgdaDatatype{Set},
like \AgdaInductiveConstructor{`Base}). The other difference is that
the mutually defined function \AgdaFunction{eval} returns a
\AgdaDatatype{ℕ} (rather than a \AgdaDatatype{Set}, like
\AgdaFunction{⟦\_⟧}.)

\begin{code}
  mutual
    data Arith : Set where
      `Num : ℕ → Arith
      `Π : (A : Arith) (f : Fin (eval A) → Arith) → Arith
  
    eval : Arith → ℕ
    eval (`Num n) = n
    eval (`Π A f) = prod (eval A)
      λ a → prod (toℕ a) λ b → eval (f (inject b))
\end{code}

Values of type \AgdaDatatype{Arith} encode ``Big
Pi'' mathematical equations up to some finite bound, such as the one
below.

\begin{equation*}
  \prod_{i=1}^{3} i
\end{equation*}

An equation may also be nested in its lower bound, upper bound, or
body. The \AgdaFunction{eval} function interprets the equation as a
natural number, using the helper function \AgdaFunction{prod} to
multiply a finite number \AgdaBound{n} of other natural numbers
together.

\begin{code}
    prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
    prod zero f = suc zero
    prod (suc n) f = f zero * prod n (f ∘ suc)
\end{code}

\subsection{\AgdaDatatype{Pathℕ} \& \AgdaFunction{lookupℕ} \& \AgdaFunction{updateℕ}}

The major difference between the base case
\AgdaInductiveConstructor{`Num} of \AgdaDatatype{Arith}, and
\AgdaInductiveConstructor{`Base} of \AgdaDatatype{Type}, is that the
former contains a \AgdaDatatype{ℕ} while the latter contains a
\AgdaDatatype{Set}. The \AgdaFunction{lookup} for \AgdaDatatype{Type}
had no choice but to return the value of type \AgdaDatatype{Set} in
the \AgdaInductiveConstructor{`Base} case, because the inability to
case analyze \AgdaDatatype{Set} prevents further lookups into that
value. In contrast, we can continue to lookup into a substructure of
\AgdaDatatype{ℕ} in the base case \AgdaInductiveConstructor{`Num} of
\AgdaFunction{lookup} for \AgdaDatatype{Arith}.
For this reason, we need \AgdaDatatype{Pathℕ}, \AgdaFunction{lookupℕ},
and \AgdaFunction{lookupℕ} definitions for natural numbers.

\AgdaDatatype{Pathℕ} is an index into the number, which can point to
that number or any smaller number. It is different from the finite set
type \AgdaDatatype{Fin} because the number pointed to can also be
\AgdaInductiveConstructor{zero}.

\begin{code}
  data Pathℕ : ℕ → Set where
    here : {n : ℕ} → Pathℕ n
    there : {n : ℕ}
      → Pathℕ n
      → Pathℕ (suc n)
\end{code}

The \AgdaFunction{lookup} function simply returns the
\AgdaDatatype{ℕ} pointed to by \AgdaDatatype{Pathℕ}. It does not have
a fancy return type, because a \AgdaDatatype{Pathℕ} always points to a
\AgdaDatatype{ℕ}.

\begin{code}
  lookupℕ : (n : ℕ) → Pathℕ n → ℕ
  lookupℕ n here = n
  lookupℕ (suc n) (there i) = lookupℕ n i
\end{code}

The \AgdaFunction{update} function replaces a subnumber within a
\AgdaDatatype{ℕ} with a \AgdaDatatype{Maybe ℕ}. The
\AgdaInductiveConstructor{nothing} case performs an identity update,
while \AgdaInductiveConstructor{just} \AgdaBound{n} replaces the
subnumber with \AgdaBound{n}.

\begin{code}
  updateℕ : (n : ℕ) → Pathℕ n → Maybe ℕ → ℕ
  updateℕ n here x = maybe id n x
  updateℕ (suc n) (there i) x = suc (updateℕ n i x)
\end{code}

\subsection{\AgdaDatatype{Path} \& \AgdaFunction{lookup} \& \AgdaFunction{update}}

The \AgdaDatatype{Path}, \AgdaFunction{lookup}, and
\AgdaFunction{lookup} definitions for \AgdaDatatype{Arith} are
nearly structurally identical to the corresponding definitions for
\AgdaDatatype{Type} from \refsec{concretelarge}. Thus, we will only
cover the \AgdaInductiveConstructor{`Num} cases of these
definitions. The old \AgdaDatatype{Type} definitions will work for the
other cases by replacing \AgdaDatatype{Type} with
\AgdaDatatype{Arith}, and by defining the following type synonym.

\begin{code}
  ⟦_⟧ : Arith → Set
  ⟦ A ⟧ = Fin (eval A)
\end{code}

The \AgdaInductiveConstructor{thereNum} case of
\AgdaDatatype{Path} can point somewhere deeper into a substructure of
the natural number contained by \AgdaInductiveConstructor{`Num} by
using a \AgdaDatatype{Pathℕ}.

\begin{code}
  data Path : Arith → Set where
    thereNum : {n : ℕ} → Pathℕ n → Path (`Num n)
\end{code}
    
\AgdaHide{
\begin{code}
    here : {A : Arith} → Path A
    thereΠ₁ : {A : Arith} {B : ⟦ A ⟧ → Arith}
      (i : Path A)
      → Path (`Π A B)
    thereΠ₂ : {A : Arith} {B : ⟦ A ⟧ → Arith}
      (f : (a : ⟦ A ⟧) → Path (B a))
      → Path (`Π A B)
\end{code}}

\AgdaHide{
\begin{code}
  Lookup : (A : Arith) → Path A → Set
\end{code}}


\AgdaHide{
\begin{code}
  Lookup A here = Arith
\end{code}}

The \AgdaInductiveConstructor{`Num} case of \AgdaFunction{Lookup}
results in a natural number.

\begin{code}
  Lookup (`Num n) (thereNum i) = ℕ
\end{code}

\AgdaHide{
\begin{code}
  Lookup (`Π A B) (thereΠ₂ f) = (a : ⟦ A ⟧) → Lookup (B a) (f a)
  Lookup (`Π A B) (thereΠ₁ i) = Lookup A i
\end{code}}

\AgdaHide{
\begin{code}
  lookup : (A : Arith) (i : Path A) → Lookup A i
\end{code}}

\AgdaHide{
\begin{code}
  lookup A here = A
\end{code}}

The \AgdaInductiveConstructor{`Num} case of \AgdaFunction{lookup}
continues to \AgdaFunction{lookupℕ} the number contained
inside. 

\begin{code}
  lookup (`Num n) (thereNum i) = lookupℕ n i
\end{code}

\AgdaHide{
\begin{code}
  lookup (`Π A B) (thereΠ₁ i) = lookup A i
  lookup (`Π A B) (thereΠ₂ f) = λ a → lookup (B a) (f a)
\end{code}}

\AgdaHide{
\begin{code}
  Update : (A : Arith) → Path A → Set
  update : (A : Arith) (i : Path A) (X : Update A i) → Arith
\end{code}}

\AgdaHide{
\begin{code}
  Update A here = Maybe Arith
\end{code}}

The \AgdaInductiveConstructor{`Num} case of \AgdaFunction{Update}
allows the user to supply a \AgdaDatatype{Maybe ℕ}, representing
either the identity update or a number to update with.

\begin{code}
  Update (`Num n) (thereNum i) = Maybe ℕ
\end{code}

\AgdaHide{
\begin{code}
  Update (`Π A B) (thereΠ₁ i) =
    Σ (Update A i) (λ X → ⟦ update A i X ⟧ → ⟦ A ⟧)
  Update (`Π A B) (thereΠ₂ f) =
    (a : ⟦ A ⟧) → Update (B a) (f a)
  
  update A here X = maybe id A X
\end{code}}

The \AgdaInductiveConstructor{`Num} case of \AgdaFunction{update}
leaves \AgdaInductiveConstructor{`Num} unchanged, but replaces the
natural number contained using \AgdaFunction{updateℕ}.

\begin{code}
  update (`Num n) (thereNum i) X = `Num (updateℕ n i X)
\end{code}

\AgdaHide{
\begin{code}
  update (`Π A B) (thereΠ₁ i) (X , f) =
    `Π (update A i X) (B ∘ f)
  update (`Π A B) (thereΠ₂ f) g =
    `Π A (λ a → update (B a) (f a) (g a))
\end{code}}


\section{Generic Open InfIR}
\label{sec:genericopen}

\AgdaHide{
\begin{code}
module GenericOpen where
\end{code}}

\subsection{\AgdaDatatype{Desc} \& \AgdaDatatype{μ}}

\begin{code}
  data Desc (O : Set) : Set₁ where
    End : (o : O) → Desc O
    Arg : (A : Set) (D : A → Desc O) → Desc O
    Rec : (A : Set) (D : (o : A → O) → Desc O) → Desc O
  
  Func : {O : Set} (D : Desc O) (X : Set) (Y : X → O) → Set
  Func (End o) X Y = ⊤
  Func (Arg A D) X Y = Σ A (λ a → Func (D a) X Y)
  Func (Rec A D) X Y = Σ (A → X) (λ f → Func (D (Y ∘ f)) X Y)
\end{code}

\begin{code}
  mutual
    data μ {O : Set} (D : Desc O) : Set where
      init : Func D (μ D) (rec D) → μ D
    
    rec : {O : Set} (D : Desc O) → μ D → O
    rec D (init xs) = recα D D xs
  
    recα : {O : Set} (D E : Desc O) → Func D (μ E) (rec E) → O
    recα (End o) E tt = o
    recα (Arg A D) E (a , xs) = recα (D a) E xs
    recα (Rec A D) E (f , xs) = recα (D (λ a → rec E (f a))) E xs
\end{code}

\subsection{\AgdaDatatype{Path}}

\begin{code}
  data Path {O : Set} (D : Desc O) : μ D → Set₁
  data Pathα {O : Set} (R : Desc O) : (D : Desc O) → Func D (μ R) (rec R) → Set₁
  
  data Path {O} D where
    here : {x : μ D} → Path D x
    there : {xs : Func D (μ D) (rec D)}
      → Pathα D D xs
      → Path D (init xs)
  
  data Pathα {O} R where
    thereArg₁ : {A : Set} {D : A → Desc O}
      {a : A} {xs : Func (D a) (μ R) (rec R)}
      → Pathα R (Arg A D) (a , xs)
    thereArg₂ : {A : Set} {D : A → Desc O}
      {a : A} {xs : Func (D a) (μ R) (rec R)}
      → Pathα R (D a) xs
      → Pathα R (Arg A D) (a , xs)
    thereRec₁ : {A : Set} {D : (o : A → O) → Desc O}
      {f : A → μ R} {xs : Func (D (rec R ∘ f)) (μ R) (rec R)}
      → ((a : A) → Path R (f a))
      → Pathα R (Rec A D) (f , xs)
    thereRec₂ : {A : Set} {D : (o : A → O) → Desc O}
      {f : A → μ R} {xs : Func (D (rec R ∘ f)) (μ R) (rec R)}
      → Pathα R (D (rec R ∘ f)) xs
      → Pathα R (Rec A D) (f , xs)
\end{code}

\subsection{\AgdaFunction{lookup}}

\begin{code}
  Lookup : {O : Set} (D : Desc O) (x : μ D) → Path D x → Set
  Lookupα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) → Pathα R D xs → Set
  
  Lookup D x here = μ D
  Lookup D (init xs) (there i) = Lookupα D D xs i
  
  Lookupα R (End o) tt ()
  Lookupα R (Arg A D) (a , xs) thereArg₁ = A
  Lookupα R (Arg A D) (a , xs) (thereArg₂ i) = Lookupα R (D a) xs i
  Lookupα R (Rec A D) (f , xs) (thereRec₁ g) = (a : A) → Lookup R (f a) (g a)
  Lookupα R (Rec A D) (f , xs) (thereRec₂ i) = Lookupα R (D (rec R ∘ f)) xs i
\end{code}

\begin{code}
  lookup : {O : Set} (D : Desc O) (x : μ D) (i : Path D x) → Lookup D x i
  lookupα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) (i : Pathα R D xs)
    → Lookupα R D xs i
  
  lookup D x here = x
  lookup D (init xs) (there i) = lookupα D D xs i
  
  lookupα R (End o) tt ()
  lookupα R (Arg A D) (a , xs) thereArg₁ = a
  lookupα R (Arg A D) (a , xs) (thereArg₂ i) = lookupα R (D a) xs i
  lookupα R (Rec A D) (f , xs) (thereRec₁ g) = λ a → lookup R (f a) (g a)
  lookupα R (Rec A D) (f , xs) (thereRec₂ i) = lookupα R (D (rec R ∘ f)) xs i
\end{code}

\subsection{\AgdaFunction{update}}

\begin{code}
  Update : {O : Set} (D : Desc O) (x : μ D) → Path D x → Set
  Updateα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) → Pathα R D xs → Set
  update : {O : Set} (D : Desc O) (x : μ D) (i : Path D x) (X : Update D x i) → μ D
  updateα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) (i : Pathα R D xs)
    → Updateα R D xs i → Func D (μ R) (rec R)
  
  Update D x here = Maybe (μ D)
  Update D (init xs) (there i) = Updateα D D xs i
  
  Updateα R (End o) tt ()
  Updateα R (Arg A D) (a , xs) thereArg₁ =
    Σ (Maybe A)
      (maybe (λ a' → Func (D a) (μ R) (rec R) → Func (D a') (μ R) (rec R)) ⊤)
  Updateα R (Arg A D) (a , xs) (thereArg₂ i) = Updateα R (D a) xs i
  Updateα R (Rec A D) (f , xs) (thereRec₁ g) =
    Σ ((a : A) → Update R (f a) (g a))
      (λ h → Func (D (rec R ∘ f)) (μ R) (rec R)
        → Func (D (λ a → rec R (update R (f a) (g a) (h a)))) (μ R) (rec R))
  Updateα R (Rec A D) (f , xs) (thereRec₂ i) =
    Updateα R (D (rec R ∘ f)) xs i
  
  update D x here X = maybe id x X
  update D (init xs) (there i) X = init (updateα D D xs i X)
  
  updateα R (End o) tt () X
  updateα R (Arg A D) (a , xs) thereArg₁ (nothing , f) = a , xs
  updateα R (Arg A D) (a , xs) thereArg₁ (just X , f) =
    X , f xs
  updateα R (Arg A D) (a , xs) (thereArg₂ i) X =
    a , updateα R (D a) xs i X
  updateα R (Rec A D) (f , xs) (thereRec₁ g) (h , F) =
    (λ a → update R (f a) (g a) (h a)) , F xs
  updateα R (Rec A D) (f , xs) (thereRec₂ i) X =
    f , updateα R (D (rec R ∘ f)) xs i X
\end{code}


\section{Generic Closed InfIR}
\label{sec:genericclosed}

\AgdaHide{
\begin{code}
module GenericClosed where

  data Desc (O : Set) : Set₁ where
    End : (o : O) → Desc O
    Arg : (A : Set) (D : A → Desc O) → Desc O
    Rec : (A : Set) (D : (o : A → O) → Desc O) → Desc O
  
  Func : {O : Set} (D : Desc O) (X : Set) (Y : X → O) → Set
  Func (End o) X Y = ⊤
  Func (Arg A D) X Y = Σ A (λ a → Func (D a) X Y)
  Func (Rec A D) X Y = Σ (A → X) (λ f → Func (D (Y ∘ f)) X Y)
  
  mutual
    data μ {O : Set} (D : Desc O) : Set where
      init : Func D (μ D) (rec D) → μ D
    
    rec : {O : Set} (D : Desc O) → μ D → O
    rec D (init xs) = recα D D xs
  
    recα : {O : Set} (D E : Desc O) → Func D (μ E) (rec E) → O
    recα (End o) E tt = o
    recα (Arg A D) E (a , xs) = recα (D a) E xs
    recα (Rec A D) E (f , xs) = recα (D (λ a → rec E (f a))) E xs
\end{code}}

\subsection{\AgdaDatatype{`Set} \& \AgdaDatatype{`Desc}}

\begin{code}
  mutual
    data `Set : Set where
      `⊥ `⊤ `Bool : `Set
      `Σ `Π : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
      `μ : {O : `Set} (D : `Desc O) → `Set
  
    ⟦_⟧ : `Set → Set
    ⟦ `⊥ ⟧ = ⊥
    ⟦ `⊤ ⟧ = ⊤
    ⟦ `Bool ⟧ = Bool
    ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)
    ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
    ⟦ `μ D ⟧ = μ ⟪ D ⟫
  
    data `Desc (O : `Set) : Set where
      `End : (o : ⟦ O ⟧) → `Desc O
      `Arg : (A : `Set) (D : ⟦ A ⟧ → `Desc O) → `Desc O
      `Rec : (A : `Set) (D : (o : ⟦ A ⟧ → ⟦ O ⟧) → `Desc O) → `Desc O
  
    ⟪_⟫ : {O : `Set} → `Desc O → Desc ⟦ O ⟧
    ⟪ `End o ⟫ = End o
    ⟪ `Arg A D ⟫ = Arg ⟦ A ⟧ λ a → ⟪ D a ⟫
    ⟪ `Rec A D ⟫ = Rec ⟦ A ⟧ λ o → ⟪ D o ⟫
\end{code}

\subsection{\AgdaDatatype{Path}}

\begin{code}
  data Path : (A : `Set) → ⟦ A ⟧ → Set
  data Pathα {O : `Set} (R : `Desc O) : (D : `Desc O) → Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫) → Set
  
  data Path where
    here : {A : `Set} {a : ⟦ A ⟧} → Path A a
    thereΣ₁ : {A : `Set} {B : ⟦ A ⟧ → `Set} {a : ⟦ A ⟧} {b : ⟦ B a ⟧}
      → Path A a
      → Path (`Σ A B) (a , b)
    thereΣ₂ : {A : `Set} {B : ⟦ A ⟧ → `Set} {a : ⟦ A ⟧} {b : ⟦ B a ⟧}
      → Path (B a) b
      → Path (`Σ A B) (a , b)
    thereΠ : {A : `Set} {B : ⟦ A ⟧ → `Set} {f : (a : ⟦ A ⟧) → ⟦ B a ⟧}
      → ((a : ⟦ A ⟧) → Path (B a) (f a))
      → Path (`Π A B) f
    thereμ : {O : `Set} {D : `Desc O} {xs : Func ⟪ D ⟫ (μ ⟪ D ⟫) (rec ⟪ D ⟫)}
      → Pathα D D xs
      → Path (`μ D) (init xs)
  
  data Pathα {O} R where
    thereArg₁ : {A : `Set} {D : ⟦ A ⟧ → `Desc O}
      {a : ⟦ A ⟧} {xs : Func ⟪ D a ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)}
      → Path A a
      → Pathα R (`Arg A D) (a , xs)
    thereArg₂ : {A : `Set} {D : ⟦ A ⟧ → `Desc O}
      {a : ⟦ A ⟧} {xs : Func ⟪ D a ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)}
      → Pathα R (D a) xs
      → Pathα R (`Arg A D) (a , xs)
    thereRec₁ : {A : `Set} {D : (o : ⟦ A ⟧ → ⟦ O ⟧) → `Desc O}
      {f : ⟦ A ⟧ → μ ⟪ R ⟫} {xs : Func ⟪ D (rec ⟪ R ⟫ ∘ f) ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)}
      → ((a : ⟦ A ⟧) → Path (`μ R) (f a))
      → Pathα R (`Rec A D) (f , xs)
    thereRec₂ : {A : `Set} {D : (o : ⟦ A ⟧ → ⟦ O ⟧) → `Desc O}
      {f : ⟦ A ⟧ → μ ⟪ R ⟫} {xs : Func ⟪ D (rec ⟪ R ⟫ ∘ f) ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)}
      → Pathα R (D (rec ⟪ R ⟫ ∘ f)) xs
      → Pathα R (`Rec A D) (f , xs)
\end{code}

\subsection{\AgdaFunction{lookup}}

\begin{code}
  Lookup : (A : `Set) (a : ⟦ A ⟧) → Path A a → Set
  Lookupα : {O : `Set} (R D : `Desc O) (xs : Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
    → Pathα R D xs → Set
  
  Lookup A a here = ⟦ A ⟧
  Lookup (`Σ A B) (a , b) (thereΣ₁ i) = Lookup A a i
  Lookup (`Σ A B) (a , b) (thereΣ₂ i) = Lookup (B a) b i
  Lookup (`Π A B) f (thereΠ g) = (a : ⟦ A ⟧) → Lookup (B a) (f a) (g a)
  Lookup (`μ D) (init xs) (thereμ i) = Lookupα D D xs i
  
  Lookupα R (`Arg A D) (a , xs) (thereArg₁ i) = Lookup A a i
  Lookupα R (`Arg A D) (a , xs) (thereArg₂ i) = Lookupα R (D a) xs i
  Lookupα R (`Rec A D) (f , xs) (thereRec₁ g) = (a : ⟦ A ⟧) → Lookup (`μ R) (f a) (g a)
  Lookupα R (`Rec A D) (f , xs) (thereRec₂ i) = Lookupα R (D (rec ⟪ R ⟫ ∘ f)) xs i
\end{code}

\begin{code}
  lookup : (A : `Set) (a : ⟦ A ⟧) (i : Path A a) → Lookup A a i
  lookupα : {O : `Set} (R D : `Desc O) (xs : Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
    (i : Pathα R D xs) → Lookupα R D xs i
  
  lookup A a here = a
  lookup (`Σ A B) (a , b) (thereΣ₁ i) = lookup A a i
  lookup (`Σ A B) (a , b) (thereΣ₂ i) = lookup (B a) b i
  lookup (`Π A B) f (thereΠ g) = λ a → lookup (B a) (f a) (g a)
  lookup (`μ D) (init xs) (thereμ i) = lookupα D D xs i
  
  lookupα R (`Arg A D) (a , xs) (thereArg₁ i) = lookup A a i
  lookupα R (`Arg A D) (a , xs) (thereArg₂ i) = lookupα R (D a) xs i
  lookupα R (`Rec A D) (f , xs) (thereRec₁ g) = λ a → lookup (`μ R) (f a) (g a)
  lookupα R (`Rec A D) (f , xs) (thereRec₂ i) = lookupα R (D (rec ⟪ R ⟫ ∘ f)) xs i
\end{code}

\subsection{\AgdaFunction{update}}

\begin{code}
  Update : (A : `Set) (a : ⟦ A ⟧) → Path A a → Set
  Updateα : {O : `Set} (R D : `Desc O) (xs : Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
    → Pathα R D xs → Set
  update : (A : `Set) (a : ⟦ A ⟧) (i : Path A a)
    → Update A a i → ⟦ A ⟧
  updateα : {O : `Set} (R D : `Desc O) (xs : Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
    (i : Pathα R D xs)
    → Updateα R D xs i
    → Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)
  
  Update A a here = Maybe ⟦ A ⟧
  Update (`Σ A B) (a , b) (thereΣ₁ i) =
    Σ (Update A a i) (λ a' → ⟦ B a ⟧ → ⟦ B (update A a i a') ⟧)
  Update (`Σ A B) (a , b) (thereΣ₂ i) = Update (B a) b i
  Update (`Π A B) f (thereΠ g) = (a : ⟦ A ⟧) → Update (B a) (f a) (g a)
  Update (`μ D) (init xs) (thereμ i) = Updateα D D xs i
  
  Updateα R (`Arg A D) (a , xs) (thereArg₁ i) =
    Σ (Update A a i)
      (λ a' → Func ⟪ D a ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫) → Func ⟪ D (update A a i a') ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
  Updateα R (`Arg A D) (a , xs) (thereArg₂ i) = Updateα R (D a) xs i
  Updateα R (`Rec A D) (f , xs) (thereRec₁ g) =
    Σ ((a : ⟦ A ⟧) → Update (`μ R) (f a) (g a))
      (λ h → Func ⟪ D (λ a → rec ⟪ R ⟫ (f a)) ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)
        → Func ⟪ D (λ a → rec ⟪ R ⟫ (update (`μ R) (f a) (g a) (h a))) ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)
      )
  Updateα R (`Rec A D) (f , xs) (thereRec₂ i) = Updateα R (D (rec ⟪ R ⟫ ∘ f)) xs i
  
  update A a here X = maybe id a X
  update (`Σ A B) (a , b) (thereΣ₁ i) (X , f) = update A a i X , f b
  update (`Σ A B) (a , b) (thereΣ₂ i) X = a , update (B a) b i X
  update (`Π A B) f (thereΠ g) h = λ a → update (B a) (f a) (g a) (h a)
  update (`μ D) (init xs) (thereμ i) X = init (updateα D D xs i X)
  
  updateα R (`Arg A D) (a , xs) (thereArg₁ i) (X , f) = update A a i X , f xs
  updateα R (`Arg A D) (a , xs) (thereArg₂ i) X = a , updateα R (D a) xs i X
  updateα R (`Rec A D) (f , xs) (thereRec₁ g) (h , F) =
    (λ a → update (`μ R) (f a) (g a) (h a)) , F xs
  updateα R (`Rec A D) (f , xs) (thereRec₂ i) X =
    f , updateα R (D (rec ⟪ R ⟫ ∘ f)) xs i X
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
