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
      `Nat : Type
      `Fun : (A : Type) (B : ⟦ A ⟧ → Type) → Type
    
    ⟦_⟧ : Type → Set
    ⟦ `Nat ⟧ = ℕ
    ⟦ `Fun A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
\end{code}

\AgdaHide{
\begin{code}
  _`→_ : (A B : Type) → Type
  A `→ B = `Fun A (λ _ → B)
\end{code}}

\noindent
This \AgdaDatatype{Type} is \emph{infinitary} because the
\AgdaInductiveConstructor{`Fun} constructor's second inductive argument
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
  NumArgs zero = `Nat
  NumArgs (suc n) = `Nat `→ NumArgs n
  
  NumFun : Type
  NumFun = `Fun `Nat NumArgs
\end{code}

While defining models and example values using infinitary
inductive-recursive types is common, writing inductively defined
\textit{functions} over them is not.

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

Our \emph{primary contribution} is to show how to write common
operations over infinitary
inductive-recursive types (such as \AgdaDatatype{Type} universes), and
then generalize those operations from functions over concrete
datatypes to generic functions over any user-defined
datatype. More specifically, our contributions are the following:

\todo[inline]{Reference sections and concrete large vs small}
\begin{itemize}
\item Index types (\AgdaDatatype{Path}s) for concrete, open universe,
  and closed universe InfIR types.
\item A \AgdaFunction{lookup} function with a heterogeneous return
  type for concrete, open universe, and closed universe InfIR types.
\item An \AgdaFunction{update} function with a heterogeneous type for
  the value to update with, for concrete, open universe,
  and closed universe InfIR types.
\item A model of a closed universe of small InfIR types.
\end{itemize}

Finally, we hope that seeing examples of writing both concrete and generic
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

In the (tranditionally) non-dependent Haskell~\cite{TODO} language there are two
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
left side (domain) of a \AgdaInductiveConstructor{`Fun} is easy, but
looking up something in the right side (codomain) requires entering a
function space.

Figuring out how to write functions like \AgdaFunction{lookup} (and more
complicated functions) over InfIR types is the subject of this
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

\begin{code}
  head₁ : {A : Set} → List A → A → A
  head₁ nil y = y
  head₁ (cons x xs) y = x
\end{code}

\item Change the codomain, for example by returning a
  \AgdaDatatype{Maybe} result.

\begin{code}
  head₂ : {A : Set} → List A → Maybe A
  head₂ nil = nothing
  head₂ (cons x xs) = just x
\end{code}

\end{enumerate}

Both options give us something to do when we apply
\AgdaFunction{head} to an empty list: either get an extra argument to
return, or we simply return
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
the \AgdaInductiveConstructor{`Base} types are parameters (of type \AgdaDatatype{Set}) instead of being hardcoded to
\AgdaDatatype{ℕ}.

\begin{code}
  mutual
    data Type : Set₁ where
      `Base : Set → Type
      `Fun : (A : Type) (B : ⟦ A ⟧ → Type) → Type
  
    ⟦_⟧ : Type → Set
    ⟦ `Base A ⟧ = A
    ⟦ `Fun A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
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
\AgdaInductiveConstructor{`Fun}, but going right requires first knowing
which element \AgdaBound{a} of the type family \AgdaBound{B a} to
continue traversing under. This requirement is neatly captured as a
dependent function type of the \AgdaBound{f} argument below.

\begin{code}
  data Path : Type → Set₁ where
    here : ∀{A} → Path A
    thereBase : ∀{A} → Path (`Base A)
    thereFun₁ : ∀{A B}
      (i : Path A)
      → Path (`Fun A B)
    thereFun₂ : ∀{A B}
      (f : (a : ⟦ A ⟧) → Path (B a))
      → Path (`Fun A B)
\end{code}

Above, \AgdaInductiveConstructor{thereFun₂} represents going right
into the codomain of \AgdaInductiveConstructor{`Fun}, but only once the
user tells you which \AgdaBound{a} to use. In a sense, going right is
like asking for a continuation that tells you where to go next, once
you have been given \AgdaBound{a}. Also note that because the argument
\AgdaBound{f} of \AgdaInductiveConstructor{thereFun₂} is a function that
returns a \AgdaDatatype{Path}, the \AgdaDatatype{Path} datatype is
infinitary (just like the \AgdaDatatype{Type} it indexes).

\subsection{\AgdaFunction{lookup}}

We were able to write a total function to \AgdaFunction{lookup} any
sub\AgdaDatatype{Tree}, but \AgdaFunction{lookup}ing up a
sub\AgdaDatatype{Type} is not always possible. Using the methodology
from \refsec{problem:total}, we can make \AgdaFunction{lookup} for
\AgdaDatatype{Type}s total by choosing to change the codomain,
depending on the input \AgdaDatatype{Type} and \AgdaDatatype{Path}.
\AgdaFunction{Lookup} computes the codomain of
\AgdaFunction{lookup}, asking for a \AgdaDatatype{Type} or \AgdaDatatype{Set} in the base
cases, or a continuation when looking to the right of a
\AgdaInductiveConstructor{`Fun}.

\begin{code}
  Lookup : (A : Type) → Path A → Set₁
  Lookup A here = Type
  Lookup (`Base A) thereBase = Set
  Lookup (`Fun A B) (thereFun₁ i) = Lookup A i
  Lookup (`Fun A B) (thereFun₂ f) = (a : ⟦ A ⟧) → Lookup (B a) (f a)
\end{code}

Finally, we can write \AgdaFunction{lookup} in terms of
\AgdaDatatype{Path} and \AgdaFunction{Lookup}. Notice that users
applying our \AgdaFunction{lookup} function need to supply
extra \AgdaBound{a} arguments exactly when they go to the right of a
\AgdaInductiveConstructor{`Fun}. Thus, our definition can expect an
extra argument \AgdaBound{a} in the
\AgdaInductiveConstructor{thereFun₂} case.

\begin{code}
  lookup : (A : Type) (i : Path A) → Lookup A i
  lookup A here = A
  lookup (`Base A) thereBase = A
  lookup (`Fun A B) (thereFun₁ i) = lookup A i
  lookup (`Fun A B) (thereFun₂ f) = λ a → lookup (B a) (f a)
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
We might expect to write a function like:

\todo[inline]{explain using Maybe nothing to update one path of a type
family}

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
a \AgdaInductiveConstructor{`Fun}.

We call the type of the substitute
\AgdaFunction{Update}, which asks for a \AgdaDatatype{Maybe Type} or a
\AgdaDatatype{Maybe Set} in the base cases (\AgdaInductiveConstructor{here}
and \AgdaInductiveConstructor{thereBase} respectively), and a continuation in the
\AgdaInductiveConstructor{thereFun₂} case. However, updating an element to
the left of a \AgdaInductiveConstructor{`Fun} is also
problematic. We would like to keep the old
\AgdaInductiveConstructor{`Fun} codomain \AgdaBound{B} unchanged, but it
still expects an \AgdaBound{a} of the original type
\AgdaFunction{⟦} \AgdaBound{A} \AgdaFunction{⟧}. Therefore, the
\AgdaInductiveConstructor{thereFun₁} case must
ask for a forgetful function \AgdaBound{f} that maps newly
updated \AgdaBound{a}'s to their original type.

\todo[inline]{Give an example of the domain type changing and being translated}

\begin{code}
  Update : (A : Type) → Path A → Set₁
  update : (A : Type) (i : Path A) (X : Update A i) → Type
  
  Update A here = Maybe Type
  Update (`Base A) thereBase = Maybe Set
  Update (`Fun A B) (thereFun₁ i) =
    Σ (Update A i) (λ X → ⟦ update A i X ⟧ → ⟦ A ⟧)
  Update (`Fun A B) (thereFun₂ f) =
    (a : ⟦ A ⟧) → Update (B a) (f a)
  
  update A here X = maybe id A X
  update (`Base A) thereBase X = maybe `Base (`Base A) X
  update (`Fun A B) (thereFun₁ i) (X , f) =
    `Fun (update A i X) (λ a → B (f a))
  update (`Fun A B) (thereFun₂ f) h =
    `Fun A (λ a → update (B a) (f a) (h a))
\end{code}

Notice that we must define \AgdaFunction{Update} and
\AgdaFunction{update} mutually, because the forgetful
function \AgdaBound{f} (the codomain of
\AgdaDatatype{Σ} in the \AgdaInductiveConstructor{thereFun₁} case of
\AgdaFunction{Update}) must refer to \AgdaFunction{update} in its
domain. Although the \AgdaInductiveConstructor{thereFun₁} case of
\AgdaFunction{update} only updates the domain of
\AgdaInductiveConstructor{`Fun}, the type family \AgdaBound{B} in the
codomain expects an \AgdaBound{a} of type
\AgdaFunction{⟦} \AgdaBound{A} \AgdaFunction{⟧}, so we use the
forgetful function \AgdaBound{f} to map back to \AgdaBound{a}'s
original type.

The base cases (\AgdaInductiveConstructor{here} and
\AgdaInductiveConstructor{thereBase}) of \AgdaFunction{update}
perform updates using the
subsitute \AgdaBound{X} (where \AgdaInductiveConstructor{nothing}
results in an identity update). The \AgdaInductiveConstructor{thereFun₂}
case of \AgdaFunction{update} leaves the domain of
\AgdaInductiveConstructor{`Fun} unchanged, and recursively updates the
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
      `Prod : (a : Arith) (f : Fin (eval a) → Arith) → Arith
  
    eval : Arith → ℕ
    eval (`Num n) = n
    eval (`Prod a f) = prod (eval a)
      λ a → prod (toℕ a) λ b → eval (f (inject b))
\end{code}

Values of type \AgdaDatatype{Arith} encode ``Big Pi''
mathematical arithmetic product equations up to some finite
bound, such as the one below.

\begin{equation*}
  \prod_{i=1}^{3} i
\end{equation*}

\begin{code}
    six : Arith
    six = `Prod (`Num 3) (λ i → `Num (toℕ i))
\end{code}


An \AgdaDatatype{Arith} equation may be nested in its upper bound or body, but the lower
bound is always the value 1.
The \AgdaFunction{eval} function interprets the equation as a
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
For this reason, we need the \AgdaDatatype{Pathℕ}, \AgdaFunction{lookupℕ},
and \AgdaFunction{updateℕ} definitions for natural numbers.

\AgdaDatatype{Pathℕ} is an index into the number, which can point to
that number or any smaller number. It is different from the standard
finite set type \AgdaDatatype{Fin} because the number pointed to may
be \AgdaInductiveConstructor{zero}.

\begin{code}
  data Pathℕ : ℕ → Set where
    here : {n : ℕ} → Pathℕ n
    there : {n : ℕ}
      (i : Pathℕ n)
      → Pathℕ (suc n)
\end{code}

The \AgdaFunction{lookup} function simply returns the
\AgdaDatatype{ℕ} pointed to by \AgdaDatatype{Pathℕ}. It has a static
return type (not a computational return type), because a
\AgdaDatatype{Pathℕ} always points to a \AgdaDatatype{ℕ}.

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
\AgdaFunction{update} definitions for \AgdaDatatype{Arith} are
nearly structurally identical to the corresponding definitions for
\AgdaDatatype{Type} from \refsec{concretelarge}. Thus, we will only
cover the \AgdaInductiveConstructor{`Num} cases of these
definitions. The old \AgdaDatatype{Type} definitions will work for the
other cases by replacing \AgdaDatatype{Type} with
\AgdaDatatype{Arith},
\AgdaInductiveConstructor{`Fun} with \AgdaInductiveConstructor{`Prod},
and by defining the following type synonym.

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
    here : ∀{A} → Path A
    thereFun₁ : ∀{A B}
      (i : Path A)
      → Path (`Prod A B)
    thereFun₂ : ∀{A B}
      (f : (a : ⟦ A ⟧) → Path (B a))
      → Path (`Prod A B)
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
  Lookup (`Prod A B) (thereFun₂ f) = (a : ⟦ A ⟧) → Lookup (B a) (f a)
  Lookup (`Prod A B) (thereFun₁ i) = Lookup A i
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
  lookup (`Prod A B) (thereFun₁ i) = lookup A i
  lookup (`Prod A B) (thereFun₂ f) = λ a → lookup (B a) (f a)
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
  Update (`Prod A B) (thereFun₁ i) =
    Σ (Update A i) (λ X → ⟦ update A i X ⟧ → ⟦ A ⟧)
  Update (`Prod A B) (thereFun₂ f) =
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
  update (`Prod A B) (thereFun₁ i) (X , f) =
    `Prod (update A i X) (B ∘ f)
  update (`Prod A B) (thereFun₂ f) g =
    `Prod A (λ a → update (B a) (f a) (g a))
\end{code}}


\section{Generic Open InfIR}
\label{sec:genericopen}

\AgdaHide{
\begin{code}
module GenericOpen where
\end{code}}

In this section we develop generic versions of the datatypes and
functions from previous sections, for any datatype encoded as an
inductive-recursive Dybjer-Setzer code~\cite{TODO}.

\subsection{\AgdaDatatype{Desc}}

First let us recall the type of datatype inductive-recursive codes
developed by Dybjer and Setzer. We refer to values of
\AgdaDatatype{Desc} defined below as ``codes''.
\footnote{
  We have renamed the original Dybjer-Setzer constructions to
  emphasize their meaning in English. The original names of our
  \AgdaDatatype{Desc}/\AgdaInductiveConstructor{End}/\AgdaInductiveConstructor{Arg}/\AgdaInductiveConstructor{Rec}
  constructions are
  \AgdaDatatype{IR}/\AgdaInductiveConstructor{$\iota$}/\AgdaInductiveConstructor{$\sigma$}/\AgdaInductiveConstructor{$\delta$}
  respectively.
  }
A code simultaneously
encodes the definition for a datatype, and a function mutually
defined with it.

\begin{code}
  data Desc (O : Set) : Set₁ where
    End : (o : O) → Desc O
    Arg : (A : Set) (D : (a : A) → Desc O) → Desc O
    Rec : (A : Set) (D : (o : A → O) → Desc O) → Desc O  
\end{code}

To a first approximation, a datatype \AgdaDatatype{Desc}ription
encodes the type signature of a single constructor, and the value
returned by the case of that constructor for the mutually defined
function. \AgdaInductiveConstructor{End} is used to specify that a
constructor takes no further arguments. However, the user must supply
a value \AgdaBound{o} of type \AgdaBound{O} to define the value returned by the
mutually defined function. \AgdaInductiveConstructor{Arg} is used to
specify a non-recursive argument of a constructor, \AgdaBound{a} of
type \AgdaBound{A}, and the remainder of the \AgdaDatatype{Desc} may depend
on the value \AgdaBound{a}. \AgdaInductiveConstructor{Rec} is used to
specify a recursive argument (of the type currently being
specified). More generally, the recursive argument may be a function
type whose codomain is the type currently being defined but whose
domain may be non-recursive.
\footnote{
  The domain is restricted to be non-recursive to enforce that encoded
  datatypes are strictly positive.
}
Above, the domain of the function is some non-recursive type
\AgdaBound{A}, and the remainder of the \AgdaDatatype{Desc} may depend
on a function \AgdaBound{o} from \AgdaBound{A} to \AgdaBound{O},
representing the result of applying the mutually defined function to
the recursive argument being specified.

Finally, to encode multiple constructors as a \AgdaDatatype{Desc}, you
simply define an \AgdaInductiveConstructor{Arg} whose domain is a
finite enumeration of types (representing each constructor), and whose
codomain is the \AgdaDatatype{Desc} corresponding to the arguments and
recursive cases for each constructor.

The abstract nature of \AgdaDatatype{Desc} makes it somewhat difficult
to understand at first, especially the \AgdaInductiveConstructor{Rec}
constructor. Let's try to understand \AgdaDatatype{Desc} better with an
example, encoding \AgdaDatatype{Arith} from
\refsec{concretesmall} below .

\AgdaHide{
\begin{code}
  postulate prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
\end{code}}

\begin{code}
  data ArithT : Set where
    NumT ProdT : ArithT

  ArithD : Desc ℕ
  ArithD = Arg ArithT λ
    { NumT → Arg ℕ (λ n → End n)
    ; ProdT
      → Rec ⊤ λ n
      → Rec (Fin (n tt)) λ f
      → End (prod (n tt) f)
    }
\end{code}

The \AgdaDatatype{Desc} begins with an \AgdaInductiveConstructor{Arg},
taking sub-\AgdaDatatype{Desc}s for each element of the finite
enumeration \AgdaDatatype{ArithT}, representing the types of each
\AgdaDatatype{Arith} constructor.

The \AgdaInductiveConstructor{NumT} description uses
\AgdaInductiveConstructor{Arg} to take a natural number
(\AgdaDatatype{ℕ}), then \AgdaInductiveConstructor{End}s with that number. Ending with that
number encodes that the \AgdaInductiveConstructor{`Num} case of the
\AgdaFunction{eval} from \refsec{concretesmall} returns the number held
by \AgdaInductiveConstructor{`Num} in the base case.

The \AgdaInductiveConstructor{ProdT} description uses
\AgdaInductiveConstructor{Rec} twice, taking two recursive
arguments. The first recursive argument is intended to encode an
\AgdaDatatype{Arith} rather than a function type, so we
make its domain a value of the trivial type \AgdaDatatype{⊤}. The
second recursive argument is intended to encode a function from
\AgdaDatatype{Fin} \AgdaBound{n} to \AgdaDatatype{Arith}, so we ask
for a \AgdaDatatype{Fin} (\AgdaBound{n}
\AgdaInductiveConstructor{tt}), where \AgdaBound{n} represents the
value returned by applying \AgdaFunction{eval} to the first recursive
argument. In fact, \AgdaBound{n} represents a function from the
trivial type \AgdaDatatype{⊤} to \AgdaDatatype{ℕ}, because first-order
recursive arguments are encoded as higher-order arguments with a
trivial domain. Finally, \AgdaInductiveConstructor{End} is used to
specify that there are no further arguments, and the
\AgdaInductiveConstructor{`Prod} case of \AgdaFunction{eval} should
result in the \AgdaFunction{prod}uct represented by the first two
recursive arguments.

\subsection{\AgdaDatatype{Data}}

Previously we used \AgdaDatatype{Desc} to encode a datatype and its
mutual function. Applying \AgdaDatatype{Data} to a description results
in the datatype it encodes, and applying \AgdaFunction{fun} to a
description results in the mutual function it encodes.

\AgdaHide{
\begin{code}
  mutual
\end{code}}

\AgdaDatatype{Data} is defined in terms of a single constructor
\AgdaInductiveConstructor{con}, which holds a dependent product of all
arguments of a particular constructor. The computational argument type
\AgdaFunction{Data′} encodes the type of this product, dependent on
the \AgdaDatatype{Desc}ription that \AgdaDatatype{Data} is
parameterized by.

For the remainder of the paper, we will establish a convention for
functions ending with a prime, like \AgdaFunction{Data′}. They will be
defined by induction over a description, but must also reference the
original description they are inducting over in the base case. Hence,
they take two \AgdaDatatype{Desc} arguments, where the first
\AgdaBound{R} is the original description (to be used in
\AgdaInductiveConstructor{Rec}ursive cases), and the second
\AgdaBound{D} is the one we induct over.

\begin{code}
    data Data {O : Set} (D : Desc O) : Set where
      con : Data′ D D → Data D

    Data′ : {O : Set} (R D : Desc O) → Set
    Data′ R (End o) = ⊤
    Data′ R (Arg A D) = Σ A (λ a → Data′ R (D a))
    Data′ R (Rec A D) = Σ (A → Data R) (λ f → Data′ R (D (fun R ∘ f)))
\end{code}

The \AgdaInductiveConstructor{End} case means no further arguments are
needed, so we ask for a trivial value of type \AgdaDatatype{⊤}. The
\AgdaInductiveConstructor{Arg} case asks for a value of type
\AgdaBound{A}, which the rest of the arguments may depend on using
\AgdaBound{a}. The \AgdaInductiveConstructor{End} case asks for a function from
\AgdaBound{A} to a recursive value \AgdaDatatype{Data} \AgdaBound{R},
and the rest of the arguments may use \AgdaBound{f} to depend on the
result of applying the mutual function (e.g. \AgdaFunction{eval}) to
the recursive argument after applying a value of type \AgdaBound{A}.

Next we define \AgdaFunction{fun} (encoding the mutual function) in
terms of \AgdaFunction{fun′}.

\begin{code}
    fun : {O : Set} (D : Desc O) → Data D → O
    fun D (con xs) = fun′ D D xs
  
    fun′ : {O : Set} (R D : Desc O) → Data′ R D → O
    fun′ R (End o) tt = o
    fun′ R (Arg A D) (a , xs) = fun′ R (D a) xs
    fun′ R (Rec A D) (f , xs) = fun′ R (D (λ a → fun R (f a))) xs
\end{code}

The \AgdaInductiveConstructor{End} case gives us what we want, the
value \AgdaBound{o} that the mutual function should return for the
encoded constructor case. The \AgdaInductiveConstructor{Arg} and
\AgdaInductiveConstructor{Rec} cases recurse, looking for an
\AgdaInductiveConstructor{End}.

\subsection{\AgdaDatatype{Path}}

\begin{code}
  mutual
    data Path {O : Set} (D : Desc O) : Data D → Set₁ where
      here : ∀{x} → Path D x
      there : ∀{xs}
        → Path′ D D xs
        → Path D (con xs)
    
    data Path′ {O : Set} (R : Desc O) : (D : Desc O) → Data′ R D → Set₁ where
      thereArg₁ : ∀{A D a xs}
        → Path′ R (Arg A D) (a , xs)
      thereArg₂ : ∀{A D a xs}
        (i : Path′ R (D a) xs)
        → Path′ R (Arg A D) (a , xs)
      thereRec₁ : ∀{A D f xs}
        (g : (a : A) → Path R (f a))
        → Path′ R (Rec A D) (f , xs)
      thereRec₂ : ∀{A D f xs}
        (i : Path′ R (D (fun R ∘ f)) xs)
        → Path′ R (Rec A D) (f , xs)
\end{code}

\subsection{\AgdaDatatype{lookup}}

\begin{code}
  Lookup : {O : Set} (D : Desc O) (x : Data D) → Path D x → Set
  Lookup′ : {O : Set} (R D : Desc O) (xs : Data′ R D) → Path′ R D xs → Set
  
  Lookup D x here = Data D
  Lookup D (con xs) (there i) = Lookup′ D D xs i
  
  Lookup′ R (End o) tt ()
  Lookup′ R (Arg A D) (a , xs) thereArg₁ = A
  Lookup′ R (Arg A D) (a , xs) (thereArg₂ i) = Lookup′ R (D a) xs i
  Lookup′ R (Rec A D) (f , xs) (thereRec₁ g) = (a : A) → Lookup R (f a) (g a)
  Lookup′ R (Rec A D) (f , xs) (thereRec₂ i) = Lookup′ R (D (fun R ∘ f)) xs i
\end{code}

\begin{code}
  lookup : {O : Set} (D : Desc O) (x : Data D) (i : Path D x) → Lookup D x i
  lookup′ : {O : Set} (R D : Desc O) (xs : Data′ R D) (i : Path′ R D xs)
    → Lookup′ R D xs i
  
  lookup D x here = x
  lookup D (con xs) (there i) = lookup′ D D xs i
  
  lookup′ R (End o) tt ()
  lookup′ R (Arg A D) (a , xs) thereArg₁ = a
  lookup′ R (Arg A D) (a , xs) (thereArg₂ i) = lookup′ R (D a) xs i
  lookup′ R (Rec A D) (f , xs) (thereRec₁ g) = λ a → lookup R (f a) (g a)
  lookup′ R (Rec A D) (f , xs) (thereRec₂ i) = lookup′ R (D (fun R ∘ f)) xs i
\end{code}

\subsection{\AgdaDatatype{update}}

\begin{code}
  Update : {O : Set} (D : Desc O) (x : Data D) → Path D x → Set
  Update′ : {O : Set} (R D : Desc O) (xs : Data′ R D) → Path′ R D xs → Set
  update : {O : Set} (D : Desc O) (x : Data D) (i : Path D x) (X : Update D x i) → Data D
  update′ : {O : Set} (R D : Desc O) (xs : Data′ R D) (i : Path′ R D xs)
    → Update′ R D xs i → Data′ R D
  
  Update D x here = Maybe (Data D)
  Update D (con xs) (there i) = Update′ D D xs i
  
  Update′ R (End o) tt ()
  Update′ R (Arg A D) (a , xs) thereArg₁ =
    Σ (Maybe A)
      (maybe (λ a' → Data′ R (D a) → Data′ R (D a')) ⊤)
  Update′ R (Arg A D) (a , xs) (thereArg₂ i) = Update′ R (D a) xs i
  Update′ R (Rec A D) (f , xs) (thereRec₁ g) =
    Σ ((a : A) → Update R (f a) (g a))
      (λ h → Data′ R (D (fun R ∘ f))
        → Data′ R (D (λ a → fun R (update R (f a) (g a) (h a)))))
  Update′ R (Rec A D) (f , xs) (thereRec₂ i) =
    Update′ R (D (fun R ∘ f)) xs i
  
  update D x here X = maybe id x X
  update D (con xs) (there i) X = con (update′ D D xs i X)
  
  update′ R (End o) tt () X
  update′ R (Arg A D) (a , xs) thereArg₁ (nothing , f) = a , xs
  update′ R (Arg A D) (a , xs) thereArg₁ (just X , f) =
    X , f xs
  update′ R (Arg A D) (a , xs) (thereArg₂ i) X =
    a , update′ R (D a) xs i X
  update′ R (Rec A D) (f , xs) (thereRec₁ g) (h , F) =
    (λ a → update R (f a) (g a) (h a)) , F xs
  update′ R (Rec A D) (f , xs) (thereRec₂ i) X =
    f , update′ R (D (fun R ∘ f)) xs i X
\end{code}


\section{Generic Closed InfIR}
\label{sec:genericclosed}

\AgdaHide{
\begin{code}
module GenericClosed where

  data Desc (O : Set) : Set₁ where
    End : (o : O) → Desc O
    Arg : (A : Set) (D : (a : A) → Desc O) → Desc O
    Rec : (A : Set) (D : (o : A → O) → Desc O) → Desc O

  mutual
    data Data {O : Set} (D : Desc O) : Set where
      con : Data′ D D → Data D

    Data′ : {O : Set} (R D : Desc O) → Set
    Data′ R (End o) = ⊤
    Data′ R (Arg A D) = Σ A (λ a → Data′ R (D a))
    Data′ R (Rec A D) = Σ (A → Data R) (λ f → Data′ R (D (fun R ∘ f)))
    
    fun : {O : Set} (D : Desc O) → Data D → O
    fun D (con xs) = fun′ D D xs
  
    fun′ : {O : Set} (R D : Desc O) → Data′ R D → O
    fun′ R (End o) tt = o
    fun′ R (Arg A D) (a , xs) = fun′ R (D a) xs
    fun′ R (Rec A D) (f , xs) = fun′ R (D (λ a → fun R (f a))) xs
\end{code}}

\subsection{\AgdaDatatype{`Set} \& \AgdaDatatype{`Desc}}

\begin{code}
  mutual
    data `Set : Set where
      `Bot `Bool : `Set
      `Fun : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
      `Data : {O : `Set} (D : `Desc O) → `Set
  
    ⟦_⟧ : `Set → Set
    ⟦ `Bot ⟧ = ⊥
    ⟦ `Bool ⟧ = Bool
    ⟦ `Fun A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
    ⟦ `Data D ⟧ = Data ⟪ D ⟫
  
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
  data Path′ {O : `Set} (R : `Desc O) : (D : `Desc O) → Data′ ⟪ R ⟫ ⟪ D ⟫ → Set
  
  data Path where
    here : ∀{A a} → Path A a
    thereFun : ∀{A B f}
      (g : (a : ⟦ A ⟧) → Path (B a) (f a))
      → Path (`Fun A B) f
    thereData : ∀{O} {D : `Desc O} {xs}
      (i : Path′ D D xs)
      → Path (`Data D) (con xs)
  
  data Path′ {O} R where
    thereArg₁ : ∀{A D a xs}
      (i : Path A a)
      → Path′ R (`Arg A D) (a , xs)
    thereArg₂ : ∀{A D a xs}
      (i : Path′ R (D a) xs)
      → Path′ R (`Arg A D) (a , xs)
    thereRec₁ : ∀{A D f xs}
      (g : (a : ⟦ A ⟧) → Path (`Data R) (f a))
      → Path′ R (`Rec A D) (f , xs)
    thereRec₂ : ∀{A D f xs}
      (i : Path′ R (D (fun ⟪ R ⟫ ∘ f)) xs)
      → Path′ R (`Rec A D) (f , xs)
\end{code}

\subsection{\AgdaDatatype{lookup}}

\begin{code}
  Lookup : (A : `Set) (a : ⟦ A ⟧) → Path A a → Set
  Lookup′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
    → Path′ R D xs → Set
  
  Lookup A a here = ⟦ A ⟧
  Lookup (`Fun A B) f (thereFun g) = (a : ⟦ A ⟧) → Lookup (B a) (f a) (g a)
  Lookup (`Data D) (con xs) (thereData i) = Lookup′ D D xs i
  
  Lookup′ R (`Arg A D) (a , xs) (thereArg₁ i) = Lookup A a i
  Lookup′ R (`Arg A D) (a , xs) (thereArg₂ i) = Lookup′ R (D a) xs i
  Lookup′ R (`Rec A D) (f , xs) (thereRec₁ g) = (a : ⟦ A ⟧) → Lookup (`Data R) (f a) (g a)
  Lookup′ R (`Rec A D) (f , xs) (thereRec₂ i) = Lookup′ R (D (fun ⟪ R ⟫ ∘ f)) xs i
\end{code}

\begin{code}
  lookup : (A : `Set) (a : ⟦ A ⟧) (i : Path A a) → Lookup A a i
  lookup′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
    (i : Path′ R D xs) → Lookup′ R D xs i
  
  lookup A a here = a
  lookup (`Fun A B) f (thereFun g) = λ a → lookup (B a) (f a) (g a)
  lookup (`Data D) (con xs) (thereData i) = lookup′ D D xs i
  
  lookup′ R (`Arg A D) (a , xs) (thereArg₁ i) = lookup A a i
  lookup′ R (`Arg A D) (a , xs) (thereArg₂ i) = lookup′ R (D a) xs i
  lookup′ R (`Rec A D) (f , xs) (thereRec₁ g) = λ a → lookup (`Data R) (f a) (g a)
  lookup′ R (`Rec A D) (f , xs) (thereRec₂ i) = lookup′ R (D (fun ⟪ R ⟫ ∘ f)) xs i
\end{code}

\subsection{\AgdaDatatype{update}}

\begin{code}
  Update : (A : `Set) (a : ⟦ A ⟧) → Path A a → Set
  Update′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
    → Path′ R D xs → Set
  update : (A : `Set) (a : ⟦ A ⟧) (i : Path A a)
    → Update A a i → ⟦ A ⟧
  update′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
    (i : Path′ R D xs)
    → Update′ R D xs i
    → Data′ ⟪ R ⟫ ⟪ D ⟫
  
  Update A a here = Maybe ⟦ A ⟧
  Update (`Fun A B) f (thereFun g) = (a : ⟦ A ⟧) → Update (B a) (f a) (g a)
  Update (`Data D) (con xs) (thereData i) = Update′ D D xs i
  
  Update′ R (`Arg A D) (a , xs) (thereArg₁ i) =
    Σ (Update A a i)
      (λ a' → Data′ ⟪ R ⟫ ⟪ D a ⟫ → Data′ ⟪ R ⟫ ⟪ D (update A a i a') ⟫)
  Update′ R (`Arg A D) (a , xs) (thereArg₂ i) = Update′ R (D a) xs i
  Update′ R (`Rec A D) (f , xs) (thereRec₁ g) =
    Σ ((a : ⟦ A ⟧) → Update (`Data R) (f a) (g a))
      (λ h → Data′ ⟪ R ⟫ ⟪ D (λ a → fun ⟪ R ⟫ (f a)) ⟫
        → Data′ ⟪ R ⟫ ⟪ D (λ a → fun ⟪ R ⟫ (update (`Data R) (f a) (g a) (h a))) ⟫
      )
  Update′ R (`Rec A D) (f , xs) (thereRec₂ i) = Update′ R (D (fun ⟪ R ⟫ ∘ f)) xs i
  
  update A a here X = maybe id a X
  update (`Fun A B) f (thereFun g) h = λ a → update (B a) (f a) (g a) (h a)
  update (`Data D) (con xs) (thereData i) X = con (update′ D D xs i X)
  
  update′ R (`Arg A D) (a , xs) (thereArg₁ i) (X , f) = update A a i X , f xs
  update′ R (`Arg A D) (a , xs) (thereArg₂ i) X = a , update′ R (D a) xs i X
  update′ R (`Rec A D) (f , xs) (thereRec₁ g) (h , F) =
    (λ a → update (`Data R) (f a) (g a) (h a)) , F xs
  update′ R (`Rec A D) (f , xs) (thereRec₂ i) X =
    f , update′ R (D (fun ⟪ R ⟫ ∘ f)) xs i X
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
