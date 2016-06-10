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
\usepackage{natbib}

\usepackage[references]{agda}

\DeclareUnicodeCharacter{8759}{\ensuremath{::}}
\DeclareUnicodeCharacter{10218}{\guillemotleft}
\DeclareUnicodeCharacter{10219}{\guillemotright}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\cL}{{\cal L}}

\newcommand{\refsec}[1]{Section \ref{sec:#1}}
\newcommand{\AgdaData}[1]{\AgdaDatatype{#1}}
\newcommand{\AgdaCon}[1]{\AgdaInductiveConstructor{#1}}
\newcommand{\AgdaFun}[1]{\AgdaFunction{#1}}
\newcommand{\AgdaVar}[1]{\AgdaBound{#1}}

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

\title{Generic Lookup and Update \\for Infinitary Inductive-Recursive Types}
%% \subtitle{Generic Lookup and Update}

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

Infinitary inductive-recursive (InfIR)
types are commonly used in dependently
typed programs to model type-theoretic universes~\citep{martinlof:universe}. For example,
consider the Agda~\citep{norell:agda} model below of the universe of natural numbers and
dependent functions
\footnote{\raggedright{
  This paper is written as a literate Adga program. The literate Agda
  source file and other accompanying code can be found at
  \tt{https://github.com/larrytheliquid/infir}
}}.

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
This \AgdaData{Type} is \emph{infinitary} because the
\AgdaCon{`Fun} constructor's second inductive argument
(\AgdaVar{B}) is a function (hence \AgdaData{Type}s can branch infinitely).
Additionally, it is \emph{inductive-recursive} because it
is mutually defined with a
function (\AgdaFun{⟦\_⟧}) operating over it.

Once you have defined a model, it is also common to provide a few
examples of values that inhabit it.
For example, below (\AgdaFun{NumFun}) is a function \AgdaData{Type}
that takes a natural number \AgdaVar{n} as input, then asks you
to construct a natural number from \AgdaVar{n} additional natural
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
\textit{functions} over them is less so.

Why isn't there much existing work on programming functions with
infinitary inductive-recursive functions? They contain inherently
complex properties and there aren't many examples to reference.
Their infinitary nature makes them
\emph{higher-order datatypes}, rather than simpler first-order
datatypes. Their inductive-recursive nature means you need to deal
with \emph{dependencies} between arguments and \emph{mutual functions} too.

Functional programming languages typically package useful datatypes
(like \AgdaData{List}s and \AgdaData{Vec}tors) with useful operations
(like \AgdaFun{lookup} and \AgdaFun{update}) in their standard
libraries. Additionally, \emph{generic} implementations of such operations
may exist as libraries for any other user-defined datatypes.

Our \emph{primary contribution} is to show how to write two particular
operations over infinitary
inductive-recursive types (such as \AgdaData{Type} universes), and
then generalize those operations from functions over concrete
datatypes to generic functions over any user-defined
datatype. The first operation is \AgdaFun{lookup}, allowing data
within an InfIR type to be extracted. The second operation is
\AgdaFun{update}, allowing a value within an InfIR type to be replaced
by another value. We also contribute a \AgdaData{Path} type used by
\AgdaFun{lookup} and \AgdaFun{update} to point at a particular
position within a datatype.
More specifically, we contribute \AgdaData{Path}, \AgdaFun{lookup},
and \AgdaFun{update} for:

\begin{itemize}
\item A concrete large InfIR type, \AgdaData{Type}, in \refsec{concretelarge}.
\item A concrete small InfIR type, \AgdaData{Arith}, in \refsec{concretesmall}.
\item A generic universe for an open theory of types, in \refsec{genericopen}.
\item A generic universe for a closed theory of types, in \refsec{genericclosed}.
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

For readers of the colored version of this paper, we use the following
Agda source code highlighting color conventions:
\AgdaKeyword{Keywords} are orange, \AgdaData{datatypes} are
dark blue, \AgdaCon{constructors} are green, \AgdaFun{functions} are
light blue, and \AgdaVar{variables} are purple.

\subsection{Background}
\label{sec:problem:background}

Let us first consider writing \AgdaFun{lookup} for a simple binary
\AgdaData{Tree}.

\AgdaHide{
\begin{code}
module Tree where
\end{code}}

\begin{code}
  data Tree : Set where
    leaf : Tree
    branch : (A B : Tree) → Tree
\end{code}

Our \AgdaData{Tree} stores no additional data in nodes, can have
binary \AgdaCon{branch}es, and ends with a
\AgdaCon{leaf}. It is easy to work with because it is
first-order, has no dependencies between arguments, and has no mutually
defined functions.

If we want to \AgdaFun{lookup}
a particular
sub\AgdaData{Tree}, we must first have a way to describe a
\AgdaData{Path} that indexes into our original tree.

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

The \AgdaCon{here} constructor indicates that we have
arrived at the subtree we would like to visit. The
\AgdaCon{there₁} constructor tells us to take a left
turn at a \AgdaCon{branch}, while
\AgdaCon{there₂} tells us to take a right turn. In general, we
adopt the convention that a numerical subscript after a
\AgdaCon{there} constructor of a \AgdaData{Path}
indicates which argument to point into.

Once we have defined \AgdaData{Path}s into a \AgdaData{Tree},
it is straightforward to defined \AgdaFun{lookup} by following
the \AgdaData{Path} until we arrive at the type appearing
\AgdaCon{here}.

\begin{code}
  lookup : (A : Tree) → Path A → Tree
  lookup A here = A
  lookup (branch A B) (there₁ i) = lookup A i
  lookup (branch A B) (there₂ i) = lookup B i
\end{code}

\subsection{\AgdaFun{lookup} with a computational return type}
\label{sec:problem:typechanging}

\AgdaHide{
\begin{code}
module List where
\end{code}}

Now let's consider writing a total \AgdaFun{lookup} function for
polymorphic \AgdaData{List}s (instead of the binary
\AgdaData{Tree}s above), where the return type of \AgdaFun{lookup}
is dynamically computed. Below is the \AgdaData{List} and its
\AgdaData{Path}.

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

The \AgdaCon{here} and
\AgdaCon{there₂} constructors are analogous to those
for \AgdaData{Tree} \AgdaData{Path}s. However,
\AgdaCon{there₁} points to a non-inductive
\AgdaVar{A} value, the first argument to
\AgdaCon{cons}, whereas this pointed to an inductive
subtree in the \AgdaData{Tree} scenario.

In the (tranditionally) non-dependent Haskell~\citep{jones:haskell} language there are two
distinct \AgdaFun{lookup}-like functions for lists.

\begin{verbatim}
  drop :: Int -> [a] -> [a]
  (!!) :: [a] -> Int -> a
\end{verbatim}

The first (\texttt{drop}) looks up inductive sublists, and the second
\texttt{(!!)} looks up non-inductive \texttt{a} values.
A depedently typed language like Agda allows us to a write a single
function that may return a \AgdaData{List} or an \AgdaVar{A},
depending on what the input \AgdaData{Path} points to.
Note that below \{A = \AgdaVar{A}\} is Agda notation for binding an
implicit argument explicitly.

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

The \AgdaFun{Lookup} function \textit{computes} the return type
of \AgdaFun{lookup}, allowing \AgdaFun{lookup} to return
either a \AgdaData{List} or an \AgdaVar{A} (the base cases of
\AgdaFun{Lookup}). I will refer to functions like
\AgdaFun{Lookup} as \textit{computational return types}.

In the colored version of this paper, you can spot a
computational type because it is a light blue \AgdaFun{Function},
whereas a non-computational (or static) \AgdaData{Datatype} is dark
blue. Both computational and static types are captizalized by convention.


\subsection{\AgdaFun{head} with a computational argument or return type}
\label{sec:problem:head}

Once we move from finitary non-dependent types like
\AgdaData{Tree} and \AgdaData{List} to an InfIR type like
\AgdaData{Type}, it is no longer obvious how to write a function like
\AgdaFun{lookup}. Looking up something in the
left side (domain) of a \AgdaCon{`Fun} is easy, but
looking up something in the right side (codomain) requires entering a
function space.

Figuring out how to write functions like \AgdaFun{lookup} (and more
complicated functions) over InfIR types is the subject of this
paper. The solution (given in the next section) involves a more
complicated version of the computational return type \AgdaFun{Lookup} above. 
But, let us first consider a general
methodology for turning a would-be partial function into a total
function. For example, say we wanted to write a total version of the
typically partial \AgdaFun{head} function.

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
  \AgdaData{Maybe} result.

\begin{code}
  head₂ : {A : Set} → List A → Maybe A
  head₂ nil = nothing
  head₂ (cons x xs) = just x
\end{code}

\end{enumerate}

Both options give us something to do when we apply
\AgdaFun{head} to an empty list: either get an extra argument to
return, or we simply return
\AgdaCon{nothing}.
However, these options are rather extreme as they require changing our
intended type signature of \AgdaFun{head} for \emph{all} possible
lists. The precision of dependent types allows us to instead
conditionally ask for an extra argument, or return
\AgdaCon{nothing} of computational value, only if the
input list is empty!

First, let's use dependent types to conditonally change the domain. We
ask for an extra argument of type \AgdaVar{A} if the
\AgdaData{List} is empty. Otherwise, we ask for an extra
argument of type unit (\AgdaData{⊤}), which is isomorphic to not
asking for anything extra at all. Below, \AgdaFun{HeadArg} is
type of the extra argument, which is dependent on the input
\AgdaVar{xs} of type \AgdaData{List}. We call functions like
\AgdaFun{HeadArg} \emph{computational argument types}.

\begin{code}
  HeadArg : {A : Set} → List A → Set
  HeadArg {A = A} nil = A
  HeadArg (cons x xs) = ⊤
  
  head₃ : {A : Set} (xs : List A) → HeadArg xs → A
  head₃ nil y = y
  head₃ (cons x xs) tt = x
\end{code}

Second, let's use dependent types to conditonally change the
codomain. \AgdaFun{HeadRet} computes our new return type,
conditionally dependent on the input list
(it is a \emph{computational return type}).
If the input list is empty,
our \AgdaFun{head₄} function returns a value of type unit (\AgdaData{⊤}). If
it is non-empty, it returns an \AgdaVar{A}. Note that returning a
value of \AgdaData{⊤} is returning nothing of computational
significance. Hence, it is as if \AgdaFun{head₄} is not defined
for empty lists.

\begin{code}
  HeadRet : {A : Set} → List A → Set
  HeadRet nil = ⊤
  HeadRet {A = A} (cons x xs) = A
  
  head₄ : {A : Set} (xs : List A) → HeadRet xs
  head₄ nil = tt
  head₄ (cons x xs) = x
\end{code}

We have seen how to take a partial function and make it total,
both with and without the extra precision afforded to us by dependent
types (via computational argument and return types).
We would like to emphasize that the extra argument
\AgdaFun{HeadArg} in \AgdaFun{head₃} is not merely a
precondition, but rather extra computational content that must be
supplied by the program to complete the cases that would
normally make it a partial function.
To see the difference, consider a total version of a function that looks up
\AgdaFun{elem}ents of a \AgdaData{List},
once given a natural number (\AgdaData{ℕ}) index.

\begin{code}
  elem : {A : Set} (xs : List A) (n : ℕ) → length xs < n → A
\end{code}

\AgdaHide{
\begin{code}
  elem = magic
\end{code}}

Because the natural number \AgdaVar{n} may index outside the bounds
of the list \AgdaVar{xs}, we need an extra argument serving as a
precondition. If this precondition is satisfied, it computes to the unit
type (\AgdaData{⊤}),
but if it fails it computes to the empty type (\AgdaData{⊥}). So,
in the failure case the precondition (\AgdaData{⊥}) is
unsatisfiable, whereas the failure case of \AgdaFun{HeadArg} is
the extra argument \AgdaVar{A} needed to complete the otherwise
partial function.

The rest of this paper expands on the ideas of this section by
defining functions like \AgdaFun{HeadArg} that non-trivially
compute extra arguments. These dependent extra arguments
are the key to writing functions over InfIR datatypes.

\section{Large InfIR \AgdaData{Type}}
\label{sec:concretelarge}

\AgdaHide{
\begin{code}
module ConcreteLarge where
\end{code}}

\refsec{problem} reviews how to
\AgdaFun{lookup} sub\AgdaData{Tree}s, sub\AgdaData{List}s,
and subelements pointed to by \AgdaData{Path}s. In this section we
define the corresponding datatypes and functions for InfIR
\AgdaData{Type}s.

\subsection{\AgdaData{Type}}

The InfIR \AgdaData{Type} used in this section is another
type universe, similar to the one in \refsec{intro}. The
\AgdaData{Type} universe is still closed under functions, but now
the \AgdaCon{`Base} types are parameters (of type \AgdaData{Set}) instead of being hardcoded to
\AgdaData{ℕ}.

\begin{code}
  mutual
    data Type : Set₁ where
      `Base : Set → Type
      `Fun : (A : Type) (B : ⟦ A ⟧ → Type) → Type
  
    ⟦_⟧ : Type → Set
    ⟦ `Base A ⟧ = A
    ⟦ `Fun A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
\end{code}

\subsection{\AgdaData{Path}}

Let's reconsider what it means to be a \AgdaData{Path}.
You can still point to a recursive \AgdaData{Type} using
\AgdaCon{here}. Now you can also point to a
non-recursive \AgdaVar{A} of type \AgdaData{Set} using
\AgdaCon{thereBase}.

When traversing a \AgdaData{Tree}, you can always go left or right at a
\AgdaCon{branch}. When traversing a
\AgdaData{Type}, you can immediately go to the left of a
\AgdaCon{`Fun}, but going right requires first knowing
which element \AgdaVar{a} of the type family \AgdaVar{B a} to
continue traversing under. This requirement is neatly captured as a
dependent function type of the \AgdaVar{f} argument below.

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

Above, \AgdaCon{thereFun₂} represents going right
into the codomain of \AgdaCon{`Fun}, but only once the
user tells you which \AgdaVar{a} to use. In a sense, going right is
like asking for a continuation that tells you where to go next, once
you have been given \AgdaVar{a}. Also note that because the argument
\AgdaVar{f} of \AgdaCon{thereFun₂} is a function that
returns a \AgdaData{Path}, the \AgdaData{Path} datatype is
infinitary (just like the \AgdaData{Type} it indexes).

\subsection{\AgdaFun{Lookup} \& \AgdaFun{lookup}}

We were able to write a total function to \AgdaFun{lookup} any
sub\AgdaData{Tree}, but \AgdaFun{lookup}ing up a
sub\AgdaData{Type} is not always possible. Using the methodology
from \refsec{problem:head}, we can make \AgdaFun{lookup} for
\AgdaData{Type}s total by choosing to change the codomain,
depending on the input \AgdaData{Type} and \AgdaData{Path}.
\AgdaFun{Lookup} (a computational return type) computes the codomain of
\AgdaFun{lookup}, asking for a \AgdaData{Type} or \AgdaData{Set} in the base
cases, or a continuation when looking to the right of a
\AgdaCon{`Fun}.

\begin{code}
  Lookup : (A : Type) → Path A → Set₁
  Lookup A here = Type
  Lookup (`Base A) thereBase = Set
  Lookup (`Fun A B) (thereFun₁ i) = Lookup A i
  Lookup (`Fun A B) (thereFun₂ f) =
    (a : ⟦ A ⟧) → Lookup (B a) (f a)
\end{code}

Finally, we can write \AgdaFun{lookup} in terms of
\AgdaData{Path} and \AgdaFun{Lookup}. Notice that users
applying our \AgdaFun{lookup} function need to supply
extra \AgdaVar{a} arguments exactly when they go to the right of a
\AgdaCon{`Fun}. Thus, our definition can expect an
extra argument \AgdaVar{a} in the
\AgdaCon{thereFun₂} case.

\begin{code}
  lookup : (A : Type) (i : Path A) → Lookup A i
  lookup A here = A
  lookup (`Base A) thereBase = A
  lookup (`Fun A B) (thereFun₁ i) = lookup A i
  lookup (`Fun A B) (thereFun₂ f) =
    λ a → lookup (B a) (f a)
\end{code}

\subsection{\AgdaFun{Update} \& \AgdaFun{update}}

Now we will write an \AgdaFun{update} function for
\AgdaData{Type}s. After supplying a \AgdaData{Path} and a
substitute \AgdaData{Type}, \AgdaFun{update} should return
the original \AgdaData{Type} but with the substitute replacing
what the \AgdaData{Path} pointed to. To make updating the InfIR
\AgdaData{Type}
more convenient, the type of the substitute will actually be
\AgdaData{Maybe Type}, where \AgdaCon{nothing}
causes an identity update.
We might expect to write a function like:

\begin{code}
  updateNaive :
    (A : Type) (i : Path A) (X : Maybe Type) → Type
\end{code}

\AgdaHide{
\begin{code}
  updateNaive = magic
\end{code}}

\noindent
Above \AgdaVar{X} is the intended \AgdaData{Type} to
\AgdaData{Maybe} substitute at position \AgdaVar{i}.
In order to write a total version of
\AgdaFun{updateNaive}, we need to change the domain by
asking for an \AgdaVar{a} whenever we update within the codomain of
a \AgdaCon{`Fun}.

We call the type of the value to substitute
\AgdaFun{Update} (a computational argument type), which asks for a \AgdaData{Maybe Type} or a
\AgdaData{Maybe Set} in the base cases (\AgdaCon{here}
and \AgdaCon{thereBase} respectively), and a continuation in the
\AgdaCon{thereFun₂} case. However, updating an element to
the left of a \AgdaCon{`Fun} is also
problematic. We would like to keep the old
\AgdaCon{`Fun} codomain \AgdaVar{B} unchanged, but it
still expects an \AgdaVar{a} of the original type
\AgdaFun{⟦} \AgdaVar{A} \AgdaFun{⟧}. Therefore, the
\AgdaCon{thereFun₁} case must
ask for a forgetful function \AgdaVar{f} that maps newly
updated \AgdaVar{a}'s to their original type.

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

Notice that we must define \AgdaFun{Update} and
\AgdaFun{update} mutually, because the forgetful
function \AgdaVar{f} (the codomain of
\AgdaData{Σ} in the \AgdaCon{thereFun₁} case of
\AgdaFun{Update}) must refer to \AgdaFun{update} in its
domain. Although the \AgdaCon{thereFun₁} case of
\AgdaFun{update} only updates the domain of
\AgdaCon{`Fun}, the type family \AgdaVar{B} in the
codomain expects an \AgdaVar{a} of type
\AgdaFun{⟦} \AgdaVar{A} \AgdaFun{⟧}, so we use the
forgetful function \AgdaVar{f} to map back to \AgdaVar{a}'s
original type.

The base cases (\AgdaCon{here} and
\AgdaCon{thereBase}) of \AgdaFun{update}
perform updates using the
subsitute \AgdaVar{X} (where \AgdaCon{nothing}
results in an identity update). The \AgdaCon{thereFun₂}
case of \AgdaFun{update} leaves the domain of
\AgdaCon{`Fun} unchanged, and recursively updates the
codmain using the substitute continuation \AgdaVar{h}.

Note that
we could have defined \AgdaFun{Update} as an inductive type,
rather than a computational type. If we had done so,
then it would be an InfIR type with \AgdaFun{update} as its
mutually defined function!


\section{Small InfIR \AgdaData{Arith}}
\label{sec:concretesmall}

\AgdaHide{
\begin{code}
module ConcreteSmall where
\end{code}}

\refsec{concretelarge} shows how to define
\AgdaFun{lookup} and \AgdaFun{update} for the large InfIR
\AgdaData{Type}. \AgdaData{Type} is called \textit{large}
because the codomain of its IR function \AgdaFun{⟦\_⟧} has type
\AgdaData{Set}. In this section we adapt our work to a
small InfIR type called \AgdaData{Arith} (it is called
\textit{small} because the codomain of its IR function is \textit{not}
\AgdaData{Set}), which is structurally similar to
\AgdaData{Type}.

\subsection{\AgdaData{Arith}}

The InfIR \AgdaData{Arith} used in this section is structurally
similar to \AgdaData{Type} from \refsec{intro}. One difference is
that the base constructor (\AgdaCon{`Num}), contains
a \AgdaData{ℕ}atural number (rather than a \AgdaData{Set},
like \AgdaCon{`Base}). The other difference is that
the mutually defined function \AgdaFun{eval} returns a
\AgdaData{ℕ} (rather than a \AgdaData{Set}, like
\AgdaFun{⟦\_⟧}.)

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

Values of type \AgdaData{Arith} encode ``Big Pi''
mathematical arithmetic product equations up to some finite
bound, such as the one below.

\begin{equation*}
  \prod_{i=1}^{3} i
\end{equation*}

\begin{code}
    six : Arith
    six = `Prod (`Num 3) (λ i → `Num (toℕ i))
\end{code}


An \AgdaData{Arith} equation may be nested in its upper bound or body, but the lower
bound is always the value 1.
The \AgdaFun{eval} function interprets the equation as a
natural number, using the helper function \AgdaFun{prod} to
multiply a finite number \AgdaVar{n} of other natural numbers
together.

\begin{code}
    prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
    prod zero f = suc zero
    prod (suc n) f = f zero * prod n (f ∘ suc)
\end{code}

\subsection{\AgdaData{Pathℕ} \& \AgdaFun{lookupℕ} \& \AgdaFun{updateℕ}}

The major difference between the base case
\AgdaCon{`Num} of \AgdaData{Arith}, and
\AgdaCon{`Base} of \AgdaData{Type}, is that the
former contains a \AgdaData{ℕ} while the latter contains a
\AgdaData{Set}. The \AgdaFun{lookup} for \AgdaData{Type}
had no choice but to return the value of type \AgdaData{Set} in
the \AgdaCon{`Base} case.
We cannot look further into the value of type \AgdaData{Set} because Agda does
not support type case. In contrast, we can continue to lookup into a substructure of
\AgdaData{ℕ} in the base case \AgdaCon{`Num} of
\AgdaFun{lookup} for \AgdaData{Arith}.
For this reason, we need the \AgdaData{Pathℕ}, \AgdaFun{lookupℕ},
and \AgdaFun{updateℕ} definitions for natural numbers.

\AgdaData{Pathℕ} is an index into the number, which can point to
that number or any smaller number. It is different from the standard
finite set type \AgdaData{Fin} because the number pointed to may
be \AgdaCon{zero}.

\begin{code}
  data Pathℕ : ℕ → Set where
    here : {n : ℕ} → Pathℕ n
    there : {n : ℕ}
      (i : Pathℕ n)
      → Pathℕ (suc n)
\end{code}

The \AgdaFun{lookup} function simply returns the
\AgdaData{ℕ} pointed to by \AgdaData{Pathℕ}. It has a static
return type (not a computational return type), because a
\AgdaData{Pathℕ} always points to a \AgdaData{ℕ}.

\begin{code}
  lookupℕ : (n : ℕ) → Pathℕ n → ℕ
  lookupℕ n here = n
  lookupℕ (suc n) (there i) = lookupℕ n i
\end{code}

The \AgdaFun{update} function replaces a subnumber within a
\AgdaData{ℕ} with a \AgdaData{Maybe ℕ}. The
\AgdaCon{nothing} case performs an identity update,
while \AgdaCon{just} \AgdaVar{n} replaces the
subnumber with \AgdaVar{n}.

\begin{code}
  updateℕ : (n : ℕ) → Pathℕ n → Maybe ℕ → ℕ
  updateℕ n here x = maybe id n x
  updateℕ (suc n) (there i) x = suc (updateℕ n i x)
\end{code}

\subsection{\AgdaData{Path} \& \AgdaFun{L}/\AgdaFun{lookup} \& \AgdaFun{U}/\AgdaFun{update}}

The \AgdaData{Path}, \AgdaFun{lookup}, and
\AgdaFun{update} definitions for \AgdaData{Arith} are
almost textually identical to the corresponding definitions for
\AgdaData{Type} from \refsec{concretelarge}. Thus, we will only
cover the \AgdaCon{`Num} cases of these
definitions. The old \AgdaData{Type} definitions will work for the
other cases by textually substituting \AgdaData{Arith} for \AgdaData{Type},
\AgdaCon{`Prod} for \AgdaCon{`Fun},
and by defining the following type synonym.

\begin{code}
  ⟦_⟧ : Arith → Set
  ⟦ A ⟧ = Fin (eval A)
\end{code}

The \AgdaCon{thereNum} case of
\AgdaData{Path} can point somewhere deeper into a substructure of
the natural number contained by \AgdaCon{`Num} by
using a \AgdaData{Pathℕ}.

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

The \AgdaCon{`Num} case of \AgdaFun{Lookup}
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

The \AgdaCon{`Num} case of \AgdaFun{lookup}
continues to \AgdaFun{lookupℕ} the number contained
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

The \AgdaCon{`Num} case of \AgdaFun{Update}
allows the user to supply a \AgdaData{Maybe ℕ}, representing
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

The \AgdaCon{`Num} case of \AgdaFun{update}
leaves \AgdaCon{`Num} unchanged, but replaces the
natural number contained using \AgdaFun{updateℕ}.

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
inductive-recursive Dybjer-Setzer code~\citep{dybjer:ir1,dybjer:ir2}.

\subsection{\AgdaData{Desc}}

First let us recall the type of inductive-recursive codes
developed by Dybjer and Setzer. We refer to values of
\AgdaData{Desc} defined below as ``codes''.
\footnote{
  We have renamed the original Dybjer-Setzer constructions to
  emphasize their meaning in English. The original names of our
  \AgdaData{Desc}/\AgdaCon{End}/\AgdaCon{Arg}/\AgdaCon{Rec}
  constructions are
  \AgdaData{IR}/\AgdaCon{$\iota$}/\AgdaCon{$\sigma$}/\AgdaCon{$\delta$}
  respectively.
  }
A \AgdaData{Desc} simultaneously
encodes the definition of a datatype and a function mutually
defined over it.

\begin{code}
  data Desc (O : Set) : Set₁ where
    End : (o : O) → Desc O
    Arg : (A : Set) (D : (a : A) → Desc O) → Desc O
    Rec : (A : Set) (D : (o : A → O) → Desc O) → Desc O  
\end{code}

To a first approximation, a datatype \AgdaData{Desc}ription
encodes the type signature of a single constructor, and the value
returned by the case of that constructor for the mutually defined
function. \AgdaCon{End} is used to specify that a
constructor takes no further arguments. However, the user must supply
a value \AgdaVar{o} of type \AgdaVar{O} to define the value returned by the
mutually defined function. \AgdaCon{Arg} is used to
specify a non-recursive argument of a constructor, \AgdaVar{a} of
type \AgdaVar{A}, and the remainder of the \AgdaData{Desc} may depend
on the value \AgdaVar{a}. \AgdaCon{Rec} is used to
specify a recursive argument (of the type currently being
specified). More generally, the recursive argument may be a function
type whose codomain is the type currently being defined but whose
domain may be non-recursive.
\footnote{
  The domain is restricted to be non-recursive to enforce that encoded
  datatypes are strictly positive.
}
Above, the domain of the function is some non-recursive type
\AgdaVar{A}, and the remainder of the \AgdaData{Desc} may depend
on a function \AgdaVar{o} from \AgdaVar{A} to \AgdaVar{O},
representing the result of applying the mutually defined function to
the recursive argument being specified.

Finally, to encode multiple constructors as a \AgdaData{Desc}, you
simply define an \AgdaCon{Arg} whose domain is a
finite enumeration of types (representing each constructor), and whose
codomain is the \AgdaData{Desc} corresponding to the arguments and
recursive cases for each constructor.

The abstract nature of \AgdaData{Desc} makes it somewhat difficult
to understand at first, especially the \AgdaCon{Rec}
constructor. Let's try to understand \AgdaData{Desc} better with an
example, encoding \AgdaData{Arith} from
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

The \AgdaData{Desc} begins with an \AgdaCon{Arg},
taking sub-\AgdaData{Desc}s for each element of the finite
enumeration \AgdaData{ArithT}, representing the types of each
\AgdaData{Arith} constructor.

The \AgdaCon{NumT} description uses
\AgdaCon{Arg} to take a natural number
(\AgdaData{ℕ}), then \AgdaCon{End}s with that number. Ending with that
number encodes that the \AgdaCon{`Num} case of the
\AgdaFun{eval} from \refsec{concretesmall} returns the number held
by \AgdaCon{`Num} in the base case.

The \AgdaCon{ProdT} description uses
\AgdaCon{Rec} twice, taking two recursive
arguments. The first recursive argument is intended to encode an
\AgdaData{Arith} rather than a function type, so we
make its domain a value of the trivial type \AgdaData{⊤}. The
second recursive argument is intended to encode a function from
\AgdaData{Fin} \AgdaVar{n} to \AgdaData{Arith}, so we ask
for a \AgdaData{Fin} (\AgdaVar{n}
\AgdaCon{tt}), where \AgdaVar{n} represents the
value returned by applying \AgdaFun{eval} to the first recursive
argument. In fact, \AgdaVar{n} represents a function from the
trivial type \AgdaData{⊤} to \AgdaData{ℕ}, because first-order
recursive arguments are encoded as higher-order arguments with a
trivial domain. Finally, \AgdaCon{End} is used to
specify that there are no further arguments, and the
\AgdaCon{`Prod} case of \AgdaFun{eval} should
result in the \AgdaFun{prod}uct represented by the first two
recursive arguments.

\subsection{\AgdaData{Data}}

Previously we used \AgdaData{Desc} to encode a datatype and its
mutual function. Applying \AgdaData{Data} to a description results
in the datatype it encodes, and applying \AgdaFun{fun} to a
description results in the mutual function it encodes.

\AgdaHide{
\begin{code}
  mutual
\end{code}}

\AgdaData{Data} is defined in terms of a single constructor
\AgdaCon{con}, which holds a dependent product of all
arguments of a particular constructor. The computational argument type
\AgdaFun{Data′} encodes the type of this product, dependent on
the \AgdaData{Desc}ription that \AgdaData{Data} is
parameterized by.

For the remainder of the paper, we will establish a convention for
functions ending with a prime, like \AgdaFun{Data′}. They will be
defined by induction over a description, but must also use the
original description they are inducting over in the \AgdaCon{Rec} case. Hence,
they take two \AgdaData{Desc} arguments, where the first
\AgdaVar{R} is the original description (to be used in
\AgdaCon{Rec}ursive cases), and the second
\AgdaVar{D} is the one we induct over.

\begin{code}
    data Data {O : Set} (D : Desc O) : Set where
      con : Data′ D D → Data D

    Data′ : {O : Set} (R D : Desc O) → Set
    Data′ R (End o) = ⊤
    Data′ R (Arg A D) = Σ A (λ a → Data′ R (D a))
    Data′ R (Rec A D) =
      Σ (A → Data R) (λ f → Data′ R (D (fun R ∘ f)))
\end{code}

The \AgdaCon{End} case means no further arguments are
needed, so we ask for a trivial value of type \AgdaData{⊤}. The
\AgdaCon{Arg} case asks for a value of type
\AgdaVar{A}, which the rest of the arguments may depend on using
\AgdaVar{a}. The \AgdaCon{End} case asks for a function from
\AgdaVar{A} to a recursive value \AgdaData{Data} \AgdaVar{R},
and the rest of the arguments may use \AgdaVar{f} to depend on the
result of applying the mutual function (e.g. \AgdaFun{eval}) to
the recursive argument after applying a value of type \AgdaVar{A}.

Next we define \AgdaFun{fun} (encoding the mutual function) in
terms of \AgdaFun{fun′}.

\begin{code}
    fun : {O : Set} (D : Desc O) → Data D → O
    fun D (con xs) = fun′ D D xs
  
    fun′ : {O : Set} (R D : Desc O) → Data′ R D → O
    fun′ R (End o) tt = o
    fun′ R (Arg A D) (a , xs) = fun′ R (D a) xs
    fun′ R (Rec A D) (f , xs) = fun′ R (D (λ a → fun R (f a))) xs
\end{code}

The \AgdaCon{End} case gives us what we want, the
value \AgdaVar{o} that the mutual function should return for the
encoded constructor case. The \AgdaCon{Arg} and
\AgdaCon{Rec} cases recurse, looking for an
\AgdaCon{End}.

\subsection{\AgdaData{Path}}

Now we will encode a generic \AgdaData{Path} type, that can be
used to index into any inductive-recursive value encoded by applying
\AgdaData{Data} to a \AgdaData{Desc}.

\AgdaHide{
\begin{code}
  mutual
\end{code}}

\begin{code}
    data Path {O : Set} (D : Desc O) : Data D → Set₁ where
      here : ∀{x} → Path D x
      there : ∀{xs}
        → Path′ D D xs
        → Path D (con xs)
\end{code}

A \AgdaData{Path} uses \AgdaCon{here} to
immediately point to the current constructor. It uses
\AgdaCon{there} to point into one of the
arguments of the current constructor, using \AgdaData{Path′} as a
sub-index.

\subsection{\AgdaData{Path′}}

A \AgdaData{Path′} points to an argument of a constructor,
one of the values of the dependent product computed by
\AgdaFun{Data′}.

\begin{code}
    data Path′ {O : Set} (R : Desc O) 
      : (D : Desc O) → Data′ R D → Set₁ where
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

The \AgdaCon{thereArg₁} case points immediately to a
non-recursive value of type \AgdaVar{A}. Recall
\AgdaCon{thereBase} from \refsec{concretelarge},
which points immediately to a non-recursive value of type
\AgdaData{Set}. The \AgdaCon{thereBase} case cannot
index further into non-recursive \AgdaData{Set}s because values of
type \AgdaData{Set} cannot be case-analyzed. Similarly, the
\AgdaCon{thereArg₁} case of our open
universe generic \AgdaData{Path′} cannot index further into
\AgdaVar{A}, because the type of \AgdaVar{A} is \AgdaData{Set}
and cannot be case-analyzed. For this reason, \AgdaData{Path′}
does not adequately capture concrete paths for types like
\AgdaData{Arith} of \refsec{concretesmall}, which has a
\AgdaData{ℕ} in the \AgdaCon{`Num} case that we
would like to index into. This is a limitation due to using open
universe \AgdaData{Desc}riptions, which we remedy using a
closed universe in \refsec{genericclosed}.

The \AgdaCon{thereArg₂} case points to a
sub-argument, skipping past the
non-recursive argument.

The \AgdaCon{thereRec₁}
points into a recursive argument. Because the recursive argument is a
function whose is a value of type \AgdaVar{A}, the
sub-\AgdaData{Path′} must also be a function taking an
\AgdaVar{A}, hence \AgdaData{Path′} is an infinitary type.
Thus, \AgdaCon{thereRec₁} is much like
\AgdaCon{thereFun₂} of \refsec{concretelarge}.

The \AgdaCon{thereRec₂} case points to a
sub-argument, skipping past the recursive argument.


\subsection{\AgdaFun{Lookup} \& \AgdaFun{lookup}}

As in \refsec{concretelarge} and \refsec{concretesmall}, our generic
open universe \AgdaFun{lookup} must have a computational return
type, \AgdaFun{Lookup}. Below, the \AgdaFun{Lookup} and
\AgdaFun{Lookup′} functions are mutually defined, and so are
\AgdaFun{lookup} and \AgdaFun{lookup′}.

\AgdaHide{
\begin{code}
  mutual
\end{code}}

\begin{code}
    Lookup : {O : Set} (D : Desc O) (x : Data D) → Path D x → Set
    Lookup D x here = Data D
    Lookup D (con xs) (there i) = Lookup′ D D xs i
\end{code}

The \AgdaCon{here} case returns a
\AgdaData{Data} of the encoded description \AgdaVar{D}
currently being pointed to. The \AgdaCon{there} case
returns a type \AgdaFun{Lookup′} of one of the arguments
to the constructor.

\begin{code}
    lookup : {O : Set} (D : Desc O) (x : Data D) (i : Path D x)
      → Lookup D x i
    lookup D x here = x
    lookup D (con xs) (there i) = lookup′ D D xs i
\end{code}

The \AgdaCon{here} case returns the value being pointed
to. The \AgdaCon{there} case returns a value within
one of the arguments of the current constructor via
\AgdaFun{lookup′}.

\subsection{\AgdaFun{Lookup′} \& \AgdaFun{lookup′}}

The function \AgdaFun{lookup′} is used to lookup a value within
an argument of a constructor, and has \AgdaData{Lookup′} as its
computational return type.

\begin{code}
    Lookup′ : {O : Set} (R D : Desc O) (xs : Data′ R D)
      → Path′ R D xs → Set
    Lookup′ R (End o) tt ()
    Lookup′ R (Arg A D) (a , xs) thereArg₁ = A
    Lookup′ R (Arg A D) (a , xs) (thereArg₂ i) =
      Lookup′ R (D a) xs i
    Lookup′ R (Rec A D) (f , xs) (thereRec₁ g) =
      (a : A) → Lookup R (f a) (g a)
    Lookup′ R (Rec A D) (f , xs) (thereRec₂ i) =
      Lookup′ R (D (fun R ∘ f)) xs i
\end{code}

The \AgdaCon{thereArg₂} and \AgdaCon{thereRec₂} cases skip past one
argument, looking for the type of a subsequent an argument pointed to
by the index. The \AgdaCon{thereArg₁} case returns the type of the
current non-recursive argument \AgdaVar{A}. The \AgdaCon{thereRec₁}
asks for a continuation, represented as a function type from
\AgdaVar{A} to the rest of the \AgdaFun{Lookup}. Because
\AgdaCon{thereRec₁} points to a recursive argument, it asks for a
\AgdaFun{Lookup} of the original description \AgdaVar{R}, rather
than a \AgdaFun{Lookup′} of some subsequent argument description.

\begin{code}
    lookup′ : {O : Set} (R D : Desc O) (xs : Data′ R D)
      (i : Path′ R D xs) → Lookup′ R D xs i
    lookup′ R (End o) tt ()
    lookup′ R (Arg A D) (a , xs) thereArg₁ = a
    lookup′ R (Arg A D) (a , xs) (thereArg₂ i) =
      lookup′ R (D a) xs i
    lookup′ R (Rec A D) (f , xs) (thereRec₁ g) =
      λ a → lookup R (f a) (g a)
    lookup′ R (Rec A D) (f , xs) (thereRec₂ i) =
      lookup′ R (D (fun R ∘ f)) xs i
\end{code}

The \AgdaCon{thereArg₂} and \AgdaCon{thereRec₂} cases skip past one
argument, and return a lookup into a subsequent argument.
The \AgdaCon{thereArg₁} case returns the non-recursive argument
\AgdaVar{a} of type \AgdaVar{A} currently being pointed to.
The \AgdaCon{thereRec₁} returns a continuation from \AgdaVar{a} of
type \AgdaVar{A} to the rest of the \AgdaFun{lookup}. Note that the
body of the continuation is a \AgdaFun{lookup} rather than a
\AgdaFun{lookup′}, matching the type specified by \AgdaFun{Lookup′}
for the \AgdaCon{thereRec₁} case.

\subsection{\AgdaFun{Update} \& \AgdaFun{update}}

Now we define the generic open universe \AgdaFun{update}
function, updating a value in the open universe with the contents of
the computational argument type \AgdaFun{Update}.
Note that \AgdaFun{Update}, \AgdaFun{Update′},
\AgdaFun{update}, and \AgdaFun{update′} \emph{all} need to
be mutually defined. The mutual dependence has to with the need for a
forgetful function, which also requires \AgdaFun{Update} and
\AgdaFun{update} to be mutually defined in \refsec{concretelarge}.

\AgdaHide{
\begin{code}
  mutual
\end{code}}

\begin{code}
    Update : {O : Set} (D : Desc O) (x : Data D)
      → Path D x → Set
    Update D x here = Maybe (Data D)
    Update D (con xs) (there i) = Update′ D D xs i
\end{code}

The \AgdaCon{here} case returns a \AgdaData{Maybe}
\AgdaData{Data} of the encoded description \AgdaVar{D}
currently being pointed to. The \AgdaCon{there} case
returns a type \AgdaFun{Update′} of one of the arguments
to the constructor.

\begin{code}
    update : {O : Set} (D : Desc O) (x : Data D)
      (i : Path D x) (X : Update D x i) → Data D
    update D x here X = maybe id x X
    update D (con xs) (there i) X = con (update′ D D xs i X)
\end{code}

The \AgdaCon{here} case keeps the old value, performing an identity
update if \AgdaVar{X} is \AgdaCon{nothing}. Otherwise, if \AgdaVar{X}
is \AgdaCon{just} of some value, it updates by returning that value.
The \AgdaCon{there} case updates
one of the arguments within the constructor \AgdaCon{con} via
\AgdaFun{update′}.

\subsection{\AgdaFun{Update′} \& \AgdaFun{update′}}

The function \AgdaFun{update′} is updates
an argument of a constructor, with the computational argument type
\AgdaData{Update′}.


\begin{code}
    Update′ : {O : Set} (R D : Desc O) (xs : Data′ R D)
      → Path′ R D xs → Set
    Update′ R (End o) tt ()
    Update′ R (Arg A D) (a , xs) thereArg₁ =
      Σ (Maybe A)
        (maybe (λ a' → Data′ R (D a) → Data′ R (D a')) ⊤)
    Update′ R (Arg A D) (a , xs) (thereArg₂ i) =
      Update′ R (D a) xs i
    Update′ R (Rec A D) (f , xs) (thereRec₁ g) =
      Σ ((a : A) → Update R (f a) (g a))
        (λ h → let f' = λ a → update R (f a) (g a) (h a)
             in Data′ R (D (fun R ∘ f))
             →  Data′ R (D (fun R ∘ f')))
    Update′ R (Rec A D) (f , xs) (thereRec₂ i) =
      Update′ R (D (fun R ∘ f)) xs i
\end{code}

The \AgdaCon{thereArg₂} and \AgdaCon{thereRec₂} cases skip past one
argument, updating the type of a subsequent an argument pointed to
by the index.

The \AgdaCon{thereArg₁} case asks for a
\AgdaData{Maybe} \AgdaVar{A} to update the left argument
with. When we define \AgdaFun{update′} for this case, 
updating with a \AgdaCon{just} \AgdaVar{a'} will require translation of
second component of the pair \AgdaVar{xs} to be indexed by the
new first component \AgdaVar{D} \AgdaVar{a'} rather than the old first
component \AgdaVar{D} \AgdaVar{a}. Therefore, we also need to ask for
a function that translates \AgdaVar{D} \AgdaVar{a} to \AgdaVar{D}
\AgdaVar{a'}.

The \AgdaCon{thereRec₁} case asks for a continuation to update the
first component of the recursive argument, but also needs a translation
function to \AgdaFun{update} the index in the codomain of the second
component. The translation functions of \AgdaCon{thereArg₁} and
\AgdaCon{therRec₁} are analogous to the forgetful function of
\AgdaFun{Update} in \refsec{concretelarge} for the \AgdaCon{thereFun₁}
case, only differing in variance (translating versus forgetting) due
to the way dependencies are captured as dependent products in
\AgdaData{Desc} codes.

\begin{code}
    update′ : {O : Set} (R D : Desc O) (xs : Data′ R D)
      (i : Path′ R D xs) → Update′ R D xs i → Data′ R D
    update′ R (End o) tt () X
    update′ R (Arg A D) (a , xs) thereArg₁ (nothing , f) =
      a , xs
    update′ R (Arg A D) (a , xs) thereArg₁ (just X , f) =
      X , f xs
    update′ R (Arg A D) (a , xs) (thereArg₂ i) X =
      a , update′ R (D a) xs i X
    update′ R (Rec A D) (f , xs) (thereRec₁ g) (h , F) =
      (λ a → update R (f a) (g a) (h a)) , F xs
    update′ R (Rec A D) (f , xs) (thereRec₂ i) X =
      f , update′ R (D (fun R ∘ f)) xs i X
\end{code}

The \AgdaCon{thereArg₂} and \AgdaCon{thereRec₂} keep the left
argument unchanged, and update a subsequent argument pointed to
by the index. The \AgdaCon{thereArg₁} case performs the identity
update in the \AgdaCon{nothing} case. In the \AgdaCon{just} case, the
left component is updated while the right comonent is translated.
The \AgdaCon{thereRec₁} case is similar, updating the left component
and translating the second. 

\section{Generic Closed InfIR}
\label{sec:genericclosed}

\refsec{genericopen} covers how to define generic constructions like
\AgdaData{Path} over an open universe of types. The open universe does
not adequately model the \AgdaData{Path} over the concrete
\AgdaData{Arith} type of \refsec{concretesmall}, as it does not let
you index into non-recursive arguments in a datatype such as the
\AgdaData{ℕ} argument to \AgdaCon{`Num}.

In this section we introduce a novel closed universe of small
InfIR types, allowing us to adequately express generic constructions
over datatypes like \AgdaData{Arith}.

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

\subsection{\AgdaData{`Set} \& \AgdaData{`Desc}}

We begin by defining a universe of codes \AgdaData{`Set} for primitive
types of our universe, along with a meaning function \AgdaFun{⟦\_⟧}
mapping each code for a type to a concrete primitive \AgdaData{Set}.

\AgdaHide{
\begin{code}
  mutual
\end{code}}

\begin{code}
    data `Set : Set where
      `Empty `Unit `Bool : `Set
      `Fun : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
      `Data : {O : `Set} (D : `Desc O) → `Set 

    ⟦_⟧ : `Set → Set
    ⟦ `Empty ⟧ = ⊥
    ⟦ `Unit ⟧ = ⊤
    ⟦ `Bool ⟧ = Bool
    ⟦ `Fun A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
    ⟦ `Data D ⟧ = Data ⟪ D ⟫
\end{code}

Having codes for the empty type \AgdaCon{`Empty}, the unit type \AgdaCon{`Unit}, booleans \AgdaCon{`Bool}, and
function \AgdaCon{`Fun} is standard an similar to the \AgdaData{Type}
universe in the introduction. However, we add a code \AgdaCon{`Data}
for inductive-recurse datatypes. The key to an adequate encoding is to
make the argument to \AgdaCon{`Data} not a primitive
\AgdaData{Desc}, but a new type \AgdaData{`Desc} of \emph{codes} for
descriptions. This type of codes for descriptions also has a meaning
function \AgdaFun{⟪\_⟫}, mapping codes of descriptions to a concrete
primitive \AgdaData{Desc}. 

\begin{code}
    data `Desc (O : `Set) : Set where
      `End : (o : ⟦ O ⟧) → `Desc O
      `Arg : (A : `Set) (D : ⟦ A ⟧ → `Desc O) → `Desc O
      `Rec : (A : `Set) (D : (o : ⟦ A ⟧ → ⟦ O ⟧) → `Desc O)
        → `Desc O
  
    ⟪_⟫ : {O : `Set} → `Desc O → Desc ⟦ O ⟧
    ⟪ `End o ⟫ = End o
    ⟪ `Arg A D ⟫ = Arg ⟦ A ⟧ (λ a → ⟪ D a ⟫)
    ⟪ `Rec A D ⟫ = Rec ⟦ A ⟧ (λ o → ⟪ D o ⟫)
\end{code}

The constructors of \AgdaData{`Desc} mirror those of \AgdaData{Desc},
but the \AgdaCon{`Arg} and \AgdaCon{`Rec} constructors take a
\AgdaData{`Set} code rather than concrete \AgdaData{Set}. This is the
key that allows us to define an adequate \AgdaData{Path}, because
we know how to case-analyze the type of codes \AgdaData{`Set}, so we
can have a path index into it.
Finally, note that the two code types and their meaning functions are
all mutually defined.

Finally, let's see a closed universe description encoding of
\AgdaData{Arith} from \refsec{concretesmall} below .

\AgdaHide{
\begin{code}
  postulate
    `ℕ : `Set
    `Fin : ⟦ `ℕ ⟧ → `Set
    prod : (n : ⟦ `ℕ ⟧) (f : ⟦ `Fin n ⟧ → ⟦ `ℕ ⟧) → ⟦ `ℕ ⟧
\end{code}}

\begin{code}
  ArithD : `Desc `ℕ
  ArithD = `Arg `Bool λ
    { true → `Arg `ℕ (λ n → `End n)
    ; false
      → `Rec `Unit λ n
      → `Rec (`Fin (n tt)) λ f
      → `End (prod (n tt) f)
    }
\end{code}

The main difference from the open universe encoding of
\AgdaData{Arith} from \refsec{genericopen} is that \AgdaCon{`Arg}
takes the primitive \AgdaCon{`Bool} of type \AgdaData{`Set}, rather
than \AgdaData{ArithT} of type \AgdaData{Set}. Because we are
operating in a closed universe, all arguments to \AgdaCon{`Arg} and
\AgdaCon{`Rec} must themselves be closed universe codes. For this
reason, \AgdaData{ArithD} is also encoded in terms
\AgdaFun{`ℕ} and \AgdaFun{`Fin}, which are \AgdaData{`Set} encodings
of their \AgdaData{Set} countersparts whose definitions have been
omitted.

\subsection{\AgdaData{Path}}

The \AgdaData{Path} type for our generic closed universe is indexed by
a type code \AgdaData{`Set} and a value of the encoded type translated
by the meaning function \AgdaFun{⟦\_⟧}. In
contrast, \AgdaData{Path} from \refsec{genericopen} is indexed by a
concrete \AgdaData{Description}.

\AgdaHide{
\begin{code}
  mutual
\end{code}}

\begin{code}
    data Path : (A : `Set) → ⟦ A ⟧ → Set where
      here : ∀{A a} → Path A a
      thereFun : ∀{A B f}
        (g : (a : ⟦ A ⟧) → Path (B a) (f a))
        → Path (`Fun A B) f
      thereData : ∀{O} {D : `Desc O} {xs}
        (i : Path′ D D xs)
        → Path (`Data D) (con xs)
\end{code}

The \AgdaCon{here} case points to the current value in our
universe. The \AgdaCon{thereFun} case points to another value in a
continuation. The \AgdaCon{thereData} case points into an argument of
an inductive-recursive \AgdaCon{con}structor.

\subsection{\AgdaData{Path′}}

A \AgdaData{Path′} points to an argument of a constructor,
a value of \AgdaFun{Data′} applied to a description code translated by the
meaning function \AgdaFun{⟪\_⟫}.

\begin{code}
    data Path′ {O : `Set} (R : `Desc O)
      : (D : `Desc O) → Data′ ⟪ R ⟫ ⟪ D ⟫ → Set where
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

The \AgdaCon{thereArg₁} case is the only constructor that behaves
differently than the open universe \AgdaData{Path′} of
\refsec{genericopen}. Crucially, it points into a non-recursive value
by requiring a \AgdaData{Path} \AgdaVar{A} \AgdaVar{a} as an
argument. In contrast, the open universe \AgdaCon{thereArg₁} does not
take an argument, thus it always points to
\AgdaVar{a} rather than some sub-value inside of it.
\emph{This} is what allows our generic closed universe paths to
adequately model a concrete path for a type like \AgdaData{Arith},
where \AgdaCon{`Num} should be able to index into its \AgdaData{ℕ}!

\subsection{\AgdaFun{Lookup} \& \AgdaFun{lookup}}

The \AgdaFun{lookup} and \AgdaFun{Lookup} functions are conceptually
similar to their open universe generic counterparts from
\refsec{genericopen}. However, like \AgdaData{Path}, they are
parameterized by a value of \AgdaData{`Set} rather than an
inductive-recursive constructor of a \AgdaData{Desc}.

\AgdaHide{
\begin{code}
  mutual
\end{code}}

\begin{code}
    Lookup : (A : `Set) (a : ⟦ A ⟧) → Path A a → Set
    Lookup A a here = ⟦ A ⟧
    Lookup (`Fun A B) f (thereFun g) =
      (a : ⟦ A ⟧) → Lookup (B a) (f a) (g a)
    Lookup (`Data D) (con xs) (thereData i) =
      Lookup′ D D xs i
\end{code}

As always, the \AgdaCon{here} case points to the current value. The
\AgdaCon{thereFun} case points further within a continuation. The
\AgdaCon{thereData} case points into a constructor argument via
\AgdaFun{Lookup′}.

\begin{code}
    lookup : (A : `Set) (a : ⟦ A ⟧) (i : Path A a) → Lookup A a i
    lookup A a here = a
    lookup (`Fun A B) f (thereFun g) =
      λ a → lookup (B a) (f a) (g a)
    lookup (`Data D) (con xs) (thereData i) =
      lookup′ D D xs i
\end{code}

The \AgdaFun{lookup} function returns the current value, a
continuation, or a \AgdaFun{lookup′} of a constructor argument
respectively for the \AgdaCon{here}, \AgdaCon{thereFun}, and
\AgdaCon{thereData} cases.

\subsection{\AgdaFun{Lookup′} \& \AgdaFun{lookup′}}

The \AgdaFun{lookup′} and \AgdaFun{Lookup′} functions are even more
similar to their open universe generic counterparts from
\refsec{genericopen}. They are parameterized by two
\AgdaData{`Desc}ription codes \AgdaVar{R} and \AgdaVar{D}, rather than
primitive \AgdaFun{Desc}riptions.

\begin{code}
    Lookup′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
      → Path′ R D xs → Set
    Lookup′ R (`Arg A D) (a , xs) (thereArg₁ i) =
      Lookup A a i
    Lookup′ R (`Arg A D) (a , xs) (thereArg₂ i) =
      Lookup′ R (D a) xs i
    Lookup′ R (`Rec A D) (f , xs) (thereRec₁ g) =
      (a : ⟦ A ⟧) → Lookup (`Data R) (f a) (g a)
    Lookup′ R (`Rec A D) (f , xs) (thereRec₂ i) =
      Lookup′ R (D (fun ⟪ R ⟫ ∘ f)) xs i
\end{code}

The \AgdaCon{thereArg₂}, \AgdaCon{thereRec₁}, and \AgdaCon{thereRec₂}
cases are like their generic open universe counterparts. However, the
\AgdaCon{thereArg₁} is different as it recursively looks for a type
within \AgdaVar{A} rather than immediately returning \AgdaVar{A}.

\begin{code}
    lookup′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
      (i : Path′ R D xs) → Lookup′ R D xs i
    lookup′ R (`Arg A D) (a , xs) (thereArg₁ i) =
      lookup A a i
    lookup′ R (`Arg A D) (a , xs) (thereArg₂ i) =
      lookup′ R (D a) xs i
    lookup′ R (`Rec A D) (f , xs) (thereRec₁ g) =
      λ a → lookup (`Data R) (f a) (g a)
    lookup′ R (`Rec A D) (f , xs) (thereRec₂ i) =
      lookup′ R (D (fun ⟪ R ⟫ ∘ f)) xs i
\end{code}

Once again, \AgdaCon{thereArg₁} is the major case that is different
from the open universe. Here, we continue looking within \AgdaVar{a}
rather than immediately returning \AgdaVar{a}.

\subsection{\AgdaFun{Update} \& \AgdaFun{update}}

Now we define the generic closed universe \AgdaFun{update} and
\AgdaFun{Update}. Once again, \AgdaFun{Update}, \AgdaFun{Update′},
\AgdaFun{update}, and \AgdaFun{update′} \emph{all} need to
be mutually defined.

\AgdaHide{
\begin{code}
  mutual
\end{code}}

\begin{code}
    Update : (A : `Set) (a : ⟦ A ⟧) → Path A a → Set
    Update A a here = Maybe ⟦ A ⟧
    Update (`Fun A B) f (thereFun g) =
      (a : ⟦ A ⟧) → Update (B a) (f a) (g a)
    Update (`Data D) (con xs) (thereData i) =
      Update′ D D xs i
\end{code}

The \AgdaCon{here} case returns a \AgdaData{Maybe} of the current
value type \AgdaVar{A}. The
\AgdaCon{thereFun} case points further within a continuation. The
\AgdaCon{thereData} case points into a constructor argument via
\AgdaFun{Update′}.

\begin{code}
    update : (A : `Set) (a : ⟦ A ⟧) (i : Path A a)
      → Update A a i → ⟦ A ⟧
    update A a here X = maybe id a X
    update (`Fun A B) f (thereFun g) h =
      λ a → update (B a) (f a) (g a) (h a)
    update (`Data D) (con xs) (thereData i) X =
      con (update′ D D xs i X)
\end{code}

The \AgdaFun{update} function updates the current value (perhaps with
an identity update), updates within a continuation, or uses
\AgdaFun{update′} on a constructor argument within \AgdaCon{con}
respectively for the \AgdaCon{here}, \AgdaCon{thereFun}, and
\AgdaCon{thereData} cases.

\subsection{\AgdaFun{Update′} \& \AgdaFun{update′}}

Next we define the generic closed universe \AgdaFun{update′} and
\AgdaFun{Update′}.
    
\begin{code}
    Update′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
      → Path′ R D xs → Set
    Update′ R (`Arg A D) (a , xs) (thereArg₁ i) =
      Σ (Update A a i)
        (λ a' → Data′ ⟪ R ⟫ ⟪ D a ⟫
              → Data′ ⟪ R ⟫ ⟪ D (update A a i a') ⟫)
    Update′ R (`Arg A D) (a , xs) (thereArg₂ i) =
      Update′ R (D a) xs i
    Update′ R (`Rec A D) (f , xs) (thereRec₁ g) =
      Σ ((a : ⟦ A ⟧) → Update (`Data R) (f a) (g a))
        (λ h → let f' = λ a → update (`Data R) (f a) (g a) (h a)
            in Data′ ⟪ R ⟫ ⟪ D (fun ⟪ R ⟫ ∘ f) ⟫
            →  Data′ ⟪ R ⟫ ⟪ D (fun ⟪ R ⟫ ∘ f') ⟫)
    Update′ R (`Rec A D) (f , xs) (thereRec₂ i) =
      Update′ R (D (fun ⟪ R ⟫ ∘ f)) xs i
\end{code}

Like with \AgdaFun{Lookup′}, \AgdaCon{thereArg₁} is the only case that
differs significantly from its open universe counterpart. The open
universe asked for a \AgdaData{Maybe} of the current value type
\AgdaVar{A} (and a translation function). Instead, the closed universe
asks recursively asks for some type within \AgdaVar{A} (and a
translation function).

\begin{code}
    update′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
      (i : Path′ R D xs) → Update′ R D xs i → Data′ ⟪ R ⟫ ⟪ D ⟫
    update′ R (`Arg A D) (a , xs) (thereArg₁ i) (X , f) =
      update A a i X , f xs
    update′ R (`Arg A D) (a , xs) (thereArg₂ i) X =
      a , update′ R (D a) xs i X
    update′ R (`Rec A D) (f , xs) (thereRec₁ g) (h , F) =
      (λ a → update (`Data R) (f a) (g a) (h a)) , F xs
    update′ R (`Rec A D) (f , xs) (thereRec₂ i) X =
      f , update′ R (D (fun ⟪ R ⟫ ∘ f)) xs i X
\end{code}

Again, the only case that differs significantly from the open universe
is \AgdaCon{thereArg₁}. Here, we recursively update something within
the value \AgdaVar{a} (rather than immediately updating the entire
\AgdaVar{a}), and apply the translation function to the second
component of the pair.

\section{Related Work}

\AgdaHide{
\begin{code}
module RelatedWork where
\end{code}}


Our work concerns programming over InfIR types. We demonstrate how to
do this by using either computational return types (like in
\AgdaFun{lookup}) or computational argument types (like in
\AgdaFun{update}).

Recall from the background \refsec{problem:head} that we could write a
total version of \AgdaFun{head} either by using a computational return
\emph{or} argument type. Thus, we could have written \AgdaFun{lookup}
using a computational argument instead. Below, imagine a computational
argument type \AgdaFun{Lookup} that gathers a product of all the
infinitary arguments. Then, we could write a version of
\AgdaFun{lookup} with a computational argument type \AgdaFun{Lookup}
and a static return type, with the following type signature.

\AgdaHide{
\begin{code}
  postulate
    Type : Set
    Path : Type → Set
    Lookup : (A : Type) → Path A → Set₁
\end{code}}

\begin{code}
    lookup : (A : Type) (i : Path A) → Lookup A i → Type
\end{code}

There are many examples in the literature of functions like
\AgdaFun{lookup}, which take an InfIR type and some extra information
using a computational argument type, to extract information using the
InfIR type. We will discuss several works that fall into this category
below.

Before we do, we point out that the way our \AgdaFun{lookup}
works is somewhat different because it uses a computational return type,
which is not common in the literature. However, the real novelty of our
work is the \AgdaFun{update} function, an example of modifying an
InfIR type. Modification of dependent types is tricky due to the
dependencies involved, and the higher-order and mutual nature of InfIR
types complicates the situation even more. The \AgdaFun{update}
function solves these problems by using translation functions supplied
by its computational \AgdaFun{Update} argument. An interesting
property of the computation argument type \AgdaFun{Update} is that it
needs to be mutually with the function that uses it,
\AgdaFun{update}. We are not aware of any other examples in literature
that perform updates to InfIR types. With that out of the way, let's
go over work related to retrieving information using InfIR types and
computational argument types.

\paragraph{File Formats}

\citet{oury:tpop} define an InfIR universe of file
\AgdaData{Format}s, where later parts of the file format may be
dependent on length information gathered from earlier parts of the
file format. They define a generic function for this universe to
\AgdaFun{parse} a list of bits to a value in this universe. They also
define a generic \AgdaFun{print} function that translates a value of
this universe into a list of bits. The meaning function of this
universe computes the type of dependent pairs, but not dependent
functions, so \AgdaFun{parse} and \AgdaFun{print} can get away with
static arguments and return types rather than computational ones.

\paragraph{Induction}

\citet{chapman:levitation} define \AgdaData{Desc}riptions for
indexed dependent types (without induction-recursion). Defining a
generic \AgdaFun{ind}unction principles for types encoded by
\AgdaData{Desc}riptions requires a computational argument type for all
the inductive hypotheses (\AgdaData{All}, also called \AgdaData{Hyps}). 
Although \AgdaData{Desc} is not inductive-recursive, it is still
infinitary so generic functions over such types, like \AgdaFun{ind},
share many of the same properties as our generic functions.

Our previous work~\citep{diehl:gelim} expands upon the work of
\citeauthor{chapman:levitation}, defining an alernative interface to
induction as generic type-theoretic
\AgdaFun{elim}inators for \AgdaData{Desc}riptions. Defining these
eliminators involves several nested constructions, where both
computational argument types (to collect inductive hypotheses) and return
types (to produce custom eliminator types for each description) are
used for information retrieval but not modification of infinitary
descriptions.

\paragraph{Termination Proofs}

\citet{coquand:realizability} proves termination of Martin-L{\"o}f’s
type theory using realizability predicates. The realizability model is
defined as a family of InfIR type indexed by syntactic
expressions. Proofs that correspond to \AgdaFun{reflect}ion into the model,
\AgdaFun{reif}ication of the model, and \AgdaFun{eval}uation of expressions into the
model all involve retrieving information contained inside the model.
The model is represented as an InfIR type in the appendix of the
paper. The InfIR type contains expressions, witnesses of the
evaluation relation, and witnesses of expression normality and
neutrality.

\paragraph{Generic Programming \& Universal Algebra}

\citet{benke:generic} uses Dybjer-Setzer InfIR \AgdaData{Desc}riptions to
perform generic programming in the domain of universal
algebra. However, a custom restriction of the \AgdaData{Desc} universe
is used for each algebra (e.g. one-sorted term algebras, many-sorted
term algebras, parameterized term algebras, etc.). Some of these
algebra restrict the universe to be finitary, some remain infinitary,
but all of them restrict the use of induction-recursion. As they
state, their work could have been instead defined as restrictions over
a universe of indexed inductive types without induction-recursion.

\paragraph{Ornaments}

\citet{mcbride:ornaments} builds a theory
of \AgdaData{Orn}aments on top of \AgdaData{Desc}riptions for
indexed dependent types (without induction-recursion). Ornaments allow
a description of one type (such as a \AgdaData{Vec}tor) to be related
to another type (such as a \AgdaData{List}) such that a \AgdaFun{forget}ful map
from the more finely indexed type to the less finely indexed type can
be derived as a generic function. \citet{dagand:ornaments} expand this
work to also derive a certain class of functions with less finely
indexed types from functions with more finely indexed types.

%% retrieving information using an InfIR versus modifying an InfIR type

%% \acks
%% Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}

% The bibliography should be embedded for final submission.

\bibliography{infir}

\end{document}
