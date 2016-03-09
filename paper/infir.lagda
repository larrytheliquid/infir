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
data Type : Set
⟦_⟧ : Type → Set

data Type where
  `ℕ : Type
  `Π : (A : Type) (B : ⟦ A ⟧ → Type) → Type

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

\subsection{Writing total functions}

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
