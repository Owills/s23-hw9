#lang scribble/manual
@require[scribble-math]
@require[scribble-math/dollar]
@require[racket/runtime-path]

@require["../../lib.rkt"]
@define-runtime-path[hw-file "hw9.lean"]


@title[#:tag "hw9" #:style (with-html5 manual-doc-style)]{Homework 9}

@bold{Released:} @italic{Monday, March 13, 2023 at 6:00pm}

@bold{Due:} @italic{Wednesday, March 22, 2023 at 6:00pm}

@nested[#:style "boxed"]{
What to Download:

@url{https://github.com/logiccomp/s23-hw9/raw/main/hw9.lean}
}

Please start with this file, filling in where appropriate, and submit your homework to the @tt{hw9} assignment on Gradescope. This page has additional information, and allows us to format things nicely.

@bold{To do this assignment in the browser: @link["https://github.com/codespaces/new?machine=basicLinux32gb&repo=578247746&location=EastUs&ref=main&devcontainer_path=.devcontainer%2Fdevcontainer.json"]{Create a Codespace}.}

In this homework assignment, you will get significantly more practice doing more challenging proofs in Lean. 

As before, we provide line counts for how long our reference solutions are: these are not the only ways to do the proofs (and you will not be penalized if you proofs take longer), and lines are a poor metric of complexity (as you can easily make things more compact or spread out), but are intended as a tool to help you not go too far down a path that isn't working. For example, if we had a proof that took 20 lines, and you are 100 lines into an attempt and it isn't working, it might be an indication that you made a decision (choice of what to do induction on, etc) that isn't working. 

@section{Problem 1: Append and Reverse}
First, a few proofs about append and reverse. For this assignment, we are using the standard library data structures, but here we define our own definition of append (called @lean{app}), instead of @lean{List.append}, and our own reverse (called @lean{rev}) instead of @lean{List.reverse}.

@minted-file-part["lean" "p1" hw-file]

@section{Problem 2: Evenness (and Relations)}

In this problem, you will practice more with expressing properties using relations (rather than boolean predicates). Here we have two different definitions of evenness (one of which you have seen in lecture before), and among other proofs, you will prove that the two are equivalent.

@minted-file-part["lean" "p2" hw-file]

@section{Problem 3: Subsequences}

In this problem, you will see a new relation, expressing when one list of natural numbers is a subsequence of another. To practice dealing with the relation (and understand how it works), you will prove a few properties about it.

@minted-file-part["lean" "p3" hw-file]



@section{Problem 4: Insertion Sort}

In this problem, you will prove insertion sort is correct. This will be done in several steps, first by proving various properties about the @lean{insert} function, which you will then be able to use to prove the same properties about @lean{isort}. 

There are two halves of the problem: first, to prove that @lean{isort} (and @lean{insert}) produces @italic{sorted} lists, where we have a relation that defines what it means to be sorted. This relation uses another relation, @lean{All}, as a helper: @lean{All} is a relation that holds when a property holds for all elements of a list, in this case, we use it to show that the front of a sorted list is less or equal to all other elements of the list. 

The other half of the problem is to ensure that @lean{isort} (and @lean{insert}) produce @italic{permutations} of the input lists. This relies upon a new definition of @italic{permutation}, which is a relation that holds when two lists have the same elements, but possibly in a different order. To practice with this definition (which is similar to the subsequence definition from Problem 3), we have a few theorems for you to prove, before proving the main results. 

We provide a few helper theorems that you may use in your proofs (we did in ours). In general, defining helper theorems is a good idea, as it can help you break down a problem into smaller pieces. 

@bold{Note: the proofs for the insert functions are where most of the work is!}

@minted-file-part["lean" "p4" hw-file]
