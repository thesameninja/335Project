# CSc 335 - Programming Language Paradigms - Project Part 1 (Spring 2025)
# Implementing and Analyzing "The Little Schemer" Interpreter (TLS)

## Project Overview

This project involves the implementation, analysis, and extension of a Scheme interpreter based on the concepts presented in Chapter 10 of "The Little Schemer" by Daniel P. Friedman and Matthias Felleisen. We refer to this interpreter and its implemented language subset as TLS (The Little Schemer) Scheme.

The project aims to deepen understanding of interpreter mechanics, functional programming (using pure R5RS Scheme), formal language definition, environment management, lexical scope, closures, recursion implementation (via the Y-combinator), and formal correctness proofs.

**Course:** CSc 335: Programming Language Paradigms
**Term:** Spring 2025
**Reference:** "The Little Schemer" (Chapters 9 & 10 primarily)
**Implementation Language:** R5RS Scheme (using DrRacket)

## Team Members

* [Sohail Ahmad]
* [Umaima Nasim]
* [Jia Xiang Zhang]

## Project Components

This repository contains the implementation and analysis covering the following components as outlined in the project description:

1.  **1.1: TLS Interpreter Implementation:**
    * A pure functional R5RS implementation of the interpreter described in Chapter 10.
    * Includes specifications (contracts, purpose statements) for each function.
    * Provides examples of TLS programs runnable by the interpreter.

2.  **1.2: TLS Language Definition and Syntax Checker:**
    * An inductive definition of the TLS Scheme fragment.
    * A purely functional R5RS syntax checker for TLS, detecting:
        * Malformed `cond` and `lambda` expressions.
        * Incorrect argument counts for primitives.
        * Unbound variables.

3.  **1.3: Environment Subsystem Analysis:**
    * A formal specification for the TLS environment subsystem.
    * Proof that the initial (Chapter 10) implementation satisfies the specification.
    * An alternative environment representation using lists of bindings.
    * Proof that the altered representation satisfies the specification and works with the interpreter.

4.  **1.4: Closures and Lexical Scope:**
    * Research write-up on closures and lexical scope.
    * Proof (using structural induction) that our TLS implementation correctly implements these concepts.

5.  **1.5: Interpreter Correctness Proof:**
    * A defined standard of correctness for the TLS interpreter.
    * Proof that our implementation meets this standard.

6.  **1.6: Dependence on Underlying R5RS:**
    * An explanation of how TLS relies on the host R5RS system (DrRacket), particularly regarding function call mechanics.

7.  **1.7: Recursion via Y-Combinator (TLS-REC):**
    * An extension of TLS (named TLS-REC) equipped with recursion using the Y-combinator (inspired by Chapter 9).
    * Research on Y-combinators.
    * Proof that the implemented combinator is a correct Y-combinator.
    * Detailed explanation of how the Y-combinator enables recursion.
    * Examples of recursive programs in TLS-REC.
