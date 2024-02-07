# Extensions of nonarchimedean norms and applications to Number Theory

This repository contains the Lean 4 version of the source code for the article "Formalizing Norm Extensions and Applications to Number Theory", [presented at ITP 2023](https://mizar.uwb.edu.pl/ITP2023/).

The field $\mathbb{R}$ of real numbers is obtained from the rational numbers 
$\mathbb{Q}$ by taking the completion with respect to the usual absolute value. We then define the complex numbers $\mathbb{C}$ as the algebraic closure of $\mathbb{R}$. The $p$-adic analogue of the real numbers is the field $\mathbb{Q}_p$ of $p$-adic numbers, obtained by completing $\mathbb{Q}$ with respect to the $p$-adic norm. In this paper, we formalize in Lean 3 the definition of the $p$-adic analogue of the complex numbers, which is the field $\mathbb{C}_p$ of $p$-adic complex numbers, a field extension of $\mathbb{Q}_p$ which is both algebraically closed and complete with respect to the extension of the  $p$-adic norm.

More generally, given a field $K$ complete with respect to a nonarchimedean real-valued norm, and an algebraic field extension  $L/K$, we show that there is a unique norm on $L$ extending the given norm on $K$, with an explicit description.

Building on the definition of the $p$-adic complex numbers, we formalize the definition of the Fontaine period ring $B_{\text{HT}}$ and discuss some applications to the theory of Galois representations and to $p$-adic Hodge theory.

The results formalized in this paper are a prerequisite to formalize Local Class Field Theory, which is a fundamental ingredient of the proof of Fermat's Last Theorem.

Copyright (C) 2024, María Inés de Frutos-Fernández
