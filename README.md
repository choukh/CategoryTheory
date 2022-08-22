# Category Theory

This project is a Coq formalization of the textbook [Categories and Toposes: Visualized and Explained](https://www.amazon.com/Categories-Toposes-Visualized-Richard-Southwell/dp/B0948LKZXX) with the help of the library [coq-category-theory](https://github.com/jwiegley/category-theory). I hope it will help learning the book and the library at the same time.

## Installation
Use [opam](https://opam.ocaml.org/) to manage dependencies.

```Bash
opam install coq
opam install coq-equations
opam install coq-category-theory
make
```

## Dependencies

```Bash
opam list
```

|  Package            | Version  | Description  |
|  ----               | ----     | ---- |
| coq                 | 8.15.2   | Formal proof management system |
| coq-equations       | 1.3+8.15 | A function definition package for Coq
| coq-category-theory | 1.0.0    |  An axiom-free formalization of category theory in Coq
