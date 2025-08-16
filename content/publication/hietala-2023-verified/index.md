---
# Documentation: https://wowchemy.com/docs/managing-content/

title: A Verified Optimizer for Quantum Circuits
subtitle: ''
summary: ''
authors:
- Kesha Hietala
- Robert Rand
- Liyi Li
- Shih-Han Hung
- Xiaodi Wu
- Michael Hicks
tags:
- Formal verification
- quantum computing
- circuit optimization
- certified compilation
categories: []
date: '2023-09-01'
lastmod: 2024-04-01T15:49:38-05:00
featured: false
draft: false

# Featured image
# To use, add an image named `featured.jpg/png` to your page's folder.
# Focal points: Smart, Center, TopLeft, Top, TopRight, Left, Right, BottomLeft, Bottom, BottomRight.
image:
  caption: ''
  focal_point: ''
  preview_only: false

# Projects (optional).
#   Associate this post with one or more of your projects.
#   Simply enter your project's folder or file name without extension.
#   E.g. `projects = ["internal-project"]` references `content/project/deep-learning/index.md`.
#   Otherwise, set `projects = []`.
projects: []
publishDate: '2024-04-01T20:49:38.465360Z'
publication_types:
- '2'
abstract: We present voqc, the first verified optimizer for quantum circuits, written
  using the Coq proof assistant. Quantum circuits are expressed as programs in a simple,
  low-level language called sqir, a small quantum intermediate representation, which
  is deeply embedded in Coq. Optimizations and other transformations are expressed
  as Coq functions, which are proved correct with respect to a semantics of sqir programs.
  sqir programs denote complex-valued matrices, as is standard in quantum computation,
  but we treat matrices symbolically to reason about programs that use an arbitrary
  number of quantum bits. sqir’s careful design and our provided automation make it
  possible to write and verify a broad range of optimizations in voqc, including full-circuit
  transformations from cutting-edge optimizers.
publication: '*ACM Transactions on Programming Languages and Systems*'
doi: 10.1145/3604630
links:
- name: URL
  url: https://doi.org/10.1145/3604630
---
