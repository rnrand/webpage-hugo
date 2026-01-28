---
# Documentation: https://wowchemy.com/docs/managing-content/

title: Compositional Quantum Control Flow with Efficient Compilation in Qunity
subtitle: ''
summary: ''
authors:
- Mikhail Mints
- Finn Voichick
- Leonidas Lampropoulos
- Robert Rand
tags:
- compiler optimizations
- high-level programming languages
- quantum control flow
- quantum programming languages
- quantum subroutines
categories: []
date: '2025-10-01'
lastmod: 2026-01-17T19:15:08+01:00
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
publishDate: '2026-01-17T18:15:08.491249Z'
publication_types:
- '1'
abstract: Most existing quantum programming languages are based on the quantum circuit
  model of computation, as higher-level abstractions are particularly challenging
  to implement—especially ones relating to quantum control flow. The Qunity language,
  proposed by Voichick et al., offered such an abstraction in the form of a quantum
  control construct, with great care taken to ensure that the resulting language is
  still realizable. However, Qunity lacked a working implementation, and the originally
  proposed compilation procedure was very inefficient, with even simple quantum algorithms
  compiling to unreasonably large circuits.    In this work, we focus on the efficient
  compilation of high-level quantum control flow constructs, using Qunity as our starting
  point. We introduce a wider range of abstractions on top of Qunity's core language
  that offer compelling trade-offs compared to its existing control construct. We
  create a complete implementation of a Qunity compiler, which converts high-level
  Qunity code into the quantum assembly language OpenQASM 3. We develop optimization
  techniques for multiple stages of the Qunity compilation procedure, including both
  low-level circuit optimizations as well as methods that consider the high-level
  structure of a Qunity program, greatly reducing the number of qubits and gates used
  by the compiler.
publication: '*Object-Oriented Programming, Systems, Languages & Applications (OOPSLA)*'
doi: 10.1145/3763056
links:
- name: arXiv
  url: https://arxiv.org/abs/2508.02857
- name: Video
  url: https://youtu.be/T-in4eBRg0E?si=fFtKI2GyBYuhZDuS
url_code: 'https://github.com/mikhailmints/qunity'
---
<iframe width="560" height="315" src="https://www.youtube.com/embed/T-in4eBRg0E?si=VWyaDKsHKcWOfUYn" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" referrerpolicy="strict-origin-when-cross-origin" allowfullscreen></iframe>