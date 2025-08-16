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
tags: []
categories: []
date: '2025-10-01'
lastmod: 2025-07-02T16:18:05+10:00
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
publishDate: '2025-07-02T06:18:05.170282Z'
publication_types:
- '1'
url_pdf: files/compiling_qunity.pdf
url_code: https://github.com/mikhailmints/qunity
abstract: "Most existing quantum programming languages are based on the quantum circuit model of computation,
as higher-level abstractions are particularly challenging to implement---especially ones relating
to quantum control flow. The Qunity language, proposed by Voichick et al., offered such an abstraction in 
the form of a quantum control construct, with great care taken to ensure that the resulting 
language is still realizable. However, Qunity lacked a working implementation, and the originally proposed compilation procedure was very inefficient, with even simple quantum algorithms compiling to unreasonably large circuits.


In this work, we focus on the efficient compilation of high-level quantum control flow constructs,
using Qunity as our starting point. We introduce a wider range of abstractions on top of Qunity's core language that offer compelling trade-offs
compared to its existing control construct. We create a complete implementation of a Qunity compiler, which converts high-level Qunity code into the quantum assembly language OpenQASM 3.
We develop optimization techniques for multiple stages of the Qunity compilation procedure, including both low-level circuit optimizations as well as methods that consider the high-level structure of a Qunity program, greatly reducing the number of qubits and gates used by the compiler."
publication: '*ACM SIGPLAN Conference on Object-Oriented Programming, Systems, Languages \& Applications (OOPSLA)*'
---
