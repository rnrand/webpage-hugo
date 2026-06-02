---
# Documentation: https://wowchemy.com/docs/managing-content/

title: A Formally Certified End-to-End Implementation of Shor's Factorization Algorithm
subtitle: ''
summary: ''
authors:
- Yuxiang Peng 
- Kesha Hietala 
- Runzhou Tao 
- Liyi Li 
- Robert Rand 
- Michael Hicks 
- Xiaodi Wu
tags: []
categories: []
date: '2023-04-18'
lastmod: 2023-04-18T16:34:22-05:00
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
publication_types:
- '2'
abstract: 'Quantum computing technology may soon deliver revolutionary improvements in algorithmic performance, but these are only
useful if computed answers are correct. While hardware-level decoherence errors have garnered significant attention, a less
recognized obstacle to correctness is that of human programming errors—“bugs”. Techniques familiar to most programmers
from the classical domain for avoiding, discovering, and diagnosing bugs do not easily transfer, at scale, to the quantum
domain because of its unique characteristics. To address this problem, we have been working to adapt formal methods to
quantum programming. With such methods, a programmer writes a mathematical specification alongside their program, and
semi-automatically proves the program correct with respect to it. The proof’s validity is automatically confirmed—certified—by
a “proof assistant”. Formal methods have successfully yielded high-assurance classical software artifacts, and the underlying
technology has produced certified proofs of major mathematical theorems. As a demonstration of the feasibility of applying
formal methods to quantum programming, we present the first formally certified end-to-end implementation of Shor’s prime
factorization algorithm, developed as part of a novel framework for applying the certified approach to general applications. By
leveraging our framework, one can significantly reduce the effects of human errors and obtain a high-assurance implementation
of large-scale quantum applications in a principled way'

publication: '*Proceedings of the National Academy of Sciences (PNAS)*'
doi: 10.1073/pnas.2218775120
<!-- url_pdf: files/shor.pdf -->
url_code: https://github.com/inQWIRE/SQIR/tree/main/examples/shor
links:
- name: arXiv
  url: https://arxiv.org/pdf/2204.07112.pdf

---
