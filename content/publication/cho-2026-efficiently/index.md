---
# Documentation: https://wowchemy.com/docs/managing-content/

title: Efficiently Verifying Quantum Programs with Few T Gates
subtitle: ''
summary: ''
authors:
- Youngchan Cho
- Robert Rand
tags: []
categories: []
date: '2026-01-01'
lastmod: 2026-01-27T13:22:39-06:00
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
publishDate: '2026-01-27T19:22:39.495070Z'
publication_types:
- '1'
abstract: 'We mechanize a lightweight quantum logic in the Rocq proof assistant to
  verify Clifford+T quantum programs, particularly those with low T counts. Our tool
  is lightweight and automation-centric: Hoare triple validation composes simple rules,
  reduces all obligations to syntactic well-formedness side-conditions, and efficiently
  discharges those conditions. We demonstrate our tool using several case studies:
  a standard low-T Toffoli decomposition, graph-state generators, and the 7-qubit
  Steane encoder. A small empirical study on graph-state families shows near-linear
  growth in the number of Clifford gates and a slightly super-quadratic trend in the
  number of qubits, consistent with implementation overheads from list-based tensor
  representations, while repeated T gates on a single qubit exhibit an exponential
  blow-up due to additive branching. The results indicate that a rule-driven, syntax-directed
  approach suffices to verify low-T quantum circuits while keeping the trusted core
  and user-facing proofs simple.'
publication: '*Verification, Model Checking, and Abstract
  Interpretation (VMCAI)*'
url_code: 'https://github.com/inQWIRE/Heisenberg-Logic'
links:
- name: Paper
  url: https://rdcu.be/e00Th
doi: 10.1007/978-3-032-15700-3_3
---
