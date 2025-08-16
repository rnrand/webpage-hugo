---
# Documentation: https://wowchemy.com/docs/managing-content/

title: 'VyZX: Formal Verification of a Graphical Quantum Language'
subtitle: ''
summary: ''
authors:
- Adrian Lehmann
- Ben Caldwell
- Bhakti Shah
- Robert Rand
tags: []
categories: []
date: '2023-01-01'
lastmod: 2024-04-02T23:35:19-05:00
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
publishDate: '2024-04-03T04:35:18.810505Z'
publication_types:
- '3'
abstract: Mathematical representations of graphs often resemble adjacency matrices or lists, representations that facilitate whiteboard reasoning and algorithm design. In the realm of proof assistants, inductive representations effectively define semantics for formal reasoning. This highlights a gap where algorithm design and proof assistants require a fundamentally different structure of graphs, particularly for process theories which represent programs using graphs. To address this gap, we present VyZX, a verified library for reasoning about inductively defined graphical languages. These inductive constructs arise naturally from category theory definitions. A key goal for VyZX is to Verify the ZX-calculus, a graphical language for reasoning about quantum computation. The ZX-calculus comes with a collection of diagrammatic rewrite rules that preserve the graph's semantic interpretation. We show how inductive graphs in VyZX are used to prove the correctness of the ZX-calculus rewrite rules and apply them in practice using standard proof assistant techniques. VyZX integrates easily with the proof engineer's workflow through visualization and automation.
publication: ''
doi: 10.48550/arXiv.2311.11571
links:
- name: arXiv
  url: https://arxiv.org/abs/2311.11571
---
