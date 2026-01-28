---
# Documentation: https://wowchemy.com/docs/managing-content/

title: A Language for Quantifying Quantum Network Behavior
subtitle: ''
summary: ''
authors:
- Anita Buckley
- Pavel Chuprikov
- Rodrigo Otoni
- Robert Soulé
- Robert Rand
- Patrick Eugster
tags:
- entanglement distribution
- probabilistic and possibilistic semantics
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
publishDate: '2026-01-17T18:15:07.872123Z'
publication_types:
- '1'
abstract: Quantum networks have capabilities that are impossible to achieve using
  only classical information. They connect quantum capable nodes, with their fundamental
  unit of communication being the Bell pair, a pair of entangled quantum bits. Due
  to the nature of quantum phenomena, Bell pairs are fragile and difficult to transmit
  over long distances, thus requiring a network of repeaters along with dedicated
  hardware and software to ensure the desired results. The intrinsic challenges associated
  with quantum networks, such as competition over shared resources and high probabilities
  of failure, require quantitative reasoning about quantum network protocols. This
  paper develops PBKAT, an expressive language for specification, verification and
  optimization of quantum network protocols for Bell pair distribution. Our language
  is equipped with primitives for expressing probabilistic and possibilistic behaviors,
  and with semantics modeling protocol executions. We establish the properties of
  PBKAT’s semantics, which we use for quantitative analysis of protocol behavior.
  We further implement a tool to automate PBKAT’s usage, which we evaluated on real-world
  protocols drawn from the literature. Our results indicate that PBKAT is well suited
  for both expressing real-world quantum network protocols and reasoning about their
  quantitative properties.
publication: '*Object-Oriented Programming, Systems, Languages & Applications (OOPSLA)*'
doi: 10.1145/3763135
links:
- name: Video
  url: https://youtu.be/ytPQyhuo0Ao?si=vGuAHYhXbWr_L2kq
url_code: https://github.com/swystems/prob-bellkat
---
<iframe width="560" height="315" src="https://www.youtube.com/embed/ytPQyhuo0Ao?si=o59eQ1ItbRCLF_n_" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" referrerpolicy="strict-origin-when-cross-origin" allowfullscreen></iframe>