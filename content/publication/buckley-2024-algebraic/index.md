---
# Documentation: https://wowchemy.com/docs/managing-content/

title: An Algebraic Language for Specifying Quantum Networks
subtitle: ''
summary: ''
authors:
- Anita Buckley
- Pavel Chuprikov
- Rodrigo Otoni
- Robert Rand
- Robert Soulé
- Patrick Eugster
tags:
- entanglement
- kleene algebra
- quantum networks
categories: []
date: '2024-01-01'
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
publishDate: '2024-04-01T20:49:38.643416Z'
publication_types:
- '1'
abstract: Quantum networks connect quantum capable nodes in order to achieve capabilities
  that are impossible only using classical information. Their fundamental unit of
  communication is the Bell pair, which consists of two entangled quantum bits. Unfortunately,
  Bell pairs are fragile and difficult to transmit directly, necessitating a network
  of repeaters, along with software and hardware that can ensure the desired results.
  To this end, we developed BellKAT, a novel specification language for quantum networks
  based upon Kleene algebra. To cater to the specific needs of quantum networks, we
  designed an algebraic structure, called BellSKA, which we use as the basis of BellKAT’s
  denotational semantics. BellKAT’s constructs describe entanglement distribution
  rules that allow for modular specification. We give BellKAT a sound and complete
  equational theory, allowing us to verify network protocols. We provide a prototype
  tool to showcase the expressiveness of BellKAT and how to verify networks in practice.
publication: '*Programming Language Design and Implementation (PLDI)*'
url_video: 'https://youtu.be/RYyAMsVD4Gs?si=iRRe_XEG-_fQCZsh'
doi: 10.1145/3656430
url_code: 'https://github.com/swystems/bellkat'
---
<iframe width="560" height="315" src="https://www.youtube.com/embed/RYyAMsVD4Gs?si=eH1ppVOEYiVKrWnQ" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" referrerpolicy="strict-origin-when-cross-origin" allowfullscreen></iframe>