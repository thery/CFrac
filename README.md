<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Continuous Fraction

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/cfrac/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/cfrac/actions/workflows/docker-action.yml




Continuous Fraction in Rocq

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Additional dependencies:
  - [MathComp ssreflect 2.5 or later](https://math-comp.github.io)
- Rocq/Coq namespace: `cfrac`
- Related publication(s): none

## Building and installation instructions

To build and install manually, do:

``` shell
git clone https://github.com/thery/cfrac.git
cd cfrac
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



