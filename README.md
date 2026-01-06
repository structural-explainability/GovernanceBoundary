# Structural Explainability: Governance Boundary

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/license/MIT)
![Build Status](https://github.com/structural-explainability/GovernanceBoundary/actions/workflows/ci-lean.yml/badge.svg?branch=main)
[![Check Links](https://github.com/structural-explainability/GovernanceBoundary/actions/workflows/links.yml/badge.svg)](https://github.com/structural-explainability/GovernanceBoundary/actions/workflows/links.yml)

> Lean 4 formalization of the Governance Boundary.

## What This Formalizes

This repository provides a Lean 4 formalization
of the Governance Boundary.

## Build and Run

```shell
lake update
lake build
lake exe verify
```

## Developer (running pre-commit)

Pre-commit is optional; CI will report exact commands if it fails.

Steps to run pre-commit locally. Install `uv`.

Initialize once:

```shell
uv self update
uvx pre-commit install
uvx pre-commit run --all-files
```

Save progress as needed:

```shell
git add -A
# If pre-commit makes changes, re-run `git add -A` before committing.
git commit -m "update"
git push -u origin main
```

## Annotations

[ANNOTATIONS.md](./ANNOTATIONS.md)

## Citation

[CITATION.cff](./CITATION.cff)

## License

[MIT](./LICENSE)
