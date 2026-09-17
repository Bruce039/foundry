---
forge: patch
foundry-cheatcodes: patch
foundry-common: patch
---

Fixed stale test and script bytecode after body-only changes to native dependencies, and dynamically linked eligible contracts outside `src` without disabling safe rewrites in mixed test files. After upgrading, run `forge test --force` once in projects with artifacts cached by an affected version.
