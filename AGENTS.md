# Working mode: speed, prototyping, and exploration

- This project prioritizes speed, prototyping, and exploration. It is not an industrial product maintenance effort.
- Take the shortest direct path to useful code and experimental feedback. Do not add process or infrastructure just because it is considered a "best practice."
- Use each project's Aeneas branch and worktree directly. Do not require or introduce commit-SHA pinning for this workflow.
- Do not add reproducibility machinery, release processes, broad test matrices, mandatory reviews, or extra approval steps unless the user requests them or they are concretely necessary for the current task.
- Keep checks focused on the current experiment and report results accurately. Do not turn exploratory work into a production-hardening exercise.
- When the user rejects unnecessary process, remove it from the plan and conflicting instructions. Do not argue for it again or reintroduce it under different wording.

# Aeneas fork development

- This repository is the user's fork: `git@github.com:xiyuzhai-husky-lang/aeneas.git`.
- The canonical local clone is `/Volumes/Extreme Pro/repos/aeneas`.
- Use `husky-patch` for shared Aeneas work and project-specific branches/worktrees such as `husky-patch-sat-chapters` and `husky-patch-batsat` for separate experiments.
- SAT/SMT chapter implementations and proofs live separately in `/Volumes/Extreme Pro/repos/amazon-ai-husky-sat-smt`, on branch `sat-smt`. Preserve completed chapters as independently reviewable implementations and proofs.
- Check the actual repository and branch before editing. The chat's default directory can belong to the separate Amazon AI Husky repository.
- Use relevant compiler guidance in `CLAUDE.md` and `documentation/skills/aeneas-compiler-dev.instructions.md` within the user-authorized scope. The user's explicit speed and exploration priorities take precedence over conflicting local workflow conventions.

# User shorthand

- `wn` means “what's next?” Answer with the next step for the current task.
- `c` means “continue.” Continue the already authorized work within its current scope.
