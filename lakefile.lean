import Lake
open Lake DSL

package «stage2-judge»

-- Pinned Mathlib revision (bump deliberately via `lake update`).
-- lake-manifest.json is the source of truth for the exact commit.
-- Currently mathlib4 tag v4.33.1, matching `lean-toolchain`.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib «JudgeMagma» where
  srcDir := "judge"
  roots := #[`JudgeMagma.Magma]

lean_lib «JudgeDecide» where
  srcDir := "judge"
  roots := #[`JudgeDecide.DecideBang]

lean_lib «JudgeFinOp» where
  srcDir := "judge"
  roots := #[`JudgeFinOp.MemoFinOp]

lean_lib «JudgeSupport» where
  srcDir := "judge"
  roots := #[`JudgeSupport.Inspect]
