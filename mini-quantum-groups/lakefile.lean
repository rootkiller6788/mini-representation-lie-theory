import Lake
open Lake DSL

package «mini-quantum-groups» where

@[default_target]
lean_lib «MiniQuantumGroups» where
  roots := #[`MiniQuantumGroups]

require «mini-object-kernel» from "../../0. mini-math-kernel/mini-object-kernel"
