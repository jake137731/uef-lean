import Lake
open Lake DSL

package uef

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib UEF where
  roots := #[`UEF, `UEFReal, `UEFRoots, `UEFTime, `UEFBell, `UEFFields, `UEFGauss, `UEFEmergence, `UEFStandardModel, `UEFGolden, `UEFDark, `UEFGravity, `UEFHolography, `UEFTorus, `UEFTunneling, `UEFContainment, `UEFMoral, `UEFCycle, `UEFCollapse]
