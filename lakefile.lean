import Lake
open Lake DSL

package omarwaCore where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib OmarwaCore where
  /- Kor modülleri kök dizinden okuyoruz; OmarwaCore.lean ve altındaki
     OmarwaCore/*.lean dosyaları aynı kütüphanede. -/
  srcDir := "."
