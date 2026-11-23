module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.InterModel

variable {X Z : Scheme.{0}} {k : Type} [Field k] [Algebra k Γ(X, ⊤)]

variable (k) {ι : Type} [Fintype ι]

theorem radical_ker (f : Z ⟶ X) [QuasiCompact f] [IsReduced Z] : f.ker.radical = f.ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  refine Ideal.IsRadical.radical fun a ⟨n, hn⟩ => ?_
  rw [RingHom.mem_ker] at hn ⊢
  rw [map_pow] at hn
  exact IsNilpotent.eq_zero ⟨n, hn⟩

theorem interNumRed_eq_interNumOn (f : Z ⟶ X) [IsClosedImmersion f] [IsReduced Z]
    (C : Closeds X) (h : Set.range f = C) (L : ι → LB X) :
    interNumRed k C L = interNumOn k f L := by
  rw [interNumOn_eq_interNumSub, interNumRed_def, ← radical_ker f,
    ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 2
  ext1
  rw [Scheme.Hom.support_ker, h, C.isClosed.closure_eq]

end GlobalTheory.InterModel
