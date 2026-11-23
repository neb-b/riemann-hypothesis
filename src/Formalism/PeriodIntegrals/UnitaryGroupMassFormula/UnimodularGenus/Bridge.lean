module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.UnimodLocalOfLocDual
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.ExistsIsomLoc

@[expose] public section

namespace PI.UG.W

open NumberField Module
open Formalism.HermitianLatticesTheory (locBasic_hcompl_not_mem locDual_mem_dualAt)

theorem isomLocStd : IsomLocStd := by
  intro E _ _ _ n hE N hN p hp hu
  have hs := hStd_isSymm E n
  have hI := stdLat_isOrtho E n
  have hFull : Submodule.IsFullLattice E N := by
    refine { toIsLattice := hN, span_eq_top := ?_ }
    let W := Submodule.span E (N : Set (Sp E n))
    change W = ⊤
    by_contra hW
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let g : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : finrank E (Module.Dual E W) < finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have horth (y : Sp E n) (hy : y ∈ W) : hStd E n y (e x) = 0 := by
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, hy⟩) (LinearMap.mem_ker.mp hx)
      rw [← (LinearMap.isSymm_def.mp hs) (e x) y, hxy, map_zero]
    -- Localization preserves the ambient span, and self-duality puts the orthogonal vector in it.
    let : p.IsPrime := hp.isPrime
    have hloc {y : Sp E n}
        (hy : y ∈ Formalism.HermitianLatticesTheory.loc (K := E) p N) : y ∈ W := by
      obtain ⟨s, hs', hsy⟩ := hy
      have hs₀ : algebraMap (𝓞 E) E s ≠ 0 := by
        intro hzero
        have : s = 0 := IsFractionRing.injective (𝓞 E) E (by simpa using hzero)
        exact locBasic_hcompl_not_mem p s hs' (this ▸ p.zero_mem)
      exact (W.smul_mem_iff hs₀).mp
        (by rw [algebraMap_smul]; exact Submodule.subset_span hsy)
    have hxW : e x ∈ W := by
      apply hloc
      change Formalism.HermitianLatticesTheory.IsUnimodularAt (hStd E n) p N at hu
      rw [Formalism.HermitianLatticesTheory.IsUnimodularAt] at hu
      rw [← hu, locDual_mem_dualAt]
      intro y hy
      rw [horth y (hloc hy)]
      exact Submodule.zero_mem _
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hpos := ReciprocityTheory.ChartRestriction.L3.isTotPosDef_of_ortho hE hs hI (e x)
      (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) φ
    simp [horth (e x) hxW] at hpos
  exact ReciprocityTheory.ChartRestriction.L3.exists_isom_loc hE hs hI hFull p hp hu

end PI.UG.W
