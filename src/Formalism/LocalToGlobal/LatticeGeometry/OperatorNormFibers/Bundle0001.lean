module

public import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.StExtInv

@[expose] public section

-- bundled from Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.HnStepEqOfNorm
section
open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

section ExtensionInterSubspace

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_compl_inf (L : Submodule (𝓞 K) V) (hL : L.FG) (W₀ : Submodule K V) :
    ∃ C : Submodule (𝓞 K) V, C ≤ L ∧
      (∀ x ∈ L, ∃ a ∈ L ⊓ W₀.restrictScalars (𝓞 K), ∃ c ∈ C, x = a + c) ∧
      ∀ u ∈ Submodule.span K (C : Set V), u ∈ W₀ → u = 0 := by
  classical
  let N : Submodule (𝓞 K) L := (W₀.restrictScalars (𝓞 K)).comap L.subtype
  have htor : Submodule.torsion (𝓞 K) (L ⧸ N) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨a, haq⟩ := (Submodule.mem_torsion_iff q).1 hq
    obtain ⟨z, rfl⟩ := N.mkQ_surjective q
    have h1 : ((a : 𝓞 K) • z) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa [Submonoid.smul_def] using haq
    have ha0 : algebraMap (𝓞 K) K (a : 𝓞 K) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    have h2 : (z : V) ∈ W₀ := by
      have h3 : ((a : 𝓞 K) • (z : V)) ∈ W₀ := h1
      rw [← algebraMap_smul K] at h3
      have h4 := W₀.smul_mem (algebraMap (𝓞 K) K a)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h4
    rw [Submodule.mem_bot]
    exact (Submodule.Quotient.mk_eq_zero N).2 h2
  have : Module.Flat (𝓞 K) (L ⧸ N) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
  have := Module.finitePresentation_of_finite (𝓞 K) (L ⧸ N)
  have : Module.Projective (𝓞 K) (L ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' : ∀ q, N.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
  refine ⟨(LinearMap.range s).map L.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact z.2
  · intro x hx
    have hmem : ((⟨x, hx⟩ : L) - s (N.mkQ ⟨x, hx⟩)) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      have := hs' (N.mkQ ⟨x, hx⟩)
      simp only [Submodule.mkQ_apply] at this ⊢
      rw [this, sub_self]
    refine ⟨x - (s (N.mkQ ⟨x, hx⟩) : V), ⟨L.sub_mem hx (s _).2, hmem⟩,
      (s (N.mkQ ⟨x, hx⟩) : V), ⟨s (N.mkQ ⟨x, hx⟩), ⟨_, rfl⟩, rfl⟩, by abel⟩
  · intro u hu huW
    obtain ⟨d, hd, hdu⟩ := Formalism.LFunctionChainParameters.LLcv.span_le_locS _ hu
    obtain ⟨_, ⟨q, rfl⟩, hq⟩ := hdu
    have hW : ((s q : L) : V) ∈ W₀ := by
      rw [show ((s q : L) : V) = d • u from hq, ← algebraMap_smul K d u]
      exact W₀.smul_mem _ huW
    have hq0 : q = 0 := by
      rw [← hs' q]
      exact (Submodule.Quotient.mk_eq_zero N).2 hW
    have h5 : d • u = 0 := by
      rw [← hq, hq0, map_zero, map_zero]
    rw [← algebraMap_smul K d u] at h5
    exact (smul_eq_zero.1 h5).resolve_left (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd)

end ExtensionInterSubspace

section Transport

variable {R : Type*} [Ring R] {V : Type*} [AddCommGroup V] [Module R V]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end Transport

end Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd
end
end

-- bundled from Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PExtInvMuB
section
open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvMu

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

section Places

variable (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']


open Classical in
theorem card_fiber [_root_.NumberField.IsTotallyComplex K] (v : InfinitePlace K) :
    (Finset.univ.filter fun v' : InfinitePlace K' => v'.comap (algebraMap K K') = v).card =
      finrank K K' := by
  classical
  have h := InfinitePlace.unramifedPlacesOver_ncard_add_eq_finrank K' v
  have h0 : InfinitePlace.ramifiedPlacesOver K' v = ∅ := by
    ext w
    simp only [InfinitePlace.ramifiedPlacesOver, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨_, hw⟩
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)
      (InfinitePlace.isRamified_iff.1 hw).2
  have h1 : InfinitePlace.unramifiedPlacesOver K' v =
      ((Finset.univ.filter fun v' : InfinitePlace K' => v'.comap (algebraMap K K') = v :
        Finset (InfinitePlace K')) : Set (InfinitePlace K')) := by
    ext w
    simp only [InfinitePlace.unramifiedPlacesOver, Set.mem_ofPred_eq, Finset.coe_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, _⟩
      exact InfinitePlace.LiesOver.comap_eq w v
    · rintro rfl
      refine ⟨⟨?_⟩, ?_⟩
      · ext x
        rfl
      · by_contra hr
        exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)
          (InfinitePlace.isRamified_iff.1 hr).2
  rw [h0, h1, Set.ncard_empty, mul_zero, add_zero, Set.ncard_coe_finset] at h
  exact h

theorem nPl_ext [_root_.NumberField.IsTotallyComplex K] [_root_.NumberField.IsTotallyComplex K'] : nPl K' = finrank K K' * nPl K := by
  have h1 := sizeMu_finrank_eq K
  have h2 := sizeMu_finrank_eq K'
  have h3 := Module.finrank_mul_finrank ℚ K K'
  rw [h1, h2] at h3
  linarith

end Places

end Formalism.L2.Geo.ExtensionFiltration.ExtInvMu
end
end

