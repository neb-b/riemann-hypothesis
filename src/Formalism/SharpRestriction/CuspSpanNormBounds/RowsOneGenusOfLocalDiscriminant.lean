module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RowsOneGenusOfCyclic
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

section Conj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem unimodAt_of_unimod {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (L : Submodule (𝓞 E) V) (hlat : Submodule.IsLattice E L) (hu : IsUnimodular h L)
    (p : Ideal (𝓞 E)) : IsUnimodularAt h p L := by
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := FaithfulSMul.algebraMap_injective _ _
  have hst : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
    fun r => cyc_star_int r
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) (self := hlat)
  unfold IsUnimodularAt
  rw [locDual_dualAt_loc h hinj hst]
  have e1 := locDual_loc_dual_le h p L
  have e2 := locDual_dualAt_le h hst p L hfg
  unfold IsUnimodular at hu
  rw [hu] at e1 e2
  exact le_antisymm e2 e1

private theorem rows_riesz (S : Formalism.BasicNotions.HSpace E) (φ : S.V →ₗ[E] E) : ∃ μ : S.V, ∀ v, S.hT μ v = φ v := by
  classical
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis S.hT S.nondeg S.frame
  refine ⟨∑ j, star (φ (S.frame j)) • bs j, fun v => ?_⟩
  have key : S.hT (∑ j, star (φ (S.frame j)) • bs j) = φ := by
    apply S.frame.ext
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    have hs : ∀ j, S.hT (star (φ (S.frame j)) • bs j) (S.frame i) =
        φ (S.frame j) * (if i = j then 1 else 0) := by
      intro j
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      congr 1
      rw [← S.herm.eq (S.frame i) (bs j), hbs]
      split_ifs <;> simp
    simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [key]

private theorem rows_span_eq_top_of_unimodular (S : Formalism.BasicNotions.HSpace E) {Λ : Submodule (𝓞 E) S.V}
    (hL : Λ.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) :
    Submodule.span E (Λ : Set S.V) = ⊤ := by
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨μ, hμ⟩ := rows_riesz S φ
  have hμ₀ : μ ≠ 0 := by
    intro h
    apply hφ₀
    ext y
    simpa [h] using (hμ y).symm
  have hline (a : E) : a • μ ∈ Λ := by
    rw [← hU]
    change a • μ ∈ Formalism.E.hdual S.hT Λ
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← S.herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
    (show μ ∉ (⊥ : Submodule E S.V) by simpa using hμ₀)
  let f := ψ.restrictScalars (𝓞 E)
  have hmap (x : E) : x ∈ Λ.map f := by
    refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
    change ψ ((x / ψ μ) • μ) = x
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
  obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors (𝓞 E)) (hL.map f)
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hne {a : 𝓞 E} (ha : a ≠ 0) : algebraMap (𝓞 E) E a ≠ 0 :=
    fun h => ha (hinj (h.trans (map_zero _).symm))
  have hinteger (x : E) : IsLocalization.IsInteger (𝓞 E) x := by
    have hx := hd _ (hmap ((algebraMap (𝓞 E) E d)⁻¹ * x))
    rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
      one_mul] at hx
  apply RingOfIntegers.not_isField E
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 E) E a)⁻¹)
  refine ⟨b, hinj ?_⟩
  rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]


theorem unimod_mem_genus (hU : LocUnimod) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (L M : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) (hM : Submodule.IsLattice E M)
    (huL : IsUnimodular S.hT L) (huM : IsUnimodular S.hT M) : M ∈ genus S.hT L :=
  ⟨{ toIsLattice := hM, span_eq_top := rows_span_eq_top_of_unimodular S hM.fg huM }, fun p hp => hU F E hc S L M hL hM p hp (unimodAt_of_unimod S.hT L hL huL p) (unimodAt_of_unimod S.hT M hM huM p)⟩

theorem unimodular_mem_genus (hU : LocUnimod) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (M : Submodule (𝓞 E) S.V) (hM : Submodule.IsLattice E M) (huM : IsUnimodular S.hT M) : M ∈ genus S.hT S.L0 :=
  unimod_mem_genus hU hc S S.L0 M S.standardTuple_isLattice hM S.baseLattice_isUnimodular huM

end Conj

section Rows

open Formalism.BasicNotions Formalism.MainNotions.BridgeLemma₂

end Rows

end Formalism.MainNotions.BridgeRowsGenus

end
