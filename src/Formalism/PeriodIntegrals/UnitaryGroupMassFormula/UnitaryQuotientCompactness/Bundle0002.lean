module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.ModBase
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.GPolar
section
open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI PI.QuotSetU

lemma uh_right {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : g * Hpk k r * gᴴ = Hpk k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hpk_mul_self]
  have h2 : g * (Hpk k r * gᴴ * Hpk k r) = 1 := mul_eq_one_comm.mp h1
  calc g * Hpk k r * gᴴ = g * Hpk k r * gᴴ * (Hpk k r * Hpk k r) := by
        rw [hpk_mul_self, Matrix.mul_one]
    _ = g * (Hpk k r * gᴴ * Hpk k r) * Hpk k r := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h2, Matrix.one_mul]

lemma uh_conjTranspose {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : gᴴ ∈ UH (Hpk k r) := by
  show gᴴᴴ * Hpk k r * gᴴ = Hpk k r
  rw [Matrix.conjTranspose_conjTranspose]
  exact uh_right hg

theorem unitary_group_polar_decomposition : PolarUH := by
  intro k r g hg
  have hHH : Hpk k r * Hpk k r = 1 := hpk_mul_self k r
  have hHt : (Hpk k r)ᴴ = Hpk k r := hpk_conjTranspose k r
  have hA0 : 0 ≤ gᴴ * g := (posSemidef_conjTranspose_mul_self g).nonneg
  have hAt : (gᴴ * g)ᴴ = gᴴ * g := (Matrix.nonneg_iff_posSemidef.mp hA0).isHermitian.eq
  have hAHA : (gᴴ * g) * Hpk k r * (gᴴ * g) = Hpk k r := by
    have h : (gᴴ * g)ᴴ * Hpk k r * (gᴴ * g) = Hpk k r := uh_mul (uh_conjTranspose hg) hg
    rwa [hAt] at h
  have hS0 : 0 ≤ CFC.sqrt (gᴴ * g) := CFC.sqrt_nonneg _
  have hSS : CFC.sqrt (gᴴ * g) * CFC.sqrt (gᴴ * g) = gᴴ * g := CFC.sqrt_mul_sqrt_self _ hA0
  set S := CFC.sqrt (gᴴ * g) with hS
  have hSt : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp hS0).isHermitian.eq
  have hgdet : IsUnit g.det := uh_det hg
  have hAdet : IsUnit (gᴴ * g).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact hgdet.star.mul hgdet
  have hSdet : IsUnit S.det := by
    have h : IsUnit (S.det * S.det) := by rw [← Matrix.det_mul, hSS]; exact hAdet
    exact isUnit_of_mul_isUnit_left h
  have hT0 : 0 ≤ Hpk k r * S * Hpk k r := by
    have h := star_left_conjugate_nonneg hS0 (Hpk k r)
    rwa [Matrix.star_eq_conjTranspose, hHt] at h
  have hSinvt : (S⁻¹)ᴴ = S⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hSt]
  have hSinv0 : 0 ≤ S⁻¹ := by
    have h := star_left_conjugate_nonneg hS0 S⁻¹
    rwa [Matrix.star_eq_conjTranspose, hSinvt, Matrix.mul_assoc, Matrix.mul_nonsing_inv S hSdet,
      Matrix.mul_one] at h
  have hsq : (Hpk k r * S * Hpk k r) * (Hpk k r * S * Hpk k r) = S⁻¹ * S⁻¹ := by
    have h1 : Hpk k r * S * Hpk k r * (Hpk k r * S * Hpk k r) = Hpk k r * (gᴴ * g) * Hpk k r := by
      calc Hpk k r * S * Hpk k r * (Hpk k r * S * Hpk k r)
          = Hpk k r * S * (Hpk k r * Hpk k r) * S * Hpk k r := by simp only [Matrix.mul_assoc]
        _ = Hpk k r * (S * S) * Hpk k r := by rw [hHH, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = Hpk k r * (gᴴ * g) * Hpk k r := by rw [hSS]
    have h2 : S⁻¹ * S⁻¹ = (gᴴ * g)⁻¹ := by rw [← Matrix.mul_inv_rev, hSS]
    have h3 : Hpk k r * (gᴴ * g) * Hpk k r * (gᴴ * g) = 1 := by
      calc Hpk k r * (gᴴ * g) * Hpk k r * (gᴴ * g)
          = Hpk k r * ((gᴴ * g) * Hpk k r * (gᴴ * g)) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hAHA, hHH]
    rw [h1, h2, (Matrix.inv_eq_left_inv h3).symm]
  have hTS : Hpk k r * S * Hpk k r = S⁻¹ := (CFC.mul_self_eq_mul_self_iff _ _ hT0 hSinv0).mp hsq
  have hSU : S ∈ UH (Hpk k r) := by
    show Sᴴ * Hpk k r * S = Hpk k r
    rw [hSt]
    have h5 : S * (Hpk k r * S * Hpk k r) = 1 := by rw [hTS, Matrix.mul_nonsing_inv S hSdet]
    calc S * Hpk k r * S = S * Hpk k r * S * (Hpk k r * Hpk k r) := by rw [hHH, Matrix.mul_one]
      _ = S * (Hpk k r * S * Hpk k r) * Hpk k r := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [h5, Matrix.one_mul]
  refine ⟨g * S⁻¹, S, uh_mul hg (uh_inv hSU), ?_, hSU, hSt, ?_⟩
  · rw [Matrix.conjTranspose_mul, hSinvt]
    calc S⁻¹ * gᴴ * (g * S⁻¹) = S⁻¹ * (gᴴ * g) * S⁻¹ := by simp only [Matrix.mul_assoc]
      _ = S⁻¹ * S * (S * S⁻¹) := by rw [← hSS]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul S hSdet, Matrix.mul_nonsing_inv S hSdet, Matrix.one_mul]
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul S hSdet, Matrix.mul_one]

theorem unitary_group_modular_function_trivial : TrivG := by
  exact trivG_of unitary_group_polar_decomposition maximal_compact_isCompact

end PI.QuotSetU.UnitaryGroupMassFormula

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.ModCore
section
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.ModW

open PI MG

variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}

theorem map_mul_right_haar (g : MG G hG) :
    (Measure.haar : Measure (MG G hG)).map (· * g) =
      Measure.modularCharacterFun g • (Measure.haar : Measure (MG G hG)) := by
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure (MG G hG)) g]
  exact Measure.isMulLeftInvariant_eq_smul_of_regular _ _

private theorem isEmbedding_MG_val : Topology.IsEmbedding (MG.val : MG G hG → MtM m) :=
  ⟨⟨rfl⟩, fun _ _ hxy => Subtype.ext hxy⟩

private theorem measurableEmbedding_MG_val :
    MeasurableEmbedding (MG.val : MG G hG → MtM m) := by
  have hr : Set.range (MG.val : MG G hG → MtM m) = {x | Matrix.of x ∈ G} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact z.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hc : IsClosed (Set.range (MG.val : MG G hG → MtM m)) := by
    rw [hr]
    exact hG.1.preimage (f := fun x : MtM m => Matrix.of x) continuous_id
  exact (Topology.IsClosedEmbedding.mk isEmbedding_MG_val hc).measurableEmbedding

theorem onG_eq (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) :
    ∃ c : ℝ≥0∞, onG hG μ = c • (Measure.haar : Measure (MG G hG)) := by
  haveI := hμ.1
  have hMe : MeasurableEmbedding (MG.val : MG G hG → MtM m) := measurableEmbedding_MG_val
  haveI : SigmaFinite (onG hG μ) := by
    refine ⟨⟨⟨fun n => MG.val ⁻¹' spanningSets μ n, fun _ => Set.mem_univ _, fun n => ?_, ?_⟩⟩⟩
    · show μ.comap MG.val _ < ⊤
      rw [hMe.comap_apply]
      exact (measure_mono (Set.image_preimage_subset _ _)).trans_lt (measure_spanningSets_lt_top μ n)
    · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]
  have hkey : ∀ h z : MG G hG, MG.val (h * z) = lmulQ (MG.toM h) (MG.val z) := by
    intro h z
    show MG.toM (h * z) = _
    rw [toM_mul']
    rfl
  haveI : Measure.IsMulLeftInvariant (onG hG μ) := by
    refine ⟨fun h => Measure.ext fun s hs => ?_⟩
    have hA : Measurable (lmulQ (MG.toM h) : MtM m → MtM m) := by
      refine Continuous.measurable (continuous_pi fun i => continuous_pi fun j => ?_)
      have hf : (fun x : MtM m => lmulQ (MG.toM h) x i j) = fun x => ∑ k, MG.toM h i k * x k j := by
        funext x
        simp only [lmulQ, Matrix.mul_apply, Matrix.of_apply]
      rw [hf]
      exact continuous_finsetSum _ fun k _ => by fun_prop
    have hvs : MeasurableSet (MG.val '' s) := hMe.measurableSet_image.2 hs
    have hinvA : Measure.map (lmulQ (MG.toM h)) μ = μ := hμ.2.2.2 _ h.2
    rw [Measure.map_apply (measurable_const_mul h) hs]
    show μ.comap MG.val _ = μ.comap MG.val _
    rw [hMe.comap_apply, hMe.comap_apply]
    apply le_antisymm
    · calc μ (MG.val '' ((h * ·) ⁻¹' s)) ≤ μ (lmulQ (MG.toM h) ⁻¹' (MG.val '' s)) := by
            apply measure_mono
            rintro _ ⟨z, hz, rfl⟩
            exact ⟨h * z, hz, hkey h z⟩
        _ = μ (MG.val '' s) := by
            rw [← Measure.map_apply hA hvs, hinvA]
    · calc μ (MG.val '' s) = μ (lmulQ (MG.toM h) ⁻¹' (MG.val '' s)) := by
            rw [← Measure.map_apply hA hvs, hinvA]
        _ ≤ μ (MG.val '' ((h * ·) ⁻¹' s) ∪ {x | Matrix.of x ∉ G}) := by
            apply measure_mono
            intro y hy
            by_cases hyG : Matrix.of y ∈ G
            · left
              obtain ⟨w, hw, hwy⟩ := hy
              obtain ⟨z, hz⟩ : ∃ z : MG G hG, MG.val z = y := ⟨⟨y, hyG⟩, rfl⟩
              refine ⟨z, ?_, hz⟩
              have hEq : h * z = w := by
                apply hMe.injective
                rw [hkey, hz, hwy]
              show h * z ∈ s
              rw [hEq]
              exact hw
            · right
              exact hyG
        _ ≤ μ (MG.val '' ((h * ·) ⁻¹' s)) + μ {x | Matrix.of x ∉ G} := measure_union_le _ _
        _ = μ (MG.val '' ((h * ·) ⁻¹' s)) := by rw [hμ.2.2.1, add_zero]
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (MG G hG)) := inferInstance
  have hK0 : (Measure.haar : Measure (MG G hG)) K ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hKt : (Measure.haar : Measure (MG G hG)) K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  exact ⟨_, measure_eq_div_smul (onG hG μ) Measure.haar hK0 hKt⟩

theorem rightInv_of (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ)
    (h1 : ∀ g : MG G hG, Measure.modularCharacterFun g = 1) : IsRightInvM G μ := by
  obtain ⟨c, hc⟩ := onG_eq μ hμ
  have hMe : MeasurableEmbedding (MG.val : MG G hG → MtM m) := measurableEmbedding_MG_val
  have hback : Measure.map MG.val (onG hG μ) = μ := by
    show Measure.map MG.val (μ.comap MG.val) = μ
    rw [hMe.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    have hset : {x | ¬ x ∈ Set.range (MG.val : MG G hG → MtM m)} = {x | Matrix.of x ∉ G} := by
      ext x
      constructor
      · intro hx hxG
        exact hx ⟨⟨x, hxG⟩, rfl⟩
      · rintro hx ⟨z, rfl⟩
        exact hx z.2
    rw [hset]
    exact hμ.2.2.1
  intro s hs
  have hR : Measurable (rmulQ s : MtM m → MtM m) := by
    refine Continuous.measurable (continuous_pi fun i => continuous_pi fun j => ?_)
    have hf : (fun x : MtM m => rmulQ s x i j) = fun x => ∑ k, x i k * s k j := by
      funext x
      simp only [rmulQ, Matrix.mul_apply, Matrix.of_apply]
    rw [hf]
    exact continuous_finsetSum _ fun k _ => by fun_prop
  have hgkey : (rmulQ s) ∘ MG.val = MG.val ∘ (· * mk hG s hs) := by
    funext z
    show _ = MG.toM (z * mk hG s hs)
    rw [toM_mul', toM_mk]
    rfl
  have hinv : Measure.map (· * mk hG s hs) (onG hG μ) = onG hG μ := by
    rw [hc, Measure.map_smul c (measurable_mul_const (mk hG s hs)).aemeasurable,
      map_mul_right_haar, h1, one_smul]
  rw [← hback, Measure.map_map hR hMe.measurable, hgkey,
    ← Measure.map_map hMe.measurable (measurable_mul_const _), hinv]

def conjE (c : Matrix (Fin m) (Fin m) ℂ) (hc : IsUnit c) (hcG : ∀ g, c * g * c⁻¹ ∈ G ↔ g ∈ G) :
    MG G hG ≃ₜ* MG G hG where
  toFun x := mk hG (c * x.toM * c⁻¹) ((hcG _).2 x.2)
  invFun x := mk hG (c⁻¹ * x.toM * c) (by
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    apply (hcG _).1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    exact x.2)
  left_inv x := by
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    apply MG.toM_injective
    simp only [toM_mk]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
  right_inv x := by
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    apply MG.toM_injective
    simp only [toM_mk]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  map_mul' x y := by
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    apply MG.toM_injective
    simp only [toM_mk, toM_mul']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc c⁻¹ c, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  continuous_toFun := by
    rw [continuous_iff_toM]
    simp only [toM_mk]
    exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const
  continuous_invFun := by
    rw [continuous_iff_toM]
    simp only [toM_mk]
    exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const

theorem modF_conj (φ : MG G hG ≃ₜ* MG G hG) (g : MG G hG) :
    Measure.modularCharacterFun (φ g) = Measure.modularCharacterFun g := by
  rw [Measure.modularCharacterFun_eq_haarScalarFactor
    (Measure.map φ (Measure.haar : Measure (MG G hG))) (φ g)]
  have hφ : Measurable φ := φ.continuous.measurable
  have e1 : Measure.map (· * φ g) (Measure.map φ (Measure.haar : Measure (MG G hG)))
      = Measure.modularCharacterFun g • Measure.map φ (Measure.haar : Measure (MG G hG)) := by
    rw [Measure.map_map (measurable_mul_const (φ g)) hφ]
    have e : ((· * φ g) ∘ ⇑φ) = (⇑φ ∘ (· * g)) := by
      funext x
      simp [map_mul]
    rw [e, ← Measure.map_map hφ (measurable_mul_const g), map_mul_right_haar g,
      Measure.map_smul _ hφ.aemeasurable]
  simp only [e1, Measure.haarScalarFactor_smul, Measure.haarScalarFactor_self, smul_eq_mul, mul_one]

theorem modF_bdd (V : Set (MG G hG)) (hV : IsCompact V) :
    ∃ M : ℝ, ∀ v ∈ V, (Measure.modularCharacterFun v : ℝ) ≤ M := by
  have K : TopologicalSpace.PositiveCompacts (MG G hG) := Classical.arbitrary _
  set C : Set (MG G hG) :=
    (fun p : MG G hG × MG G hG => p.1 * p.2⁻¹) '' ((K : Set (MG G hG)) ×ˢ V) with hCdef
  have hC : IsCompact C := (K.isCompact.prod hV).image (continuous_fst.mul continuous_snd.inv)
  have hK0 : 0 < (Measure.haar : Measure (MG G hG)) K :=
    Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty
  have hKt : (Measure.haar : Measure (MG G hG)) K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hCt : (Measure.haar : Measure (MG G hG)) C ≠ ⊤ := hC.measure_lt_top.ne
  refine ⟨((Measure.haar : Measure (MG G hG)) C / (Measure.haar : Measure (MG G hG)) K).toReal,
    fun v hv => ?_⟩
  have h := (MeasurableEquiv.mulRight v).map_apply (μ := (Measure.haar : Measure (MG G hG)))
    (K : Set (MG G hG))
  rw [MeasurableEquiv.coe_mulRight, map_mul_right_haar v, Measure.smul_apply, ENNReal.smul_def] at h
  have hsub : (fun x => x * v) ⁻¹' (K : Set (MG G hG)) ⊆ C := by
    intro x hx
    exact ⟨(x * v, v), ⟨hx, hv⟩, by simp⟩
  have hle : (Measure.modularCharacterFun v : ℝ≥0∞) * (Measure.haar : Measure (MG G hG)) K
      ≤ (Measure.haar : Measure (MG G hG)) C := by
    rw [← smul_eq_mul, h]
    exact measure_mono hsub
  have hle' : (Measure.modularCharacterFun v : ℝ≥0∞)
      ≤ (Measure.haar : Measure (MG G hG)) C / (Measure.haar : Measure (MG G hG)) K :=
    (ENNReal.le_div_iff_mul_le (Or.inl hK0.ne') (Or.inl hKt)).2 hle
  rw [← ENNReal.coe_toReal]
  exact ENNReal.toReal_mono (ENNReal.div_ne_top hCt hK0.ne') hle'

end PI.QuotSetU.UnitaryGroupMassFormula.ModW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.NilpotentSubgroup
section
open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.SW

open PI PI.QuotSetU

variable {k r : ℕ}

def NC (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0

lemma mem_Nset_iff (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Nset k r ↔ g ∈ UH (Hpk k r) ∧ NC k r g := by
  simp only [Nset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hU, h2, h3⟩
    refine ⟨hU, fun i j hj hi => ?_⟩
    by_cases hjr : j.val < r
    · have hej : eI k r ⟨j.val, hjr⟩ = j := Fin.ext (by simp [eI])
      have h := h2 ⟨j.val, hjr⟩ i (by rw [min_eq_left hjr.le] at hi; exact hi)
      rwa [hej] at h
    · push_neg at hjr
      exact h3 i j hjr hj (by rwa [min_eq_right hjr] at hi)
  · rintro ⟨hU, hN⟩
    refine ⟨hU, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩
    · have hv : (eI k r a).val = a.val := by simp [eI]
      exact hN i (eI k r a) (by rw [hv]; omega) (by rw [hv, min_eq_left a.isLt.le]; exact hai)
    · exact hN i j hj2 (by rw [min_eq_right hj1]; exact hi)

lemma nc_one : NC k r (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := by
  intro i j _ _
  rw [Matrix.one_apply]

lemma nc_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : NC k r a) (hb : NC k r b) : NC k r (a * b) := by
  intro i j hj hi
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hb j j hj (min_le_left _ _), if_pos rfl, mul_one]
    exact ha i j hj hi
  · intro l _ hlj
    by_cases hl : min j.val r ≤ l.val
    · rw [hb l j hj hl, if_neg hlj, mul_zero]
    · push_neg at hl
      have hlr : l.val < r := lt_of_lt_of_le hl (min_le_right _ _)
      have h := ha i l (by omega) (by rw [min_eq_left hlr.le]; omega)
      rw [h, if_neg (by intro h'; rw [h'] at hi; omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

private lemma mul_apply_eq_ite_of_lower_block_scalar {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : NC k r a) (c : ℂ)
    {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hx : ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → min j.val r ≤ i.val →
      x i j = if i = j then c else 0) :
    ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → min j.val r ≤ i.val →
      (x * a) i j = if i = j then c else 0 := by
  intro i j hj hi
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [ha j j hj (min_le_left _ _), if_pos rfl, mul_one]
    exact hx i j hj hi
  · intro l _ hlj
    by_cases hl : min j.val r ≤ l.val
    · rw [ha l j hj hl, if_neg hlj, mul_zero]
    · push_neg at hl
      have hlr : l.val < r := lt_of_lt_of_le hl (min_le_right _ _)
      have h := hx i l (by omega) (by rw [min_eq_left hlr.le]; omega)
      rw [h, if_neg (by intro h'; rw [h'] at hi; omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

lemma nc_inv {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : a ∈ UH (Hpk k r)) (ha : NC k r a) : NC k r a⁻¹ := by
  have hfix := mul_apply_eq_ite_of_lower_block_scalar (k := k) (r := r) (a := a) ha
  let V : Submodule ℂ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    { carrier := {x | ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → min j.val r ≤ i.val →
          x i j = if i = j then x 0 0 else 0}
      add_mem' := by
        intro x y hx hy i j hj hi
        simp only [Set.mem_setOf_eq] at hx hy
        rw [Matrix.add_apply, hx i j hj hi, hy i j hj hi, Matrix.add_apply]
        split_ifs <;> simp
      zero_mem' := by
        intro i j _ _
        simp
      smul_mem' := by
        intro c x hx i j hj hi
        simp only [Set.mem_setOf_eq] at hx
        rw [Matrix.smul_apply, hx i j hj hi, Matrix.smul_apply]
        split_ifs <;> simp }
  have hV : ∀ x ∈ V, LinearMap.mulRight ℂ a x ∈ V := by
    intro x hx i j hj hi
    have h00 : (x * a) 0 0 = x 0 0 := by
      rw [hfix (x 0 0) hx 0 0 (by simp) (by simp), if_pos rfl]
    show (x * a) i j = if i = j then (x * a) 0 0 else 0
    rw [h00]
    exact hfix (x 0 0) hx i j hj hi
  let f : V →ₗ[ℂ] V := (LinearMap.mulRight ℂ a).restrict hV
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * a = y * a := congrArg Subtype.val hxy
    have h2 := congrArg (· * a⁻¹) h1
    simp only [Matrix.mul_assoc, mul_inv_UH hU, Matrix.mul_one] at h2
    exact Subtype.ext h2
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  have h1V : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ V := by
    intro i j _ _
    simp [Matrix.one_apply]
  obtain ⟨x, hx⟩ := hsurj ⟨1, h1V⟩
  have hxa : (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * a = 1 := congrArg Subtype.val hx
  have hxinv : (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = a⁻¹ := by
    calc (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = x * (a * a⁻¹) := by rw [mul_inv_UH hU, Matrix.mul_one]
      _ = (x * a) * a⁻¹ := by rw [Matrix.mul_assoc]
      _ = a⁻¹ := by rw [hxa, Matrix.one_mul]
  have hc : (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) 0 0 = 1 := by
    have h := hfix ((x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) 0 0) x.2 0 0 (by simp) (by simp)
    rw [hxa, if_pos rfl, Matrix.one_apply_eq] at h
    exact h.symm
  intro i j hj hi
  rw [← hxinv]
  have h := x.2 i j hj hi
  rw [hc] at h
  exact h

theorem nilpotent_subgroup : NGroup := by
  intro k r
  refine ⟨(mem_Nset_iff 1).2 ⟨one_mem_UH, nc_one⟩, fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨haU, haN⟩ := (mem_Nset_iff a).1 ha
    obtain ⟨hbU, hbN⟩ := (mem_Nset_iff b).1 hb
    exact (mem_Nset_iff _).2 ⟨mul_mem_UH haU hbU, nc_mul haN hbN⟩
  · obtain ⟨haU, haN⟩ := (mem_Nset_iff a).1 ha
    exact (mem_Nset_iff _).2 ⟨inv_mem_UH haU, nc_inv haU haN⟩

lemma inv_inv_UH {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : a ∈ UH (Hpk k r)) :
    a⁻¹⁻¹ = a := Matrix.nonsing_inv_nonsing_inv a (Matrix.isUnit_det_of_right_inverse (mul_inv_UH hU))

lemma n_ut {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r)
    (i j : Fin (2 * r + k + 1)) (hij : j.val ≤ i.val) : n i j = if i = j then 1 else 0 := by
  obtain ⟨hU, hN⟩ := (mem_Nset_iff n).1 hn
  by_cases hj : j.val ≤ r + k
  · exact hN i j hj (le_trans (min_le_left _ _) hij)
  · push_neg at hj
    have hinv : NC k r n⁻¹ := nc_inv hU hN
    have hvj : (piI k r j).val = 2 * r + k - j.val := by
      rw [piI_val, if_neg (by omega)]
    have hvi : (piI k r i).val = 2 * r + k - i.val := by
      rw [piI_val, if_neg (by omega)]
    have h1 := hinv (piI k r j) (piI k r i) (by omega)
      (by rw [hvi, hvj, min_eq_left (by omega)]; omega)
    rw [inv_eq_UH hU, Hpk_mul_mul_Hpk_apply, piI_piI, piI_piI, conjTranspose_apply] at h1
    have he1 : epsI k r (piI k r j) = 1 := by
      simp only [epsI]; rw [if_neg (by omega)]
    have he2 : epsI k r (piI k r i) = 1 := by
      simp only [epsI]; rw [if_neg (by omega)]
    rw [he1, he2, one_mul, mul_one] at h1
    have h2 := congrArg star h1
    rw [star_star] at h2
    rw [h2]
    by_cases hij' : i = j
    · subst hij'
      simp
    · have hne : piI k r j ≠ piI k r i := by
        intro h
        have h' := congrArg (piI k r) h
        rw [piI_piI, piI_piI] at h'
        exact hij' h'.symm
      rw [if_neg hne, if_neg hij', star_zero]

end PI.QuotSetU.UnitaryGroupMassFormula.SW
end
end

