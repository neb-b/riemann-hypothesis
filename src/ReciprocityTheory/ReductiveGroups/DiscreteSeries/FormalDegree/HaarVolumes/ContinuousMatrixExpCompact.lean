module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.KdMeasImageProd
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0001

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem compactMatrix_off_block {ε : Fin n → Bool} (w : KCo ε) {a b : Fin n} (h : ε a ≠ ε b) :
    kMat w a b = 0 := by
  have hab : a ≠ b := fun e => h (e ▸ rfl)
  unfold kMat
  rw [if_neg hab, dif_neg (fun h' => h h'.2), dif_neg (fun h' => h h'.2.symm)]

theorem compactMatrix_conjTranspose {ε : Fin n → Bool} (w : KCo ε) : (kMat w)ᴴ = -kMat w := by
  ext a b
  change star (kMat w b a) = -(kMat w a b)
  by_cases hab : a = b
  · subst hab
    simp only [kMat, if_true]
    simp [Complex.ext_iff]
  · have hba : b ≠ a := Ne.symm hab
    by_cases h1 : b < a ∧ ε a = ε b
    · have h2 : ¬ (a < b ∧ ε b = ε a) := fun h => lt_asymm h.1 h1.1
      simp only [kMat, if_neg hab, if_neg hba, dif_pos h1, dif_neg h2, star_neg, star_star]
    · by_cases h2 : a < b ∧ ε b = ε a
      · simp only [kMat, if_neg hab, if_neg hba, dif_pos h2, dif_neg h1, neg_neg]
      · simp only [kMat, if_neg hab, if_neg hba, dif_neg h2, dif_neg h1, star_zero, neg_zero]

theorem compactMatrix_comm_signature {ε : Fin n → Bool} (w : KCo ε) : kMat w * Jm ε = Jm ε * kMat w := by
  ext a b
  simp only [Jm, mul_diagonal, diagonal_mul]
  by_cases h : ε a = ε b
  · rw [h, mul_comm]
  · rw [compactMatrix_off_block w h]; simp

theorem compactMatrix_inK {ε : Fin n → Bool} (w : KCo ε) : inK ε (kMat w) := by
  refine ⟨?_, compactMatrix_comm_signature w⟩
  unfold inG
  rw [compactMatrix_conjTranspose, Matrix.neg_mul, compactMatrix_comm_signature, neg_add_cancel]

theorem exists_compact_exp {ε : Fin n → Bool} (w : KCo ε) :
    ∃ k : KG ε, toMK k = NormedSpace.exp (kMat w) :=
  exists_toMK (exp_mem_Kset (compactMatrix_inK w))

theorem compactMatrix_injective (ε : Fin n → Bool) : Function.Injective (kMat (ε := ε)) := by
  intro w w' h
  have h1 : ∀ a b, kMat w a b = kMat w' a b := fun a b => by rw [h]
  refine Prod.ext (funext fun a => ?_) (funext fun ab => ?_)
  · have h2 := congrArg Complex.im (h1 a a)
    simpa [kMat] using h2
  · have h2 := h1 ab.1.1 ab.1.2
    have hne : ab.1.1 ≠ ab.1.2 := ne_of_gt ab.2.1
    simp only [kMat, if_neg hne, dif_pos ab.2] at h2
    exact h2

theorem compactMatrix_continuous (ε : Fin n → Bool) :
    Continuous (fun w : KCo ε => (kMat w : Matrix (Fin n) (Fin n) ℂ)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold kMat
  by_cases h0 : a = b
  · simp only [h0, if_true]; fun_prop
  · simp only [if_neg h0]
    by_cases h1 : b < a ∧ ε a = ε b
    · simp only [dif_pos h1]; fun_prop
    · simp only [dif_neg h1]
      by_cases h2 : a < b ∧ ε b = ε a
      · simp only [dif_pos h2]; fun_prop
      · simp only [dif_neg h2]; fun_prop

theorem compactMatrix_zero (ε : Fin n → Bool) : kMat (0 : KCo ε) = 0 := by
  ext a b
  simp only [kMat]
  split_ifs <;> simp

theorem continuous_matrix_exp_compact : Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  exact continuous_iff_continuousAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℂ) x).continuousAt

theorem exists_exp_injOn_nhds_zero : ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ (0 : Matrix (Fin n) (Fin n) ℂ) ∈ U ∧
    Set.InjOn (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) U := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] _)) 0 := by
    rw [ContinuousLinearEquiv.coe_refl]
    exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  exact ⟨_, (h.toOpenPartialHomeomorph _).open_source, h.mem_toOpenPartialHomeomorph_source,
    (h.toOpenPartialHomeomorph _).injOn⟩

def expCompactMatrix {ε : Fin n → Bool} (w : KCo ε) : Fin n → Fin n → ℂ :=
  (NormedSpace.exp (kMat w) : Matrix (Fin n) (Fin n) ℂ)

theorem continuous_exp_compactMatrix (ε : Fin n → Bool) : Continuous (expCompactMatrix (ε := ε)) :=
  continuous_matrix_exp_compact.comp (compactMatrix_continuous ε)

theorem exp_compact_injOn (ε : Fin n → Bool) : ∃ δ > 0, Set.InjOn (expCompactMatrix (ε := ε)) {w | ‖w‖ < δ} := by
  obtain ⟨U, hU, h0, hinj⟩ := (exists_exp_injOn_nhds_zero (n := n))
  have hV : IsOpen ((fun w : KCo ε => (kMat w : Matrix (Fin n) (Fin n) ℂ)) ⁻¹' U) :=
    hU.preimage (compactMatrix_continuous ε)
  have h0V : (0 : KCo ε) ∈ (fun w : KCo ε => (kMat w : Matrix (Fin n) (Fin n) ℂ)) ⁻¹' U := by
    show kMat (0 : KCo ε) ∈ U
    rw [compactMatrix_zero]; exact h0
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hV 0 h0V
  refine ⟨δ, hδ, fun w hw w' hw' h => compactMatrix_injective ε (hinj ?_ ?_ h)⟩
  · exact hball (by simpa using hw)
  · exact hball (by simpa using hw')

def expImageOfCompact {ε : Fin n → Bool} (B : Set (KCo ε)) : Set (KG ε) :=
  {k | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)}

def compactToMatrixEntries (ε : Fin n → Bool) : KG ε → (Fin n → Fin n → ℂ) := fun k => toMK k

theorem measurableSet_exp_image {ε : Fin n → Bool} {B : Set (KCo ε)} (hB : MeasurableSet B)
    (hinj : Set.InjOn (expCompactMatrix (ε := ε)) B) : MeasurableSet (expImageOfCompact B) := by
  have hI : MeasurableSet (expCompactMatrix (ε := ε) '' B) :=
    hB.image_of_continuousOn_injOn (continuous_exp_compactMatrix ε).continuousOn hinj
  have hc : Continuous (compactToMatrixEntries ε) := (continuous_toM ε).comp continuous_subtype_val
  have hm : Measurable (compactToMatrixEntries ε) := hc.measurable
  have e : expImageOfCompact B = compactToMatrixEntries ε ⁻¹' (expCompactMatrix (ε := ε) '' B) := by
    ext k
    constructor
    · rintro ⟨w, hw, h⟩
      exact ⟨w, hw, h.symm⟩
    · rintro ⟨w, hw, h⟩
      exact ⟨w, hw, h.symm⟩
  rw [e]
  exact hm hI

theorem polarSet_product_eq {ε : Fin n → Bool} (B : Set (KCo ε)) (C : Set (PCoord ε → ℂ)) :
    polSet (B ×ˢ C) =
      (intMuCD_eM ε) ⁻¹' (intMuCD_pM ε '' (expImageOfCompact B ×ˢ C)) := by
  ext g
  constructor
  · rintro ⟨s, hs, hg⟩
    obtain ⟨k, hk⟩ := exists_compact_exp s.1
    refine ⟨(k, s.2), ⟨⟨s.1, hs.1, hk⟩, hs.2⟩, ?_⟩
    show toMK k * NormedSpace.exp (pmat s.2) = toM g
    rw [hk, hg]
  · rintro ⟨⟨k, z⟩, ⟨⟨w, hw, hk⟩, hz⟩, hg⟩
    refine ⟨(w, z), ⟨hw, hz⟩, ?_⟩
    have hg' : toMK k * NormedSpace.exp (pmat z) = toM g := hg
    rw [← hg', hk]

theorem polar_measure_product_eq {ε : Fin n → Bool} {B : Set (KCo ε)} {C : Set (PCoord ε → ℂ)}
    (hA : MeasurableSet (expImageOfCompact B)) (hC : MeasurableSet C) :
    muPolar ε (polSet (B ×ˢ C)) = (∫⁻ z in C, ENNReal.ofReal (Jac z)) * dk ε (expImageOfCompact B) := by
  let R := expImageOfCompact B ×ˢ C
  have hpolar : MeasurableEmbedding (intMuCD_pM ε) :=
    (show Topology.IsClosedEmbedding (intMuCD_pM ε) from polarM_isClosedEmbedding ε).measurableEmbedding
  have htoM : MeasurableEmbedding (intMuCD_eM ε) :=
    (show Topology.IsClosedEmbedding (intMuCD_eM ε) from isClosedEmbedding_toM ε).measurableEmbedding
  have hT : MeasurableSet (intMuCD_pM ε '' R) := hpolar.measurableSet_image.2 (hA.prod hC)
  have hrange : intMuCD_pM ε '' R ⊆ Set.range (intMuCD_eM ε) := by
    rintro _ ⟨kz, _, rfl⟩
    change polarM kz ∈ Set.range (fun g : UJ ε => toM g)
    rw [range_toM]
    exact polarM_inUJ kz
  rw [polarSet_product_eq]
  change Measure.comap (β := Fin n → Fin n → ℂ) (intMuCD_eM ε) (muPolarMat ε)
    ((intMuCD_eM ε) ⁻¹' (intMuCD_pM ε '' R)) = _
  rw [htoM.comap_apply, Set.image_preimage_eq_of_subset hrange]
  change (Measure.map (β := Fin n → Fin n → ℂ) (intMuCD_pM ε) ((dk ε).prod
    (volume.withDensity fun z => ENNReal.ofReal (Jac z)))) (intMuCD_pM ε '' R) = _
  rw [Measure.map_apply hpolar.measurable hT, Set.preimage_image_eq _ hpolar.injective,
    show R = expImageOfCompact B ×ˢ C from rfl, Measure.prod_prod, withDensity_apply _ hC, mul_comm]

end ReciprocityTheory.ChartRestriction.DS
