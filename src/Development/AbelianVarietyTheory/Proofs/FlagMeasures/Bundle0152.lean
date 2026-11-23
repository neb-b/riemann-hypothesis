module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZetaProdSphereVolumeBounds

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarisableOfCompact
section
open MeasureTheory GlobalTheory.Dec
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.UniTrick

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem continuous_lin {ι : Type} [Fintype ι] (ρ : Representation ℂ G V)
    (hρ : ∀ (φ : V →ₗ[ℂ] ℂ) (v : V), Continuous fun g => φ (ρ g v))
    (f : V →ₗ[ℂ] EuclideanSpace ℂ ι) (v : V) : Continuous fun g => f (ρ g v) := by
  have h : ∀ i, Continuous fun g => (f (ρ g v)) i := fun i =>
    hρ ((EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).toLinearMap ∘ₗ f) v
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi h)

variable [MeasurableSpace G] [BorelSpace G]

variable [CompactSpace G]

end GlobalTheory.UniTrick

namespace GlobalTheory

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJLieCoordsConjLinear
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.UnitaryCoords

open Formalism.REAL

lemma re_trace_eq_zero {n : ℕ} (J Z Y : Matrix (Fin n) (Fin n) ℂ) (hJ : J * J = 1)
    (hZ : Zᴴ * J = J * Z) (hY : Yᴴ * J + J * Y = 0) : ((Z * Yᴴ).trace).re = 0 := by
  have hY' : Yᴴ = -(J * Y * J) := by
    have h1 : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
    calc Yᴴ = Yᴴ * J * J := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = _ := by rw [h1, Matrix.neg_mul]
  have hZ' : Zᴴ = J * Z * J := by
    calc Zᴴ = Zᴴ * J * J := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = _ := by rw [hZ]
  have h1 : ((Z * Yᴴ).trace).re = ((Y * Zᴴ).trace).re := by
    have : Y * Zᴴ = (Z * Yᴴ)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [this, Matrix.trace_conjTranspose]
    simp
  have h2 : (Y * Zᴴ).trace = -(Z * Yᴴ).trace := by
    rw [hZ', hY', Matrix.mul_neg, Matrix.trace_neg, neg_neg]
    calc (Y * (J * Z * J)).trace = ((Y * J) * (Z * J)).trace := by simp only [Matrix.mul_assoc]
      _ = ((Z * J) * (Y * J)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h2, Complex.neg_re] at h1
  linarith

lemma uMat_mul' {n : ℕ} {ε : Fin n → Bool} (a b : UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

lemma uMat_mul_inv' {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) : uMat a * uMat a⁻¹ = 1 := by
  rw [← uMat_mul', mul_inv_cancel]; rfl

lemma conjTranspose_mul_J {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) :
    (uMat a)ᴴ * Jm ε = Jm ε * uMat a⁻¹ := by
  have h : (uMat a)ᴴ * Jm ε * uMat a = Jm ε := a.2
  calc (uMat a)ᴴ * Jm ε = (uMat a)ᴴ * Jm ε * (uMat a * uMat a⁻¹) := by
        rw [uMat_mul_inv', Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h]

lemma inv_conjTranspose_mul_J {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) :
    (uMat a⁻¹)ᴴ * Jm ε = Jm ε * uMat a := by
  simpa using conjTranspose_mul_J a⁻¹

lemma coord_eq {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : inG ε Y) :
    2 * (((uMat a - 1) * Yᴴ).trace).re = (((uMat a - uMat a⁻¹) * Yᴴ).trace).re := by
  have h := re_trace_eq_zero (Jm ε) (uMat a + uMat a⁻¹ - 1 - 1) Y (Jm_mul_self ε) (by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, conjTranspose_mul_J a,
      inv_conjTranspose_mul_J a, Matrix.one_mul, Matrix.mul_one]
    abel) hY
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.trace_sub, Matrix.trace_add, Complex.sub_re,
    Complex.add_re] at h ⊢
  linarith

lemma inG_sub_inv {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) : inG ε (uMat a - uMat a⁻¹) := by
  unfold inG
  simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, conjTranspose_mul_J a,
    inv_conjTranspose_mul_J a]
  abel

lemma coord_sum {n d : ℕ} (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (t : Fin d → ℝ) (i : Fin d) :
    (((∑ k, t k • E k) * (E i)ᴴ).trace).re = t i := by
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, hE]
  simp

theorem coords_conj : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ (g m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ), uMat g - 1 ∈ A → uMat g⁻¹ - 1 ∈ A → (∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) → (fun i => (((uMat (m * g * m⁻¹) - 1) * (E i)ᴴ).trace).re) = L *ᵥ (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) := by
  intro n ε A d E hE hA g m L hg hg' hL
  have hEG : ∀ i, inG ε (E i) := fun i =>
    ((hA (E i)).2 (Submodule.subset_span ⟨i, rfl⟩)).2
  have hX : uMat g - uMat g⁻¹ ∈ Submodule.span ℝ (Set.range E) := by
    refine (hA _).1 ⟨?_, inG_sub_inv g⟩
    have := A.sub_mem hg hg'
    simpa using this
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hX
  have h1 : ∀ i, 2 * (((uMat g - 1) * (E i)ᴴ).trace).re = t i := fun i => by
    rw [coord_eq g _ (hEG i), ← ht, coord_sum E hE]
  have h2 : uMat (m * g * m⁻¹) - uMat (m * g * m⁻¹)⁻¹ = ∑ i, (∑ k, L i k * t k) • E i := by
    have e : (m * g * m⁻¹)⁻¹ = m * g⁻¹ * m⁻¹ := by group
    rw [e, uMat_mul', uMat_mul', uMat_mul', uMat_mul', ← Matrix.sub_mul, ← Matrix.mul_sub, ← ht,
      Finset.mul_sum, Finset.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, hL, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  funext i
  have h3 := coord_eq (m * g * m⁻¹) _ (hEG i)
  rw [h2, coord_sum E hE] at h3
  simp only [Matrix.mulVec, dotProduct]
  have h4 : ∑ k, L i k * t k = 2 * ∑ k, L i k * (((uMat g - 1) * (E k)ᴴ).trace).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← h1 k]; ring
  linarith

end GlobalTheory.UnitaryCoords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJMapConjEqSmulOfNormalizing
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.ConjScalesMeasure

theorem eq_smul_map_haar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (M : Subgroup G) [LocallyCompactSpace M] (hM : IsClosed (M : Set G)) (μ : Measure G)
    (hμ : μ (M : Set G)ᶜ = 0)
    (hinv : ∀ s ∈ M, μ.map (fun g => s * g) = μ) [IsFiniteMeasureOnCompacts μ] :
    ∃ c : NNReal, μ = (c : ENNReal) • (Measure.haar : Measure M).map (Subtype.val : M → G) := by
  haveI : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology (M : Set G)
  have hemb : MeasurableEmbedding (Subtype.val : M → G) := MeasurableEmbedding.subtype_coe hM.measurableSet
  set ν : Measure M := μ.comap Subtype.val with hν
  have hmap : ν.map Subtype.val = μ := by
    rw [hν, hemb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem hμ
  have hinj : ∀ ρ : Measure M, (ρ.map (Subtype.val : M → G)).comap Subtype.val = ρ := fun ρ => hemb.comap_map ρ
  haveI : ν.IsMulLeftInvariant := by
    refine ⟨fun s => ?_⟩
    rw [← hinj (ν.map _), Measure.map_map hemb.measurable (measurable_const_mul s)]
    have : (Subtype.val : M → G) ∘ (fun g => s * g) = (fun g => (s : G) * g) ∘ Subtype.val := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hemb.measurable, hmap, hinv s s.2]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rw [hν, hemb.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top
  have e1 := Measure.isMulLeftInvariant_eq_smul ν (Measure.haar : Measure M)
  refine ⟨Measure.haarScalarFactor ν (Measure.haar : Measure M), ?_⟩
  rw [← Measure.map_smul _ hemb.measurable.aemeasurable]
  conv_lhs => rw [← hmap, e1]
  rfl

theorem map_conj_eq_smul_of_group {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (S : Subgroup G) (μ : Measure G) (hS : IsClosed (S : Set G)) (hμ : μ (S : Set G)ᶜ = 0)
    (hinv : ∀ s ∈ S, μ.map (fun g => s * g) = μ) (hfin : IsFiniteMeasureOnCompacts μ) (h0 : μ ≠ 0)
    (m : G) (hm : ∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) :
    ∃ c : NNReal, μ.map (fun u => m * u * m⁻¹) = (c : ENNReal) • μ := by
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hcm : Measurable (fun u : G => m * u * m⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  haveI : IsFiniteMeasureOnCompacts (μ.map (fun u => m * u * m⁻¹)) :=
    Measure.IsFiniteMeasureOnCompacts.map μ ((Homeomorph.mulLeft m).trans (Homeomorph.mulRight m⁻¹))
  obtain ⟨a, ha⟩ := eq_smul_map_haar S hS μ hμ hinv
  obtain ⟨b, hb⟩ := eq_smul_map_haar S hS (μ.map (fun u => m * u * m⁻¹))
    (by
      rw [Measure.map_apply hcm hS.measurableSet.compl]
      convert hμ using 2
      ext g
      exact not_congr (hm g).symm)
    (by
      intro s hs
      have hs' : m⁻¹ * s * m ∈ S := (hm _).2 (by simpa [mul_assoc] using hs)
      rw [Measure.map_map (measurable_const_mul s) hcm]
      have : (fun g => s * g) ∘ (fun u : G => m * u * m⁻¹)
          = (fun u : G => m * u * m⁻¹) ∘ (fun g => (m⁻¹ * s * m) * g) := by
        funext g
        simp [mul_assoc]
      rw [this, ← Measure.map_map hcm (measurable_const_mul _), hinv _ hs'])
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using ha)
  refine ⟨b / a, ?_⟩
  rw [hb]
  conv_rhs => rw [ha]
  rw [smul_smul, ← ENNReal.coe_mul, div_mul_cancel₀ _ ha0]

theorem map_conj_eq_smul : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)) (μ : Measure (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → μ (S : Set (Formalism.REAL.UJ ε))ᶜ = 0 → (∀ s ∈ S, μ.map (fun g => s * g) = μ) → IsFiniteMeasureOnCompacts μ → μ ≠ 0 → ∀ m : Formalism.REAL.UJ ε, (∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) → ∃ c : NNReal, μ.map (fun u => m * u * m⁻¹) = (c : ENNReal) • μ :=
  fun _ _ S μ hS hμ hinv hfin h0 m hm => map_conj_eq_smul_of_group S μ hS hμ hinv hfin h0 m hm

end GlobalTheory.ConjScalesMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarySphereVolumeProductRatioAndInvBounds
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.SphereRatio

theorem sphV_succ (i : ℕ) : sphV (i + 1) = sphV i * (2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)) := by
  unfold sphV
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

theorem sphV_pos (i : ℕ) : 0 < sphV i := by
  unfold sphV
  refine Finset.prod_pos fun l _ => ?_
  have := Real.pi_pos
  positivity

theorem le_exp : (32.5 : ℝ) ≤ Real.exp 3.49 := by
  have h := Real.sum_le_exp_of_nonneg (x := (3.49 : ℝ)) (by norm_num) 10
  refine le_trans ?_ h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

theorem sphV_add_le (m j : ℕ) : sphV (m + j) ≤ sphV m * Real.exp (3.49 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := GlobalTheory.zetaProd_sphereVolume_bounds.2.2 (m + j + 1) (by omega)
    rw [Nat.add_sub_cancel] at h
    have h2 := h.trans le_exp
    have hp := Real.pi_pos
    have hm := sphV_pos m
    rw [← add_assoc, sphV_succ]
    calc sphV (m + j) * (2 * Real.pi ^ (m + j + 1) / ((m + j).factorial : ℝ))
        ≤ (sphV m * Real.exp (3.49 * j)) * Real.exp 3.49 :=
          mul_le_mul ih h2 (by positivity) (by positivity)
      _ = sphV m * Real.exp (3.49 * ((j + 1 : ℕ) : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add]
          push_cast
          ring_nf

theorem inv_sphV_le (J : ℕ) : (sphV J)⁻¹ ≤ (J : ℝ) ^ (J * (J - 1) / 2) := by
  induction J with
  | zero => simp [sphV]
  | succ J ih =>
    have hp : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have h1 : (1 : ℝ) ≤ 2 * Real.pi ^ (J + 1) := by
      have := one_le_pow₀ (n := J + 1) hp
      linarith
    have hf : (J.factorial : ℝ) ≤ (J : ℝ) ^ J := by exact_mod_cast Nat.factorial_le_pow J
    have h2 : (2 * Real.pi ^ (J + 1) / (J.factorial : ℝ))⁻¹ ≤ (J : ℝ) ^ J := by
      rw [inv_div]
      exact (div_le_self (by positivity) h1).trans hf
    have he : (J + 1) * (J + 1 - 1) / 2 = J * (J - 1) / 2 + J := Nat.triangle_succ J
    have hJ := sphV_pos J
    rw [sphV_succ, mul_inv, he]
    calc (sphV J)⁻¹ * (2 * Real.pi ^ (J + 1) / (J.factorial : ℝ))⁻¹
        ≤ (J : ℝ) ^ (J * (J - 1) / 2) * (J : ℝ) ^ J :=
          mul_le_mul ih h2 (by positivity) (by positivity)
      _ = (J : ℝ) ^ (J * (J - 1) / 2 + J) := by rw [pow_add]
      _ ≤ ((J + 1 : ℕ) : ℝ) ^ (J * (J - 1) / 2 + J) :=
          pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _

end GlobalTheory.SphereRatio

theorem GlobalTheory.sphV_ratio_and_inv_bounds :
    (∀ q j : ℕ, j ≤ q → Real.log (sphV q / sphV (q - j)) ≤ 3.49 * j) ∧
      ∀ J : ℕ, 0 < sphV J ∧ (sphV J)⁻¹ ≤ (J : ℝ) ^ (J * (J - 1) / 2) := by
  refine ⟨fun q j h => ?_, fun J => ⟨GlobalTheory.SphereRatio.sphV_pos J, GlobalTheory.SphereRatio.inv_sphV_le J⟩⟩
  have h1 := GlobalTheory.SphereRatio.sphV_add_le (q - j) j
  rw [Nat.sub_add_cancel h] at h1
  have hq := GlobalTheory.SphereRatio.sphV_pos q
  have hm := GlobalTheory.SphereRatio.sphV_pos (q - j)
  rw [Real.log_le_iff_le_exp (by positivity), div_le_iff₀ hm, mul_comm]
  exact h1
end

