module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.FrameInvMulVecNegativeVector
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DominantRootSums
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.DominantRootSums

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma sum_index_mul_root_eq_sub' {n : ℕ} (a b : Fin n) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * _root_.PI.UpqRep.root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [_root_.PI.UpqRep.root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.DominantRootSums.not_cDom_add_root : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (a b : Fin n), a < b →
    ¬ _root_.PI.UpqRep.CDom ε (Λ + _root_.PI.UpqRep.root a b) Λ := by
  intro n ε Λ a b hab hdom
  unfold _root_.PI.UpqRep.CDom at hdom
  obtain ⟨c, hc, hsum⟩ := hdom
  rw [show Λ - (Λ + _root_.PI.UpqRep.root a b) = -_root_.PI.UpqRep.root a b by abel] at hsum
  have h1 := congrArg (fun v : Fin n → ℝ => ∑ i : Fin n, ((i : ℕ) : ℝ) * v i) hsum
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, sum_index_mul_root_eq_sub'] at h1
  have hR : ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ a', ∑ b', (c a' b' : ℝ) • _root_.PI.UpqRep.root a' b') i
      = ∑ a', ∑ b', (c a' b' : ℝ) * (((a' : ℕ) : ℝ) - ((b' : ℕ) : ℝ)) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [← sum_index_mul_root_eq_sub', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hR] at h1
  have hle : ∑ a', ∑ b', (c a' b' : ℝ) * (((a' : ℕ) : ℝ) - ((b' : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun a' _ => Finset.sum_nonpos fun b' _ => ?_
    by_cases h0 : c a' b' = 0
    · simp [h0]
    · have hlt : ((a' : ℕ) : ℝ) < ((b' : ℕ) : ℝ) := by exact_mod_cast (hc a' b' h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

end GlobalTheory.DominantRootSums
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DstInvContinuousOn
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LengthCont

variable {n ι : Type} [Fintype n] [DecidableEq n]

def dst (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) (A : Matrix n n ℂ) : ℝ :=
  Metric.infDist (WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)
    (Submodule.span ℂ ((fun b => (WithLp.toLp 2 (A *ᵥ f b) : EuclideanSpace ℂ n)) '' s) : Set _)

def opn (M : Matrix n n ℂ) : ℝ := ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M‖

lemma opn_cont : Continuous (opn (n := n)) := by

  let L : Matrix n n ℂ →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
    { toFun := fun M => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M
      map_add' := fun M N => map_add _ M N
      map_smul' := fun c M => map_smul _ c M }
  exact continuous_norm.comp (LinearMap.continuous_of_finiteDimensional L)

lemma opn_one [Nonempty n] : opn (1 : Matrix n n ℂ) = 1 := by
  unfold opn
  rw [map_one]
  exact norm_one

private lemma infDist_image_le_opNorm_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (y : E) (K : Set E) (hK : K.Nonempty) :
    Metric.infDist (T y) (T '' K) ≤ ‖T‖ * Metric.infDist y K := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (‖T‖ + 1) := by positivity
  obtain ⟨p, hp, hd⟩ := (Metric.infDist_lt_iff hK).1 (lt_add_of_pos_right (Metric.infDist y K) hδ)
  have hTε : ‖T‖ * (ε / (‖T‖ + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg T]
  calc Metric.infDist (T y) (T '' K) ≤ dist (T y) (T p) :=
        Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem T hp)
    _ ≤ ‖T‖ * dist y p := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]; exact T.le_opNorm _
    _ ≤ ‖T‖ * (Metric.infDist y K + ε / (‖T‖ + 1)) := by gcongr
    _ ≤ ‖T‖ * Metric.infDist y K + ε := by rw [mul_add]; linarith

lemma dst_mul_le (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) (M A : Matrix n n ℂ) :
    dst x f s (M * A) ≤ opn M * dst x f s A := by
  unfold dst
  set T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M
  have key : ∀ v : n → ℂ, (WithLp.toLp 2 ((M * A) *ᵥ v) : EuclideanSpace ℂ n) =
      T (WithLp.toLp 2 (A *ᵥ v)) := fun v => by
    rw [← Matrix.mulVec_mulVec]; rfl
  simp only [key]
  set S : Set (EuclideanSpace ℂ n) := (fun b => (WithLp.toLp 2 (A *ᵥ f b) : EuclideanSpace ℂ n)) '' s
  have himg : (fun b => T (WithLp.toLp 2 (A *ᵥ f b))) '' s = T '' S := (Set.image_image _ _ _).symm
  rw [himg]

  have hsub : T '' (Submodule.span ℂ S : Set _) ⊆ (Submodule.span ℂ (T '' S) : Set _) := by
    rintro _ ⟨p, hp, rfl⟩
    exact Submodule.apply_mem_span_image_of_mem_span (T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) hp
  calc Metric.infDist (T (WithLp.toLp 2 (A *ᵥ x))) (Submodule.span ℂ (T '' S) : Set _)
      ≤ Metric.infDist (T (WithLp.toLp 2 (A *ᵥ x))) (T '' (Submodule.span ℂ S : Set _)) :=
        Metric.infDist_le_infDist_of_subset hsub ⟨T 0, 0, Submodule.zero_mem _, rfl⟩
    _ ≤ ‖T‖ * Metric.infDist (WithLp.toLp 2 (A *ᵥ x)) (Submodule.span ℂ S : Set _) :=
        infDist_image_le_opNorm_mul T _ _ ⟨0, Submodule.zero_mem _⟩
    _ = opn M * Metric.infDist (WithLp.toLp 2 (A *ᵥ x)) (Submodule.span ℂ S : Set _) := rfl

lemma dst_inv_continuousOn [Nonempty n] (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) :
    ContinuousOn (fun g : Matrix n n ℂ => dst x f s g⁻¹) {g | IsUnit g.det} := by
  set U : Set (Matrix n n ℂ) := {g | IsUnit g.det}

  have hinv : ContinuousOn (fun g : Matrix n n ℂ => g⁻¹) U := by
    have h : (fun g : Matrix n n ℂ => g⁻¹) = fun g => (g.det)⁻¹ • g.adjugate := by
      funext g; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h]
    exact (continuous_id.matrix_det.continuousOn.inv₀ fun (g : Matrix n n ℂ) (hg : g ∈ U) => (show IsUnit g.det from hg).ne_zero).smul
      continuous_id.matrix_adjugate.continuousOn
  intro g0 hg0
  have hg0' : IsUnit g0.det := hg0
  set a0 := dst x f s g0⁻¹

  have hu : Filter.Tendsto (fun g => opn (g⁻¹ * g0)) (nhdsWithin g0 U) (nhds 1) := by
    have hc : ContinuousWithinAt (fun g => opn (g⁻¹ * g0)) U g0 :=
      opn_cont.continuousAt.comp_continuousWithinAt ((hinv g0 hg0).mul continuousWithinAt_const)
    have h1 : opn (g0⁻¹ * g0) = 1 := by rw [Matrix.nonsing_inv_mul _ hg0', opn_one]
    have := hc.tendsto
    rwa [h1] at this
  have hv : Filter.Tendsto (fun g => opn (g0⁻¹ * g)) (nhdsWithin g0 U) (nhds 1) := by
    have hc : Continuous fun g => opn (g0⁻¹ * g) := opn_cont.comp (continuous_const.mul continuous_id)
    have h1 : opn (g0⁻¹ * g0) = 1 := by rw [Matrix.nonsing_inv_mul _ hg0', opn_one]
    have := hc.continuousWithinAt (s := U) (x := g0) |>.tendsto
    rwa [h1] at this
  have hup : ∀ g ∈ U, dst x f s g⁻¹ ≤ opn (g⁻¹ * g0) * a0 := by
    intro g _
    have h := dst_mul_le x f s (g⁻¹ * g0) g0⁻¹
    rwa [mul_assoc, Matrix.mul_nonsing_inv _ hg0', mul_one] at h
  have hlow : ∀ g ∈ U, a0 ≤ opn (g0⁻¹ * g) * dst x f s g⁻¹ := by
    intro g hg
    have h := dst_mul_le x f s (g0⁻¹ * g) g⁻¹
    rwa [mul_assoc, Matrix.mul_nonsing_inv _ (show IsUnit g.det from hg), mul_one] at h
  have hpos : ∀ᶠ g in nhdsWithin g0 U, 0 < opn (g0⁻¹ * g) := hv.eventually (lt_mem_nhds one_pos)
  have hL : Filter.Tendsto (fun g => a0 / opn (g0⁻¹ * g)) (nhdsWithin g0 U) (nhds a0) := by
    have := (tendsto_const_nhds (x := a0)).div hv one_ne_zero
    rwa [div_one] at this
  have hR : Filter.Tendsto (fun g => opn (g⁻¹ * g0) * a0) (nhdsWithin g0 U) (nhds a0) := by
    have := hu.mul_const a0
    rwa [one_mul] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hR ?_ (eventually_nhdsWithin_of_forall hup)
  filter_upwards [hpos, eventually_nhdsWithin_of_forall hlow] with g hg1 hg2
  rw [div_le_iff₀ hg1, mul_comm]
  exact hg2

theorem lenA_continuousOn : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    0 < Formalism.QuantumDeterminants.Tz k r z → ∀ a, ContinuousOn (fun g => lenA k r z g a) (GG k r) := by
  intro k r z _ _ a

  have hsub : GG k r ⊆ {g : Mx k r | IsUnit g.det} := by
    intro g hg
    have h1 : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    have hdet : (Formalism.QuantumDeterminants.Hpk k r).det * (Formalism.QuantumDeterminants.Hpk k r).det = 1 := by
      rw [← Matrix.det_mul, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    show IsUnit g.det
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h2
    rw [← h2, mul_zero] at hdet
    exact zero_ne_one hdet
  exact (dst_inv_continuousOn (Formalism.QuantumDeterminants.fvec k r z a) (Formalism.QuantumDeterminants.fvec k r z) {b | b < a}).mono hsub

end GlobalTheory.LengthCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqSmulOfTwoSided
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.UnipotentRadicalHaar

theorem eq_smul_of_twoSided {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    {μ ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : PI.BesselPeriodGGP.IsHaarOn U μ) (hν : B.IsHaarOn U ν) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ μ = c • ν := by
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => hν.finite_compact K hK⟩
  obtain ⟨c, -, c1, e⟩ := GlobalTheory.BesselPeriodCompare.haar_unique hU hμ
    (ν := ν) ⟨inferInstance, hν.ne_zero, hν.conc, hν.left⟩
  exact ⟨c, c1, e⟩

theorem unimodular_normal : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → PI.IsRightInvM (Formalism.QuantumDeterminants.UWset k r z) μW ∧ IsFiniteMeasure μW ∧ PI.IsRightInvM (Formalism.QuantumDeterminants.Nset k r) μN ∧ (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, h * m * h⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r) ∧ ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, μN.map (fun x : Formalism.QuantumDeterminants.Mt k r => (fun i j => (h * Matrix.of x * h⁻¹) i j : Formalism.QuantumDeterminants.Mt k r)) = μN := by
  intro k r z μW μN hz hT hW hN
  obtain ⟨νW, hνW⟩ := P.weyl_haar_exists k r z hz hT
  obtain ⟨νN, hνN⟩ := P.unipotent_haar_exists k r
  obtain ⟨a, a1, ea⟩ := eq_smul_of_twoSided (P.B2x3.closedW k r z) hW hνW
  obtain ⟨b, -, eb⟩ := eq_smul_of_twoSided (P.B2x2.closedN k r) hN hνN
  refine ⟨fun s hs => ?_, ⟨?_⟩, fun s hs => ?_,
    fun h hh m hm => (Formalism.QuantumDeterminants.uWNormal k r z hz h hh m hm).1, fun h hh => ?_⟩
  · rw [ea, Measure.map_smul _ (by
      apply Continuous.aemeasurable
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [PI.rmulQ, Matrix.mul_apply, Matrix.of_apply]
      fun_prop)]
    exact congrArg (a • ·) (hνW.right s hs)
  · have hK : IsCompact (Formalism.QuantumDeterminants.UWset k r z) := P.weyl_subgroup_compact k r z hz hT
    have h1 : νW (Formalism.QuantumDeterminants.UWset k r z) < ⊤ := hνW.finite_compact _ hK
    have h2 : νW Set.univ ≤ νW (Formalism.QuantumDeterminants.UWset k r z) + νW (Formalism.QuantumDeterminants.UWset k r z)ᶜ :=
      measure_univ_le_add_compl _
    have h3 : νW (Formalism.QuantumDeterminants.UWset k r z)ᶜ = 0 := hνW.conc
    rw [h3, add_zero] at h2
    rw [ea, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top a1.lt_top (h2.trans_lt h1)
  · rw [eb, Measure.map_smul _ (by
      apply Continuous.aemeasurable
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [PI.rmulQ, Matrix.mul_apply, Matrix.of_apply]
      fun_prop)]
    exact congrArg (b • ·) (hνN.right s hs)
  · rw [eb, Measure.map_smul _ (by
      apply Continuous.aemeasurable
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply]
      fun_prop)]
    exact congrArg (b • ·) (P.b2_conjInvRaw_proof k r z νN hz hT hνN h hh)

end GlobalTheory.UnipotentRadicalHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFrameConjUnitaryBlockEqUnitaryComplement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselFrame

open Formalism.FourierDecayAlt.P.SettingConstruction

section forms
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)

lemma quasi_reflection (hH : Hᴴ = H) (u v : ι → ℂ)
    (huv : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H v v)
    (hne : Formalism.QuantumDeterminants.herm H u u ≠ Formalism.QuantumDeterminants.herm H u v) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v ∧
      ∀ x, Formalism.QuantumDeterminants.herm H x u = 0 → Formalism.QuantumDeterminants.herm H x v = 0 → g *ᵥ x = x := by
  set d := u - v with hd
  set s := Formalism.QuantumDeterminants.herm H u d with hs
  have hs' : s = Formalism.QuantumDeterminants.herm H u u - Formalism.QuantumDeterminants.herm H u v := by rw [hs, hd, herm_sub_right]
  have hs0 : s ≠ 0 := by rw [hs']; exact sub_ne_zero.mpr hne
  have hss : star s = Formalism.QuantumDeterminants.herm H u u - Formalism.QuantumDeterminants.herm H v u := by
    rw [hs, herm_symm H hH, hd, herm_sub_left]
  have hq : Formalism.QuantumDeterminants.herm H d d = s + star s := by
    rw [hss, hs', hd]
    simp only [herm_sub_left, herm_sub_right]
    linear_combination -huv
  set a : ℂ := s⁻¹ with ha'
  have ha : a * s = 1 := inv_mul_cancel₀ hs0
  have hsa : star a * star s = 1 := by rw [← star_mul', ha, star_one]
  refine ⟨rk H d 1 (-a), unitary_of_form H _ fun x y => ?_, ?_, fun x hxu hxv => ?_⟩
  · rw [rk_mulVec, rk_mulVec]
    have hY : star (Formalism.QuantumDeterminants.herm H y d) = Formalism.QuantumDeterminants.herm H d y := herm_symm H hH y d
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, star_mul', hY, hq,
      star_neg, star_one]
    linear_combination (star a * Formalism.QuantumDeterminants.herm H x d * Formalism.QuantumDeterminants.herm H d y) * ha +
      (a * Formalism.QuantumDeterminants.herm H x d * Formalism.QuantumDeterminants.herm H d y) * hsa
  · rw [rk_mulVec, ← hs, neg_mul, ha, hd]
    simp
  · rw [rk_mulVec, hd, herm_sub_right, hxu, hxv]
    simp

lemma exists_isometry (hH : Hᴴ = H) (u v : ι → ℂ)
    (huv : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H v v) (h0 : Formalism.QuantumDeterminants.herm H u u ≠ 0) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v ∧
      ∀ x, Formalism.QuantumDeterminants.herm H x u = 0 → Formalism.QuantumDeterminants.herm H x v = 0 → g *ᵥ x = x := by
  by_cases hne : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H u v
  swap
  · exact quasi_reflection H hH u v huv hne
  have e1 : Formalism.QuantumDeterminants.herm H ((-1 : ℂ) • u) ((-1 : ℂ) • u) = Formalism.QuantumDeterminants.herm H u u := by
    simp only [herm_smul_left, herm_smul_right]; simp
  obtain ⟨g₁, h1, h2, h3⟩ := quasi_reflection H hH u ((-1 : ℂ) • u) e1.symm (by
    rw [herm_smul_right]
    intro h; apply h0
    simp only [star_neg, star_one] at h
    linear_combination h / 2)
  obtain ⟨g₂, k1, k2, k3⟩ := quasi_reflection H hH ((-1 : ℂ) • u) v (e1.trans huv) (by
    rw [e1, herm_smul_left, ← hne]
    intro h; apply h0
    linear_combination h / 2)
  refine ⟨g₂ * g₁, ?_, ?_, fun x hxu hxv => ?_⟩
  · calc (g₂ * g₁)ᴴ * H * (g₂ * g₁) = g₁ᴴ * (g₂ᴴ * H * g₂) * g₁ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [k1, h1]
  · rw [← Matrix.mulVec_mulVec, h2, k2]
  · have : Formalism.QuantumDeterminants.herm H x ((-1 : ℂ) • u) = 0 := by rw [herm_smul_right, hxu, mul_zero]
    rw [← Matrix.mulVec_mulVec, h3 x hxu this, k3 x this hxv]

end forms

open PI.UpqRep PI.HwUniqW

variable {k r : ℕ}

lemma herm_right_bvec (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.herm (Hpk k r) y (bvec i) = epsI k r i * y (piI k r i) := by
  rw [← Hpk_mulVec_apply]
  simp [Formalism.QuantumDeterminants.herm, bvec, Pi.star_single]

lemma herm_bvec_eq_zero {y : Fin (2 * r + k + 1) → ℂ} (hy : inWb k r y) {i : Fin (2 * r + k + 1)}
    (hi : i.val < r ∨ r + k < i.val) : Formalism.QuantumDeterminants.herm (Hpk k r) (bvec i) y = 0 := by
  rw [← herm_symm _ Hpk_conjTranspose, herm_right_bvec, hy (piI k r i), mul_zero, star_zero]
  rw [piI_val]
  have := i.isLt
  split_ifs <;> omega

lemma exists_isFrameW (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∃ g, IsFrameW k r z g := by
  set T := Tz k r z with hTdef
  set u : Fin (2 * r + k + 1) → ℂ := ((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)) with hu
  have hw : Formalism.QuantumDeterminants.herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) = -1 := by
    have hp : piI k r (wI k r (Fin.last k)) = wI k r (Fin.last k) := by
      unfold piI; rw [if_pos (by simp [wI])]
    rw [herm_right_bvec, hp, bvec_apply, if_pos rfl]
    simp [epsI, wI]
  have huu : Formalism.QuantumDeterminants.herm (Hpk k r) u u = -(T : ℂ) := by
    rw [hu, herm_smul_left, herm_smul_right, hw]
    have h1 : star ((Real.sqrt T : ℝ) : ℂ) = ((Real.sqrt T : ℝ) : ℂ) := Complex.conj_ofReal _
    have h2 : ((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ) = (T : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]
    rw [h1]
    linear_combination -h2
  have hzz : Formalism.QuantumDeterminants.herm (Hpk k r) z z = -(T : ℂ) := by
    have h1 : star (Formalism.QuantumDeterminants.herm (Hpk k r) z z) = Formalism.QuantumDeterminants.herm (Hpk k r) z z :=
      herm_symm _ Hpk_conjTranspose z z
    have h2 : T = -(Formalism.QuantumDeterminants.herm (Hpk k r) z z).re := rfl
    rw [h2, Complex.ofReal_neg, neg_neg]
    exact (Complex.conj_eq_iff_re.mp h1).symm
  have huW : inWb k r u := by
    intro i hi
    rw [hu, Pi.smul_apply, bvec_apply, if_neg, smul_zero]
    rintro rfl
    simp [wI] at hi
  obtain ⟨g, h1, h2, h3⟩ := exists_isometry (Hpk k r) Hpk_conjTranspose u z (huu.trans hzz.symm) (by
    rw [huu, neg_ne_zero]; exact_mod_cast hT.ne')
  refine ⟨g, h1, fun a => ⟨?_, ?_⟩, h2⟩
  · have ha : (eI k r a).val < r ∨ r + k < (eI k r a).val := Or.inl a.isLt
    exact h3 _ (herm_bvec_eq_zero huW ha) (herm_bvec_eq_zero hz ha)
  · have ha : (esI k r a).val < r ∨ r + k < (esI k r a).val := by
      have := a.isLt
      right; simp only [esI]; omega
    exact h3 _ (herm_bvec_eq_zero huW ha) (herm_bvec_eq_zero hz ha)

lemma blockW_fix (x : Matrix (Fin k) (Fin k) ℂ) {j : Fin (2 * r + k + 1)} (hj : ¬ InB k r j) :
    blockW k r x *ᵥ bvec j = bvec j := by
  funext i
  rw [mulVec_bvec_apply, bvec_apply]
  by_cases hi : InB k r i
  · rw [blockW_in_out _ hi hj, if_neg (ne_of_inB hi hj)]
  · rw [blockW_out _ hi]

lemma blockW_mem_UH {x : Matrix (Fin k) (Fin k) ℂ} (hx : x ∈ UJset (allPos k)) :
    blockW k r x ∈ UH (Hpk k r) := by
  show (blockW k r x)ᴴ * Hpk k r * blockW k r x = Hpk k r
  rw [blockW_conjTranspose, ← Hpk_blockW_comm, Matrix.mul_assoc, blockW_mul, mem_UJset_allPos.mp hx,
    blockW_one, Matrix.mul_one]

lemma conj_mem_UW {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : IsFrameW k r z g) {x : Matrix (Fin k) (Fin k) ℂ} (hx : x ∈ UJset (allPos k)) :
    g * blockW k r x * g⁻¹ ∈ UWset k r z := by
  refine ⟨mul_mem_UH (mul_mem_UH hg.1 (blockW_mem_UH hx)) (inv_mem_UH hg.1), fun a => ⟨?_, ?_⟩, ?_⟩
  · have := a.isLt
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hg.1 (hg.2.1 a).1,
      blockW_fix x (by unfold InB eI; simp only; omega), (hg.2.1 a).1]
  · have := a.isLt
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hg.1 (hg.2.1 a).2,
      blockW_fix x (by unfold InB esI; simp only; omega), (hg.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, frame_inv_mulVec_negativeVector hg, Matrix.mulVec_smul,
      blockW_fix x (by unfold InB wI; simp), hg.2.2]

theorem frame_exists : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∃ g, PI.UpqRep.IsFrameW k r z g ∧ (∀ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), g * PI.UpqRep.blockW k r x * g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z) ∧ ∀ y ∈ Formalism.QuantumDeterminants.UWset k r z, ∃ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), y = g * PI.UpqRep.blockW k r x * g⁻¹ := by
  intro k r z hz hT
  have hT' : 0 < PI.UpqRep.Tz k r z := hT
  obtain ⟨g, hg⟩ := exists_isFrameW z hz hT'
  refine ⟨g, hg, fun x hx => conj_mem_UW hg hx, fun y hy => ?_⟩
  obtain ⟨x, hx, -, e⟩ := UW_eq_conj hT' hg hy
  exact ⟨x, hx, e⟩

end GlobalTheory.BesselFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsAlgClosedAddValuationIsAdicComplete
section
namespace GlobalTheory

open scoped NNReal

theorem expNegTop_inj_of_eq {a b : WithTop ℚ} (h : expNegTop a = expNegTop b) : a = b :=
  le_antisymm ((expNegTop_le_iff _ _).1 h.ge) ((expNegTop_le_iff _ _).1 h.le)

noncomputable def expNegAbsoluteValue {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) :
    AbsoluteValue F ℝ where
  toFun x := (expNegValuation v x : ℝ)
  map_mul' x y := by rw [map_mul, NNReal.coe_mul]
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by rw [NNReal.coe_eq_zero, Valuation.zero_iff]
  add_le' x y := by
    have h := (expNegValuation v).map_add x y
    have h' : expNegValuation v (x + y) ≤ expNegValuation v x + expNegValuation v y :=
      h.trans (max_le le_self_add le_add_self)
    exact_mod_cast h'

theorem isNonarchimedean_expNegAbsoluteValue {F : Type} [Field F]
    (v : AddValuation F (WithTop ℚ)) : IsNonarchimedean (expNegAbsoluteValue v) := by
  intro x y
  have h := (expNegValuation v).map_add x y
  change ((expNegValuation v (x + y) : ℝ≥0) : ℝ) ≤
    max ((expNegValuation v x : ℝ≥0) : ℝ) ((expNegValuation v y : ℝ≥0) : ℝ)
  exact_mod_cast h

theorem exists_norm_eq_of_completion {K : Type*} [NormedField K] [IsUltrametricDist K]
    (x : UniformSpace.Completion K) : ∃ y : K, ‖x‖ = ‖y‖ := by
  haveI : IsUltrametricDist (UniformSpace.Completion K) := IsUltrametricDist.of_normedAlgebra K
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp⟩
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.1 (UniformSpace.Completion.denseRange_coe (α := K)) x
    ‖x‖ (norm_pos_iff.2 hx)
  refine ⟨y, ?_⟩
  rw [← UniformSpace.Completion.norm_coe y]
  rw [dist_comm, dist_eq_norm] at hy
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x) (y := y - x) hy.ne'
  rw [add_sub_cancel, max_eq_left hy.le] at h
  exact h.symm

theorem exists_addValuation_expNegTop_eq_nnnorm {C : Type} [NormedField C] [IsUltrametricDist C]
    (h : ∀ x : C, ∃ t : WithTop ℚ, expNegTop t = ‖x‖₊) :
    ∃ v : AddValuation C (WithTop ℚ), ∀ x, expNegTop (v x) = ‖x‖₊ := by
  choose f hf using h
  refine ⟨AddValuation.of f ?_ ?_ ?_ ?_, hf⟩
  · apply expNegTop_inj_of_eq
    rw [hf, nnnorm_zero, expNegTop_top]
  · apply expNegTop_inj_of_eq
    rw [hf, nnnorm_one, expNegTop_zero]
  · intro x y
    rcases le_max_iff.1 (IsUltrametricDist.nnnorm_add_le_max x y) with h | h
    · exact min_le_of_left_le ((expNegTop_le_iff _ _).1 (by rwa [hf, hf]))
    · exact min_le_of_right_le ((expNegTop_le_iff _ _).1 (by rwa [hf, hf]))
  · intro x y
    apply expNegTop_inj_of_eq
    rw [expNegTop_add, hf, hf, hf, nnnorm_mul]

end GlobalTheory
end

