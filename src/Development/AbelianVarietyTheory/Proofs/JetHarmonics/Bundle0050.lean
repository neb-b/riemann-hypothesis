module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensLen

open Formalism.HermitianLatticeCounting.ExpansionTerms (majorantDistance)

section general

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem infDist_add_mem (S : Submodule ℂ V) (x w : V) (hw : w ∈ S) :
    Metric.infDist (x + w) (S : Set V) = Metric.infDist x (S : Set V) := by
  have h := Metric.infDist_image (isometry_add_right w) (x := x) (t := (S : Set V))
  have h2 : (fun y => y + w) '' (S : Set V) = S := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact S.add_mem hy hw
    · intro hv
      exact ⟨v - w, S.sub_mem hv hw, by simp⟩
  rwa [h2] at h

theorem len_eq_of_unitriangular {n : ℕ} (y y' : Fin n → V) (U : Matrix (Fin n) (Fin n) ℂ)
    (h0 : ∀ c a, a < c → U c a = 0) (h1 : ∀ c, U c c = 1) (h : ∀ a, y a = ∑ c, U c a • y' c) (a : Fin n) :
    majorantDistance y a = majorantDistance y' a := by
  have hrest : ∀ (S : Submodule ℂ V) (b : Fin n), (∀ c, c < b → y' c ∈ S) →
      ∑ c ∈ univ.erase b, U c b • y' c ∈ S := by
    intro S b hS
    refine S.sum_mem fun c hc => ?_
    rcases lt_trichotomy c b with hcb | hcb | hcb
    · exact S.smul_mem _ (hS c hcb)
    · exact absurd hcb (Finset.ne_of_mem_erase hc)
    · rw [h0 c b hcb, zero_smul]; exact S.zero_mem
  have hy : ∀ b, y b = y' b + ∑ c ∈ univ.erase b, U c b • y' c := by
    intro b
    rw [h b, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), h1, one_smul]
  have hspan : Submodule.span ℂ (y '' {b | b < a}) = Submodule.span ℂ (y' '' {b | b < a}) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      rw [hy b]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨b, hb, rfl⟩)
        (hrest _ b fun c hc => Submodule.subset_span ⟨c, lt_trans hc hb, rfl⟩)
    · rw [Submodule.span_le]
      have key : ∀ b, b < a → y' b ∈ Submodule.span ℂ (y '' {b | b < a}) := by
        intro b
        induction b using WellFoundedLT.induction with
        | ind b ih =>
          intro hb
          rw [eq_sub_of_add_eq (hy b).symm]
          exact Submodule.sub_mem _ (Submodule.subset_span ⟨b, hb, rfl⟩)
            (hrest _ b fun c hc => ih c hc (lt_trans hc hb))
      rintro _ ⟨b, hb, rfl⟩
      exact key b hb
  unfold majorantDistance
  rw [hspan, hy a]
  exact infDist_add_mem _ _ _ (hrest _ a fun c hc => Submodule.subset_span ⟨c, hc, rfl⟩)

theorem len_pos {n : ℕ} (y : Fin n → V) (hy : LinearIndependent ℂ y) (a : Fin n) : 0 < majorantDistance y a := by
  unfold majorantDistance
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (y '' {b | b < a})) :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  refine ((Submodule.closed_of_finiteDimensional _).notMem_iff_infDist_pos ⟨0, Submodule.zero_mem _⟩).1 ?_
  exact hy.notMem_span_image (by simp)

theorem len_zero {n : ℕ} (y : Fin (n + 1) → V) : majorantDistance y 0 = ‖y 0‖ := by
  unfold majorantDistance
  have : y '' {b | b < 0} = ∅ := by simp
  rw [this, Submodule.span_empty, Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]

end general

theorem cmp_mulVec_wedge {n l : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin l → Fin n → ℂ) :
    BranchingSupport.cmp l g *ᵥ wedge f = wedge (fun b => g *ᵥ f b) := by
  funext I
  have h := Formalism.HermitianLatticeCounting.P.ge_cauchyBinet (g.submatrix (I.1.orderEmbOfFin I.2) id)
    (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)
  refine Eq.trans ?_ (h.symm.trans ?_)
  · simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [mul_comm]
    rfl
  · rfl

theorem sum_norm_wedge {n l : ℕ} (f : Fin l → Fin n → ℂ) :
    ∑ J, ‖wedge f J‖ ^ 2 =
      ∏ a, majorantDistance (fun b => (WithLp.toLp 2 (f b) : EuclideanSpace ℂ (Fin n))) a ^ 2 := by
  have h := Formalism.HermitianLatticeCounting.P.gram_matrix_product_formula (EuclideanSpace ℂ (Fin n)) l (fun b => WithLp.toLp 2 (f b))
  have h2 := Formalism.HermitianLatticeCounting.P.ge_cauchyBinet (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)ᴴ
    (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)
  have h3 : (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)ᴴ *
      (Matrix.of fun (i : Fin n) (b : Fin l) => f b i) =
      Matrix.of fun a b => inner ℂ (WithLp.toLp 2 (f a) : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 (f b)) := by
    ext a b
    simp [Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  rw [h3, h] at h2
  apply Complex.ofReal_injective
  rw [h2]
  push_cast
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose, RCLike.star_def, Complex.mul_conj']
  rfl

theorem sum_norm_sq_eq {n : ℕ} (v : Fin n → ℂ) : ((∑ c, ‖v c‖ ^ 2 : ℝ) : ℂ) = v ⬝ᵥ star v := by
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj']

theorem sum_norm_dual {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (hg : gᴴ * H * g = H) (hu : IsUnit g.det) (f : Fin n → ℂ) :
    ∑ c, ‖(dualM g⁻¹ *ᵥ (fun c => Formalism.QuantumDeterminants.herm H (Pi.single c 1) f)) c‖ ^ 2 = ∑ c, ‖(g⁻¹ *ᵥ f) c‖ ^ 2 := by
  have h1 : (fun c => Formalism.QuantumDeterminants.herm H (Pi.single c 1) f) = star f ᵥ* H := by
    funext c
    simp [Formalism.QuantumDeterminants.herm, vecMul, dotProduct]
  have h2 : H * g = (g⁻¹)ᴴ * H := by
    conv_rhs => rw [← hg]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hu,
      conjTranspose_one, Matrix.one_mul]
  have h3 : dualM g⁻¹ *ᵥ (star f ᵥ* H) = star (H *ᵥ (g⁻¹ *ᵥ f)) := by
    rw [dualM, nonsing_inv_nonsing_inv _ hu, mulVec_transpose, vecMul_vecMul, h2, star_mulVec, star_mulVec,
      vecMul_vecMul, hH]
  rw [h1, h3]
  apply Complex.ofReal_injective
  rw [sum_norm_sq_eq, sum_norm_sq_eq, star_star, star_mulVec, hH, dotProduct_mulVec, vecMul_vecMul, hHH,
    vecMul_one, dotProduct_comm]

theorem fvec_indep (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) : LinearIndependent ℂ (Formalism.QuantumDeterminants.fvec k r z) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [Formalism.QuantumDeterminants.Tz, Formalism.QuantumDeterminants.herm] at hT
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz0
  have hir : r ≤ i.val := by
    by_contra hlt
    exact hi (hz i (Or.inl (by omega)))
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  by_cases ha : a.val < r
  · have := congrFun hc ⟨a.val, by omega⟩
    rw [Finset.sum_apply, Finset.sum_eq_single a] at this
    · rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_lt z hz _ _ ha] at this
      simpa using this
    · intro b _ hb
      rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_lt z hz _ _ ha, if_neg (fun h => hb (Fin.ext h)), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have := congrFun hc i
    rw [Finset.sum_apply, Finset.sum_eq_single a] at this
    · rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_ge z _ _ hir, if_pos (by omega)] at this
      exact (mul_eq_zero.1 this).resolve_right hi
    · intro b _ hb
      rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_ge z _ _ hir,
        if_neg (fun h => hb (Fin.ext (by omega))), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem isUnit_det_of_unitary {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hHH : H * H = 1)
    (hg : gᴴ * H * g = H) : IsUnit g.det := by
  have h : (H * (gᴴ * H)) * g = 1 := by rw [Matrix.mul_assoc, hg, hHH]
  exact Matrix.isUnit_det_of_left_inverse h

theorem lengths : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∀ g ∈ GG k r, (∑ J, ‖(cmp (r + 1) g⁻¹ *ᵥ (wedge (Formalism.QuantumDeterminants.fvec k r z))) J‖ ^ 2 = ∏ a, lenA k r z g a ^ 2) ∧ (∑ c, ‖(dualM g⁻¹ *ᵥ (flat k r (Formalism.QuantumDeterminants.fvec k r z 0))) c‖ ^ 2 = lenA k r z g 0 ^ 2) ∧ (∀ a, 0 < lenA k r z g a) ∧ ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ a, lenA k r z (s * g) a = lenA k r z g a := by
  intro k r z hz hT g hg
  obtain ⟨hH, hHH, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have hu : IsUnit g.det := isUnit_det_of_unitary hHH hg
  have hl : ∀ g a, lenA k r z g a = majorantDistance (fun b => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) :
      EuclideanSpace ℂ (Fin (2 * r + k + 1)))) a := fun _ _ => rfl
  refine ⟨?_, ?_, fun a => ?_, fun s hs a => ?_⟩
  · rw [cmp_mulVec_wedge, sum_norm_wedge]
    rfl
  · rw [hl, len_zero, EuclideanSpace.norm_sq_eq]
    exact sum_norm_dual _ g hH hHH hg hu _
  · rw [hl]
    refine len_pos _ ?_ a
    have hinj : Function.Injective (g⁻¹).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det g hu))
    have h1 := (fvec_indep k r z hz hT).map' (Matrix.mulVecLin g⁻¹) (LinearMap.ker_eq_bot.2 hinj)
    exact h1.map' (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap (LinearEquiv.ker _)
  · obtain ⟨U, h0, h1, hF⟩ := Formalism.QuantumDeterminants.S_F hz hs
    have hsu : IsUnit s.det := isUnit_det_of_unitary hHH (Formalism.QuantumDeterminants.Sset_UH hs)
    rw [hl, hl]
    symm
    refine len_eq_of_unitriangular _ _ U h0 h1 (fun b => ?_) a
    have hcol : s *ᵥ Formalism.QuantumDeterminants.fvec k r z b = ∑ c, U c b • Formalism.QuantumDeterminants.fvec k r z c := by
      funext i
      have := congrFun (congrFun hF i) b
      simpa [Matrix.mul_apply, Formalism.QuantumDeterminants.Fm, mulVec, dotProduct, mul_comm] using this
    have h2 : g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b = (s * g)⁻¹ *ᵥ (s *ᵥ Formalism.QuantumDeterminants.fvec k r z b) := by
      rw [mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul _ hsu, Matrix.mul_one]
    rw [h2, hcol, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, WithLp.toLp_sum, WithLp.toLp_smul]

end GlobalTheory.TensLen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqIntegralInnerWeightLe
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem norm_sq_integral_inner_smul_le (Ω V : Type) [MeasurableSpace Ω] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (ν : Measure Ω) (f g : Ω → V) (ph : Ω → ℂ)
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν)
    (hp : AEStronglyMeasurable ph ν) :
    ENNReal.ofReal (‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ ^ 2) ≤
      (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) *
        ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν := by
  set F : Ω → ℝ≥0∞ := fun x => ‖ph x‖ₑ * ‖f x‖ₑ with hF
  set G : Ω → ℝ≥0∞ := fun x => ‖g x‖ₑ with hG
  have hFm : AEMeasurable F ν := hp.enorm.mul hf.enorm
  have hGm : AEMeasurable G ν := hg.enorm
  have h1 : ‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ₑ ≤ ∫⁻ x, (F * G) x ∂ν := by
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
    have h : ‖⟪f x, ph x • g x⟫_ℂ‖ ≤ ‖ph x‖ * ‖f x‖ * ‖g x‖ := by
      refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
      rw [norm_smul]; ring
    have := ENNReal.ofReal_le_ofReal h
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ofReal_norm_eq_enorm, ofReal_norm_eq_enorm, ofReal_norm_eq_enorm,
      ofReal_norm_eq_enorm] at this
    exact this
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hFm hGm
  have e1 : (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) = ∫⁻ x, F x ^ (2 : ℝ) ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [← mul_pow, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity),
      ofReal_norm_eq_enorm, ofReal_norm_eq_enorm, ENNReal.rpow_two]
  have e2 : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν) = ∫⁻ x, G x ^ (2 : ℝ) ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (by positivity), ofReal_norm_eq_enorm, ENNReal.rpow_two]
  rw [e1, e2, ENNReal.ofReal_pow (by positivity), ofReal_norm_eq_enorm]
  refine (pow_le_pow_left' (h1.trans h2) 2).trans (le_of_eq ?_)
  have k : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num
  rw [mul_pow, k, k]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyProductBoundConstantLe
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomNum

theorem mom_num : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (T : ℝ), Num k r lam u b bv ga h q0 → 0 < T → (((2 * r + k + 1) : ℝ) ^ 2 * (T * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * (b ^ 2) ^ (2 * r) ≤ Hsq r T b := by
  intro k r lam u b bv ga h q0 T hN hT
  obtain ⟨-, -, -, -, -, -, h7, h8, -, -, -, -, -, -, h15⟩ := hN
  have ha := (h7 ⟨k, by omega⟩ (by simp)).2
  have hb := (abs_le.mp (h8 ⟨k, by omega⟩)).1
  have hbv : bv ≤ b := by linarith
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hn7 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 := le_self_pow₀ hn1 (by norm_num)
  have hcast : ((2 * r + k + 1 : ℕ) : ℝ) = ((2 * r + k + 1) : ℝ) := by push_cast; ring
  rw [hcast] at hn1 hn7 h15
  set n : ℝ := (2 * r + k + 1 : ℝ) with hn
  have hnb : n ≤ b := by linarith
  have hbv6 : 6 ≤ bv := by linarith
  have hb6 : 6 ≤ b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have h6 : 6 * bv ≤ b ^ 2 := by nlinarith
  have hb0 : 0 ≤ b := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hbv0 : 0 ≤ 6 * bv := by linarith
  have hTm : T ≤ max 1 T := le_max_right _ _
  have hm0 : 0 ≤ max 1 T := le_trans zero_le_one (le_max_left _ _)
  unfold Hsq
  calc n ^ 2 * (T * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2)) * (b ^ 2) ^ (2 * r)
      ≤ b ^ 2 * (max 1 T * b ^ 4) * (b ^ 2) ^ (2 * (2 * r + 2)) * (b ^ 2) ^ (2 * r) := by
        gcongr
    _ = max 1 T * b ^ (12 * r + 14) := by ring
    _ ≤ max 1 T * b ^ (20 * (r + 1)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 (by omega)) hm0

end GlobalTheory.MomNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.NumFam

theorem eps_adj (k r : ℕ) (a c : Fin (2 * r + k + 1)) (ha : k ≤ a.val + 1) (hc : c.val = a.val + 1) :
    PI.BesselPeriodGGP.eps48 k r a ≠ PI.BesselPeriodGGP.eps48 k r c := by
  have h1 : ¬ a.val < k - 1 := by omega
  have h2 : ¬ c.val < k - 1 := by omega
  simp only [PI.BesselPeriodGGP.eps48]
  rw [if_neg h1, if_neg h2, hc]
  rcases Nat.mod_two_eq_zero_or_one (a.val - (k - 1)) with h3 | h3
  · have h4 : (a.val + 1 - (k - 1)) % 2 = 1 := by omega
    simp [h3, h4]
  · have h4 : (a.val + 1 - (k - 1)) % 2 = 0 := by omega
    simp [h3, h4]

theorem abs_le_of_lOneNorm_le_coord {n : ℕ} (ν : Fin n → ℤ) (q0 : ℕ) (h : n1 ν ≤ q0) (a : Fin n) : |(ν a : ℝ)| ≤ q0 := by
  have h1 : (ν a).natAbs ≤ n1 ν := by
    unfold n1
    exact Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
  have h2 : |(ν a : ℝ)| = ((ν a).natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [h2]
  exact_mod_cast h1.trans h

theorem gapOK_mono (k r : ℕ) {h h' : ℝ} (hh : h ≤ h') (H : GapOK k r h) : GapOK k r h' := by
  obtain ⟨h1, h2, h3, h4⟩ := H
  have ha : aOf r h ≤ aOf r h' := by
    unfold aOf
    gcongr
  exact ⟨h1, h2.trans hh, h3.trans ha, h4.trans ha⟩

private lemma le_bv_and_lam_gap_of_num (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ)
    (q0 : ℕ) (H : Num k r lam u b bv ga h q0) :
    h ≤ bv ∧ ∀ a c : Fin (2 * r + k + 1), a < c → 100 * ((q0 : ℝ) + 1) ≤ lam a - lam c := by
  obtain ⟨hk, ⟨hanti, -⟩, -, -, -, hcl, hnd, -, -, hga, hgap, -, hq1, hq2, -⟩ := H
  have hhb : h ≤ bv := by
    have he := eps_adj k r ⟨k - 1, by omega⟩ ⟨k, by omega⟩ (show k ≤ k - 1 + 1 by omega)
      (show k = k - 1 + 1 by omega)
    have h0 := hnd ⟨k - 1, by omega⟩ (show k ≤ k - 1 + 1 by omega)
    have h1 := hnd ⟨k, by omega⟩ (show k ≤ k + 1 by omega)
    have hg := hgap _ _ he
    have hb : |lam ⟨k - 1, by omega⟩ - lam ⟨k, by omega⟩| ≤ bv :=
      abs_sub_le_iff.mpr ⟨by linarith [h0.1, h0.2, h1.1, h1.2], by linarith [h0.1, h0.2, h1.1, h1.2]⟩
    linarith
  have hadj : ∀ a c : Fin (2 * r + k + 1), c.val = a.val + 1 →
      100 * ((q0 : ℝ) + 1) ≤ lam a - lam c := by
    intro a c hac
    have hlt : a < c := Fin.lt_def.mpr (by omega)
    have hlam : lam c < lam a := hanti hlt
    by_cases h1 : k ≤ a.val + 1
    · have hg := hgap a c (eps_adj k r a c h1 hac)
      rw [abs_of_pos (by linarith)] at hg
      linarith
    · by_cases h2 : c.val + 1 < k
      · linarith [hga a c hlt h2]
      · have h3 := hcl a (by omega)
        have h4 := hnd c (by omega)
        linarith [h3.1, h4.2]
  refine ⟨hhb, fun a c hac => ?_⟩
  have h5 : a.val < c.val := hac
  have hcN := c.isLt
  have hle : a ≤ ⟨c.val - 1, by omega⟩ := Fin.le_def.mpr (show a.val ≤ c.val - 1 by omega)
  have h6 := hadj ⟨c.val - 1, by omega⟩ c (show c.val = c.val - 1 + 1 by omega)
  have h7 := hanti.antitone hle
  linarith

theorem num_fam : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → (bv ≤ b ∧ (1000000 : ℝ) ≤ bv ∧ ((2 * r + k + 1) : ℝ) ≤ b ∧ 100 * (q0 : ℝ) ≤ bv ∧ GapOK k r (h / 2)) ∧ ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → Formalism.QuantumDeterminants.IsHCParam (fun a => lam a + (ν a : ℝ)) ∧ Shape (PI.BesselPeriodGGP.eps48 k r) k (fun a => lam a + (ν a : ℝ)) bv ∧ Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (h / 2) ∧ ∀ a c, a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
  intro k r lam u b bv ga h q0 H
  obtain ⟨hhb, hgaps⟩ := le_bv_and_lam_gap_of_num k r lam u b bv ga h q0 H
  obtain ⟨hk, ⟨hanti, hint⟩, -, -, -, hcl, hnd, hlb, -, -, hgap, hok, hq1, hq2, hbv⟩ := H
  have hq0 : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hN7 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 := le_self_pow₀ hN1 (by norm_num)
  have hNc : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  have hL := hnd ⟨2 * r + k, by omega⟩ (show k ≤ 2 * r + k + 1 by omega)
  have hLb := hlb ⟨2 * r + k, by omega⟩
  have hLa := neg_le_abs (lam ⟨2 * r + k, by omega⟩)
  have hbvb : bv ≤ b := by linarith [hL.2]
  have h100 : 100 * (q0 : ℝ) ≤ bv := by linarith
  refine ⟨⟨hbvb, by linarith, by linarith, h100, gapOK_mono k r (by linarith) hok⟩, fun ν hν => ?_⟩
  have hνb : ∀ a, -(q0 : ℝ) ≤ ν a ∧ (ν a : ℝ) ≤ q0 := fun a => abs_le.mp (abs_le_of_lOneNorm_le_coord ν q0 hν a)
  have hgap2 : ∀ a c : Fin (2 * r + k + 1), a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
    intro a c hac
    linarith [hgaps a c hac, (hνb a).1, (hνb a).2, (hνb c).1, (hνb c).2]
  refine ⟨⟨fun a c hac => ?_, fun a => ?_⟩, ⟨hk, by omega, fun a c hac => hgap2 a c hac, fun a ha => ?_,
    fun a ha => ?_, hbv⟩, fun a c he => ?_, fun a c hac => hgap2 a c hac⟩
  · show lam c + (ν c : ℝ) < lam a + ν a
    linarith [hgap2 a c hac]
  · obtain ⟨m, hm⟩ := hint a
    refine ⟨m + ν a, ?_⟩
    show lam a + (ν a : ℝ) - (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 = ((m + ν a : ℤ) : ℝ)
    push_cast
    linarith
  · refine ⟨?_, ?_, ?_⟩
    · simp [PI.BesselPeriodGGP.eps48, show a.val < k - 1 by omega]
    · show -(bv / 100) ≤ lam a + (ν a : ℝ)
      linarith [(hcl a ha).1, (hνb a).1]
    · show lam a + (ν a : ℝ) ≤ bv / 8 + bv / 100
      linarith [(hcl a ha).2, (hνb a).2]
  · refine ⟨?_, ?_⟩
    · show -2 * bv - bv / 100 ≤ lam a + (ν a : ℝ)
      linarith [(hnd a ha).1, (hνb a).1]
    · show lam a + (ν a : ℝ) ≤ -bv + bv / 100
      linarith [(hnd a ha).2, (hνb a).2]
  · show h / 2 ≤ |(lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ))|
    have hg := hgap a c he
    rcases le_abs.mp hg with h1 | h1
    · exact le_abs.mpr (Or.inl (by linarith [(hνb a).1, (hνb a).2, (hνb c).1, (hνb c).2]))
    · exact le_abs.mpr (Or.inr (by linarith [(hνb a).1, (hνb a).2, (hνb c).1, (hνb c).2]))

end GlobalTheory.NumFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PositiveRankOneProportional
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem hermitian_rankOne_kernel_shape : ∀ (T W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] (l₀ La : T → W), (∀ v w, ContinuousLinearMap.adjoint ((innerSL ℂ (La v)).smulRight (l₀ w)) = (innerSL ℂ (La w)).smulRight (l₀ v)) → (∀ v ξ, (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).im = 0 ∧ 0 ≤ (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).re) → (∃ v, l₀ v ≠ 0) → ∃ c : ℝ, 0 ≤ c ∧ ∀ v, La v = (c : ℂ) • l₀ v := by
  intro T W _ _ _ l₀ La hadj hpos ⟨v₀, hv₀⟩
  set a : ℂ := ⟪La v₀, l₀ v₀⟫_ℂ with ha
  set n : ℝ := ‖l₀ v₀‖ ^ 2 with hn
  have hnpos : 0 < n := by rw [hn]; exact pow_pos (norm_pos_iff.mpr hv₀) 2
  have hnn : ⟪l₀ v₀, l₀ v₀⟫_ℂ = (n : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hn]; simp
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  obtain ⟨him, hre⟩ := hpos v₀ (l₀ v₀)
  have e : ⟪l₀ v₀, ((innerSL ℂ (La v₀)).smulRight (l₀ v₀)) (l₀ v₀)⟫_ℂ = a * (n : ℂ) := by
    rw [ContinuousLinearMap.smulRight_apply, inner_smul_right, hnn, innerSL_apply_apply]
  rw [e] at him hre
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add, sub_zero] at him hre
  have haim : a.im = 0 := (mul_eq_zero.mp him).resolve_right hnpos.ne'
  have hare : 0 ≤ a.re := nonneg_of_mul_nonneg_left hre hnpos
  have hareal : a = (a.re : ℂ) := Complex.ext (by simp) (by simp [haim])
  refine ⟨a.re / n, div_nonneg hare hnpos.le, fun v => ?_⟩
  have key : (n : ℂ) • La v = a • l₀ v := by
    apply ext_inner_right ℂ
    intro y
    have h := ContinuousLinearMap.adjoint_inner_left
      ((innerSL ℂ (La v)).smulRight (l₀ v₀)) y (l₀ v₀)
    rw [hadj v v₀, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, innerSL_apply_apply, inner_smul_right, hnn, ← ha] at h
    rw [h, inner_smul_left, Complex.conj_ofReal, mul_comm]
  have : La v = (n : ℂ)⁻¹ • ((n : ℂ) • La v) := by rw [smul_smul, inv_mul_cancel₀ hnc, one_smul]
  rw [this, key, smul_smul]
  congr 1
  rw [Complex.ofReal_div, ← hareal, div_eq_inv_mul]

end GlobalTheory
end

