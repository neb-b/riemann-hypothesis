module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLetterMulBoundedFactorMemNormalFormSpan
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem bmon_mul_mem_nfSpan_of_mem (d : Q.NFData P A) (T : Set A) (i j n : ℕ) {c : A} (hc : c ∈ bmon d)
    {x : A} (hx : x ∈ nfSpan d T i j n) : c * x ∈ nfSpan d T i j n := by
  unfold nfSpan at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, H, hHl, hH, hrest⟩ := hy
    have e : c * y = (c * b) * d.L.Di ^ i * TL.gI d.L ^ j * H.prod := by
      rw [hrest]; simp only [mul_assoc]
    rw [e]
    exact Submodule.subset_span ⟨c * b, mul_mem hc hb, H, hHl, hH, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hy

theorem nfSpan_one_mul_mem_of_letters (d : Q.NFData P A) (T : Set A) {c : A}
    (hc : ∀ X ∈ T, X * c ∈ nfSpan d T 0 0 1) {x : A} (hx : x ∈ nfSpan d T 0 0 1) :
    x * c ∈ nfSpan d T 0 0 1 := by
  unfold nfSpan at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, H, hHl, hH, hrest⟩ := hy
    rcases H with _ | ⟨h, _ | ⟨h', t⟩⟩
    · simp at hHl
    · have hhT : h ∈ T := hH h (by simp)
      have e : y * c = b * (h * c) := by
        rw [hrest]; simp [mul_assoc]
      rw [e]
      exact bmon_mul_mem_nfSpan_of_mem d T 0 0 1 hb (hc h hhT)
    · simp at hHl
  | zero => simp
  | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hy

end

theorem hats_mul_bmon_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ X ∈ hats d.L, ∀ b ∈ bmon d, X * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  intro P A _ _ _ _ d hd X hX b hb
  have key : ∀ X ∈ hats d.L, X * b ∈ nfSpan d (hats d.L) 0 0 1 := by
    clear hX X
    unfold bmon at hb
    induction hb using Submonoid.closure_induction with
    | mem b hb =>
      intro X hX
      rcases hX with ((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩
      · exact (GlobalTheory.T.Ahat_mul_and_R0_mul_mem_nfSpan_hats P A d hd b hb y).1
      · exact (GlobalTheory.T.Ahat_mul_and_R0_mul_mem_nfSpan_hats P A d hd b hb y).2
      · exact (GlobalTheory.T.Ahatv_mul_and_R0v_mul_mem_nfSpan_hats P A d hd b hb y).1
      · exact (GlobalTheory.T.Ahatv_mul_and_R0v_mul_mem_nfSpan_hats P A d hd b hb y).2
    | one =>
      intro X hX
      exact Submodule.subset_span ⟨1, one_mem _, [X], rfl, by simpa using hX, by simp⟩
    | mul b₁ b₂ _ _ h₁ h₂ =>
      intro X hX
      rw [← mul_assoc]
      exact nfSpan_one_mul_mem_of_letters d _ h₂ (h₁ X hX)
  exact key X hX

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermExpHasDeriv
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

noncomputable section

namespace GlobalTheory.TensorDualDifferential

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def hermLin {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ where
  toFun M := herm H (M *ᵥ v) w
  map_add' M N := by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add]
  map_smul' c M := by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul]

theorem herm_exp_hasDeriv {n : ℕ} (H X : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => herm H (NormedSpace.exp ((t : ℂ) • X) *ᵥ v) w) (herm H (X *ᵥ v) w) 0 := by
  have h : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 :=
    hasDerivAt_iff_tendsto_slope.2 (Formalism.REAL.tendsto_slope_exp_smul X)
  exact (((LinearMap.toContinuousLinearMap (hermLin H v w)).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt
    (0 : ℝ) h

theorem herm_skew {n : ℕ} {H X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (v w : Fin n → ℂ) :
    herm H v (X *ᵥ w) = -herm H (X *ᵥ v) w := by
  have h : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h,
    Matrix.neg_mulVec, dotProduct_neg]

theorem dOp_tensor {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (V →L[ℂ] V)} {B : Fin k → (Fin (2 * r + k + 1) → ℂ)}
    {πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))}
    (hπ : IsRepW k r z π) (hπt : IsRepW k r z πt) (hB : IsFrameOf k r [z] B)
    (h : ∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (y d))
    {X : Mx k r} (hX : InLieW k r z X) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    dOp πt X y c = dOp π X (y c) - ∑ d, hermLin (Hpk k r) (B c) (B d) X • y d := by
  have h1 := dOp_hasDeriv hπt.1 hπt.2 hX
  have h2 := dOp_hasDeriv hπ.1 hπ.2 hX
  have h3 : HasDerivAt (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) (dOp πt X y c) 0 :=
    (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin k => V) c).comp
      (ContinuousLinearMap.apply ℂ _ y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h4 : ∀ d, HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) (y d)) (dOp π X (y d)) 0 :=
    fun d => ((ContinuousLinearMap.apply ℂ V (y d)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h5 := HasDerivAt.fun_sum (u := Finset.univ) fun d _ =>
    (herm_exp_hasDeriv (Hpk k r) X (B d) (B c)).star.fun_smul (h4 d)
  have h6 : (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) = fun t : ℝ =>
      ∑ d, star (herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ B d) (B c)) •
        π (NormedSpace.exp ((t : ℂ) • X)) (y d) := funext fun t => h _ (exp_uw hX t) y c
  rw [h6] at h3
  rw [h3.unique h5, Finset.sum_add_distrib]
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, hπ.1.1, hB.2.1,
    Qx2.herm_star, herm_skew hX.1.1]
  simp [hermLin, sub_eq_add_neg]

theorem EB_tensor : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))), inWb k r z → 0 < Tz k r z → IsRepW k r z π → IsRepW k r z πt → IsFrameOf k r [z] B → (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (y d)) → ∀ a b y c, EB πt B a b y c = EB π B a b (y c) - if c = b then y a else 0 := by
  intro V _ _ _ k r z π B πt _ _ hπ hπt hB h a b y c
  have hl := frame_lie hB a b
  have e1 := dOp_tensor hπ hπt hB h hl.1 y c
  have e2 := dOp_tensor hπ hπt hB h hl.2 y c
  have e3 : ∑ d, hermLin (Hpk k r) (B c) (B d) (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) • y d +
      Complex.I • ∑ d, hermLin (Hpk k r) (B c) (B d) (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) • y d =
      if c = b then y a else 0 := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    have e4 : ∀ d, hermLin (Hpk k r) (B c) (B d) (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) • y d +
        Complex.I • hermLin (Hpk k r) (B c) (B d) (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) • y d =
        if a = d then (if c = b then y d else 0) else 0 := by
      intro d
      rw [smul_smul, ← add_smul, ← smul_eq_mul Complex.I, ← map_smul, ← map_add (f := _), LieListProducts.hsum]
      have e5 : hermLin (Hpk k r) (B c) (B d) (unitB (Hpk k r) B a b) =
          herm (Hpk k r) (B c) (B b) * herm (Hpk k r) (B a) (B d) := by
        show herm (Hpk k r) (unitB (Hpk k r) B a b *ᵥ B c) (B d) = _
        rw [Qx8.unitB_mulVec]
        simp [herm, Matrix.mulVec_smul]
      rw [e5, hB.2.1, hB.2.1]
      split_ifs <;> simp
    simp [e4]
  have e6 : EB πt B a b y c = dOp πt (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) y c +
      Complex.I • dOp πt (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) y c := rfl
  have e7 : EB π B a b (y c) = dOp π (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) (y c) +
      Complex.I • dOp π (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) (y c) := rfl
  rw [e6, e7, e1, e2, ← e3, smul_sub]
  abel

end GlobalTheory.TensorDualDifferential
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntertwinerExpOfIntertwiner
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

noncomputable section

namespace GlobalTheory

theorem intertwiner_exp_of_intertwiner {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁]
    {V₂ : Type} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂]
    (T : V₁ →ₗ[ℂ] V₂) {A₁ : V₁ →L[ℂ] V₁} {A₂ : V₂ →L[ℂ] V₂} (h : ∀ v, T (A₁ v) = A₂ (T v)) (v : V₁) :
    T (NormedSpace.exp A₁ v) = NormedSpace.exp A₂ (T v) := by
  have : CompleteSpace V₁ := FiniteDimensional.complete ℂ V₁
  have : CompleteSpace V₂ := FiniteDimensional.complete ℂ V₂
  have hp : ∀ n : ℕ, ∀ v, T ((A₁ ^ n) v) = (A₂ ^ n) (T v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih, h]
  have h1 := ((LinearMap.toContinuousLinearMap T).comp (ContinuousLinearMap.apply ℂ V₁ v)).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A₁)
  have h2 := (ContinuousLinearMap.apply ℂ V₂ (T v)).hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A₂)
  refine h1.unique (h2.congr_fun ?_)
  intro n
  show T (((n.factorial : ℂ)⁻¹) • (A₁ ^ n) v) = ((n.factorial : ℂ)⁻¹) • (A₂ ^ n) (T v)
  rw [map_smul, hp]

theorem intertwiner_dOp_of_EB {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁]
    {V₂ : Type} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π₁ : Mx k r → (V₁ →L[ℂ] V₁)} {π₂ : Mx k r → (V₂ →L[ℂ] V₂)} (T : V₁ →ₗ[ℂ] V₂)
    {B : Fin k → Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hzz : herm (Hpk k r) z z ≠ 0)
    (h₁ : IsRepW k r z π₁) (h₂ : IsRepW k r z π₂) (hB : IsFrameOf k r [z] B)
    (hT : ∀ a b v, T (EB π₁ B a b v) = EB π₂ B a b (T v)) {X : Mx k r} (hX : InLieW k r z X) :
    ∀ v, T (dOp π₁ X v) = dOp π₂ X (T v) := by
  have hE := elementary_lie_elements
  let Gd : Mx k r → Prop := fun Z => InGlW k r z Z ∧ ∀ v, T (ecOp π₁ Z v) = ecOp π₂ Z (T v)
  have gadd : ∀ Z Z', Gd Z → Gd Z' → Gd (Z + Z') := by
    intro Z Z' h h'
    have e₁ := (hE V₁ k r z π₁ h₁ Z Z' h.1 h'.1).1
    have e₂ := (hE V₂ k r z π₂ h₂ Z Z' h.1 h'.1).1
    refine ⟨e₁.1, fun v => ?_⟩
    rw [e₁.2, e₂.2, _root_.add_apply, _root_.add_apply, map_add (f := _), h.2, h'.2]
  have gsmul : ∀ (c : ℂ) Z, Gd Z → Gd (c • Z) := by
    intro c Z h
    have e₁ := (hE V₁ k r z π₁ h₁ Z Z h.1 h.1).2.1 c
    have e₂ := (hE V₂ k r z π₂ h₂ Z Z h.1 h.1).2.1 c
    refine ⟨e₁.1, fun v => ?_⟩
    rw [e₁.2, e₂.2, _root_.smul_apply, _root_.smul_apply, map_smul, h.2]
  have g0 : Gd 0 := by
    refine ⟨SkewHermitianParts.inGl_zero z, fun v => ?_⟩
    have e₁ := ((hE V₁ k r z π₁ h₁ 0 0 (SkewHermitianParts.inGl_zero z) (SkewHermitianParts.inGl_zero z)).2.1 0).2
    have e₂ := ((hE V₂ k r z π₂ h₂ 0 0 (SkewHermitianParts.inGl_zero z) (SkewHermitianParts.inGl_zero z)).2.1 0).2
    rw [zero_smul, zero_smul] at e₁ e₂
    rw [e₁, e₂]
    simp
  have gu : ∀ a b, Gd (unitB (Hpk k r) B a b) := fun a b => ⟨frame_lie hB a b, fun v => hT a b v⟩
  have hsum : Gd (∑ a, ∑ b, herm (Hpk k r) (X *ᵥ B b) (B a) • unitB (Hpk k r) B a b) :=
    Finset.sum_induction _ Gd gadd g0 fun a _ =>
      Finset.sum_induction _ Gd gadd g0 fun b _ => gsmul _ _ (gu a b)
  rw [← SkewHermitianParts.lie_expand hz hzz hB hX] at hsum
  have e₁ : ecOp π₁ X = dOp π₁ X := by
    unfold ecOp
    rw [SkewHermitianParts.hpart1_skew hX.1.1, SkewHermitianParts.hpart2_skew hX.1.1, SkewHermitianParts.dOp_zero, smul_zero, add_zero]
  have e₂ : ecOp π₂ X = dOp π₂ X := by
    unfold ecOp
    rw [SkewHermitianParts.hpart1_skew hX.1.1, SkewHermitianParts.hpart2_skew hX.1.1, SkewHermitianParts.dOp_zero, smul_zero, add_zero]
  rw [← e₁, ← e₂]
  exact hsum.2

theorem intertwiner_group_of_EB : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π₁ : Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (T : V₁ →ₗ[ℂ] V₂) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π₁ → IsRepW k r z π₂ → IsFrameOf k r [z] B → (∀ a b v, T (EB π₁ B a b v) = EB π₂ B a b (T v)) → ∀ h ∈ UWset k r z, ∀ v, T (π₁ h v) = π₂ h (T v) := by
  intro V₁ _ _ _ V₂ _ _ _ k r z π₁ π₂ T B hz hTz h₁ h₂ hB hT h hh
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    rw [Qx8.herm_self']
    intro h0
    rw [neg_eq_zero, Complex.ofReal_eq_zero] at h0
    exact hTz.ne' h0
  refine (exp_generates k r z hz hTz (fun h => h ∈ UWset k r z ∧ ∀ v, T (π₁ h v) = π₂ h (T v))
    ⟨Qx8.uw_one z, fun v => ?_⟩ ?_ h hh).2
  · rw [h₁.1.1, h₂.1.1]
    rfl
  · intro X g hX hg
    have e0 : NormedSpace.exp X ∈ UWset k r z := by
      have := exp_uw hX 1
      simpa using this
    have e₁ : π₁ (NormedSpace.exp X) = NormedSpace.exp (dOp π₁ X) := by
      have := representation_exp V₁ k r z π₁ h₁ X hX 1
      simpa using this
    have e₂ : π₂ (NormedSpace.exp X) = NormedSpace.exp (dOp π₂ X) := by
      have := representation_exp V₂ k r z π₂ h₂ X hX 1
      simpa using this
    refine ⟨SkewHermitianParts.uw_mul e0 hg.1, fun v => ?_⟩
    rw [h₁.1.2 _ e0 _ hg.1, h₂.1.2 _ e0 _ hg.1, e₁, e₂]
    show T (NormedSpace.exp (dOp π₁ X) (π₁ g v)) = NormedSpace.exp (dOp π₂ X) (π₂ g (T v))
    rw [intertwiner_exp_of_intertwiner T (intertwiner_dOp_of_EB T hz hzz h₁ h₂ hB hT hX), hg.2]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitSpecOfIsLocalRing
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FormalPoint

namespace GlobalTheory.AdicColimit


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.AdicColimit.isAdicColimit_spec_of_isLocalRing (R : Type) [CommRing R] (I : Ideal R) (A : Type) [CommRing A]
    [IsLocalRing A] (φ : R →+* A) (hA : IsAdicComplete (I.map φ) A) :
    _root_.GlobalTheory.AdicColimit.IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  have hthick : ∀ e : ℕ, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans R I e ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1) = _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e := by
    intro e
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans _root_.ReciprocityTheory.ChartRestriction.G.Out.thick
    rw [← Spec.map_comp]
    rfl
  have hPV : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ = Spec.map (CommRingCat.ofHom φ) := rfl
  have hC : ∀ e, _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) =
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) := fun e => rfl
  have hD_fst : ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1)) =
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) := by
    intro e; exact pullback.lift_fst _ _ _
  have hD_snd : ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1)) =
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans R I e := by
    intro e
    exact pullback.lift_snd _ _ _
  have hcond : ∀ e, pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫
      Spec.map (CommRingCat.ofHom φ) =
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e :=
    fun e => pullback.condition
  have hq : ∀ e, _root_.GlobalTheory.FormalPoint.levelMap I φ e ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e =
      _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1) ≫ Spec.map (CommRingCat.ofHom φ) := fun e => by
    rw [_root_.GlobalTheory.FormalPoint.levelMap_thick, hPV]
  obtain ⟨s, hs_fst, hs_snd⟩ : ∃ s : ∀ e : ℕ, Spec (CommRingCat.of (A ⧸ I.map φ ^ (e + 1))) ⟶
      pullback (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e),
      (∀ e, s e ≫ pullback.fst _ _ = _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1)) ∧
      (∀ e, s e ≫ pullback.snd _ _ = _root_.GlobalTheory.FormalPoint.levelMap I φ e) :=
    ⟨fun e => pullback.lift _ _ (hq e).symm, fun e => pullback.lift_fst _ _ _,
      fun e => pullback.lift_snd _ _ _⟩
  have hsec : ∀ e, ∃ l, l ≫ s e = 𝟙 _ := by
    intro e
    obtain ⟨l, hl⟩ := _root_.GlobalTheory.FormalPoint.exists_factor_level I φ
      (pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e))
      (pullback.snd _ _) (by rw [hPV]; exact hcond e)
    refine ⟨l, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hs_fst, Category.id_comp, hl]
    · rw [← cancel_mono (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e), Category.assoc, Category.assoc, ← Category.assoc (s e), hs_snd, hq,
        ← Category.assoc, hl, Category.id_comp, hcond]
  intro X f hf
  have hfam : _root_.GlobalTheory.IsAdicFamily (I.map φ) (fun e => s e ≫ f e) := by
    intro n
    have hmap : _root_.GlobalTheory.adicLevelMap (I.map φ) (by omega : n + 1 ≤ n + 1 + 1) ≫ s (n + 1) =
        s n ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I n (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
      apply pullback.hom_ext
      · rw [Category.assoc, hs_fst, _root_.GlobalTheory.adicLevelMap_ι, Category.assoc, hD_fst, hs_fst]
      · rw [← cancel_mono (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (n + 1))]
        simp only [Category.assoc]
        rw [← Category.assoc (s (n + 1)), hs_snd, hq, _root_.GlobalTheory.adicLevelMap_ι_assoc, ← Category.assoc (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I n (Over.mk (Spec.map (CommRingCat.ofHom φ)))), hD_snd,
          Category.assoc, hthick, ← Category.assoc, hs_snd, hq]
    show _root_.GlobalTheory.adicLevelMap (I.map φ) _ ≫ s (n + 1) ≫ f (n + 1) = s n ≫ f n
    rw [← Category.assoc, hmap, Category.assoc, hf]
  haveI := hA
  obtain ⟨g, hg, hgu⟩ := _root_.GlobalTheory.existsUnique_of_isAdicFamily hfam
  have key : ∀ y : Spec (CommRingCat.of A) ⟶ X,
      (∀ e, _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫ y = f e) ↔
      (∀ n, _root_.GlobalTheory.adicLevelι (I.map φ) (n + 1) ≫ y = s n ≫ f n) := by
    intro y
    constructor
    · intro hy n
      rw [← hs_fst, Category.assoc, ← hC, hy]
    · intro hy e
      obtain ⟨l, hl⟩ := hsec e
      have h1 : _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) =
          l ≫ _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1) := by
        rw [← hs_fst, ← Category.assoc, hl, Category.id_comp, hC]
      rw [h1, Category.assoc, hy, ← Category.assoc, hl]
      exact Category.id_comp _
  exact ⟨g, (key g).2 hg, fun y hy => hgu y ((key y).1 hy)⟩

end GlobalTheory.AdicColimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.KerJetAugEqSpanTorusUnionQuotient
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace JetGenerators

theorem exists_tangent {k A : Type} [Field k] [CommRing A] [Algebra k A] (aug : A →ₐ[k] k)
    {I : Ideal A} {n : ℕ} (hJ : (RingHom.ker aug) ^ (n + 1) = ⊥) (hI : I ≤ RingHom.ker aug)
    (hne : ¬ RingHom.ker aug ≤ I) :
    ∃ φ : A →ₐ[k] DualNumber k, (TrivSqZeroExt.fstHom k k k).comp φ = aug ∧ (∀ a ∈ I, φ a = 0) ∧
      ∃ a ∈ RingHom.ker aug, φ a ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.NotLeSqSup.main
  | exact _root_.GlobalTheory.NotLeSqSup.main
  | (apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NotLeSqSup.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NotLeSqSup.main ..)

theorem spMap_jetAug {k : Type} [CommRing k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G] {d : ℕ}
    {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin d) m) ⟶ G} (hx : Chart.IsUnivChart G d x)
    (n : ℕ) {A : Type} [CommRing A] [Algebra k A] :
    Chart.spMap ((Algebra.ofId k A).comp (Chart.jetAug k (Fin d) n)) ≫ x n = 1 := by
  have : (Algebra.ofId k A).comp (Chart.jetAug k (Fin d) n) =
      ((Algebra.ofId k A).comp (Chart.jetAug k (Fin d) 0)).comp (Chart.jetZeroR k (Fin d) n) := by
    apply Chart.jet_ext
    intro j
    rfl
  rw [this, ← Chart.spMap_comp, Category.assoc, hx.2.1 n, MonObj.comp_one]

theorem eq_one_of_basis {S : Scheme.{0}} {X : Type} [AddCommGroup X] {κ : Type}
    (b : Module.Basis κ ℤ X) {Z : Over S} (y : Z ⟶ splitTorus S X)
    (h : ∀ j, y.left.appTop.hom (charUnit S X (b j)).val = 1) : y = 1 := by
  obtain ⟨e, he⟩ := exists_splitTorus_points_mulEquiv S X Z
  apply e.injective
  rw [map_one]
  have h1 : (MonoidHom.toAdditiveRight (e y)).toIntLinearMap = 0 := by
    apply b.ext
    intro j
    change Additive.ofMul (e y (Multiplicative.ofAdd (b j))) = Additive.ofMul 1
    congr 1
    exact Units.ext ((he y (b j)).trans (h j))
  refine MonoidHom.ext fun χ => ?_
  exact congrArg Additive.toMul (LinearMap.congr_fun h1 χ.toAdd)

end JetGenerators

theorem ker_jetAug_eq_span_torus_union_quotient :
    ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] (r : ℕ) (b : Module.Basis (Fin r) ℤ X) (G B : Over (Spec (CommRingCat.of k))) [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G), IsMonHom q → IsMonHom i → IsPullback i (toUnit _) q η[B] → ∀ (d g n : ℕ) (x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin d) m) ⟶ G) (xB : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin g) m) ⟶ B), Chart.IsUnivChart G d x → Chart.IsUnivChart B g xB → ∀ (ψ : (Chart.JetR k (Fin g) n) →ₐ[k] (Chart.JetR k (Fin d) n)), x n ≫ q = Chart.spMap ψ ≫ xB n → ∀ T : Fin r → (Chart.JetR k (Fin d) n), (∀ j, Chart.jetAug k (Fin d) n (T j) = 0) → (∀ (φ : (Chart.JetR k (Fin d) n) →ₐ[k] DualNumber k) (y : Chart.sp (R₀ := k) (DualNumber k) ⟶ splitTorus (Spec (CommRingCat.of k)) X), Chart.spMap φ ≫ x n = y ≫ i → ∀ j, (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom (1 + φ (T j)) = y.left.appTop.hom (charUnit (Spec (CommRingCat.of k)) X (b j)).val) → RingHom.ker (Chart.jetAug k (Fin d) n) = Ideal.span (Set.range T ∪ Set.range fun l => ψ (Chart.zR n l)) := by
  intro k _ X _ r b G B _ _ q i hq hi hpb d g n x xB hx hxB ψ hψ T hT hchar
  have hI : Ideal.span (Set.range T ∪ Set.range fun l => ψ (Chart.zR n l)) ≤
      RingHom.ker (Chart.jetAug k (Fin d) n) := by
    rw [Ideal.span_le]
    rintro _ (⟨j, rfl⟩ | ⟨l, rfl⟩)
    · exact hT j
    · have hz : IsNilpotent (Chart.zR (R := k) n l) := ⟨n + 1, by
        have := Ideal.pow_mem_pow (Chart.zR_mem_ker (R := k) n l) (n + 1)
        rwa [Chart.ker_jetAug_pow, Ideal.mem_bot] at this⟩
      exact ((hz.map ψ).map (Chart.jetAug k (Fin d) n)).eq_zero
  refine le_antisymm ?_ hI
  by_contra hne
  obtain ⟨φ, hφ1, hφ2, a, haJ, ha⟩ :=
    JetGenerators.exists_tangent _ (Chart.ker_jetAug_pow (R := k) (Fin d) n) hI hne
  have hn : n ≠ 0 := by
    rintro rfl
    have : RingHom.ker (Chart.jetAug k (Fin d) 0) = ⊥ :=
      (pow_one _).symm.trans (Chart.ker_jetAug_pow (R := k) (Fin d) 0)
    exact hne (this ▸ bot_le)
  have hφψ : φ.comp ψ = (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin g) n) := by
    apply Chart.jet_ext
    intro l
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Chart.jetAug_zR, map_zero]
    exact hφ2 _ (Ideal.subset_span (Or.inr ⟨l, rfl⟩))
  have hq1 : (Chart.spMap φ ≫ x n) ≫ q = toUnit _ ≫ η[B] := by
    rw [Category.assoc, hψ, ← Category.assoc, Chart.spMap_comp, hφψ, JetGenerators.spMap_jetAug hxB]
    rfl
  have hy := (hpb.lift_fst _ _ hq1).symm
  have hy1 : hpb.lift _ _ hq1 = 1 := by
    apply JetGenerators.eq_one_of_basis b
    intro j
    rw [← hchar φ _ hy j, hφ2 _ (Ideal.subset_span (Or.inl ⟨j, rfl⟩)), add_zero, map_one]
  rw [hy1, MonObj.one_comp] at hy
  have hker : (RingHom.ker (TrivSqZeroExt.fstHom k k k)) ^ (n + 1) = ⊥ := by
    rw [← le_bot_iff]
    refine (Ideal.pow_le_pow_right (show 2 ≤ n + 1 by omega)).trans ?_
    rw [pow_two, Ideal.mul_le]
    intro u hu v hv
    have hu' : u.fst = 0 := hu
    have hv' : v.fst = 0 := hv
    rw [Ideal.mem_bot]
    ext <;> simp [hu', hv']
  have huniq := (hx.2.2 (DualNumber k) (TrivSqZeroExt.fstHom k k k) n hker 1
    (MonObj.comp_one _)).unique (y₁ := φ)
    (y₂ := (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin d) n)) ⟨hφ1, hy.symm⟩
    ⟨by ext1 z; simp, (JetGenerators.spMap_jetAug hx n).symm⟩
  apply ha
  have h0 : Chart.jetAug k (Fin d) n a = 0 := haJ
  rw [huniq, AlgHom.comp_apply, h0, map_zero]

end GlobalTheory
end

