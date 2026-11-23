module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledThetaTestFunctionSesquilinearHeisenberg
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianHeisenbergOperatorLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionSpec

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledGaussianKernelDiagonalTranslationInvarian
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.Diag

open GlobalTheory.SW.DblLin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)


variable (X) in
noncomputable def kRow (x₁ x₂ : Frame X.Ψ r) (z w : Fin g → ℂ) : ℂ :=
  ∑ τ, cz' X idx x₁ x₂ τ (z, w) ⬝ᵥ (imH (dblZ X x₁ x₂ τ))⁻¹ *ᵥ cz X idx x₁ x₂ τ (z, w)

theorem kZero_eq (x₁ x₂ : Frame X.Ψ r) (z w : Fin n → Fin g → ℂ) :
    kZero X idx x₁ x₂ z w =
      (∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹) *
        cexp (π * ∑ k, kRow X idx x₁ x₂ (z k) (w k)) := by
  simp only [kZero, Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.mul_sum, kRow]
  rw [Finset.sum_comm]
  rfl

theorem kRow_per (hs : IsSympl X bas) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom)
    (y : Fin r → E) (z z' : Fin g → ℂ) :
    kRow X idx x₁ x₂ (pv X idx x₁ y + z) (fun i => conj ((pv X idx x₂ y + z') i)) =
      hx X bas idx x₁ (z + (1 / 2 : ℂ) • pv X idx x₁ y) (pv X idx x₁ y) +
      conj (hx X bas idx x₂ (z' + (1 / 2 : ℂ) • pv X idx x₂ y) (pv X idx x₂ y)) +
      kRow X idx x₁ x₂ z (fun i => conj (z' i)) := by
  have h := expo_row idx hs h₁ h₂ y y z (star z')
  have e0 : ∀ τ : X.Ψ, Data.emb τ.1 (0 : Fin r → E) = 0 := fun τ => by
    funext a; simp [Data.emb]
  have e1 : (fun i => conj ((pv X idx x₂ y + z') i)) = star z' + star (per X x₂ y ∘ idx) := by
    funext i; simp [pv, add_comm]
  rw [e1, add_comm (pv X idx x₁ y) z]
  simp only [sub_self, e0, star_zero, zero_dotProduct, dotProduct_zero, add_zero,
    Finset.sum_const_zero, mul_zero, Pi.zero_apply, star_star, hermForm_Hm] at h
  simp only [cc, map_zero, mul_zero, Finset.sum_const_zero, Rat.cast_zero, add_zero] at h
  exact h

theorem continuous_kRow (x₁ x₂ : Frame X.Ψ r) :
    Continuous fun p : (Fin g → ℂ) × (Fin g → ℂ) => kRow X idx x₁ x₂ p.1 p.2 := by
  refine continuous_finsetSum _ fun τ _ => ?_
  exact (cz' X idx x₁ x₂ τ).continuous_of_finiteDimensional.dotProduct
    (continuous_const.matrix_mulVec (cz X idx x₁ x₂ τ).continuous_of_finiteDimensional)

theorem continuous_hx (x : Frame X.Ψ r) :
    Continuous fun z : Fin g → ℂ => hx X bas idx x z z :=
  (continuous_const.matrix_mulVec continuous_id).dotProduct
    (continuous_const.matrix_mulVec (continuous_const.matrix_mulVec continuous_id).star)

theorem kernel_diag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ a b w : WR X n, cexp (π * I * (EFR X w (a - b) : ℝ)) * (gaussR X bas idx x₁ (zR X idx x₁ (w + a)) * conj (gaussR X bas idx x₂ (zR X idx x₂ (w + b))) * kZero X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i))) = gaussR X bas idx x₁ (zR X idx x₁ a) * conj (gaussR X bas idx x₂ (zR X idx x₂ b)) * kZero X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i)) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn x₁ h₁ x₂ h₂ a b w
  obtain ⟨⟨L₁, hL₁⟩, im₁, -, hd, -⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x₁ h₁
  obtain ⟨⟨L₂, hL₂⟩, im₂, -⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x₂ h₂
  have add₁ (u v : WR X n) : zR X idx x₁ (u + v) = zR X idx x₁ u + zR X idx x₁ v := by
    rw [← hL₁, ← hL₁, ← hL₁, map_add (f := _)]
  have add₂ (u v : WR X n) : zR X idx x₂ (u + v) = zR X idx x₂ u + zR X idx x₂ v := by
    rw [← hL₂, ← hL₂, ← hL₂, map_add (f := _)]
  have hE (w : WR X n) : EFR X w (a - b) = EFR X w a - EFR X w b := by
    rw [← im₁, ← im₁, ← im₁, ← sub_im, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eq_sub_iff_add_eq, ← GlobalTheory.Dict.fock_hx_add_right, ← Pi.add_apply (zR X idx x₁ (a - b)),
      ← add₁, sub_add_cancel]
  have key : ∀ w : WR X n, π * I * (EFR X w (a - b) : ℝ) +
      (-(π / 2 * ∑ k, hx X bas idx x₁ (zR X idx x₁ (w + a) k) (zR X idx x₁ (w + a) k)) +
        conj (-(π / 2 * ∑ k, hx X bas idx x₂ (zR X idx x₂ (w + b) k) (zR X idx x₂ (w + b) k))) +
        π * ∑ k, kRow X idx x₁ x₂ (zR X idx x₁ (w + a) k) (fun i => conj (zR X idx x₂ (w + b) k i))) =
      -(π / 2 * ∑ k, hx X bas idx x₁ (zR X idx x₁ a k) (zR X idx x₁ a k)) +
        conj (-(π / 2 * ∑ k, hx X bas idx x₂ (zR X idx x₂ b k) (zR X idx x₂ b k))) +
        π * ∑ k, kRow X idx x₁ x₂ (zR X idx x₁ a k) (fun i => conj (zR X idx x₂ b k i)) := by
    intro w
    refine hd.induction_on w (isClosed_eq ?_ continuous_const) fun y => ?_
    · have c₁ (k) : Continuous fun w : WR X n => zR X idx x₁ (w + a) k := by
        simp only [← hL₁]; fun_prop
      have c₂ (k) : Continuous fun w : WR X n => zR X idx x₂ (w + b) k := by
        simp only [← hL₂]; fun_prop
      have c₃ : Continuous fun w : WR X n => EFR X w (a - b) := by
        unfold EFR hermC; fun_prop
      have c₄ := continuous_finsetSum Finset.univ fun k _ =>
        (continuous_hx (bas := bas) idx x₁).comp (c₁ k)
      have c₅ := continuous_finsetSum Finset.univ fun k _ =>
        (continuous_hx (bas := bas) idx x₂).comp (c₂ k)
      have c₆ := continuous_finsetSum Finset.univ fun k _ =>
        (continuous_kRow idx x₁ x₂).comp ((c₁ k).prodMk (c₂ k).star)
      exact (continuous_const.mul (continuous_ofReal.comp c₃)).add
        (((continuous_const.mul c₄).neg.add
          (continuous_conj.comp (continuous_const.mul c₅).neg)).add (continuous_const.mul c₆))
    · have i₁ := sub_conj (∑ k, hx X bas idx x₁ (zR X idx x₁ (embR X y) k) (zR X idx x₁ a k))
      have i₂ := sub_conj (∑ k, hx X bas idx x₂ (zR X idx x₂ (embR X y) k) (zR X idx x₂ b k))
      rw [im₁] at i₁
      rw [im₂] at i₂
      rw [hE, add₁, add₂]
      simp only [Pi.add_apply (zR X idx _ (embR X y)), zR_embR] at i₁ i₂ ⊢
      simp only [kRow_per idx hs h₁ h₂]
      have s₁ (k) := GlobalTheory.Dict.fock_hx_conj X bas idx x₁ hs h₁ (pv X idx x₁ (y k)) (zR X idx x₁ a k)
      have s₂ (k) := GlobalTheory.Dict.fock_hx_conj X bas idx x₂ hs h₂ (pv X idx x₂ (y k)) (zR X idx x₂ b k)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [GlobalTheory.Dict.fock_hx_add_left, GlobalTheory.Dict.fock_hx_add_right, GlobalTheory.Dict.fock_hx_smul_left,
        s₁, s₂, Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum, map_add, map_mul, map_neg,
        conj_conj, map_div₀, conj_ofReal, map_ofNat, map_one]
      push_cast at i₁ i₂ ⊢
      linear_combination (-(π : ℂ) / 2) * i₁ + ((π : ℂ) / 2) * i₂
  simp only [gaussR, kZero_eq, ← Complex.exp_conj]
  have := congrArg cexp (key w)
  simp only [Complex.exp_add] at this
  linear_combination (∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹) * this

end GlobalTheory.Ker.Diag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilDoubledTestFunctionZeroEqZero
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

namespace DblVan

theorem vecMul_inv_inl {E : Type} [Field E] {N : ℕ} {γ : M2 E N} (hγ : IsUnit γ.det)
    {u : Fin N ⊕ Fin N → E} (hu : u ∈ botSpan γ) (a : Fin N) : (u ᵥ* γ⁻¹) (Sum.inl a) = 0 := by
  change u ∈ Submodule.span E (Set.range fun b : Fin N => γ (Sum.inr b)) at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx

    have hrow : (γ (Sum.inr b) ᵥ* γ⁻¹) (Sum.inl a) = (γ * γ⁻¹) (Sum.inr b) (Sum.inl a) := rfl
    rw [hrow, Matrix.mul_nonsing_inv γ hγ, Matrix.one_apply_ne (by simp)]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_vecMul, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [Matrix.smul_vecMul, Pi.smul_apply, hx, smul_zero]

theorem heisH_zero_apply_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
    (b : Matrix (Fin n) (Fin N) E) (ψ : Matrix (Fin n) (Fin N) E → ℂ) : heisH 0 b ψ 0 = ψ 0 := by
  simp [heisH, cc]

theorem toCols_eq_zero {E : Type} [Field E] {n N : ℕ} {γ T : M2 E N} (hγ : IsUnit γ.det)
    {ξ : Fin N → E} (hu : Sum.elim ξ 0 ᵥ* T ∈ botSpan γ) (v : Fin n → E) :
    (Matrix.fromCols (vecMulVec v ξ) (0 : Matrix (Fin n) (Fin N) E) * T * γ⁻¹).toCols₁ = 0 := by
  ext k a
  rw [Matrix.toCols₁_apply, Matrix.zero_apply]

  have hrow : (Matrix.fromCols (vecMulVec v ξ) (0 : Matrix (Fin n) (Fin N) E) * T) k =
      v k • (Sum.elim ξ 0 ᵥ* T) := by
    ext j
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, vecMulVec_apply,
      Finset.mul_sum, mul_assoc]
  have hentry : (Matrix.fromCols (vecMulVec v ξ) (0 : Matrix (Fin n) (Fin N) E) * T * γ⁻¹) k
      (Sum.inl a) = ((v k • (Sum.elim ξ 0 ᵥ* T)) ᵥ* γ⁻¹) (Sum.inl a) := by
    rw [← hrow]; rfl
  rw [hentry]
  exact vecMul_inv_inl hγ (Submodule.smul_mem _ _ hu) a

end DblVan


open DblVan in
theorem weil_dbl_zero_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ ξ : Fin r → E, (∃ (s : Finset (Fin n → E)) (a : (Fin n → E) → ℂ), ∑ v ∈ s, a v ≠ 0 ∧ ∑ v ∈ s, a v • heisG X bas (vecMulVec v ξ) φ₁ = 0) → ∀ γ ∈ UU E r, Sum.elim ξ 0 ᵥ* dblT X ∈ botSpan γ → weil X.Ψ γ (dbl X bas idx φ₁ φ₂) 0 = 0 := by
  intro E _ _ _ r X g bas idx n hs hn φ₁ φ₂ h₁ h₂ ξ hker γ hγ hξ
  obtain ⟨s, a, hsum, hkill⟩ := hker
  have hΨ : IsType X.Ψ := X.cmType
  have hγu : IsUnit γ.det := (HAct.group_part hγ).1

  have hSBd : ∀ ψ : TF n g, IsSB ψ → IsSB (dbl X bas idx ψ φ₂) := fun ψ hψ =>
    (_root_.GlobalTheory.SW.DblEx.dbl_spec E r X g bas idx n hs hn ψ φ₂ hψ h₂).1
  have hΦ := hSBd φ₁ h₁
  have hG := (heisG_laws E r X g bas idx n hs hn).2.2.2
  have hwadd : ∀ f f' : Matrix (Fin n) (Fin r) E → ℂ, IsSB f → IsSB f' →
      weil X.Ψ γ (f + f') = weil X.Ψ γ f + weil X.Ψ γ f' := fun f f' hf hf' =>
    ((_root_.GlobalTheory.SW.weil_action E X.Ψ hΨ n r hn γ hγ f hf).2.2.2.1 f' hf').2
  have hwsmul : ∀ (c : ℂ) (f : Matrix (Fin n) (Fin r) E → ℂ), IsSB f →
      weil X.Ψ γ (c • f) = c • weil X.Ψ γ f := fun c f hf =>
    (_root_.GlobalTheory.SW.weil_action E X.Ψ hΨ n r hn γ hγ f hf).2.2.2.2.1 c

  have hdbl0 : dbl X bas idx (0 : TF n g) φ₂ = 0 := by
    have h := (_root_.GlobalTheory.SW.DblLin.dbl_lin E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂).2.1 0 1
    rwa [zero_smul, one_smul, zero_mul, zero_smul] at h
  have hw0 : weil X.Ψ γ (0 : Matrix (Fin n) (Fin r) E → ℂ) = 0 := by
    have h := hwsmul 0 _ hΦ
    rwa [zero_smul, zero_smul] at h

  have hone : ∀ v : Fin n → E, weil X.Ψ γ (dbl X bas idx (heisG X bas (vecMulVec v ξ) φ₁) φ₂) 0 =
      weil X.Ψ γ (dbl X bas idx φ₁ φ₂) 0 := by
    intro v
    have h3 := (_root_.GlobalTheory.SW.DblLin.dbl_lin E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂).2.2 (vecMulVec v ξ) 0
    rw [(hG 0 φ₂ h₂).2.1] at h3
    rw [h3, (_root_.GlobalTheory.SW.heisH_laws E X.Ψ hΨ n r hn _ _ _ hΦ).2.2 γ hγ, Matrix.fromCols_toCols,
      DblVan.toCols_eq_zero hγu hξ v, DblVan.heisH_zero_apply_zero]

  have hlin : ∀ t : Finset (Fin n → E),
      IsSB (∑ v ∈ t, a v • heisG X bas (vecMulVec v ξ) φ₁) ∧
      weil X.Ψ γ (dbl X bas idx (∑ v ∈ t, a v • heisG X bas (vecMulVec v ξ) φ₁) φ₂) =
        ∑ v ∈ t, a v • weil X.Ψ γ (dbl X bas idx (heisG X bas (vecMulVec v ξ) φ₁) φ₂) := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨isSB_zero, by rw [Finset.sum_empty, Finset.sum_empty, hdbl0, hw0]⟩
    | insert w t hw ih =>
      obtain ⟨hS, hval⟩ := ih
      have hGw := (hG (vecMulVec w ξ) φ₁ h₁).1
      have hcGw := (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) _ _ hGw hGw).2.1 (a w)
      rw [Finset.sum_insert hw, Finset.sum_insert hw]
      refine ⟨(isSB_algebra_haar_linear ℚ (Fin n) (Fin g) _ _ hcGw hS).1, ?_⟩
      have hI := _root_.GlobalTheory.SW.DblLin.dbl_lin E r X g bas idx n hs hn _ φ₂ hcGw h₂
      have hJ := _root_.GlobalTheory.SW.DblLin.dbl_lin E r X g bas idx n hs hn _ φ₂ hGw h₂
      have hsm : dbl X bas idx (a w • heisG X bas (vecMulVec w ξ) φ₁) φ₂ =
          a w • dbl X bas idx (heisG X bas (vecMulVec w ξ) φ₁) φ₂ := by
        have h := hJ.2.1 (a w) 1
        rwa [one_smul, map_one, mul_one] at h
      rw [(hI.1 _ hS).1, hwadd _ _ (hSBd _ hcGw) (hSBd _ hS), hval, hsm,
        hwsmul _ _ (hSBd _ hGw)]

  have hmain := (hlin s).2
  rw [hkill, hdbl0, hw0] at hmain
  have h0 := congrFun hmain 0
  simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hone,
    ← Finset.sum_mul] at h0
  exact (mul_eq_zero.mp h0.symm).resolve_left hsum

end GlobalTheory.SW
end

