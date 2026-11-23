module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CosetRepresentativeTraceFixedProperties
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem cosetTrace_fixed_props : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)], ∀ z ∈ Fix L N, (∀ g : G, g • cosetTrace N z = cosetTrace N z) ∧ (v z ≤ 1 → v (cosetTrace N z) ≤ 1) ∧ ∀ e : L, (∀ g : G, g • e = e) → cosetTrace N (e * z) = e * cosetTrace N z := by
  intro L _ v G _ _ hv N _ z hz
  have hfix : ∀ n : G, n ∈ N → n • z = z := fun n hn => hz ⟨n, hn⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g
    unfold cosetTrace
    rw [Finset.smul_sum]
    have key : ∀ q : G ⧸ N, g • q.out • z = (g • q).out • z := by
      intro q
      have h1 : (QuotientGroup.mk (g * q.out) : G ⧸ N) = g • q := by
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have h2 : ((g • q).out)⁻¹ * (g * q.out) ∈ N := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', h1]
      have h3 : g * q.out = (g • q).out * (((g • q).out)⁻¹ * (g * q.out)) := by group
      rw [smul_smul, h3, mul_smul, hfix _ h2]
    simp_rw [key]
    exact Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ N => q.out • z)
  · intro hz1
    unfold cosetTrace
    apply Valuation.map_sum_le
    intro q _
    rw [hv]; exact hz1
  · intro e he
    unfold cosetTrace
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [smul_mul', he]

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormGamma1InterGamma0SlashRatIsZeroAt
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.Hk

private theorem finiteIndex_lev_of_pos' (N l : ℕ) (hN : 0 < N) (hl : 0 < l) : (lev N l).FiniteIndex := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  unfold lev
  infer_instance

private theorem isCusp_SL2Z_ratGL_smul' (g : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  exact ⟨g • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

theorem cuspForm_slash_rat_isZeroAt : ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l →
    0 < (g.det : ℚ) → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ,
    IsCusp c (GlobalTheory.Hk.lev N l) →
    c.IsZeroAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  intro N l k g hN hl _ f c hc
  haveI := finiteIndex_lev_of_pos' N l hN hl
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [← OnePoint.IsZeroAt.smul_iff]
  have h := isCusp_SL2Z_ratGL_smul' g hc
  rw [← Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z ((GlobalTheory.Hk.lev N l : Subgroup SL(2, ℤ)) :
    Subgroup (GL (Fin 2) ℝ))] at h
  exact f.zero_at_cusps' h

end GlobalTheory.Hk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormSlashHoloDecay
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane Filter Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm
open scoped Manifold Pointwise

namespace GlobalTheory.HeckeFamilyMatrices

theorem cuspForm_norm_le_exp_of_one_le_im (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] (k : ℤ)
    (g : CuspForm G k) :
    ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖g τ‖ ≤ C * Real.exp (-c * τ.im) := by
  obtain ⟨c, hc, hd⟩ := CuspFormClass.exp_decay_atImInfty' (Γ := G) (k := k) g
  obtain ⟨C₀, hC₀⟩ := CuspFormClass.petersson_bounded_left k G g g
  obtain ⟨D, hD, h⟩ := hd.exists_pos
  rw [Asymptotics.isBigOWith_iff, atImInfty, eventually_comap, eventually_atTop] at h
  obtain ⟨y, hy⟩ := h
  have hC₀0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ UpperHalfPlane.I)
  set M : ℝ := 1 + C₀ * |y| ^ k.natAbs with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨max D (M * Real.exp (c * |y|)), c, hc, fun τ hτ => ?_⟩
  rcases le_total y τ.im with h1 | h1
  · have h2 := hy _ h1 τ rfl
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h2
    exact h2.trans (by gcongr; exact le_max_left _ _)
  · have hy' : τ.im ≤ |y| := h1.trans (le_abs_self y)
    have hp : ‖g τ‖ ^ 2 * τ.im ^ k ≤ C₀ := by
      have := hC₀ τ
      simp only [UpperHalfPlane.petersson, norm_mul, Complex.norm_conj, norm_zpow,
        Complex.norm_real, Real.norm_of_nonneg τ.im_pos.le] at this
      calc _ = ‖g τ‖ * ‖g τ‖ * τ.im ^ k := by ring
        _ ≤ C₀ := this
    have hpos := τ.im_pos
    have hk : 1 ≤ τ.im ^ k * τ.im ^ k.natAbs := by
      rw [← zpow_natCast, ← zpow_add₀ hpos.ne']
      exact one_le_zpow₀ hτ (by omega)
    have h4 : ‖g τ‖ ^ 2 ≤ C₀ * |y| ^ k.natAbs :=
      calc ‖g τ‖ ^ 2 ≤ ‖g τ‖ ^ 2 * (τ.im ^ k * τ.im ^ k.natAbs) :=
            le_mul_of_one_le_right (by positivity) hk
        _ = ‖g τ‖ ^ 2 * τ.im ^ k * τ.im ^ k.natAbs := by ring
        _ ≤ C₀ * |y| ^ k.natAbs := by gcongr
    have h5 : ‖g τ‖ ≤ M := by nlinarith [sq_nonneg (‖g τ‖ - 1), norm_nonneg (g τ)]
    have h3 : 1 ≤ Real.exp (c * |y|) * Real.exp (-c * τ.im) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    calc ‖g τ‖ ≤ M := h5
      _ ≤ M * (Real.exp (c * |y|) * Real.exp (-c * τ.im)) := le_mul_of_one_le_right hM0 h3
      _ = M * Real.exp (c * |y|) * Real.exp (-c * τ.im) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem cuspForm_slash_holo_decay : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℤ), Γ.FiniteIndex →
    ∀ (f : CuspForm Γ k) (σ : SL(2, ℤ)), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[k] σ) ∧
      ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖(⇑f ∣[k] σ) τ‖ ≤ C * Real.exp (-c * τ.im) := by
  intro Γ k hΓ f σ
  have : ((ConjAct.toConjAct (σ : GL (Fin 2) ℝ)⁻¹) • (Γ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj (Γ : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ σ)⁻¹
  exact ⟨(CuspForm.translate f (σ : GL (Fin 2) ℝ)).holo',
    cuspForm_norm_le_exp_of_one_le_im _ k (CuspForm.translate f (σ : GL (Fin 2) ℝ))⟩

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeformMultipleZerosLinearFamily
section
open Polynomial

set_option linter.deprecated false

namespace GlobalTheory.DeformZeros

variable {k J I : Type} [Field k] [Fintype J] [Fintype I]

noncomputable def sys (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k)
    (x : J ⊕ I → PowerSeries k) : Option (I × Fin N) → PowerSeries k
  | none => ∑ j, x (Sum.inl j) * ξ j
  | some (i, l) => ∑ j, x (Sum.inl j) *
      (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst (x (Sum.inr i)) : PowerSeries k)

noncomputable def linFun (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k)
    (v : J ⊕ I → k) : Option (I × Fin N) → k
  | none => ∑ j, v (Sum.inl j) * PowerSeries.constantCoeff (ξ j)
  | some (i, l) => ∑ j, v (Sum.inl j) *
        PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
      + v (Sum.inr i) * ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j))

noncomputable def lin (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k) :
    (J ⊕ I → k) →ₗ[k] (Option (I × Fin N) → k) where
  toFun := linFun N ξ s y₀
  map_add' v w := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, add_mul, Finset.sum_add_distrib] <;> ring
  map_smul' c v := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, Finset.mul_sum, mul_assoc, mul_add]

lemma iter_eq (f : PowerSeries k) (l : ℕ) :
    (PowerSeries.derivativeFun)^[l] f = (PowerSeries.derivative (R := k))^[l] f := by
  induction l generalizing f with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]; rfl

lemma cc_subst (φ a : PowerSeries k) (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ :=
  (_root_.GlobalTheory.taylor_subst_first_order k φ a 0 1 le_rfl ha).1

end GlobalTheory.DeformZeros

namespace GlobalTheory.DeformZeros

variable {k : Type} [Field k]

lemma dvd_step {m : ℕ} (hm : 1 ≤ m) (y g S S' : PowerSeries k) (y0 c A : k)
    (hy : PowerSeries.constantCoeff y = y0) (hS : PowerSeries.constantCoeff S = A)
    (hT : (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      S' - S - PowerSeries.X ^ m * PowerSeries.C c) :
    (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      (y + PowerSeries.X ^ m * g) * S' - y * S
        - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff g * A + y0 * c) := by
  obtain ⟨r, hr⟩ := hT
  have hS' : S' = S + PowerSeries.X ^ m * PowerSeries.C c + PowerSeries.X ^ (m + 1) * r := by
    linear_combination hr
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have heq : (y + PowerSeries.X ^ (n + 1) * g) * S' - y * S
      - PowerSeries.X ^ (n + 1) * PowerSeries.C (PowerSeries.constantCoeff g * A + y0 * c)
      = PowerSeries.X ^ (n + 1) * (y * PowerSeries.C c - PowerSeries.C (y0 * c)
          + (g * S - PowerSeries.C (PowerSeries.constantCoeff g * A)))
        + PowerSeries.X ^ (n + 1 + 1) * (y * r + PowerSeries.X ^ n *
          (g * PowerSeries.C c + PowerSeries.X * g * r)) := by
    rw [hS', map_add (f := _)]; ring
  rw [heq]
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [pow_succ]
  refine mul_dvd_mul_left _ ?_
  rw [PowerSeries.X_dvd_iff]
  simp [hy, hS]

end GlobalTheory.DeformZeros

namespace GlobalTheory.DeformZeros

theorem deform : ∀ (k J I : Type) [Field k] [CharZero k] [Fintype J] [Fintype I] (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k), 1 ≤ N →
 ∑ j, y₀ j * PowerSeries.constantCoeff (ξ j) = 0 →
 (∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (s i j) = 0) → (∀ i, ∑ j, y₀ j * PowerSeries.coeff N (s i j) ≠ 0) →
 (∀ (e₀ : k) (e : I → ℕ → k), ∃ h : J → k, ∑ j, h j * PowerSeries.constantCoeff (ξ j) = e₀ ∧ ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (s i j) = e i l) →
 ∃ (y : J → PowerSeries k) (a : I → PowerSeries k), (∀ j, PowerSeries.constantCoeff (y j) = y₀ j) ∧ (∀ i, PowerSeries.constantCoeff (a i) = 0) ∧
   ∑ j, y j * ξ j = 0 ∧ ∀ i, ∀ l < N, ∑ j, y j * (((PowerSeries.derivativeFun)^[l] (s i j)).subst (a i) : PowerSeries k) = 0 := by
  intro k J I _ _ _ _ N ξ s y₀ hN h0 hlow hN' hsurj

  have hA : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l] f)
      = (l.factorial : k) * PowerSeries.coeff l f := by
    intro f l; rw [iter_eq]; exact PowerSeries.constantCoeff_iterate_derivative f l
  have hB : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l] f)
      = ((2 : ℕ).ascFactorial l : k) * PowerSeries.coeff (1 + l) f := by
    intro f l; rw [iter_eq]; exact PowerSeries.coeff_iterate_derivative f l 1
  have hsur : Function.Surjective (lin N ξ s y₀) := by

    intro w
    have hfac : ∀ l : ℕ, (l.factorial : k) ≠ 0 := fun l => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero l)
    obtain ⟨hv, hv0, hvl⟩ := hsurj (w none)
      (fun i l => if hl : l < N then w (some (i, ⟨l, hl⟩)) / (l.factorial : k) else 0)
    have hN1 : N - 1 < N := by omega
    have hS : ∀ i, ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[N - 1] (s i j)) ≠ 0 := by
      intro i
      simp only [hB]
      have e1 : 1 + (N - 1) = N := by omega
      rw [e1]
      have hasc : ((Nat.ascFactorial 2 (N - 1) : ℕ) : k) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.ascFactorial_pos 1 (N - 1)).ne'
      calc ∑ j, y₀ j * (((Nat.ascFactorial 2 (N - 1) : ℕ) : k) * PowerSeries.coeff N (s i j))
          = ((Nat.ascFactorial 2 (N - 1) : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff N (s i j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ ≠ 0 := mul_ne_zero hasc (hN' i)
    refine ⟨Sum.elim hv (fun i => (w (some (i, ⟨N - 1, hN1⟩)) - ∑ j, hv j *
        PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[N - 1] (s i j))) /
        ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[N - 1] (s i j))), ?_⟩
    funext e
    rcases e with _ | ⟨i, l⟩
    · simpa [lin, linFun] using hv0
    · simp only [lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
      rcases Nat.lt_or_ge (l.1 + 1) N with hl | hl
      · have h1 : ∑ j, hv j * PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
            = w (some (i, l)) := by
          simp only [hA]
          have := hvl i l.1 hl
          rw [dite_eq_left l.2] at this
          calc ∑ j, hv j * ((l.1.factorial : k) * PowerSeries.coeff l.1 (s i j))
              = (l.1.factorial : k) * ∑ j, hv j * PowerSeries.coeff l.1 (s i j) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ = w (some (i, l)) := by rw [this, mul_div_assoc', mul_div_cancel_left₀ _ (hfac _)]
        have h2 : ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j)) = 0 := by
          simp only [hB]
          calc ∑ j, y₀ j * (((Nat.ascFactorial 2 l.1 : ℕ) : k) * PowerSeries.coeff (1 + l.1) (s i j))
              = ((Nat.ascFactorial 2 l.1 : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff (1 + l.1) (s i j) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ = 0 := by rw [hlow i (1 + l.1) (by omega), mul_zero]
        rw [h1, h2, mul_zero, add_zero]
      · have hl' : l = ⟨N - 1, hN1⟩ := Fin.ext (by simp; omega)
        subst hl'
        rw [div_mul_cancel₀ _ (hS i)]
        ring
  have hbase : ∀ e, PowerSeries.constantCoeff
      (sys N ξ s (fun i => PowerSeries.C (Sum.elim y₀ 0 i)) e) = 0 := by

    intro e
    rcases e with _ | ⟨i, l⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [sys, map_sum, h0]
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [sys, map_sum, map_mul, PowerSeries.constantCoeff_C, Sum.elim_inl, Sum.elim_inr]
      have h' : ∀ j, PowerSeries.constantCoeff (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst
          (PowerSeries.C ((0 : I → k) i)) : PowerSeries k) = (l.1.factorial : k) * PowerSeries.coeff l.1 (s i j) := by
        intro j; rw [cc_subst _ _ (by simp), hA]
      simp only [h']
      calc ∑ j, y₀ j * ((l.1.factorial : k) * PowerSeries.coeff l.1 (s i j))
          = (l.1.factorial : k) * ∑ j, y₀ j * PowerSeries.coeff l.1 (s i j) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hlow i l.1 l.2, mul_zero]
  have htay : ∀ (x h : J ⊕ I → PowerSeries k) (m : ℕ), 1 ≤ m →
      (∀ i, PowerSeries.constantCoeff (x i) = Sum.elim y₀ 0 i) → ∀ e,
      (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ sys N ξ s (fun i => x i + PowerSeries.X ^ m * h i) e
        - sys N ξ s x e - PowerSeries.X ^ m *
          PowerSeries.C (lin N ξ s y₀ (fun i => PowerSeries.constantCoeff (h i)) e) := by

    intro x h m hm hx0 e
    rcases e with _ | ⟨i, l⟩
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl]
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) * ξ j - ∑ j, x (Sum.inl j) * ξ j
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))
          = PowerSeries.X ^ m * (∑ j, h (Sum.inl j) * ξ j - PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))) := by
        rw [mul_sub, Finset.mul_sum]; simp only [add_mul, Finset.sum_add_distrib, mul_assoc]; ring
      rw [heq, pow_succ]
      refine mul_dvd_mul_left _ ?_
      rw [PowerSeries.X_dvd_iff]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk]
      set a := x (Sum.inr i)
      set b := h (Sum.inr i)
      have ha : PowerSeries.constantCoeff a = 0 := by simpa using hx0 (Sum.inr i)
      have key : ∀ j, (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
          (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j)))) := by
        intro j
        have T := _root_.GlobalTheory.taylor_subst_first_order k ((PowerSeries.derivativeFun)^[l.1] (s i j)) a b m hm ha
        exact dvd_step hm _ _ _ _ _ _ _ (by simpa using hx0 (Sum.inl j)) T.1 T.2
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - ∑ j, x (Sum.inl j) * (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
              + PowerSeries.constantCoeff b * ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j)))
          = ∑ j, ((x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j))))) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum,
          Finset.sum_add_distrib, Finset.mul_sum (a := PowerSeries.constantCoeff b)]
        congr 4
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [heq]
      exact Finset.dvd_sum fun j _ => key j
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.newton_powerSeries_target k (J ⊕ I) (Option (I × Fin N)) (sys N ξ s) (Sum.elim y₀ 0)
    (lin N ξ s y₀) hsur hbase htay
  refine ⟨fun j => x (Sum.inl j), fun i => x (Sum.inr i), fun j => by simpa using hx0 (Sum.inl j),
    fun i => by simpa using hx0 (Sum.inr i), hx none, ?_⟩
  intro i l hl
  exact hx (some (i, ⟨l, hl⟩))

end GlobalTheory.DeformZeros
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DegreeCountMaximalIdealGeneratesProduct
section
open Polynomial

namespace GlobalTheory

theorem degree_count_generates : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (D P₀ P : Ideal A) (Q Q' : I → Ideal A) (f₀ f : A), P₀.IsMaximal → P.IsMaximal → (∀ i, (Q i).IsMaximal) → (∀ i, (Q' i).IsMaximal) → Function.Injective Q' → (∀ i, Q' i ≠ P) → (∀ i, ¬ D ≤ Q' i) → ¬ D ≤ P →
 f₀ ≠ 0 → f ≠ 0 → Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N → f ∈ D → f ∈ P → (∀ i, f ∈ Q' i ^ N) → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀}) →
 Ideal.span {f} = P * D * ∏ i, Q' i ^ N := by
  intro k A _ _ _ _ _ _ _ N I _ D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hQ'P hDQ' hDP hf₀ hf hspan hfD hfP hfQ' hdeg
  obtain ⟨_hfin, hmax, hmul, hle⟩ := _root_.GlobalTheory.DedekindCodim.dedekind_finiteType_codim k A
  have hPne : P ≠ ⊥ := by
    intro h; apply hf; rw [h] at hfP; simpa using hfP
  have hmaxne : ∀ M : Ideal A, M.IsMaximal → M ≠ ⊥ := by
    intro M hM h
    subst h
    exact hPne (hM.eq_of_le hP.ne_top bot_le).symm
  have hDne : D ≠ ⊥ := by
    intro h; exact hDP (h ▸ bot_le)
  have hprodne : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) → (∏ i ∈ s, g i) ≠ ⊥ := by
    intro s g hg
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro i _; rw [Ideal.zero_eq_bot]; exact hg i
  have hpowne : ∀ (M : Ideal A) (n : ℕ), M ≠ ⊥ → M ^ n ≠ ⊥ := by
    intro M n hM
    rw [← Ideal.zero_eq_bot] at hM ⊢
    exact pow_ne_zero n hM
  have hmulne : ∀ (M M' : Ideal A), M ≠ ⊥ → M' ≠ ⊥ → M * M' ≠ ⊥ := by
    intro M M' hM hM'
    rw [← Ideal.zero_eq_bot] at hM hM' ⊢
    exact mul_ne_zero hM hM'
  have htop : Module.finrank k (A ⧸ (⊤ : Ideal A)) = 0 := by
    haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton
  have hpow : ∀ (M : Ideal A) (n : ℕ), M.IsMaximal → Module.finrank k (A ⧸ M ^ n) = n := by
    intro M n hM
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, htop]
    | succ n ih =>
      rw [pow_succ, hmul _ _ (hpowne M n (hmaxne M hM)) (hmaxne M hM), ih, (hmax M hM).1]
  have hprod : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) →
      Module.finrank k (A ⧸ ∏ i ∈ s, g i) = ∑ i ∈ s, Module.finrank k (A ⧸ g i) := by
    intro s g hg
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, Ideal.one_eq_top, htop]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, hmul _ _ (hg a) (hprodne s g hg), ih]
  have hPowProd : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) →
      Module.finrank k (A ⧸ ∏ i, R i ^ N) = N * Fintype.card I := by
    intro R hR
    rw [hprod _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))]
    simp only [hpow _ _ (hR _), Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have hPowNe : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) → (∏ i, R i ^ N) ≠ ⊥ :=
    fun R hR => hprodne _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))
  have h0 : Module.finrank k (A ⧸ Ideal.span {f₀}) =
      1 + Module.finrank k (A ⧸ D) + N * Fintype.card I := by
    rw [hspan, hmul _ _ (hmulne _ _ (hmaxne _ hP₀) hDne) (hPowNe Q hQ),
      hmul _ _ (hmaxne _ hP₀) hDne, (hmax _ hP₀).1, hPowProd Q hQ]
  have hcop_max : ∀ M M' : Ideal A, M.IsMaximal → M'.IsMaximal → M ≠ M' → IsCoprime M M' := by
    intro M M' hM hM' hne
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have h1 := hM.eq_of_le h le_sup_left
    have h2 := hM'.eq_of_le h le_sup_right
    exact hne (h1.trans h2.symm)
  have hcopD : ∀ M : Ideal A, M.IsMaximal → ¬ D ≤ M → IsCoprime M D := by
    intro M hM hDM
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    exact hDM (le_sup_right.trans (hM.eq_of_le h le_sup_left).ge)
  have hdvd : ∀ M : Ideal A, f ∈ M → M ∣ Ideal.span {f} := fun M hM =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hM)
  have hX : (∏ i, Q' i ^ N) ∣ Ideal.span {f} := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact (hcop_max _ _ (hQ' i) (hQ' j) (hinj.ne hij)).pow
    · intro i _; exact hdvd _ (hfQ' i)
  have hPD : P * D ∣ Ideal.span {f} := (hcopD P hP hDP).mul_dvd (hdvd _ hfP) (hdvd _ hfD)
  have hPDX : IsCoprime (P * D) (∏ i, Q' i ^ N) :=
    IsCoprime.mul_left
      (IsCoprime.prod_right fun i _ => (hcop_max P (Q' i) hP (hQ' i) (hQ'P i).symm).pow_right)
      (IsCoprime.prod_right fun i _ => (hcopD (Q' i) (hQ' i) (hDQ' i)).symm.pow_right)
  have hJ : P * D * ∏ i, Q' i ^ N ∣ Ideal.span {f} := hPDX.mul_dvd hPD hX
  apply hle _ _ _ (Ideal.le_of_dvd hJ)
  · rw [hmul _ _ (hmulne _ _ hPne hDne) (hPowNe Q' hQ'), hmul _ _ hPne hDne, (hmax _ hP).1,
      hPowProd Q' hQ']
    rw [h0] at hdeg; exact hdeg
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact hf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSpectralValuationAlgebraicExtensionStatement
section
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spectral_valuation_algebraic_extension : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (f : AbsoluteValue K ℝ), IsNonarchimedean f → f.IsNontrivial → CompleteSpace (WithAbs f) → ∃ v : Valuation Ω ℝ≥0, (∀ x : K, (v (algebraMap K Ω x) : ℝ) = f x) ∧ ∀ x : Ω, v x ≤ 1 ↔ ∀ i, f ((minpoly K x).coeff i) ≤ 1 := by
  first | exact @GlobalTheory.exists_spectralValuation | exact GlobalTheory.exists_spectralValuation | (intros; apply GlobalTheory.exists_spectralValuation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GramDetIndexSublatticeStatement
section
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_eq_sq_mul_gram_det_of_mem_span : ∀ (U V ι κ : Type) [AddCommGroup U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (φ : U →ₗ[ℤ] V) (u : ι → U) (v : κ → U), Fintype.card ι = Fintype.card κ → (∀ k, v k ∈ Submodule.span ℤ (Set.range u)) → ∃ m : ℕ, (Matrix.gram ℝ fun k => φ (v k)).det = (m : ℝ) ^ 2 * (Matrix.gram ℝ fun i => φ (u i)).det ∧ ∀ i, (m : ℤ) • u i ∈ Submodule.span ℤ (Set.range v) := by
  first | exact @GlobalTheory.gram_det_index_sublattice | exact GlobalTheory.gram_det_index_sublattice | (intros; apply GlobalTheory.gram_det_index_sublattice <;> assumption)
end

