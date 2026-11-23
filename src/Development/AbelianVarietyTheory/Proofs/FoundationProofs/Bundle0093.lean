module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiKummerRelationPadicSmul
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem smul_cls_eq_cls_pow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (r : ℤ_[l]) (f : X.Kˣ) :
    r • X.cls l n f = X.cls l n (f ^ (PadicInt.toZModPow n r).val) := by
  have hker : r - ((PadicInt.toZModPow n r).val : ℤ_[l]) ∈ idl l ^ n := by
    rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp
  unfold Tower.cls
  have hk : ∀ (k : ℕ) (y : Additive X.Kˣ), (1 : ℤ_[l]) ⊗ₜ[ℤ] (k • y) = k • ((1 : ℤ_[l]) ⊗ₜ[ℤ] y) :=
    fun k y => map_nsmul (TensorProduct.mk ℤ ℤ_[l] (Additive X.Kˣ) 1) k y
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ofMul_pow, hk,
    ← Nat.cast_smul_eq_nsmul ℤ_[l], ← sub_smul]
  exact Submodule.smul_mem_smul hker Submodule.mem_top

theorem isRoot_pow (X : Tower Ω ε) {m : ℕ} {f : X.Kˣ} {a b : ℂ → ℂ} (h : H3.IsRoot X m f a b) (k : ℕ) :
    H3.IsRoot X m (f ^ k) (a ^ k) (b ^ k) := by
  obtain ⟨ha, hb, hb0, hab⟩ := h
  refine ⟨ha.pow k, hb.pow k, ?_, ?_⟩
  · intro h0
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · haveI := hs_codiscrete_neBot
      rw [pow_zero] at h0
      exact one_ne_zero (α := Mero) h0
    · apply hb0
      have h1 : (b ^ k) =ᶠ[Filter.codiscreteWithin Hs] 0 := Filter.Germ.coe_eq.1 h0
      have h2 : b =ᶠ[Filter.codiscreteWithin Hs] 0 := by
        filter_upwards [h1] with z hz
        exact pow_eq_zero_iff hk.ne' |>.1 hz
      exact Filter.Germ.coe_eq.2 h2
  · rw [Filter.Germ.coe_pow, Filter.Germ.coe_pow, Units.val_pow_eq_pow_val, map_pow, ← pow_mul, ← pow_mul,
      mul_comm k m, pow_mul, pow_mul, ← mul_pow, hab]

theorem exp_val_mul (l n : ℕ) [Fact l.Prime] (s t : ZMod (l ^ n)) :
    Complex.exp (2 * Real.pi * Complex.I * ((s * t).val : ℂ) / ((l : ℂ) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * (t.val : ℂ) / ((l : ℂ) ^ n)) ^ s.val := by
  have hl : (l : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  rw [← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-((s.val * t.val / l ^ n : ℕ) : ℤ), ?_⟩
  have h : (((s * t).val : ℕ) : ℂ) + (l : ℂ) ^ n * ((s.val * t.val / l ^ n : ℕ) : ℂ) = (s.val : ℂ) * t.val := by
    rw [ZMod.val_mul]
    exact_mod_cast Nat.mod_add_div (s.val * t.val) (l ^ n)
  rw [Int.cast_neg, Int.cast_natCast]
  field_simp
  linear_combination h

theorem kum_smul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (r : ℤ_[l]) {x : X.Khat l}
    {χ : SL(2, ℤ) → ZMod (l ^ n)} (h : H3.Kum X l n x χ) :
    H3.Kum X l n (r • x) (fun δ => PadicInt.toZModPow n r * χ δ) := by
  obtain ⟨f, a, b, M, hM, hx, hroot, hδ⟩ := h
  refine ⟨f ^ (PadicInt.toZModPow n r).val, a ^ (PadicInt.toZModPow n r).val, b ^ (PadicInt.toZModPow n r).val,
    M, hM, ?_, isRoot_pow X hroot _, fun δ hd z hz => ?_⟩
  · rw [map_smul, hx, smul_cls_eq_cls_pow]
  · rw [exp_val_mul]
    simp only [Pi.pow_apply]
    rw [← mul_pow, ← mul_pow, ← mul_pow, hδ δ hd z hz]

theorem btZ_smul (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (r : ℤ_[l]) (b : X.Fn l)
    (c : Gam N l → MvPolynomial (Fin 2) ℤ_[l]) (h : BtZ X N l b c) : BtZ X N l (r • b) (r • c) := by
  intro n u
  obtain ⟨χ, hχ, M, hM, hc⟩ := h n u
  refine ⟨fun δ => PadicInt.toZModPow n r * χ δ, kum_smul X l n r hχ, M, hM, fun δ hd => ?_⟩
  have := hc δ hd
  simp only [Pi.smul_apply, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C]
  rw [this]

end GlobalTheory.KZ.BettiB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterEigenspaceIsComplPrincipalSeriesTwisted
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem Datum.theta_ne_zero_of_mem {G : Type} [Group G] [TopologicalSpace G] {H : Set G} {θ : G → ℂ}
    (hD : Datum H θ) {j : G} (hj : j ∈ H) : θ j ≠ 0 := by
  intro h0
  have h := hD.val_mul j hj j⁻¹ (hD.inv j hj)
  rw [mul_inv_cancel, hD.val_one, h0, zero_mul] at h
  exact one_ne_zero h

theorem eig_compl_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ →
    (∀ u ∈ aug π H θ, IsEig π H θ u → u = 0) ∧ ∀ w : V, ∃ w' : V, IsEig π H θ w' ∧ w - w' ∈ aug π H θ := by
  intro G V _ _ _ _ _ π hπ H θ hD
  refine ⟨fun u hu he => ?_, fun w => ?_⟩
  · obtain ⟨R, hR1, hRH, hs⟩ := _root_.GlobalTheory.PsType.aug_avg_zero G V π hπ H θ hD u hu
    have hc : (R.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨1, hR1⟩).ne'
    have hsum : ∑ j ∈ R, (θ j)⁻¹ • π j u = (R.card : ℂ) • u := by
      rw [Finset.sum_congr rfl (g := fun _ => u), Finset.sum_const, Nat.cast_smul_eq_nsmul]
      intro j hj
      rw [he j (hRH j hj), smul_smul, inv_mul_cancel₀ (hD.theta_ne_zero_of_mem (hRH j hj)), one_smul]
    rw [hsum] at hs
    exact (smul_eq_zero.mp hs).resolve_left hc
  · obtain ⟨R, hR1, hRH, hs⟩ := _root_.GlobalTheory.PsType.avg_eig G V π hπ H θ hD w
    have hc : (R.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨1, hR1⟩).ne'
    refine ⟨(R.card : ℂ)⁻¹ • ∑ j ∈ R, (θ j)⁻¹ • π j w, ?_, ?_⟩
    · intro h hh
      rw [(π h).map_smul, hs h hh]
      exact smul_comm _ _ _
    · have e : w - (R.card : ℂ)⁻¹ • ∑ j ∈ R, (θ j)⁻¹ • π j w
          = (R.card : ℂ)⁻¹ • ∑ j ∈ R, (w - (θ j)⁻¹ • π j w) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
          inv_mul_cancel₀ hc, one_smul]
      rw [e]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j hj => ?_)
      have hθ := hD.theta_ne_zero_of_mem (hRH j hj)
      have e2 : w - (θ j)⁻¹ • π j w = -(θ j)⁻¹ • (π j w - θ j • w) := by
        rw [neg_smul, smul_sub, smul_smul, inv_mul_cancel₀ hθ, one_smul, neg_sub]
      rw [e2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hRH j hj, w, rfl⟩)

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormsEqZeroOfPeriodSubConjCoboundary
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Positivity

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma eichler_mem_degreeLT_succ (w : ℕ) (g : ℍ → ℂ) (τ : ℍ) :
    _root_.GlobalTheory.HeckeFamilyMatrices.eichler w g τ ∈ ℂ[X]_(w + 1) := by
  rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [_root_.GlobalTheory.EichlerChange.coeff_eichler, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma map_conj_mem_degreeLT {n : ℕ} {p : ℂ[X]} (hp : p ∈ ℂ[X]_n) :
    p.map (starRingEnd ℂ) ∈ ℂ[X]_n := by
  rw [Polynomial.mem_degreeLT] at hp ⊢
  rwa [Polynomial.degree_map]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma sl_denom_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  have h := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  simpa [UpperHalfPlane.denom] using h

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma eval_eq_denom_pow_mul_eval_of_slP_invariant (w : ℕ) (V : ℍ → ℂ[X]) (γ : SL(2, ℤ)) (τ : ℍ)
    (hmem : V (γ • τ) ∈ ℂ[X]_(w + 1))
    (hrel : _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (V (γ • τ)) = V τ) :
    eval (τ : ℂ) (V τ) =
      (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ w * eval ((γ • τ : ℍ) : ℂ) (V (γ • τ)) := by
  rw [← hrel, _root_.GlobalTheory.HeckeFamilyMatrices.eval_polySlash w _ _ _ hmem (sl_denom_ne_zero γ τ)]
  congr 2
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma im_sl_smul_eq_im_div_normSq_denom (γ : SL(2, ℤ)) (τ : ℍ) :
    (γ • τ).im = τ.im / Complex.normSq (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [ModularGroup.sl_moeb, UpperHalfPlane.im_smul_eq_div_normSq]
  simp [UpperHalfPlane.denom]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma continuous_eval_of_continuous_coeff_of_degree_le (w : ℕ) (V : ℍ → ℂ[X])
    (hmem : ∀ τ, V τ ∈ ℂ[X]_(w + 1)) (hc : ∀ n, Continuous fun τ => (V τ).coeff n) :
    Continuous fun τ : ℍ => eval (τ : ℂ) (V τ) := by
  have h : (fun τ : ℍ => eval (τ : ℂ) (V τ)) =
      fun τ => ∑ i ∈ Finset.range (w + 1), (V τ).coeff i * (τ : ℂ) ^ i := by
    funext τ
    apply eval_eq_sum_range'
    by_cases h0 : V τ = 0
    · simp [h0]
    · have := hmem τ
      rw [mem_degreeLT] at this
      exact (natDegree_lt_iff_degree_lt h0).2 this
  rw [h]
  exact continuous_finsetSum _ fun i _ => (hc i).mul (continuous_coe.pow i)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma exists_norm_eval_le_mul_im_rpow_of_slP_invariant (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (w : ℕ)
    (V : ℍ → ℂ[X]) (hmem : ∀ τ, V τ ∈ ℂ[X]_(w + 1))
    (hc : ∀ n, Continuous fun τ => (V τ).coeff n)
    (hrel : ∀ γ ∈ Γ, ∀ τ, _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (V (γ • τ)) = V τ)
    (hdecay : ∀ g : SL(2, ℤ), Filter.Tendsto
      (fun τ => ‖eval ((g • τ : ℍ) : ℂ) (V (g • τ))‖ * (g • τ).im ^ (-(w : ℝ) / 2))
      atImInfty (nhds 0)) :
    ∃ C, ∀ τ : ℍ, ‖eval (τ : ℂ) (V τ)‖ ≤ C * τ.im ^ ((w : ℝ) / 2) := by
  have hinv : ∀ γ ∈ Γ, ∀ τ : ℍ,
      ‖eval ((γ • τ : ℍ) : ℂ) (V (γ • τ))‖ * (γ • τ).im ^ (-(w : ℝ) / 2) =
        ‖eval (τ : ℂ) (V τ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
    intro γ hγ τ
    have he := eval_eq_denom_pow_mul_eval_of_slP_invariant w V γ τ (hmem _) (hrel γ hγ τ)
    have hD := sl_denom_ne_zero γ τ
    set D := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) with hDdef
    have hDpos : 0 < ‖D‖ := norm_pos_iff.2 hD
    have hx : (‖D‖ ^ (2 : ℕ)) ^ (-(w : ℝ) / 2) = (‖D‖ ^ w)⁻¹ := by
      rw [← Real.rpow_natCast ‖D‖ 2, ← Real.rpow_mul (norm_nonneg _),
        show ((2 : ℕ) : ℝ) * (-(w : ℝ) / 2) = -(w : ℝ) by push_cast; ring,
        Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
    rw [he, im_sl_smul_eq_im_div_normSq_denom, ← hDdef, Real.div_rpow τ.im_pos.le (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq, hx, norm_mul, norm_pow]
    have hw : 0 < ‖D‖ ^ w := pow_pos hDpos w
    field_simp
  obtain ⟨C, hC⟩ := ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO
    (f := fun τ : ℍ => ‖eval (τ : ℂ) (V τ)‖ * τ.im ^ (-(w : ℝ) / 2))
    (((continuous_eval_of_continuous_coeff_of_degree_le w V hmem hc).norm).mul
      (UpperHalfPlane.continuous_im.rpow_const fun τ => Or.inl τ.im_pos.ne'))
    le_rfl (fun g => by simpa using (hdecay g).isBigO_one ℝ) (Γ := Γ) hinv
  refine ⟨C, fun τ => ?_⟩
  have h1 := hC τ
  rw [Real.rpow_zero, mul_one, Real.norm_of_nonneg (by positivity)] at h1
  have hpos : 0 < τ.im ^ ((w : ℝ) / 2) := Real.rpow_pos_of_pos τ.im_pos _
  calc ‖eval (τ : ℂ) (V τ)‖
      = ‖eval (τ : ℂ) (V τ)‖ * τ.im ^ (-(w : ℝ) / 2) * τ.im ^ ((w : ℝ) / 2) := by
        rw [mul_assoc, ← Real.rpow_add τ.im_pos]
        simp [neg_div]
    _ ≤ C * τ.im ^ ((w : ℝ) / 2) := mul_le_mul_of_nonneg_right h1 hpos.le

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma eq_zero_of_eichler_conj_slash_relation (Γ : Subgroup SL(2, ℤ)) (k : ℕ)
    (hΓ : Γ.FiniteIndex) (hk : 3 ≤ k)
    (f h : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) k) (p : ℂ[X])
    (hp : p ∈ ℂ[X]_(k - 1))
    (hrel : ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
      (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ)) - p) =
      _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ) - p) :
    h = 0 := by
  set V : ℍ → ℂ[X] := fun τ => _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ -
    map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ) - p with hV
  have hk1 : k - 1 = k - 2 + 1 := by omega
  have hp' : p ∈ ℂ[X]_(k - 2 + 1) := by rw [← hk1]; exact hp
  have hmem : ∀ τ, V τ ∈ ℂ[X]_(k - 2 + 1) := fun τ =>
    sub_mem (sub_mem (eichler_mem_degreeLT_succ _ _ _)
      (map_conj_mem_degreeLT (eichler_mem_degreeLT_succ _ _ _))) hp'
  have hcf : ∀ g : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) k, ∀ n : ℕ,
      Continuous fun τ => (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g τ).coeff n := by
    intro g n
    simp_rw [_root_.GlobalTheory.EichlerChange.coeff_eichler]
    refine continuous_const.mul (continuous_iff_continuousAt.2 fun τ => ?_)
    exact ((_root_.GlobalTheory.EichlerChange.hasDerivAt_ecoef (k - 2) g (CuspFormClass.holo g) n τ
      τ.im_pos).continuousAt).comp continuous_coe.continuousAt
  have hc : ∀ n, Continuous fun τ => (V τ).coeff n := by
    intro n
    simp only [hV, coeff_sub, coeff_map]
    exact ((hcf f n).sub (Complex.continuous_conj.comp (hcf h n))).sub continuous_const
  have hrel' : ∀ γ ∈ Γ, ∀ τ,
      _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (V (γ • τ)) = V τ :=
    fun γ hγ τ => hrel ⟨γ, hγ⟩ τ
  have hdecay := _root_.GlobalTheory.HeckeFamilyMatrices.Decay.decay_at_cusp Γ k hΓ hk f h p hp hrel
  have hw : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  obtain ⟨C, hC⟩ := exists_norm_eval_le_mul_im_rpow_of_slP_invariant Γ (k - 2) V hmem hc hrel'
    (by rw [hw]; exact hdecay)
  obtain ⟨n, hn, -, hTn⟩ :=
    Subgroup.exists_pow_mem_of_index_ne_zero hΓ.index_ne_zero ModularGroup.T
  refine _root_.GlobalTheory.EichlerPositivity.cuspForm_eq_zero_of_periodic_of_bound Γ k hΓ hk f h p n C hn (fun τ => ?_)
    (fun τ => by rw [← hw]; exact hC τ)
  have hT : ModularGroup.T ^ n • τ = (n : ℝ) +ᵥ τ := by
    rw [← zpow_natCast, modular_T_zpow_smul]; simp
  have he := eval_eq_denom_pow_mul_eval_of_slP_invariant (k - 2) V (ModularGroup.T ^ n) τ (hmem _) (hrel' _ hTn τ)
  have h10 : ((ModularGroup.T ^ n) 1 0 : ℤ) = 0 ∧ ((ModularGroup.T ^ n) 1 1 : ℤ) = 1 := by
    rw [← zpow_natCast, ModularGroup.coe_T_zpow]; simp
  rw [h10.1, h10.2] at he
  simp only [Int.cast_zero, zero_mul, zero_add, Int.cast_one, one_pow, one_mul, hT] at he
  exact he.symm


open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
theorem _root_.GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N →
    Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)),
    _root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑f - _root_.GlobalTheory.HeckeFamilyMatrices.cj (_root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑h) ∈
      _root_.GlobalTheory.HeckeFamilyMatrices.B1 Γ (k - 2) → f = 0 ∧ h = 0 := by
  intro N Γ k _ _ hΓ hk f h hB
  unfold _root_.GlobalTheory.HeckeFamilyMatrices.B1 at hB
  obtain ⟨⟨q, hq⟩, hqe⟩ := hB
  have hcoc : ∀ γ : Γ, _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) q - q =
      _root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑f γ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑h γ) := fun γ => by
    have := congrFun hqe γ
    simpa [_root_.GlobalTheory.HeckeFamilyMatrices.cj] using this
  have hper : ∀ g : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) k,
      ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑g γ =
        _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
            (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g (γ • τ)) -
          _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g τ := fun g =>
    (_root_.GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub Γ k (by omega) (CuspForm.toModularFormₗ g)).2
  have hmemE : ∀ (g : ℍ → ℂ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g τ ∈ ℂ[X]_(k - 2 + 1) :=
    fun g τ => eichler_mem_degreeLT_succ _ _ _
  have hconj : ∀ p ∈ ℂ[X]_(k - 2 + 1), ∀ γ : SL(2, ℤ),
      map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) p) =
        _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (map (starRingEnd ℂ) p) :=
    fun p hp γ =>
      (_root_.GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) 1 p hp).2.2.2
  have hcc : ∀ p : ℂ[X], map (starRingEnd ℂ) (map (starRingEnd ℂ) p) = p := fun p => by
    ext n; simp [coeff_map]
  have hk1 : k - 1 = k - 2 + 1 := by omega
  have rel1 : ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
      (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ)) - q) =
      _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ) - q := by
    intro γ τ
    have h1 := hcoc γ
    rw [hper f γ τ, hper h γ τ, Polynomial.map_sub, hconj _ (hmemE _ _)] at h1
    rw [map_sub, map_sub]
    linear_combination -h1
  have rel2 : ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
      (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ)) - -map (starRingEnd ℂ) q) =
      _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ) - -map (starRingEnd ℂ) q := by
    intro γ τ
    have h2 := congrArg (map (starRingEnd ℂ)) (rel1 γ τ)
    rw [hconj _ (sub_mem (sub_mem (hmemE _ _) (map_conj_mem_degreeLT (hmemE _ _))) hq)] at h2
    simp only [Polynomial.map_sub, hcc] at h2
    have hneg : _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ)) - -map (starRingEnd ℂ) q =
        -(map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ)) -
          _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ) - map (starRingEnd ℂ) q) := by ring
    rw [hneg, map_neg, h2]
    ring
  have hq' : q ∈ ℂ[X]_(k - 1) := by rw [hk1]; exact hq
  exact ⟨eq_zero_of_eichler_conj_slash_relation Γ k hΓ hk h f _
      (neg_mem (map_conj_mem_degreeLT hq')) rel2,
    eq_zero_of_eichler_conj_slash_relation Γ k hΓ hk f h q hq' rel1⟩

end GlobalTheory.HeckeFamilyMatrices.Positivity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicCharacterFrobV
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem rootOfUnity_eq_one_of_val {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    {m : ℕ} (hm : ¬ v (m : K) < 1) {η : K} (hη : η ^ m = 1) (h1 : v (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hm
  have hv : v η = 1 := by
    have := v.map_one_add_of_lt h1
    simpa using this
  have hi : ∀ i : ℕ, v (1 - η ^ i) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : 1 - η ^ (i + 1) = (1 - η ^ i) + -(η ^ i * (η - 1)) := by ring
      rw [e]
      refine v.map_add_lt ih ?_
      rw [v.map_neg, map_mul, map_pow, hv, one_pow, one_mul]
      exact h1
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have e : (m : K) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact v.map_sum_lt one_ne_zero fun i _ => hi i

theorem not_val_lt_one_of_coprime {K : Type*} [Field K] (V : ValuationSubring K) {m q : ℕ} (h : Nat.Coprime m q)
    (hq : V.valuation (q : K) < 1) : ¬ V.valuation (m : K) < 1 := by
  intro hm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have e : (1 : K) = (a : K) * m + (b : K) * q := by
    have := congrArg (Int.cast : ℤ → K) hab
    push_cast at this
    exact this.symm
  have hz : ∀ (c : ℤ) (x : K), V.valuation x < 1 → V.valuation ((c : K) * x) < 1 := by
    intro c x hx
    rw [map_mul]
    have hc : V.valuation (c : K) ≤ 1 := (V.valuation_le_one_iff _).mpr (intCast_mem V c)
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hx
  have := V.valuation.map_add_lt (hz a _ hm) (hz b _ hq)
  rw [← e, map_one] at this
  exact lt_irrefl _ this

theorem FrobV.apply_rootOfUnity {Ω : Type} [Field Ω] [Algebra ℚ Ω] {V : ValuationSubring Ω} {q : ℕ}
    {s : Ω ≃ₐ[ℚ] Ω} (hs : FrobV V q s) {m : ℕ} (hm0 : m ≠ 0) (hm : Nat.Coprime m q) {ζ : Ω} (hζ : ζ ^ m = 1) :
    s ζ = ζ ^ q := by
  have hq : V.valuation (q : Ω) < 1 := V.mem_nonunits_iff.mp hs.1
  have hv : V.valuation ζ = 1 := by
    have := congrArg V.valuation hζ
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_left hm0).mp this
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hv
  have hV : ζ ∈ V := (V.valuation_le_one_iff _).mp hv.le
  have h := (hs.2 ζ hV).2.2
  have hq0 : ζ ^ q ≠ 0 := pow_ne_zero _ hζ0
  have key : s ζ / ζ ^ q = 1 := by
    refine rootOfUnity_eq_one_of_val V.valuation (not_val_lt_one_of_coprime V hm hq) ?_ ?_
    · rw [div_pow, ← map_pow, hζ, map_one, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, div_one]
    · rw [div_sub_one hq0, map_div₀, map_pow, hv, one_pow, div_one]
      exact h
  exact (div_eq_one_iff_eq hq0).mp key

theorem cyclotomicCharacter_frobV : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l q : ℕ) [Fact l.Prime],
    q.Prime → q ≠ l → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s →
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) = q := by
  intro Ω _ _ _ l q hl hq hql V s hs
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, NeZero ((l ^ i : ℕ) : Ω) := fun i => ⟨by exact_mod_cast pow_ne_zero i hl.out.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [cyclotomicCharacter.toZModPow, map_natCast]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : (t : Ω) ^ (l ^ n) = 1 := (mem_rootsOfUnity' _ _).mp ht
  have hc : Nat.Coprime (l ^ n) q := ((Nat.coprime_primes hl.out hq).mpr hql.symm).pow_left n
  have := hs.apply_rootOfUnity (pow_ne_zero n hl.out.ne_zero) hc ht'
  rw [ZMod.val_natCast, ← pow_eq_pow_mod q ht']
  exact this

end GlobalTheory.KZ.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntExponentCongrCyclotomicCharacterStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_exponent_congr_cyclotomicCharacter : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (n M : ℕ), 0 < M → l ^ n ∣ M → ∃ e : ℤ, (∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e) ∧ (e : ℤ_[l]) - (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ∈ (idl l) ^ n := by
  first | exact @GlobalTheory.KZ.exists_int_exponent_cyclotomic | exact GlobalTheory.KZ.exists_int_exponent_cyclotomic | (intros; apply GlobalTheory.KZ.exists_int_exponent_cyclotomic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElementStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monic_irreducible_integral_primitive_element : ∀ {F : Type} [Field F] [CharZero F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic ∧ Irreducible Φ ∧ Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 ∧ ∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F), Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω := by
  first | exact @GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive | exact GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive | (intros; apply GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive <;> assumption)
end

