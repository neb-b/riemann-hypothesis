module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionNormAndOverlapBound
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.PhiNorm

section Product

variable {κ ι α : Type} [Fintype κ] [Fintype ι]

theorem sum_left (s : Finset α) (f : α → Matrix κ ι ℚ → ℂ) {ψ : Matrix κ ι ℚ → ℂ}
    (hs : ∀ a ∈ s, IsSB (f a)) (h' : IsSB ψ) :
    IsSB (∑ a ∈ s, f a) ∧ SW.ip (∑ a ∈ s, f a) ψ = ∑ a ∈ s, SW.ip (f a) ψ := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨isSB_zero, ?_⟩
    have := TensVac.ip_smul_left 0 h' h'
    simpa using this
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun φ hφ => hs φ (Finset.mem_insert_of_mem hφ)
    have h3 := hs a (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, TensVac.ip_add_left h3 h1 h', h2]
    exact ⟨(_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ h3 h1).1, rfl⟩

theorem ip_sum_diag (s : Finset α) (f f' : α → Matrix κ ι ℚ → ℂ) (hf : ∀ a ∈ s, IsSB (f a))
    (hf' : ∀ a ∈ s, IsSB (f' a)) (h : ∀ a ∈ s, ∀ b ∈ s, SW.ip (f a) (f' b) ≠ 0 → a = b) :
    SW.ip (∑ a ∈ s, f a) (∑ a ∈ s, f' a) = ∑ a ∈ s, SW.ip (f a) (f' a) := by
  rw [(sum_left s f hf (sum_left s f' hf' isSB_zero).1).2]
  refine Finset.sum_congr rfl fun a ha => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [TensVac.ip_conj (sum_left s f' hf' isSB_zero).1 (hf a ha), (sum_left s f' hf' (hf a ha)).2,
    map_sum, Finset.sum_eq_single_of_mem a ha, ← TensVac.ip_conj (hf' a ha) (hf a ha)]
  intro b hb hba
  rw [← TensVac.ip_conj (hf' b hb) (hf a ha)]
  by_contra h0
  exact hba (h a ha b hb h0).symm

end Product

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem pair_int (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {w : E}
    {v v' : TF n g} (hv : IsSB v) (hv' : IsSB v') {δ y y' : Matrix (Fin n) (Fin r) E}
    (h : epsW X w δ • heisG X bas δ v = v) (h' : epsW X w δ • heisG X bas δ v' = v')
    (h0 : SW.ip (heisG X bas y v) (heisG X bas y' v') ≠ 0) :
    ∃ k : ℤ, ∑ i, EF X (δ i) ((y - y') i) = k := by
  have H := (heisG_laws E r X g bas idx n hs hn).2.2.2
  have key : ∀ (y : Matrix (Fin n) (Fin r) E) (v : TF n g), IsSB v →
      epsW X w δ • heisG X bas δ v = v → epsW X w δ • heisG X bas δ (heisG X bas y v) =
        cexp (-(2 * π * I * ((∑ k, EF X (δ k) (y k) : ℚ) : ℂ))) • heisG X bas y v := by
    intro y v hv h
    have e : heisG X bas δ (heisG X bas y v) =
        cexp (-(2 * π * I * ((∑ k, EF X (δ k) (y k) : ℚ) : ℂ))) •
          heisG X bas y (heisG X bas δ v) := by
      rw [(H δ v hv).2.2.1 y, (H y v hv).2.2.1 δ, smul_smul, ← Complex.exp_add, add_comm y,
        TensVac.sumEF_swap hs δ y]
      congr 2
      push_cast
      ring
    rw [e, smul_comm, ← TensVac.heisG_smul, h]
  have h1 := (H y v hv).1
  have h2 := (H y' v' hv').1
  have h3 := (H δ _ h1).2.2.2.1 _ h2
  have h4 : SW.ip (epsW X w δ • heisG X bas δ (heisG X bas y v))
      (epsW X w δ • heisG X bas δ (heisG X bas y' v')) =
      SW.ip (heisG X bas y v) (heisG X bas y' v') := by
    rw [TensVac.ip_smul_left _ (H δ _ h1).1 (TensVac.sb_smul _ (H δ _ h2).1),
      TensVac.ip_smul_right _ (H δ _ h1).1 (H δ _ h2).1, ← mul_assoc, TensVac.epsW_mul_conj,
      one_mul, h3]
  rw [key y v hv h, key y' v' hv' h', TensVac.ip_smul_left _ h1 (TensVac.sb_smul _ h2),
    TensVac.ip_smul_right _ h1 h2, ← mul_assoc, mul_left_eq_self₀, or_iff_left h0,
    ← Complex.exp_conj, ← Complex.exp_add, Complex.exp_eq_one_iff] at h4
  obtain ⟨k, hk⟩ := h4
  refine ⟨-k, ?_⟩
  have e : ∑ i, EF X (δ i) ((y - y') i) = ∑ i, EF X (δ i) (y i) - ∑ i, EF X (δ i) (y' i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (y - y') i = y i - y' i := rfl
    simp only [TensLat.EF_eq_bilin, this, map_sub]
  rw [e]
  simp only [map_neg, map_mul, conj_ofReal, conj_I, map_ratCast, map_ofNat] at hk
  have hπ : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  apply Rat.cast_injective (α := ℂ)
  apply mul_left_cancel₀ hπ
  push_cast at hk ⊢
  linear_combination -hk

theorem coprime_cc {𝔪 : Ideal (𝓞 E)} {t t' : 𝓞 E} (ht : (t' : E) = cc (t : E))
    (h : IsCoprime (Ideal.span {t}) (conjI 𝔪)) : IsCoprime (Ideal.span {t'}) 𝔪 := by
  let c : 𝓞 E → 𝓞 E := fun a => ⟨cc (a : E), Base.isIntegral_cc a.isIntegral_coe⟩
  have hc : ∀ a, ((c a : 𝓞 E) : E) = cc (a : E) := fun _ => rfl
  have hm : ∀ m ∈ conjI 𝔪, c m ∈ 𝔪 := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, e⟩ := hx
      have : c x = b := by ext; rw [hc, e]; simp [cc]
      rwa [this]
    | zero =>
      have : c 0 = 0 := by ext; rw [hc]; simp [cc]
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : c (x + y) = c x + c y := by ext; push_cast; simp [hc, cc]
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : c (a • x) = c a * c x := by ext; push_cast; simp [hc, cc]
      rw [this]; exact Ideal.mul_mem_left _ _ hx
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  refine Ideal.isCoprime_iff_exists.2 ⟨c u * t', Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, c b,
    hm b hb, ?_⟩
  have := congrArg (fun a : 𝓞 E => cc (a : E)) hab
  ext
  push_cast at this ⊢
  simpa [hc, ht, cc] using this


omit [IsCMField E] in
theorem smul_mem_smul {𝔪 : Ideal (𝓞 E)} {L L' : Lt E r} {t : 𝓞 E} (h : ∀ v ∈ L, t • v ∈ L')
    {v : Fin r → E} (hv : v ∈ 𝔪 • L) : t • v ∈ 𝔪 • L' := by
  refine Submodule.smul_induction_on hv (fun a ha u hu => ?_) fun a b ha hb => ?_
  · rw [smul_comm]; exact Submodule.smul_mem_smul ha (h u hu)
  · rw [smul_add]; exact add_mem ha hb

theorem cong_of_pair (D : Level X) {M : ℕ} (hM : (M : 𝓞 E) ∈ D.𝔪) {L L' : Lt E r}
    (hL : L ∈ D.lats) (hL' : L' ∈ D.lats) (hS : SelfD X (D.sh L)) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) {y y' : Matrix (Fin n) (Fin r) E}
    (h : ∀ δ ∈ tens Λ (D.sh L), δ ∈ tens Λ (D.sh L') →
      ∃ k : ℤ, ∑ i, EF X (δ i) ((y - y') i) = k) (k : Fin n) : Cong X D.𝔪 (y k) (y' k) := by
  obtain ⟨-, s, hs, hs1, -⟩ := hL
  obtain ⟨-, s', hs', -, hs2⟩ := hL'
  obtain ⟨N, -, hN, -, hN2⟩ := hΛ.2.2
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 D.cop
  let t : 𝓞 E := ⟨cc ((s' * s : 𝓞 E) : E), Base.isIntegral_cc (s' * s).isIntegral_coe⟩
  have ht : (t : E) = cc ((s' * s : 𝓞 E) : E) := rfl
  have h1 : ∀ v ∈ D.sh L, (s' * s) • v ∈ D.sh L' := fun v hv c hc => by
    rw [smul_comm]
    exact smul_mem_smul (fun u hu => by rw [mul_smul]; exact hs2 _ (hs1 u hu)) (hv c hc)
  have hctr : ∀ (c : E) (d : Matrix (Fin n) (Fin r) E) (v : Fin n → E),
      TensLat.ctr (c • d) v = c • TensLat.ctr d v := fun c d v => by
    funext j
    simp [TensLat.ctr, Finset.sum_apply, Finset.mul_sum, mul_left_comm]
  have h2 : (t : E) • (y - y') ∈ tens Λ (D.sh L) := by
    refine (TensLat.tens_selfDual hΛ hS _).2 fun δ hδ => ?_
    obtain ⟨m, hm⟩ := h (((s' * s : 𝓞 E) : E) • δ)
      (TensLat.smul_mem_tens hΛ (s' * s).isIntegral_coe hδ) (by
        rw [TensLat.mem_tens_iff hΛ] at hδ ⊢
        intro v hv
        rw [hctr]
        exact h1 _ (hδ v hv))
    refine ⟨-m, ?_⟩
    rw [Int.cast_neg, ← hm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensLat.EF_swap]
    exact congrArg Neg.neg (TensLat.EF_smul X _ _ _).symm
  have h3 := (TensLat.mem_tens_iff hΛ _ _).1 h2 _
    (hN2 (Pi.single k 1) (Submodule.subset_span ⟨k, rfl⟩))
  have h4 : TensLat.ctr ((t : E) • (y - y')) ((N : E) • (Pi.single k 1 : Fin n → E)) =
      ((N : 𝓞 E) * t) • (y k - y' k) := by
    rw [TensLat.ctr, Finset.sum_eq_single k]
    · funext j
      change _ = (((N : 𝓞 E) * t : 𝓞 E) : E) * (y k j - y' k j)
      simp [cc, mul_assoc, Algebra.smul_def]
    · intro j _ hj; simp [hj, cc]
    · simp
  rw [h4] at h3
  refine ⟨s * (b * (N * t)), ?_, ?_⟩
  · simp only [← Ideal.span_singleton_mul_span_singleton]
    refine hs.of_mul_right_left.mul_left (IsCoprime.mul_left ?_ (IsCoprime.mul_left ?_ ?_))
    · exact Ideal.isCoprime_iff_exists.2 ⟨b, Ideal.mem_span_singleton_self b, a, ha,
        (add_comm _ _).trans hab⟩
    · obtain ⟨p, q, hpq⟩ : IsCoprime (N : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.2 hN
      refine Ideal.isCoprime_iff_exists.2 ⟨p * N, Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, q * M,
        Ideal.mul_mem_left _ _ hM, ?_⟩
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hpq
    · refine coprime_cc ht ?_
      rw [← Ideal.span_singleton_mul_span_singleton]
      exact hs'.of_mul_right_right.mul_left hs.of_mul_right_right
  · rw [mul_smul, mul_smul]
    exact smul_mem_smul hs1 (h3 b hb)

theorem eq_rpow {a : ℝ} {m n : ℕ} (ha : 0 ≤ a) (h : ((m ^ n : ℕ) : ℝ) * a ^ 2 = 1) :
    a = (m : ℝ) ^ (-(n : ℝ) / 2) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rw [← pow_left_inj₀ ha (Real.rpow_nonneg hm _) two_ne_zero, ← Real.rpow_natCast (_ ^ _),
    ← Real.rpow_mul hm, show -(n : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(n : ℝ) by push_cast; ring,
    Real.rpow_neg hm, Real.rpow_natCast]
  exact eq_inv_of_mul_eq_one_right (by exact_mod_cast h)

theorem phi_norm_overlap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ L ∈ D.lats, ∀ Λ ∈ Vset E n M, SW.ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L Λ) = (Nat.card D.J : ℂ) ∧ ∀ L' ∈ D.lats, ‖SW.ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L' Λ)‖ ≤ (Nat.card D.J : ℝ) * (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2) := by
  intro E _ _ _ r X g bas idx n hs hev D hn M hM0 hM v₀ hv₀ L hL Λ hΛ
  have H := (heisG_laws E r X g bas idx n hs hev).2.2.2
  have P := GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs hev D hn M hM0 hM v₀ hv₀
  have Lv := (_root_.GlobalTheory.SW.level_laws E r X g bas idx n hs hev D hn).2.2.2.1
  have hv := (P L hL Λ hΛ).2.1
  have main : ∀ L' ∈ D.lats, SW.ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L' Λ) =
      (Nat.card D.J : ℂ) * SW.ip (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)))
        (unitv (projA X bas D.w (tens Λ (D.sh L')) (v₀ L'))) := by
    intro L' hL'
    have hv' := (P L' hL' Λ hΛ).2.1
    obtain ⟨s, hcard, hsy, e, e'⟩ := (P L hL Λ hΛ).2.2.1 L' hL'
    rw [e, e', ip_sum_diag s _ _ (fun y _ => TensVac.sb_smul _ (H y _ hv.1).1)
      (fun y _ => TensVac.sb_smul _ (H y _ hv'.1).1), ← hcard, ← nsmul_eq_mul,
      ← Finset.sum_const]
    · refine Finset.sum_congr rfl fun y hy => ?_
      rw [TensVac.ip_smul_left _ (H y _ hv.1).1 (TensVac.sb_smul _ (H y _ hv'.1).1),
        TensVac.ip_smul_right _ (H y _ hv.1).1 (H y _ hv'.1).1, ← mul_assoc, Complex.mul_conj',
        (hsy y hy).2.1, (H y _ hv.1).2.2.2.1 _ hv'.1]
      simp
    · intro y hy y' hy' h0
      rw [TensVac.ip_smul_left _ (H y _ hv.1).1 (TensVac.sb_smul _ (H y' _ hv'.1).1),
        TensVac.ip_smul_right _ (H y _ hv.1).1 (H y' _ hv'.1).1] at h0
      refine (hsy y hy).2.2 y' hy' (cong_of_pair D hM hL hL' (Lv L hL).1 hΛ fun δ hδ hδ' => ?_)
      exact pair_int idx hs hev hv.1 hv'.1 (hv.2.2 δ hδ) (hv'.2.2 δ hδ')
        (right_ne_zero_of_mul (right_ne_zero_of_mul h0))
  refine ⟨by rw [main L hL, hv.2.1, mul_one], fun L' hL' => ?_⟩
  have hv' := (P L' hL' Λ hΛ).2.1
  have h1 := (TensVac.vacua E r X g bas idx n hs hev D.w D.w_int D.w_tr _ (Lv L hL).1 M Λ
    hΛ).2.2.2 _ (Lv L' hL').1 Λ hΛ _ _ hv hv'
  rw [((TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hev D.w D.w_int D.w_tr _
    (Lv L hL).1 M Λ hΛ).2.2.2.2.1 _ (Lv L' hL').1).1, (Lv L hL).2.2.1 L' hL'] at h1
  rw [main L' hL', norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Nat.cast_nonneg _)
  exact eq_rpow (norm_nonneg _) h1

end GlobalTheory.SW.PhiNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionOverlapEqZeroOutsideLevel
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Supp

open Lev TensVac

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem row_mul (γ : GL (Fin r) E) (y : Matrix (Fin n) (Fin r) E) (j : Fin n) :
    (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) j = lin γ (y j) := by
  funext i; simp [lin_apply, Matrix.mul_apply, mulVec, dotProduct, mul_comm]

theorem tens_mapL {Λ : Lt E n} {L : Lt E r} {γ : GL (Fin r) E} {y : Matrix (Fin n) (Fin r) E}
    (hy : y ∈ tens Λ (mapL γ L)) :
    ∃ z ∈ tens Λ L, y = z * (γ : Matrix (Fin r) (Fin r) E)ᵀ := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, hv, _, ⟨u, hu, rfl⟩, rfl⟩ := hx
    refine ⟨vecMulVec v u, AddSubgroup.subset_closure ⟨v, hv, u, hu, rfl⟩, ?_⟩
    rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    rfl
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, add_mem ha hb, by rw [Matrix.add_mul]⟩
  | neg x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨-a, neg_mem ha, by rw [Matrix.neg_mul]⟩

theorem epsW_mul {γ : GL (Fin r) E} (h : IsUn X γ) (w : E) (y : Matrix (Fin n) (Fin r) E) :
    epsW X w (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) = epsW X w y := by
  have (k : Fin n) : EF X (lin γ (y k)) (w • lin γ (y k)) = EF X (y k) (w • y k) := by
    have : w • lin γ (y k) = lin γ (w • y k) := by simp [lin_apply, Matrix.mulVec_smul]
    rw [this, EF_lin h, lin_inv]
  simp only [epsW, row_mul, this]

variable {D : Level X}

theorem row_mem {M : ℕ} (hM : (M : 𝓞 E) ∈ D.𝔪) {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {L : Lt E r}
    (hL : L ∈ D.lats) {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ (D.sh L)) (k : Fin n) :
    y k ∈ loc D.𝔪 (D.𝔪 • X.Λ) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hx
    obtain ⟨-, -, s, -, hs, h1, -⟩ := hΛ
    obtain ⟨-, t, ht, h2, -⟩ := hL
    obtain ⟨m, hm, m', hm', e⟩ := Ideal.isCoprime_iff_exists.1 D.cop
    have hs' : IsCoprime (Ideal.span {(s : 𝓞 E)}) D.𝔪 := by
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hs
      refine cop_iff.2 ⟨(a : 𝓞 E), (b : 𝓞 E) * M, Ideal.mul_mem_left _ _ hM, ?_⟩
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
    have hu' : u ∈ loc D.𝔪 (D.𝔪 • X.Λ) :=
      loc_loc (s := m') (cop_iff.2 ⟨1, m, hm, by linear_combination e⟩)
        ⟨t, ht.of_mul_right_left, smul_map_mem LinearMap.id h2 (hu m' hm')⟩
    have hi : IsIntegral ℤ ((s : E) * v k) := (Base.mem_stdL _).1 (h1 v hv) k
    refine loc_loc hs' ?_
    have : (s : 𝓞 E) • vecMulVec v u k = (⟨_, hi⟩ : 𝓞 E) • u := by
      funext i
      exact (mul_assoc (s : E) (v k) (u i)).symm
    rw [this]
    exact Submodule.smul_mem _ _ hu'
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem red_of_red {γ : GL (Fin r) E} {u : Fin r → Fin r → E} {k l : GL (Fin r) (𝓞 E ⧸ D.𝔪)}
    (h : D.Red u k) (h' : D.Red (fun i => lin γ (u i)) l) :
    D.Red (fun i => lin γ (D.β i)) (l * k⁻¹) := by
  obtain ⟨b, hb⟩ := exists_lift k⁻¹
  have h3 := red_comb h hb
  rw [mul_inv_cancel] at h3
  have h4 := cong_of_red red_one h3
  have h0 (i) : lin γ (u i) ∈ loc D.𝔪 X.Λ := by
    obtain ⟨a, -, h'⟩ := h'
    have := add_mem (loc_mono Submodule.smul_le_right (cong_iff.1 (h' i)))
      (le_loc _ (X.Λ.sum_mem (t := Finset.univ) fun j _ => X.Λ.smul_mem (a j i) (D.β_mem j)))
    rwa [sub_add_cancel] at this
  have h2 : X.Λ ≤ (loc D.𝔪 X.Λ).comap (lin γ) ⊔ D.𝔪 • X.Λ := by
    refine D.β_span.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right)
    rintro _ ⟨i, rfl⟩
    refine mem_of_loc (D.β_mem i) le_sup_right ?_
    have := add_mem (loc_mono (le_sup_right (a := (loc D.𝔪 X.Λ).comap (lin γ)))
      (cong_iff.1 (h4 i)))
      (le_loc _ (Submodule.mem_sup_left (((loc D.𝔪 X.Λ).comap (lin γ)).sum_mem
        (t := Finset.univ) fun j _ => Submodule.smul_mem _ (b j i) (x := u j) (h0 j))))
    rwa [sub_add_cancel] at this
  obtain ⟨t, ht, h2⟩ := nakayama X.Λ_fg h2
  have h1 : mapL γ X.Λ ≤ loc D.𝔪 X.Λ := by
    rintro _ ⟨v, hv, rfl⟩
    refine loc_loc ht ?_
    change t • lin γ v ∈ _
    rw [← map_smul]
    exact h2 v hv
  obtain ⟨s, hs, h1⟩ := exists_mul_of_fg (X.Λ_fg.map _) h1
  refine red_congr (fun i => ?_) (red_comb h' hb)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, map_smul] using cong_lin hs (fun v hv => h1 _ ⟨v, hv, rfl⟩) (h4 i)

theorem red_of_dat (hn : r ≤ n) {y : Matrix (Fin n) (Fin r) E} (h : ‖D.dat hn y‖ = 1) :
    ∃ k : D.J, D.Red (fun i => y (Fin.castLE hn i)) k := by
  by_contra H
  rw [Level.dat, dite_eq_right fun H' => H H'.1, norm_zero] at h
  exact zero_ne_one h

variable {w : E} {A A' : AddSubgroup (Matrix (Fin n) (Fin r) E)}
  (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
include idx hs hn

theorem ip_heis_zero (hA : Good X w A) {v : TF n g} (hv : IsVac X bas w A v) {y}
    (hy : y ∉ A) : SW.ip (heisG X bas y v) v = 0 := by
  have h := hA.ip_eq_zero idx hs hn hv hy
  rw [ip_smul_left _ (laws idx hs hn y hv.1).1 hv.1] at h
  exact (mul_eq_zero.1 h).resolve_left (Complex.exp_ne_zero _)

theorem ip_heis_vac (hA : Good X w A) (hA' : Good X w A') {v v' : TF n g}
    (hv : IsVac X bas w A v) (hv' : IsVac X bas w A' v') {t} (ht : ∀ a ∈ A, a + t ∉ A') :
    SW.ip (heisG X bas t v') v = 0 := by
  have hφ := (laws idx hs hn t hv'.1).1
  have hfin := hA.finite idx hs hn hφ
  have hsb : ∀ ψ ∈ hfin.toFinset, IsSB ψ := by
    intro ψ hψ
    obtain ⟨y, -, rfl⟩ := hfin.mem_toFinset.1 hψ
    exact rho_sb idx hs hn y hφ
  obtain ⟨h1, h2⟩ := sum_sb_ip _ hsb hv'.1
  have h3 := congrArg (SW.ip · v') (hA.proj idx hs hn hφ hv).2
  rw [projA, finsum_mem_eq_finite_toFinset_sum _ hfin, ip_smul_left _ h1 hv'.1, h2,
    Finset.sum_eq_zero, mul_zero, ip_smul_left _ hv.1 hv'.1] at h3
  · refine (mul_eq_zero.1 h3.symm).resolve_right fun h => ?_
    have := hA.overlap idx hs hn hA' hv hv'
    simp [h] at this
  · intro ψ hψ
    obtain ⟨a, ha, rfl⟩ := hfin.mem_toFinset.1 hψ
    beta_reduce
    rw [(laws idx hs hn a hv'.1).2.2.1, smul_smul,
      ip_smul_left _ (laws idx hs hn _ hv'.1).1 hv'.1, ip_heis_zero idx hs hn hA' hv' (ht a ha),
      mul_zero]

theorem ip_heis_heis (hA : Good X w A) (hA' : Good X w A') {v v' : TF n g}
    (hv : IsVac X bas w A v) (hv' : IsVac X bas w A' v') {y z}
    (ht : ∀ a ∈ A, a + (-y + z) ∉ A') : SW.ip (heisG X bas z v') (heisG X bas y v) = 0 := by
  rw [← (laws idx hs hn (-y) (laws idx hs hn z hv'.1).1).2.2.2 _ (laws idx hs hn y hv.1).1,
    (laws idx hs hn (-y) hv'.1).2.2.1, (laws idx hs hn (-y) hv.1).2.2.1, neg_add_cancel,
    (laws idx hs hn 0 hv.1).2.1, ip_smul_left _ (laws idx hs hn _ hv'.1).1 (sb_smul _ hv.1),
    ip_smul_right _ (laws idx hs hn _ hv'.1).1 hv.1, ip_heis_vac idx hs hn hA hA' hv hv' ht,
    mul_zero, mul_zero]

theorem isVac_wG {γ : GL (Fin r) E} (hγ : IsUn X γ) {Λ : Lt E n} {L : Lt E r} {v : TF n g}
    (hv : IsVac X bas w (tens Λ L) v) :
    IsVac X bas w (tens Λ (mapL γ L)) (wG X bas idx γ v) := by
  obtain ⟨h1, -, h2, -, -, -, h3⟩ := wG_laws E r X g bas idx n hs hn γ hγ v hv.1
  refine ⟨h1, (h2 v hv.1).1.trans hv.2.1, fun y hy => ?_⟩
  obtain ⟨z, hz, rfl⟩ := tens_mapL hy
  rw [epsW_mul hγ, ← h3, ← (wG_laws E r X g bas idx n hs hn γ hγ _
    (laws idx hs hn z hv.1).1).2.2.2.1, hv.2.2 z hz]

end GlobalTheory.SW.Supp

namespace GlobalTheory.SW

open Lev TensVac Supp

theorem phi_overlap_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ γ, IsUn X γ → γ ∉ D.grp → ∀ L ∈ D.lats, ∀ L' ∈ D.lats, ∀ Λ ∈ Vset E n M, ip (D.phi bas hn v₀ L Λ) (wG X bas idx γ (D.phi bas hn v₀ L' Λ)) = 0 := by
  intro E _ _ _ r X g bas idx n hs he D hn M hM0 hM v₀ hv₀ γ hγ hγ' L hL L' hL' Λ hΛ
  obtain ⟨hsb, hv, H, -⟩ := GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs he D hn M hM0 hM v₀ hv₀ L hL Λ hΛ
  obtain ⟨hsb', hv', -⟩ := GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs he D hn M hM0 hM v₀ hv₀ L' hL' Λ hΛ
  obtain ⟨s, -, hs1, e, e'⟩ := H L' hL'
  generalize unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)) = v at hv e
  generalize unitv (projA X bas D.w (tens Λ (D.sh L')) (v₀ L')) = v' at hv' e'
  have good (L) (hL : SelfD X L) : Good X D.w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ :=
      GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs he D.w D.w_int D.w_tr L hL M Λ hΛ
    exact ⟨h1, h2, h3⟩
  have hA := good _ (selfD_idq D.ne_bot D.proper D.cop hL.1)
  have hA' := good _ (selfD_mapL hγ (selfD_idq D.ne_bot D.proper D.cop hL'.1))
  have hw := isVac_wG idx hs he hγ hv'
  have W := wG_laws E r X g bas idx n hs he γ hγ
  have key : ∀ y ∈ s, ∀ y' ∈ s, SW.ip (heisG X bas y v)
      (heisG X bas (y' * (γ : Matrix (Fin r) (Fin r) E)ᵀ) (wG X bas idx γ v')) = 0 := by
    intro y hy y' hy'
    rw [ip_conj (laws idx hs he _ hw.1).1 (laws idx hs he _ hv.1).1,
      ip_heis_heis idx hs he hA hA' hv hw, map_zero]
    intro a ha h
    obtain ⟨a', ha', h⟩ := tens_mapL h
    obtain ⟨k, hk⟩ := red_of_dat hn (hs1 y hy).2.1
    obtain ⟨k', hk'⟩ := red_of_dat hn (hs1 y' hy').2.1
    have h1 : (y' - a') * (γ : Matrix (Fin r) (Fin r) E)ᵀ = y - a := by
      rw [Matrix.sub_mul, ← h]; abel
    have hsub (p q : Matrix (Fin n) (Fin r) E) (j) : (p - q) j - p j = -q j :=
      sub_sub_cancel_left (p j) (q j)
    have h2 : D.Red (fun i => (y' - a') (Fin.castLE hn i)) k' := red_congr (fun i => by
      rw [cong_iff, hsub]
      exact neg_mem (row_mem hM hΛ hL' ha' _)) hk'
    have h3 : D.Red (fun i => lin γ ((y' - a') (Fin.castLE hn i))) k := red_congr (fun i => by
      rw [cong_iff, ← row_mul, h1, hsub]
      exact neg_mem (row_mem hM hΛ hL ha _)) hk
    exact hγ' ((mem_grp γ).2 ⟨hγ, _, mul_mem k.2 (inv_mem k'.2), red_of_red h2 h3⟩)
  have add {φ ψ : TF n g} (h : IsSB φ) (h' : IsSB ψ) : IsSB (φ + ψ) :=
    (_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ _ _ _ _ h h').1
  have zero {ψ : TF n g} (h : IsSB ψ) : SW.ip 0 ψ = 0 := by simpa using ip_smul_left 0 h h
  have key2 : ∀ y ∈ s, SW.ip (wG X bas idx γ (D.phi bas hn v₀ L' Λ)) (heisG X bas y v) = 0 := by
    intro y hy
    have hy1 := (laws idx hs he y hv.1).1
    rw [e']
    refine (Finset.sum_induction _ (fun φ => IsSB φ ∧ SW.ip (wG X bas idx γ φ) (heisG X bas y v) = 0)
      (fun φ ψ hφ hψ => ⟨add hφ.1 hψ.1, ?_⟩) ⟨isSB_zero, ?_⟩ fun y' hy' => ?_).2
    · rw [((W φ hφ.1).2.2.1 ψ hψ.1).2.1, ip_add_left (W φ hφ.1).1 (W ψ hψ.1).1 hy1, hφ.2, hψ.2,
        add_zero]
    · have := (W 0 isSB_zero).2.2.2.1 0
      rw [zero_smul, zero_smul] at this
      rw [this, zero hy1]
    · have h1 := (laws idx hs he y' hv'.1).1
      refine ⟨sb_smul _ h1, ?_⟩
      rw [(W _ h1).2.2.2.1, ip_smul_left _ (W _ h1).1 hy1, (W _ hv'.1).2.2.2.2.2.2,
        ip_conj hy1 (laws idx hs he _ hw.1).1, key y hy y' hy', map_zero, mul_zero]
  have hW := (W _ hsb').1
  rw [e]
  refine (Finset.sum_induction _ (fun φ => IsSB φ ∧
      SW.ip φ (wG X bas idx γ (D.phi bas hn v₀ L' Λ)) = 0)
    (fun φ ψ hφ hψ => ⟨add hφ.1 hψ.1, ?_⟩) ⟨isSB_zero, zero hW⟩ fun y hy => ?_).2
  · rw [ip_add_left hφ.1 hψ.1 hW, hφ.2, hψ.2, add_zero]
  · have h1 := (laws idx hs he y hv.1).1
    refine ⟨sb_smul _ h1, ?_⟩
    rw [ip_smul_left _ h1 hW, ip_conj hW h1, key2 y hy, map_zero, mul_zero]

end GlobalTheory.SW
end

