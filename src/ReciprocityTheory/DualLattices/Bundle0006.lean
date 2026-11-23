module

public import ReciprocityTheory.DualLattices.Bundle0001
public import ReciprocityTheory.DualLattices.Bundle0003
public import Mathlib
public import ReciprocityTheory.DualLattices.SqZeroOfSpan

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.MapSmulOneMulVec
section
namespace ReciprocityTheory.PGsh

open Matrix

private theorem smul_one_mulVec_dual_lattices {D n : Type*} [CommRing D] [Fintype n] [DecidableEq n] (c : D)
    (v : n → D) : (c • (1 : Matrix n n D)) *ᵥ v = c • v := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

private lemma map_smul_one_mulVec {D K n : Type*} [CommRing D] [Field K] [Algebra D K]
    [Fintype n] [DecidableEq n] (c : D) (v : n → K) :
    ((c • (1 : Matrix n n D)).map (algebraMap D K)) *ᵥ v = c • v := by
  have h : ((c • (1 : Matrix n n D)).map (algebraMap D K)) = (algebraMap D K c) • (1 : Matrix n n K) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [h, smul_one_mulVec_dual_lattices, algebraMap_smul]

private theorem exists_mulVec_eq_smul_of_mul_eq_smul_one {D p n : Type*} [CommRing D] [Fintype n] [Fintype p]
    [DecidableEq p] (H : Matrix p n D) (L : Matrix n p D) (c : D) (h : H * L = c • 1) (f : p → D) :
    ∃ t : n → D, H *ᵥ t = c • f :=
  ⟨L *ᵥ f, by rw [Matrix.mulVec_mulVec, h, smul_one_mulVec_dual_lattices]⟩

private theorem exists_integral_smul_of_mulVec_integral {D K p n : Type*} [CommRing D] [Field K] [Algebra D K]
    [Fintype n] [Fintype p] [DecidableEq p] (B : Matrix p n D) (W : Matrix n p D) (c : D)
    (h : B * W = c • 1) (x : p → K) (w : n → D)
    (hx : W.map (algebraMap D K) *ᵥ x = algebraMap D K ∘ w) :
    ∃ y : p → D, c • x = algebraMap D K ∘ y := by
  refine ⟨B *ᵥ w, ?_⟩
  rw [← map_smul_one_mulVec c x, ← h, Matrix.map_mul, ← Matrix.mulVec_mulVec, hx]
  funext i
  exact (RingHom.map_mulVec (algebraMap D K) B w i).symm

private theorem exists_mulVec_eq_of_mulVec_eq_zero {D K p n : Type*} [CommRing D] [Field K] [Algebra D K]
    [IsFractionRing D K] [Fintype n] [DecidableEq n] [Fintype p] (H B : Matrix p n D)
    (L W : Matrix n p D) (c : D) (hc : c ≠ 0) (h : L * H + W * B = c • 1) (t : n → K)
    (ht : H.map (algebraMap D K) *ᵥ t = 0) :
    ∃ x : p → K, W.map (algebraMap D K) *ᵥ x = t := by
  have hc' : algebraMap D K c ≠ 0 := by
    intro h0
    exact hc (IsFractionRing.injective D K (h0.trans (map_zero _).symm))
  have hmap : L.map (algebraMap D K) * H.map (algebraMap D K)
      + W.map (algebraMap D K) * B.map (algebraMap D K)
      = (c • (1 : Matrix n n D)).map (algebraMap D K) := by
    rw [← h, Matrix.map_add _ (fun a b => map_add (algebraMap D K) a b), Matrix.map_mul,
      Matrix.map_mul]
  have e1 : (L.map (algebraMap D K) * H.map (algebraMap D K)) *ᵥ t = 0 := by
    rw [← Matrix.mulVec_mulVec, ht, Matrix.mulVec_zero]
  have hWB : c • t = (W.map (algebraMap D K) * B.map (algebraMap D K)) *ᵥ t := by
    rw [← map_smul_one_mulVec c t, ← hmap, Matrix.add_mulVec, e1, zero_add]
  refine ⟨(algebraMap D K c)⁻¹ • (B.map (algebraMap D K) *ᵥ t), ?_⟩
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hWB, ← algebraMap_smul K c t,
    inv_smul_smul₀ hc']

theorem a1 : ExistsPointLeviLogNormSqPos := by
  unfold ExistsPointLeviLogNormSqPos
  intro D _ _ g E Φ c hE hdiag hdet hc hΦ
  dsimp only
  have hEinv : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E hdet
  have hF : (Eᵀ)⁻¹ = -E⁻¹ := by
    rw [hE]
    exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, hEinv])
  obtain ⟨N, hN⟩ : ∃ N, N = E⁻¹ * Φᵀ * stdJ D g := ⟨_, rfl⟩
  have hNΦ : N * Φ = c • (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) := by
    rw [hN, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Φᵀ, hΦ, Matrix.mul_smul, hEinv]
  have hdetΦ : Φ.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hNΦ
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have hΦN : Φ * N = c • (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) := by
    have h2 : (Φ * N - c • 1) * Φ = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hNΦ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h3 : Φ.det • (Φ * N - c • 1) = 0 := by
      rw [← Matrix.mul_one (Φ * N - c • 1), ← Matrix.mul_smul, ← Matrix.mul_adjugate Φ,
        ← Matrix.mul_assoc (Φ * N - c • 1) Φ (Matrix.adjugate Φ), h2, Matrix.zero_mul]
    have h4 : Φ * N - c • 1 = 0 := by
      ext i j
      have := congrFun (congrFun h3 i) j
      simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this).resolve_left hdetΦ
    exact sub_eq_zero.mp h4
  have hJJ : stdJ D g * stdJ D g = -1 := by
    rw [stdJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have hG : Φ * E⁻¹ * Φᵀ = -(c • stdJ D g) := by
    have h := congrArg (· * stdJ D g) hΦN
    simp only [hN, Matrix.mul_assoc, hJJ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_neg,
      Matrix.mul_one] at h
    rw [← h, neg_neg, Matrix.mul_assoc]
  have hsub : ∀ r s : Fin g → Fin g ⊕ Fin g,
      Φ.submatrix r id * E⁻¹ * (Φ.submatrix s id)ᵀ = (-(c • stdJ D g)).submatrix r s := by
    intro r s
    rw [← hG]
    ext a b
    rfl
  have hHH : Φ.submatrix Sum.inl id * E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ = 0 := by
    rw [hsub]; ext a b; simp [stdJ]
  have hBH : Φ.submatrix Sum.inr id * E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ
      = -(c • (1 : Matrix (Fin g) (Fin g) D)) := by
    rw [hsub]; ext a b; by_cases h : a = b <;> simp [stdJ, h]
  have hHB : Φ.submatrix Sum.inl id * E⁻¹ * (Φ.submatrix Sum.inr id)ᵀ
      = c • (1 : Matrix (Fin g) (Fin g) D) := by
    rw [hsub]; ext a b; by_cases h : a = b <;> simp [stdJ, h]
  have hJΦ1 : ∀ a j, (stdJ D g * Φ) (Sum.inl a) j = -Φ (Sum.inr a) j := by
    intro a j; simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hJΦ2 : ∀ a j, (stdJ D g * Φ) (Sum.inr a) j = Φ (Sum.inl a) j := by
    intro a j; simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hform : (Φ.submatrix Sum.inr id)ᵀ * Φ.submatrix Sum.inl id
      - (Φ.submatrix Sum.inl id)ᵀ * Φ.submatrix Sum.inr id = c • E := by
    rw [← hΦ]
    ext i j
    rw [Matrix.mul_assoc Φᵀ, Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [hJΦ1, hJΦ2]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      id_eq, mul_neg, Finset.sum_neg_distrib]
    ring
  have hkey : E⁻¹ * (Φ.submatrix Sum.inr id)ᵀ * Φ.submatrix Sum.inl id
      + (-E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ) * Φ.submatrix Sum.inr id = c • 1 := by
    have h := congrArg (E⁻¹ * ·) hform
    simp only [Matrix.mul_sub, Matrix.mul_smul, hEinv] at h
    rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← sub_eq_add_neg]
    exact h
  have h2 : Φ.submatrix Sum.inl id * (-E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ) = 0 := by
    rw [Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hHH, neg_zero]
  have h3 : Φ.submatrix Sum.inr id * (-E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ)
      = c • (1 : Matrix (Fin g) (Fin g) D) := by
    rw [Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hBH, neg_neg]
  have hT : (-E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ)ᵀ = Φ.submatrix Sum.inl id * E⁻¹ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_neg,
      Matrix.transpose_nonsing_inv, hF, neg_neg]
  rw [hF]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact exists_mulVec_eq_smul_of_mul_eq_smul_one _ (E⁻¹ * (Φ.submatrix Sum.inr id)ᵀ) c
      (by rw [← Matrix.mul_assoc]; exact hHB)
  · exact h2
  · exact h3
  · rw [hT, Matrix.mul_assoc (Φ.submatrix Sum.inl id) E⁻¹ E, hEinv, Matrix.mul_one]
    exact h2
  · intro t ht
    exact exists_mulVec_eq_of_mulVec_eq_zero _ _ _ _ c hc hkey t ht
  · rintro x ⟨w, hw⟩
    exact exists_integral_smul_of_mulVec_integral _ _ c h3 x w hw

end ReciprocityTheory.PGsh
end

-- bundled from ReciprocityTheory.DualLattices.MapTensorSpan
section
noncomputable section

namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem map_tensorSpan {X Y : Type} (σ : Y → X) (M : Submodule R (X → C)) :
    (tensorSpan R M).map (LinearMap.funLeft R C (Prod.map σ σ)) =
      tensorSpan R (M.map (LinearMap.funLeft R C σ)) := by
  rw [tensorSpan, tensorSpan, Submodule.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨_, ⟨g, hg, h, hh, rfl⟩, rfl⟩
    exact ⟨_, Submodule.mem_map_of_mem hg, _, Submodule.mem_map_of_mem hh, by
      funext p; simp [LinearMap.funLeft_apply]⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, _, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, h, hh, rfl⟩, by funext p; simp [LinearMap.funLeft_apply]⟩

end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
end
end

-- bundled from ReciprocityTheory.DualLattices.MulIterateRootEqZero
section
noncomputable section

open WittVector Ideal TensorProduct

namespace ReciprocityTheory.PGsh

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

private lemma frob_bij : Function.Bijective (WittVector.frobenius : WittVector p R → WittVector p R) := by
  constructor
  · intro x y h
    ext n
    have h' := congrArg (fun z => WittVector.coeff z n) h
    simp only [WittVector.coeff_frobenius_charP] at h'
    apply (frobeniusEquiv R p).injective
    rw [_root_.frobeniusEquiv_apply, _root_.frobeniusEquiv_apply, frobenius_def, frobenius_def]
    exact h'
  · intro x
    refine ⟨WittVector.mk p (fun n => (frobeniusEquiv R p).symm (x.coeff n)), ?_⟩
    ext n
    rw [WittVector.coeff_frobenius_charP, WittVector.coeff_mk]
    have h := (frobeniusEquiv R p).apply_symm_apply (x.coeff n)
    rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h

lemma mem_span_p_iff (x : WittVector p R) : x ∈ span {(p : WittVector p R)} ↔ x.coeff 0 = 0 := by
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [← WittVector.verschiebung_frobenius, WittVector.verschiebung_coeff_zero]
  · intro hx
    obtain ⟨y, hy⟩ := (frob_bij (p := p) (R := R)).2 (WittVector.mk p (fun n => x.coeff (n + 1)))
    refine Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩
    rw [← WittVector.verschiebung_frobenius, hy]
    ext n
    cases n with
    | zero => rw [WittVector.verschiebung_coeff_zero, hx]
    | succ n => exact WittVector.verschiebung_coeff_succ _ n

lemma p_mul_eq_zero (x : WittVector p R) (h : x * p = 0) : x = 0 := by
  rw [← WittVector.verschiebung_frobenius] at h
  have h2 : WittVector.frobenius x = 0 := by
    ext n
    have h3 := congrArg (fun z => WittVector.coeff z n.succ) h
    simpa only [WittVector.verschiebung_coeff_succ, WittVector.zero_coeff] using h3
  apply (frob_bij (p := p) (R := R)).1
  rw [h2, map_zero]

lemma p_mem_nonZeroDivisors : (p : WittVector p R) ∈ nonZeroDivisors (WittVector p R) := mem_nonZeroDivisors_iff.mpr
  ⟨fun x hx => p_mul_eq_zero x (by rwa [mul_comm] at hx), fun x hx => p_mul_eq_zero x hx⟩

private lemma mul_root_eq_zero (w y : R) (h : w * y = 0) :
    w * (frobeniusEquiv R p).symm y = 0 := by
  have hr : ((frobeniusEquiv R p).symm y) ^ p = y := by
    have h1 := (frobeniusEquiv R p).apply_symm_apply y
    rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h1
  have hz : (w * (frobeniusEquiv R p).symm y) ^ p = 0 := by
    rw [mul_pow, hr]
    calc w ^ p * y = w ^ (p - 1) * (w * y) := by
          rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.out.pos]
      _ = 0 := by rw [h, mul_zero]
  apply (frobeniusEquiv R p).injective
  rw [map_zero, _root_.frobeniusEquiv_apply, frobenius_def, hz]

private lemma mul_iterate_root_eq_zero (w y : R) (h : w * y = 0) (n : ℕ) :
    w * ((frobeniusEquiv R p).symm^[n]) y = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact mul_root_eq_zero w _ ih

end Witt

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type*} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

lemma pflat_mul_eq_zero (hO : ∀ x : O, (p : O) * x = 0 → x = 0) (pflat : PreTilt O p)
    (hpf : pflat.untilt = (p : O)) (x : PreTilt O p) (hx : pflat * x = 0) : x = 0 := by
  have hu0 : (0 : PreTilt O p).untilt = 0 := by
    have h1 : (0 : PreTilt O p).untilt = (p : O) * (0 : PreTilt O p).untilt := by
      rw [← hpf, ← map_mul, mul_zero]
    have hJ := IsAdicComplete.le_jacobson_bot (span {(p : O)}) (Ideal.mem_span_singleton_self (p : O))
    rw [Ideal.mem_jacobson_bot] at hJ
    have h2 : ((p : O) * -1 + 1) * (0 : PreTilt O p).untilt = 0 := by
      linear_combination h1
    exact ((hJ (-1)).mul_right_eq_zero).mp h2
  have hzero : ∀ y : PreTilt O p, pflat * y = 0 → PreTilt.coeff 0 y = 0 := by
    intro y hy
    have h1 : (p : O) * y.untilt = 0 := by rw [← hpf, ← map_mul, hy, hu0]
    rw [← PreTilt.mk_untilt_eq_coeff_zero, hO _ h1, map_zero]
  have hred : ∀ n : ℕ, pflat * ((frobeniusEquiv (PreTilt O p) p).symm^[n]) x = 0 :=
    mul_iterate_root_eq_zero pflat x hx
  have hli : Function.LeftInverse (frobenius (PreTilt O p) p) (frobeniusEquiv (PreTilt O p) p).symm :=
    fun z => by rw [← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  apply Perfection.ext
  intro n
  have key := Perfection.coeff_iterate_frobenius (R := ModP O p) (p := p)
    ((frobeniusEquiv (PreTilt O p) p).symm^[n] x) 0 n
  rw [zero_add] at key
  erw [hli.iterate n x] at key
  exact key.trans ((hzero _ (hred n)).trans (map_zero (Perfection.coeff (ModP O p) p n)).symm)

end Tilt

section Main

variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem regular (hO : ∀ x : O, (p : O) * x = 0 → x = 0) : RegularStatement p O := by
  intro pflat hpf
  refine ⟨p_mem_nonZeroDivisors, ?_, ?_⟩
  · intro x hx
    rw [mem_span_p_iff] at hx ⊢
    rw [WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero] at hx
    exact pflat_mul_eq_zero hO pflat hpf _ hx
  · intro htop
    have h1 : (1 : WittVector p (PreTilt O p)) ∈
        span {(p : WittVector p (PreTilt O p)), teichmuller p pflat} := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨c, e, hce⟩ := Ideal.mem_span_pair.mp h1
    have h2 := congrArg (fun z => WittVector.coeff z 0) hce
    simp only [WittVector.add_coeff_zero, WittVector.mul_coeff_zero,
      WittVector.teichmuller_coeff_zero, WittVector.one_coeff_zero] at h2
    have hp0 : (p : WittVector p (PreTilt O p)).coeff 0 = 0 := by
      rw [← mem_span_p_iff]; exact Ideal.mem_span_singleton_self _
    rw [hp0, mul_zero, zero_add, mul_comm] at h2
    have hu : IsUnit pflat := ⟨⟨pflat, _, h2, by rw [mul_comm]; exact h2⟩, rfl⟩
    have h3 := hu.map (PreTilt.untilt (O := O) (p := p))
    rw [hpf] at h3
    exact (Fact.out : ¬IsUnit (p : O)) h3

end Main

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.QExpansionMonoWCoeffZero
section
namespace ReciprocityTheory.PGsh

open UpperHalfPlane hiding I
open Complex ModularForm ModularFormClass MatrixGroups EisensteinSeries

def monoIdx (w : ℕ) : Finset ℕ :=
  (Finset.range (w + 1)).filter fun a => 4 * a ≤ w ∧ 6 ∣ w - 4 * a

def monoB (w a : ℕ) : ℕ := (w - 4 * a) / 6

theorem monoIdx_wt {w a : ℕ} (h : a ∈ monoIdx w) : 4 * a + 6 * monoB w a = w := by
  simp only [monoIdx, Finset.mem_filter, Finset.mem_range] at h
  obtain ⟨_, h1, h2⟩ := h
  unfold monoB
  omega

noncomputable def monoW (w a : ℕ) : ModularForm 𝒮ℒ (w : ℤ) :=
  if h : 4 * a + 6 * monoB w a = w then
    ModularForm.mcast (by omega) ((E₄.pow a).mul (E₆.pow (monoB w a)))
  else 0

theorem coe_monoW {w a : ℕ} (h : a ∈ monoIdx w) :
    (⇑(monoW w a) : ℍ → ℂ) = (⇑E₄) ^ a * (⇑E₆) ^ monoB w a := by
  simp [monoW, monoIdx_wt h]

theorem qExpansion_monoW {w a : ℕ} (h : a ∈ monoIdx w) :
    qExpansion 1 (monoW w a) =
      PowerSeries.map (Int.castRingHom ℂ) (e4Z ^ a * e6Z ^ monoB w a) := by
  simp only [monoW, monoIdx_wt h, dite_true, ModularForm.qExpansion_mcast]
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, qExpansion_E₄_eq,
    qExpansion_E₆_eq, map_mul, map_pow, map_pow]

theorem qExpansion_monoW_coeff_zero {w a : ℕ} (h : a ∈ monoIdx w) :
    (qExpansion 1 (monoW w a)).coeff 0 = 1 := by
  have h4 : PowerSeries.constantCoeff e4Z = 1 := by simp [e4Z]
  have h6 : PowerSeries.constantCoeff e6Z = 1 := by simp [e6Z]
  rw [qExpansion_monoW h, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, map_pow, map_pow, h4, h6]
  simp

theorem monoIdx_nonempty {w : ℕ} (he : Even w) (h2 : w ≠ 2) : ∃ a, a ∈ monoIdx w := by
  obtain ⟨m, rfl⟩ := he
  simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
  by_cases h : m % 2 = 0
  · exact ⟨(m + m) / 4, by omega, by omega, ⟨0, by omega⟩⟩
  · exact ⟨(m + m - 6) / 4, by omega, by omega, ⟨1, by omega⟩⟩

noncomputable def monoSpanF (w : ℕ) : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ (Set.range fun a : monoIdx w => (⇑(monoW w a) : ℍ → ℂ))

theorem mono_mem_monoSpanF {w a : ℕ} (h : a ∈ monoIdx w) : (⇑(monoW w a) : ℍ → ℂ) ∈ monoSpanF w :=
  Submodule.subset_span ⟨⟨a, h⟩, rfl⟩

theorem mulDisc_mem {w : ℕ} (hw : 12 ≤ w) {φ : ℍ → ℂ} (hφ : φ ∈ monoSpanF (w - 12)) :
    (ModularForm.discriminant : ℍ → ℂ) * φ ∈ monoSpanF w := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hx
    have hwt := monoIdx_wt ha
    have ha3 : a + 3 ∈ monoIdx w := by
      simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ⟨monoB (w - 12) a, by omega⟩⟩
    have ha0 : a ∈ monoIdx w := by
      simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ⟨monoB (w - 12) a + 2, by omega⟩⟩
    have hb3 : monoB w (a + 3) = monoB (w - 12) a := by
      have := monoIdx_wt ha3; omega
    have hb0 : monoB w a = monoB (w - 12) a + 2 := by
      have := monoIdx_wt ha0; omega
    have heq : (ModularForm.discriminant : ℍ → ℂ) * ⇑(monoW (w - 12) a) =
        (1728 : ℂ)⁻¹ • ((⇑(monoW w (a + 3)) : ℍ → ℂ) - ⇑(monoW w a)) := by
      rw [coe_monoW ha, coe_monoW ha3, coe_monoW ha0, hb3, hb0]
      funext z
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
      ring
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (mono_mem_monoSpanF ha3)
      (mono_mem_monoSpanF ha0))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem coe_mem_monoSpanF (w : ℕ) (f : ModularForm 𝒮ℒ (w : ℤ)) : (⇑f : ℍ → ℂ) ∈ monoSpanF w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  rcases Nat.even_or_odd w with he | ho
  · by_cases h2 : w = 2
    · subst h2
      have : f = 0 := rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero f
      subst this
      simp
    obtain ⟨a, ha⟩ := monoIdx_nonempty he h2
    set g := f - (qExpansion 1 f).coeff 0 • monoW w a with hg
    have hgc : (qExpansion 1 g).coeff 0 = 0 :=
      (ModularForm.isCuspForm_iff_coeffZero_eq_zero g).mp
        (ModularForm.sub_smul_isCuspForm f _ (qExpansion_monoW_coeff_zero ha))
    have hfg : (⇑f : ℍ → ℂ) = ⇑g + (qExpansion 1 f).coeff 0 • ⇑(monoW w a) := by
      rw [hg]; simp
    rw [hfg]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (mono_mem_monoSpanF ha))
    by_cases h12 : w < 12
    · have h0 : ModularForm.toCuspForm g hgc = 0 :=
        rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by omega)) _
      have : (⇑g : ℍ → ℂ) = 0 := by
        funext z
        have := congrArg (fun F : CuspForm 𝒮ℒ (w : ℤ) => F z) h0
        simpa using this
      rw [this]; exact Submodule.zero_mem _
    · replace h12 : 12 ≤ w := by omega
      set h := CuspForm.discriminantEquiv (ModularForm.toCuspForm g hgc) with hh
      have hmem := ih (w - 12) (by omega) (ModularForm.mcast (by omega) h)
      have hgd : (⇑g : ℍ → ℂ) = (ModularForm.discriminant : ℍ → ℂ) * ⇑h := by
        have := ModularForm.discriminant_mul_discriminantEquiv (ModularForm.toCuspForm g hgc)
        rw [hh, this]; rfl
      rw [hgd]
      exact mulDisc_mem h12 hmem
  · have : f = 0 := ModularForm.levelOne_odd_weight_eq_zero (by exact_mod_cast ho.natCast) f
    subst this
    simp

end ReciprocityTheory.PGsh
end

-- bundled from ReciprocityTheory.DualLattices.SeriesState
section
namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

def PairingPropertiesStatement (B : BX R₀) : Prop :=
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R), N • x = 0 → N • y = 0 → ∃ z, B.IsPairing N x y z) ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z z' : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x y z' → z = z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x x' y : B.G R) (z z' w : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x' y z' → B.IsPairing N (x + x') y w → w = z * z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y y' : B.G R) (z z' w : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x y' z' → B.IsPairing N x (y + y') w → w = z * z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z z' : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N y x z' → z * z' = 1) ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ), B.IsPairing N x y z → z ^ N = 1) ∧
  (∀ (R S : LAlg R₀) (f : LHom R S) (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N (B.map f x) (B.map f y) (Units.map (f.1 : R →* S) z)) ∧
  (∀ (R : LAlg R₀) (N p : ℕ) (x y : B.G R) (z : (R : Type u)ˣ), N • x = 0 → (N * p) • y = 0 →
    B.IsPairing (N * p) x y z → B.IsPairing N x (p • y) z)

end ReciprocityTheory.PGsh
end

