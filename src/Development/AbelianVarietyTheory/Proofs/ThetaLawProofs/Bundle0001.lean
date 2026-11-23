module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.AlternatingSumChooseMulSubPow
section
namespace GlobalTheory

open Finset

theorem fwdDiff_iter_affine_pow (g : ℕ) (a b y : ℤ) :
    (fwdDiff (1 : ℤ))^[g] (fun r : ℤ => (a * r + b) ^ g) y = g.factorial * a ^ g := by
  have hsplit : (fun r : ℤ => (a * r + b) ^ g) =
      (fun r : ℤ => ∑ k ∈ range g, (a ^ k * b ^ (g - k) * (g.choose k : ℤ)) * r ^ k) +
        a ^ g • (fun r : ℤ => r ^ g) := by
    funext r
    rw [Pi.add_apply, add_pow, sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, Pi.smul_apply,
      smul_eq_mul]
    congr 1
    · exact sum_congr rfl fun k _ => by ring
    · ring
  have hlow : (fwdDiff (1 : ℤ))^[g]
      (fun r : ℤ => ∑ k ∈ range g, (a ^ k * b ^ (g - k) * (g.choose k : ℤ)) * r ^ k) = 0 :=
    fwdDiff_iter_sum_mul_pow_eq_zero _
  rw [hsplit, fwdDiff_iter_add, hlow, fwdDiff_iter_const_smul, fwdDiff_iter_eq_factorial]
  simp [mul_comm]

theorem alternating_sum_choose_mul_sub_pow :
    ∀ g n l : ℕ, g * n ≤ l → ∑ j ∈ Finset.range (g + 1),
      (-1 : ℤ) ^ j * (g.choose j : ℤ) * (((l - j * n) ^ g : ℕ) : ℤ)
        = (g.factorial * n ^ g : ℕ) := by
  intro g n l hgl
  have key := fwdDiff_iter_affine_pow g (-(n : ℤ)) (l : ℤ) 0
  rw [fwdDiff_iter_eq_sum_shift] at key
  simp only [smul_eq_mul, nsmul_eq_mul, zero_add, mul_one] at key
  have hterm : ∀ k ∈ range (g + 1),
      (-1 : ℤ) ^ k * (g.choose k : ℤ) * (((l - k * n) ^ g : ℕ) : ℤ) =
        (-1) ^ g * ((-1 : ℤ) ^ (g - k) * (g.choose k : ℤ) * (-(n : ℤ) * (k : ℤ) + l) ^ g) := by
    intro k hk
    have hkg : k ≤ g := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkn : k * n ≤ l := le_trans (Nat.mul_le_mul_right n hkg) hgl
    have hsign : (-1 : ℤ) ^ k = (-1) ^ g * (-1) ^ (g - k) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkg
      rw [Nat.add_sub_cancel_left, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    rw [hsign, Nat.cast_pow, Nat.cast_sub hkn]
    push_cast
    ring
  rw [sum_congr rfl hterm, ← mul_sum, key]
  have hsq : (-1 : ℤ) ^ g * (-1) ^ g = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  push_cast
  rw [neg_pow]
  linear_combination ((g.factorial : ℤ) * (n : ℤ) ^ g) * hsq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CardHomVanishingOfDiagBasis
section
open Module

namespace GlobalTheory

theorem card_hom_vanishing_of_diag_basis {M A ι : Type} [AddCommGroup M] [AddCommGroup A]
    [Fintype ι] (N : Submodule ℤ M) (b : Basis ι ℤ M) (c : Basis ι ℤ N) (a : ι → ℤ)
    (h : ∀ i, (c i : M) = a i • b i) :
    Nat.card {f : M →ₗ[ℤ] A // ∀ x ∈ N, f x = 0} = ∏ i, Nat.card {y : A // a i • y = 0} := by
  rw [← Nat.card_pi, ← Nat.card_congr (Equiv.subtypePiEquivPi (p := fun i (y : A) => a i • y = 0))]
  symm
  refine Nat.card_congr ((b.constr ℤ).toEquiv.subtypeEquiv fun y => ?_)
  constructor
  · intro hy x hx
    have : (b.constr ℤ y) ∘ₗ N.subtype = 0 := c.ext fun i => by
      simp [h, hy, -Basis.constr_apply_fintype]
    exact LinearMap.congr_fun this ⟨x, hx⟩
  · intro hy i
    have := hy _ (c i).2
    simpa [h, -Basis.constr_apply_fintype] using this

theorem card_ker_int_matrix_four (G : Type) [CommGroup G] (m r : ℕ)
    (al : Matrix (Fin 4) (Fin 4) ℤ) (hm : 1 ≤ m)
    (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hG : ∀ k : ℕ, k ∣ m → Nat.card {x : G // x ^ k = 1} = k ^ r) :
    Nat.card {ξ : Fin 4 → G // ∀ c, ∏ r', ξ r' ^ al r' c = 1} = m ^ (2 * r) := by
  classical
  have hdet : al.det.natAbs = m ^ 2 := by
    have h1 := congrArg Matrix.det hal
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at h1
    have h2 := congrArg Int.natAbs h1
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h2
    exact Nat.mul_self_inj.mp (by rw [h2]; ring)
  have hdet0 : al.det ≠ 0 := by
    intro h0
    rw [h0] at hdet
    have : 0 < m ^ 2 := by positivity
    simp at hdet
    omega
  have hal' : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have hreg := Matrix.isRegular_of_isLeftRegular_det (A := al)
      (IsRegular.of_ne_zero hdet0).left
    apply hreg.right
    simp only [Matrix.mul_assoc, hal]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  set f : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) := Matrix.toLin' al with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet0 (by simpa [hf] using hv)
  set N := LinearMap.range f with hN
  have hrank : finrank ℤ N = finrank ℤ (Fin 4 → ℤ) :=
    (LinearEquiv.ofInjective f hinj).finrank_eq.symm
  let b0 := Pi.basisFun ℤ (Fin 4)
  let a := Submodule.smithNormalFormCoeffs b0 hrank
  let b := Submodule.smithNormalFormTopBasis b0 hrank
  let c := Submodule.smithNormalFormBotBasis b0 hrank
  have hc : ∀ i, (c i : Fin 4 → ℤ) = a i • b i := Submodule.smithNormalFormBotBasis_def b0 hrank
  have hprod : ∏ i, (a i).natAbs = m ^ 2 := by
    have h1 := Submodule.natAbs_det_equiv N (LinearEquiv.ofInjective f hinj)
    rw [Nat.card_congr (Submodule.quotientEquivPiZMod N b0 hrank).toEquiv, Nat.card_pi] at h1
    simp_rw [Nat.card_zmod] at h1
    rw [← h1, ← hdet, ← LinearMap.det_toLin']
    congr 2
  have hdvd : ∀ i, (a i).natAbs ∣ m := by
    intro i
    have hmem : (m : ℤ) • b i ∈ N := ⟨al.transpose.mulVec (b i), by
      simp [hf, Matrix.mulVec_mulVec, hal', Matrix.smul_mulVec]⟩
    have h1 := congrArg (fun x : N => b.repr (x : Fin 4 → ℤ) i) (c.sum_repr ⟨_, hmem⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Submodule.coe_sum, Submodule.coe_smul, hc, map_sum, map_smul, Basis.repr_self,
      Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    exact Int.natAbs_dvd_natAbs.mpr (Dvd.intro_left _ h1)
  have key := card_hom_vanishing_of_diag_basis (A := Additive G) N b c a hc
  have h3 : ∀ i, Nat.card {y : Additive G // a i • y = 0} = (a i).natAbs ^ r := by
    intro i
    rw [← hG _ (hdvd i)]
    refine Nat.card_congr (Additive.toMul.subtypeEquiv fun y => ?_)
    rw [pow_natAbs_eq_one, ← toMul_zsmul, toMul_eq_one]
  simp_rw [h3] at key
  rw [Finset.prod_pow, hprod, ← pow_mul] at key
  rw [← key]
  refine Nat.card_congr (Equiv.subtypeEquiv
    ((Equiv.piCongrRight fun _ => Additive.ofMul).trans (b0.constr ℤ).toEquiv) fun ξ => ?_)
  have h4 : ∀ j, (b0.constr ℤ (fun i => Additive.ofMul (ξ i))) (f (b0 j)) =
      Additive.ofMul (∏ r', ξ r' ^ al r' j) := by
    intro j
    rw [Basis.constr_apply_fintype, ofMul_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [b0, hf, ofMul_zpow]
  constructor
  · rintro hξ _ ⟨x, rfl⟩
    have : (b0.constr ℤ (fun i => Additive.ofMul (ξ i))) ∘ₗ f = 0 :=
      b0.ext fun j => by
        rw [LinearMap.comp_apply, h4, hξ]; rfl
    exact LinearMap.congr_fun this x
  · intro hξ j
    have := hξ (f (b0 j)) ⟨_, rfl⟩
    exact ofMul_eq_zero.mp ((h4 j).symm.trans this)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CoeffEqZeroOfMemSpanPow
section
namespace GlobalTheory.SocleDet

open Matrix

section General

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem det_mul_sub_adjugate_mul_mem (I : Ideal R) (M : Matrix n n R) (x : n → R) (i l : n)
    (h : ∀ r, r ≠ i → (M *ᵥ x) r ∈ I) :
    M.det * x l - M.adjugate l i * (M *ᵥ x) i ∈ I := by
  have h1 : (M.adjugate *ᵥ (M *ᵥ x)) l = M.det * x l := by
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
    simp
  have h2 : (M.adjugate *ᵥ (M *ᵥ x)) l = ∑ r, M.adjugate l r * (M *ᵥ x) r := rfl
  rw [← h1, h2, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
  exact I.sum_mem fun r hr => I.mul_mem_left _ (h r (Finset.ne_of_mem_erase hr))

theorem det_mul_mem (I : Ideal R) (M : Matrix n n R) (x : n → R) (l : n)
    (h : ∀ r, (M *ᵥ x) r ∈ I) : M.det * x l ∈ I := by
  have := det_mul_sub_adjugate_mul_mem I M x l l fun r _ => h r
  have h2 := I.add_mem this (I.mul_mem_left (M.adjugate l l) (h l))
  simpa using h2

theorem adjugate_updateRow (M : Matrix n n R) (i l : n) (v : n → R) :
    (M.updateRow i v).adjugate l i = M.adjugate l i := by
  rw [adjugate_apply, adjugate_apply, updateRow_idem]

theorem adjugate_cross_mem (I : Ideal R) (M : Matrix n n R) (x : n → R) (i j l : n)
    (h : ∀ r, r ≠ i → (M *ᵥ x) r ∈ I) :
    M.adjugate j i * x l - M.adjugate l i * x j ∈ I := by
  have := det_mul_sub_adjugate_mul_mem I (M.updateRow i (Pi.single j 1)) x i l (by
    intro r hr
    have : (M.updateRow i (Pi.single j 1) *ᵥ x) r = (M *ᵥ x) r := by
      simp [mulVec, updateRow_ne hr]
    rw [this]; exact h r hr)
  rw [adjugate_updateRow, ← adjugate_apply] at this
  have e : (M.updateRow i (Pi.single j 1) *ᵥ x) i = x j := by
    simp [mulVec]
  rwa [e] at this

theorem sum_mul_mem_of_syzygy (I : Ideal R) (x C : n → R)
    (hx : ∀ (S : Finset n) (i : n), i ∉ S → ∀ p : R, p * x i ∈ Ideal.span (x '' S) →
      p ∈ Ideal.span (x '' S))
    (hC : ∀ j l, C j * x l - C l * x j ∈ I) (S : Finset n) :
    ∀ s : n → R, ∑ j ∈ S, s j * x j = 0 → ∑ j ∈ S, s j * C j ∈ I := by
  induction S using Finset.induction_on with
  | empty => intro s _; simp
  | insert i S hi ih =>
    intro s hs
    rw [Finset.sum_insert hi] at hs ⊢
    have h1 : s i * x i ∈ Ideal.span (x '' S) := by
      rw [eq_neg_of_add_eq_zero_left hs]
      exact neg_mem (Ideal.sum_mem _ fun j hj =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, hj, rfl⟩))
    obtain ⟨t, ht⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' R).1 (hx S i hi _ h1)
    simp only [smul_eq_mul] at ht
    have h2 := ih (fun j => s j + t j * x i) (by
      rw [← hs, ← ht, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring)
    have h3 : ∑ j ∈ S, t j * (C i * x j - C j * x i) ∈ I :=
      I.sum_mem fun j _ => I.mul_mem_left _ (hC i j)
    have h4 := I.add_mem h2 h3
    convert h4 using 1
    rw [← ht, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem det_sub_det_mem (I : Ideal R) (x : n → R)
    (hx : ∀ (S : Finset n) (i : n), i ∉ S → ∀ p : R, p * x i ∈ Ideal.span (x '' S) →
      p ∈ Ideal.span (x '' S))
    (c c' : Matrix n n R) (h : c *ᵥ x = c' *ᵥ x) (hI : ∀ r, (c *ᵥ x) r ∈ I) :
    c'.det - c.det ∈ I := by
  have key : ∀ S : Finset n, (Matrix.of (fun r j => if r ∈ S then c' r j else c r j)).det - c.det ∈ I := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : Matrix.of (fun r j => if r ∈ (∅ : Finset n) then c' r j else c r j) = c := by
        ext r j; simp
      rw [this]; simp
    | insert i S hi ih =>
      set M : Matrix n n R := Matrix.of (fun r j => if r ∈ S then c' r j else c r j) with hM
      have e1 : Matrix.of (fun r j => if r ∈ insert i S then c' r j else c r j)
          = M.updateRow i (c' i) := by
        ext r j
        by_cases hr : r = i
        · subst hr; simp
        · simp [hM, hr, updateRow_ne hr]
      have e2 : ∀ r, (M *ᵥ x) r = (c *ᵥ x) r := by
        intro r
        by_cases hr : r ∈ S
        · rw [h]
          simp [hM, mulVec, dotProduct, hr]
        · simp [hM, mulVec, dotProduct, hr]
      have h1 := sum_mul_mem_of_syzygy I x (fun j => M.adjugate j i) hx
        (fun j l => adjugate_cross_mem I M x i j l fun r _ => e2 r ▸ hI r) Finset.univ
        (fun j => c' i j - M i j) (by
          have a1 : ∑ j, c' i j * x j = (c *ᵥ x) i := by rw [h]; rfl
          have a2 : ∑ j, M i j * x j = (c *ᵥ x) i := by rw [← e2]; rfl
          simp only [sub_mul, Finset.sum_sub_distrib, a1, a2, sub_self])
      have h2 := I.add_mem h1 ih
      convert h2 using 1
      rw [e1, det_eq_sum_mul_adjugate_row (M.updateRow i (c' i)) i,
        det_eq_sum_mul_adjugate_row M i]
      simp only [adjugate_updateRow, updateRow_self, sub_mul, Finset.sum_sub_distrib]
      ring
  have := key Finset.univ
  have e : Matrix.of (fun r j => if r ∈ (Finset.univ : Finset n) then c' r j else c r j) = c' := by
    ext r j; simp
  rwa [e] at this

end General

section PowerSeries

open MvPowerSeries

variable {k : Type*} [CommRing k] {σ : Type*}

theorem coeff_eq_zero_of_mem_span_pow (N : ℕ) (S : Set σ) (p : MvPowerSeries σ k)
    (hp : p ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k) ^ N) '' S))
    (m : σ →₀ ℕ) (hm : ∀ j ∈ S, m j < N) : coeff m p = 0 := by
  classical
  obtain ⟨t, ht, c, rfl⟩ := (Submodule.mem_span_image_iff_exists_fun _).1 hp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact X_pow_dvd_iff.1 (Dvd.intro_left _ rfl) m (hm j (ht j.2))

theorem mem_span_X_of_coeff (S : Finset σ) : ∀ p : MvPowerSeries σ k,
    (∀ m : σ →₀ ℕ, (∀ j ∈ S, m j = 0) → coeff m p = 0) →
      p ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro p hp
    have : p = 0 := MvPowerSeries.ext fun m => hp m (by simp)
    simp [this]
  | insert i S hi ih =>
    intro p hp
    let q : MvPowerSeries σ k := fun m => if m i = 0 then coeff m p else 0
    have hq : ∀ m, coeff m q = if m i = 0 then coeff m p else 0 := fun _ => rfl
    have h1 : q ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' (insert i S : Finset σ)) := by
      refine Ideal.span_mono (Set.image_mono (by simp)) (ih q fun m hm => ?_)
      rw [hq]
      split_ifs with h
      · refine hp m fun j hj => ?_
        rcases Finset.mem_insert.1 hj with rfl | hj
        exacts [h, hm j hj]
      · rfl
    have h2 : (X i : MvPowerSeries σ k) ∣ p - q :=
      X_dvd_iff.2 fun m hm => by rw [map_sub, hq, if_pos hm, sub_self]
    obtain ⟨r, hr⟩ := h2
    rw [eq_add_of_sub_eq hr]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, by simp, rfl⟩)) h1

theorem mem_span_X_of_mul_X (S : Finset σ) (i : σ) (hi : i ∉ S) (p : MvPowerSeries σ k)
    (hp : p * X i ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' S)) :
    p ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' S) := by
  classical
  refine mem_span_X_of_coeff S p fun m hm => ?_
  have := coeff_eq_zero_of_mem_span_pow 1 S (p * X i) (by simpa using hp)
    (m + Finsupp.single i 1) (fun j hj => by
      have hne : j ≠ i := fun h => hi (h ▸ hj)
      simp [hm j hj, Finsupp.single_eq_of_ne hne])
  rwa [X_def, coeff_add_mul_monomial, mul_one] at this

end PowerSeries

theorem det_notMem_span (k : Type) [Field k] (g N : ℕ) (f : Fin g → MvPowerSeries (Fin g) k)
    (a : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k))
    (hf : ∀ i, f i = ∑ j, a i j * MvPowerSeries.X j)
    (hN : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin g) k) ^ N ∈ Ideal.span (Set.range f)) :
    a.det ∉ Ideal.span (Set.range f) := by
  intro hdet
  set x : Fin g → MvPowerSeries (Fin g) k := fun i => MvPowerSeries.X i with hx
  have hN' : ∀ i, x i ^ (N + 1) ∈ Ideal.span (Set.range f) := fun i => by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ (hN i)
  choose b hb using fun i => Ideal.mem_span_range_iff_exists_fun.1 (hN' i)
  set I : Ideal (MvPowerSeries (Fin g) k) := Ideal.span ((fun i => x i ^ (N + 1)) '' Set.univ)
    with hI
  have hxI : ∀ i, x i ^ (N + 1) ∈ I := fun i => Ideal.subset_span ⟨i, trivial, rfl⟩
  let B : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k) := Matrix.of b
  have hBf : ∀ i, (B *ᵥ f) i = x i ^ (N + 1) := hb
  have haf : a *ᵥ x = f := funext fun i => (hf i).symm
  obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.1 hdet
  have h1 : (B * a).det ∈ I := by
    rw [det_mul, ← hu, Finset.mul_sum]
    refine I.sum_mem fun j _ => ?_
    rw [mul_left_comm]
    exact I.mul_mem_left _ (det_mul_mem I B f j fun r => hBf r ▸ hxI r)
  have h2 := det_sub_det_mem I x mem_span_X_of_mul_X (B * a) (diagonal fun i => x i ^ N)
    (by
      funext i
      rw [← mulVec_mulVec, haf, hBf, mulVec_diagonal, pow_succ])
    (fun r => by rw [← mulVec_mulVec, haf, hBf]; exact hxI r)
  have h3 : ∏ i, x i ^ N ∈ I := by
    simpa [det_diagonal] using I.add_mem h2 h1
  have h4 : ∏ i, x i ^ N = MvPowerSeries.monomial (∑ i, Finsupp.single i N) (1 : k) := by
    simp only [hx, MvPowerSeries.X_pow_eq]
    rw [MvPowerSeries.prod_monomial]
    simp
  have h5 := coeff_eq_zero_of_mem_span_pow (N + 1) Set.univ _ h3 (∑ i, Finsupp.single i N)
    (fun j _ => by simp [Finsupp.finsetSum_apply, Finsupp.single_apply])
  rw [h4, MvPowerSeries.coeff_monomial_same] at h5
  exact one_ne_zero h5

end GlobalTheory.SocleDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DetKroneckerPower
section
namespace GlobalTheory

open Kronecker

theorem det_kroneckerPower (R : Type) [CommRing R] (N r : ℕ) (B : Matrix (Fin N) (Fin N) R) :
    (Matrix.of fun (I I' : Fin (r + 1) → Fin N) => ∏ c, B (I c) (I' c)).det
      = B.det ^ ((r + 1) * N ^ r) := by
  induction r with
  | zero =>
    have h : (Matrix.of fun (I I' : Fin (0 + 1) → Fin N) => ∏ c, B (I c) (I' c))
        = B.submatrix (Equiv.funUnique (Fin 1) (Fin N)) (Equiv.funUnique (Fin 1) (Fin N)) := by
      ext I I'
      simp
    rw [h, Matrix.det_submatrix_equiv_self]
    simp
  | succ r ih =>
    have h : (Matrix.of fun (I I' : Fin (r + 1 + 1) → Fin N) => ∏ c, B (I c) (I' c))
        = (B ⊗ₖ (Matrix.of fun (I I' : Fin (r + 1) → Fin N) => ∏ c, B (I c) (I' c))).submatrix
          (Fin.consEquiv (fun _ : Fin (r + 1 + 1) => Fin N)).symm
          (Fin.consEquiv (fun _ : Fin (r + 1 + 1) => Fin N)).symm := by
      ext I I'
      rw [Matrix.of_apply, Fin.prod_univ_succ]
      rfl
    rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, ih, ← pow_mul, ← pow_add]
    congr 1
    simp only [Fintype.card_fun, Fintype.card_fin]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableOnCoordOfLinearIndependent
section
namespace GlobalTheory

open Filter Topology

theorem differentiableAt_det_of_entries {E I : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype I] [DecidableEq I] (A : E → Matrix I I ℂ) (x : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun e => A e i j) x) :
    DifferentiableAt ℂ (fun e => (A e).det) x := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  exact (HasFDerivAt.finsetProd (fun i _ => (h (σ i) i).hasFDerivAt)).differentiableAt

theorem differentiableOn_coord_of_linearIndependent :
    ∀ (E Z I : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype I] (W : Set E) (Th : I → E → Z → ℂ) (F : E → Z → ℂ) (c : E → I → ℂ), IsOpen W → (∀ k z, DifferentiableOn ℂ (fun e => Th k e z) W) → (∀ z, DifferentiableOn ℂ (fun e => F e z) W) → (∀ e ∈ W, LinearIndependent ℂ (fun k => Th k e)) → (∀ e ∈ W, ∀ z, F e z = ∑ k, c e k * Th k e z) → ∀ k, DifferentiableOn ℂ (fun e => c e k) W := by
  intro E Z I _ _ _ W Th F c hW hTh hF hli hc k e₀ he₀
  classical
  apply DifferentiableAt.differentiableWithinAt
  have hnh : W ∈ 𝓝 e₀ := hW.mem_nhds he₀
  have hspan : Submodule.span ℂ (Set.range (flip (fun k => Th k e₀))) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.2 (hli e₀ he₀)
  have hl : ∀ i : I, ∃ l : Z →₀ ℂ, ∀ j, (∑ z ∈ l.support, l z * Th j e₀ z) = (1 : Matrix I I ℂ) i j := by
    intro i
    have hm : (fun j => (1 : Matrix I I ℂ) i j) ∈
        Submodule.span ℂ (Set.range (flip (fun k => Th k e₀))) := by
      rw [hspan]; trivial
    obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hm
    refine ⟨l, fun j => ?_⟩
    have := congrFun hl j
    simpa [Finsupp.sum, flip, Finset.sum_apply] using this
  choose l hl using hl
  let A : E → Matrix I I ℂ := fun e => Matrix.of fun i j => ∑ z ∈ (l i).support, l i z * Th j e z
  let b : E → I → ℂ := fun e i => ∑ z ∈ (l i).support, l i z * F e z
  have hA0 : A e₀ = 1 := by
    ext i j; exact hl i j
  have hAd : ∀ i j, DifferentiableAt ℂ (fun e => A e i j) e₀ := by
    intro i j
    simp only [A, Matrix.of_apply]
    exact DifferentiableAt.fun_sum fun z _ => ((hTh j z).differentiableAt hnh).const_mul _
  have hbd : ∀ i, DifferentiableAt ℂ (fun e => b e i) e₀ := by
    intro i
    exact DifferentiableAt.fun_sum fun z _ => ((hF z).differentiableAt hnh).const_mul _
  have hdet := differentiableAt_det_of_entries A e₀ hAd
  have hne : (A e₀).det ≠ 0 := by rw [hA0]; simp
  have hnum : DifferentiableAt ℂ (fun e => ((A e).updateCol k (b e)).det) e₀ := by
    refine differentiableAt_det_of_entries _ e₀ fun i j => ?_
    simp only [Matrix.updateCol_apply]
    by_cases h : j = k
    · simpa [h] using hbd i
    · simpa [h] using hAd i j
  have hb : ∀ e ∈ W, b e = (A e).mulVec (c e) := by
    intro e he
    funext i
    simp only [b, A, Matrix.mulVec, dotProduct, Matrix.of_apply, hc e he, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun z _ => by ring
  refine (hnum.mul (hdet.inv hne)).congr_of_eventuallyEq ?_
  filter_upwards [hnh, hdet.continuousAt.eventually_ne hne] with e he hne'
  have h1 : ((A e).updateCol k (b e)).det = (A e).det * c e k := by
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, hb e he, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul]
    simp [Matrix.smul_mulVec]
  simp only [Pi.mul_apply, Pi.inv_apply, h1]
  field_simp

end GlobalTheory
end

