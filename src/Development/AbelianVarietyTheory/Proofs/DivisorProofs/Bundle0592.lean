module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaTotallyRealAtMostSimplePole
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdeal
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.HasValCong

open scoped Nat

section Ring

variable {B : Type} [CommRing B]

theorem pow_eq_pow_factorization_mul (p : ℕ) (hp : p.Prime) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) :
    ∀ n : ℕ, 0 < n → ∀ x ∈ J, ∃ y ∈ J, x ^ n = (p : B) ^ ((n)!.factorization p) * y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn x hx
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hmn : m < p * m := by
        have := hp.two_le
        nlinarith
      obtain ⟨y, hy, hxy⟩ := hJ x hx
      obtain ⟨y', hy', hyy⟩ := ih m hmn hm y hy
      refine ⟨y', hy', ?_⟩
      rw [Nat.factorization_factorial_mul hp, pow_mul, hxy, mul_pow, hyy, pow_add]
      ring
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact ⟨x, hx, by simp⟩
      obtain ⟨y, hy, hxy⟩ := ih k (by omega) hk x hx
      refine ⟨x * y, J.mul_mem_left x hy, ?_⟩
      have h0 : (k + 1).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
      rw [Nat.factorial_succ, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero k),
        Finsupp.coe_add, Pi.add_apply, h0, zero_add, pow_succ, hxy]
      ring

theorem pow_eq_factorial_mul (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (n : ℕ) (hn : 0 < n) (x : B) (hx : x ∈ J) :
    ∃ y ∈ J, x ^ n = ((n ! : ℕ) : B) * y := by
  obtain ⟨y, hy, hxy⟩ := pow_eq_pow_factorization_mul p hp J hJ n hn x hx
  obtain ⟨u, hu'⟩ := hu (n ! / p ^ (n !).factorization p)
    (Nat.coprime_ordCompl hp (Nat.factorial_ne_zero n)).symm
  refine ⟨(↑u⁻¹ : B) * y, J.mul_mem_left _ hy, ?_⟩
  have hfac : ((n ! : ℕ) : B) =
      (p : B) ^ (n !).factorization p * ((n ! / p ^ (n !).factorization p : ℕ) : B) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  rw [hxy, hfac, ← hu', mul_assoc, ← mul_assoc (u : B), Units.mul_inv, one_mul]

theorem sum_eq_mul_mem {ι : Type} (s : Finset ι) (c : B) (J : Ideal B) (f : ι → B)
    (h : ∀ i ∈ s, ∃ y ∈ J, f i = c * y) : ∃ y ∈ J, ∑ i ∈ s, f i = c * y := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨y, hy, e⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨y', hy', e'⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact ⟨y + y', J.add_mem hy hy', by rw [Finset.sum_insert hi, e, e', mul_add]⟩

theorem add_pow_sub_pow (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (a j : B) (hj : j ∈ J) (n : ℕ) :
    ∃ y ∈ J, (a + j) ^ n - a ^ n = (n : B) * y := by
  rcases n with _ | n
  · exact ⟨0, J.zero_mem, by simp⟩
  rw [add_comm a j, add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
  rw [add_sub_cancel_right]
  apply sum_eq_mul_mem
  intro k _
  obtain ⟨y, hy, hjy⟩ := pow_eq_factorial_mul p hp hu J hJ (k + 1) (Nat.succ_pos k) j hj
  refine ⟨((n.descFactorial k : ℕ) : B) * a ^ (n + 1 - (k + 1)) * y, J.mul_mem_left _ hy, ?_⟩
  have h : (n + 1).choose (k + 1) * (k + 1)! = (n + 1) * n.descFactorial k := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.succ_descFactorial_succ]
  have h' : (((n + 1).choose (k + 1) : ℕ) : B) * (((k + 1)! : ℕ) : B) =
      ((n + 1 : ℕ) : B) * ((n.descFactorial k : ℕ) : B) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, h]
  rw [hjy]
  linear_combination (a ^ (n + 1 - (k + 1)) * y) * h'

end Ring

section Monomial

variable {B : Type} [CommRing B] {σ : Type}

theorem prod_pow_sub_prod_pow (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (α : σ → ℕ) (s : Finset σ) :
    ∃ b : σ → B, (∀ i, b i ∈ J) ∧
      ∏ i ∈ s, z i ^ α i - ∏ i ∈ s, z' i ^ α i = ∑ i ∈ s, (α i : B) * b i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ => J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨b, hb, e⟩ := ih
    obtain ⟨y, hy, ey⟩ := add_pow_sub_pow p hp hu J hJ (z' i) (z i - z' i) (hz i) (α i)
    have hzz : z' i + (z i - z' i) = z i := by ring
    rw [hzz] at ey
    refine ⟨Function.update (fun k => z' i ^ α i * b k) i (y * ∏ k ∈ s, z k ^ α k), ?_, ?_⟩
    · intro k
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self]
        exact J.mul_mem_right _ hy
      · rw [Function.update_of_ne hk]
        exact J.mul_mem_left _ (hb k)
    · rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, Function.update_self]
      have h1 : ∑ k ∈ s, (α k : B) *
          Function.update (fun k => z' i ^ α i * b k) i (y * ∏ k ∈ s, z k ^ α k) k =
          z' i ^ α i * ∑ k ∈ s, (α k : B) * b k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Function.update_of_ne (by rintro rfl; exact hi hk)]
        ring
      rw [h1]
      linear_combination (∏ k ∈ s, z k ^ α k) * ey + z' i ^ α i * e

theorem sum_eq_map_mem {Q : Type} [CommRing Q] [Algebra B Q] {ι : Type} (s : Finset ι)
    (J : Ideal B) (f : ι → Q) (h : ∀ i ∈ s, ∃ b ∈ J, f i = algebraMap B Q b) :
    ∃ b ∈ J, ∑ i ∈ s, f i = algebraMap B Q b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨y, hy, e⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨y', hy', e'⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact ⟨y + y', J.add_mem hy hy', by rw [Finset.sum_insert hi, e, e', map_add (f := _)]⟩

variable [Fintype σ] {Q : Type} [CommRing Q] [Algebra B Q]

theorem monomial_val_sub (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (α : σ →₀ ℕ) (a : Q) (ha : ∀ i, ∃ c : B, (α i : Q) * a = algebraMap B Q c) :
    ∃ b ∈ J, a * (∏ i, algebraMap B Q (z i) ^ α i) - a * ∏ i, algebraMap B Q (z' i) ^ α i =
      algebraMap B Q b := by
  choose c hc using ha
  obtain ⟨b, hb, e⟩ := prod_pow_sub_prod_pow p hp hu J hJ z z' hz α Finset.univ
  refine ⟨∑ i, b i * c i, J.sum_mem (fun i _ => J.mul_mem_right _ (hb i)), ?_⟩
  have e' := congrArg (algebraMap B Q) e
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_prod, map_pow, map_sum, map_mul, map_natCast] at e'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← mul_sub, e', Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← hc i]
  ring

theorem eval_sub_eval (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (P : MvPolynomial σ Q)
    (hP : ∀ (α : σ →₀ ℕ) i, ∃ c : B, (α i : Q) * P.coeff α = algebraMap B Q c) :
    ∃ b ∈ J, MvPolynomial.eval (fun i => algebraMap B Q (z i)) P -
      MvPolynomial.eval (fun i => algebraMap B Q (z' i)) P = algebraMap B Q b := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply sum_eq_map_mem
  intro v _
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  exact monomial_val_sub p hp hu J hJ z z' hz v (P.coeff v) (hP v)

end Monomial

theorem hasVal_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ]
    [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ J : Ideal B,
    (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (z' : σ → B) (f : MvPowerSeries σ Q) (q q' : Q),
    (∀ i, z i - z' i ∈ J) → DIn (⊤ : Ideal B) f → HasVal p z f q → HasVal p z' f q' →
    ∀ m : ℕ, ∃ b ∈ J, ∃ b' : B, q - q' = algebraMap B Q (b + p ^ m * b') := by
  intro p hpf B O Q _ _ _ _ θ hF σ _ _ z _ J hJ z' f q q' hzz hD hv hv' m
  have hp : p.Prime := hpf.out
  obtain ⟨N1, h1⟩ := hv m
  obtain ⟨N2, h2⟩ := hv' m
  obtain ⟨b1, e1⟩ := h1 (max N1 N2) (le_max_left _ _)
  obtain ⟨b2, e2⟩ := h2 (max N1 N2) (le_max_right _ _)
  have hP : ∀ (α : σ →₀ ℕ) i, ∃ c : B, (α i : Q) *
      (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => max N1 N2) f).coeff α =
        algebraMap B Q c := by
    intro α i
    rw [coeff_trunc']
    split_ifs
    · obtain ⟨c, -, hc⟩ := hD α i
      exact ⟨c, hc⟩
    · exact ⟨0, by simp⟩
  obtain ⟨b, hb, e⟩ := eval_sub_eval p hp hF.unit_coprime J hJ z z' hzz _ hP
  refine ⟨b, hb, b1 - b2, ?_⟩
  simp only [map_add (f := _), map_mul, map_sub, map_pow, map_natCast] at e1 e2 ⊢
  linear_combination e1 - e2 + e

end GlobalTheory.HasValCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationOfFunctionalEquation
section
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe : GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo := by
  intro hFE F _ _ _ hf 𝔞 𝔟
  have hD0 : (differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) ∈ (Ideal (𝓞 F))⁰ :=
    mem_nonZeroDivisors_of_ne_zero (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  let D : (Ideal (𝓞 F))⁰ := ⟨_, hD0⟩
  obtain ⟨Zb, Zb', hZb, hZb', hFEb⟩ := hFE F (ClassGroup.mk F 𝔟)⁻¹ (ClassGroup.mk0 D * ClassGroup.mk F 𝔟) D rfl
    (by rw [mul_comm, mul_inv_cancel_right])
  obtain ⟨R, hR, hZR⟩ := _root_.GlobalTheory.ZetaPole.zeta_simple_pole F _ _ Zb Zb' hZb hZb' hFEb
  obtain ⟨Za, Za', hZa, hZa', hFEa⟩ := hFE F (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) (ClassGroup.mk F 𝔞)⁻¹ D rfl
    (mul_inv_cancel_right _ _)
  have hgood : IsGood (gFun Zb 𝔞 𝔟) :=
    _root_.GlobalTheory.HeckeTwo.isGood_add F _ _ (_root_.GlobalTheory.HeckeTwo.isGood_add F _ _ (_root_.GlobalTheory.HeckeTwo.goodConst F _ (_root_.GlobalTheory.HeckeTwo.aPart_differentiableOn F 𝔞)) (GlobalTheory.T.heckeEisensteinZeroFrequencyPart_isSmoothHolomorphic F hf 𝔞 𝔟 Zb R hR hZR))
      (GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_mul_left F _ _ ((kFac_differentiable.mul_const _).differentiableOn) (_root_.GlobalTheory.HeckeTwo.bOne_isGood F 𝔞 𝔟))
  have hdF : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hcK : (cK F 2 : ℂ) ≠ 0 := by
    have : 0 < cK F 2 := by unfold cK; positivity
    exact_mod_cast this.ne'
  have hω : (omegaFactor 𝔞 : ℂ) ≠ 0 := by
    have hn : 0 < nrm 𝔞 := by
      unfold nrm
      have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
        rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
      have h3 := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) h2.symm
      exact_mod_cast h3
    have : 0 < omegaFactor 𝔞 := by unfold omegaFactor; positivity
    exact_mod_cast this.ne'
  have hG0 : ∀ z, gFun Zb 𝔞 𝔟 0 z = aPart 𝔞 0 + kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z := by
    intro z; simp [gFun, bZero]
  have hB : ∀ z ∈ upperHalf F, kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z =
      (∑' c, qClass 𝔞 𝔟 2 z c) * (omegaFactor 𝔞 : ℂ) ^ 2 / (cK F 2 : ℂ) := by
    intro z hz
    rw [← (_root_.GlobalTheory.HeckeTwoExp.bOne_zero_qExpansion F 𝔞 𝔟 z hz).2]
    field_simp
  refine ⟨gFun Zb 𝔞 𝔟, ⟨fun σ hσ z hz => _root_.GlobalTheory.HeckeTwoEq.gFun_eq_eisSum F 𝔞 𝔟 Zb hZb σ hσ z hz, hgood.1, hgood.2⟩, ?_, ?_⟩
  · refine DifferentiableOn.congr (f := fun z => aPart 𝔞 0 + (∑' c, qClass 𝔞 𝔟 2 z c) * ((omegaFactor 𝔞 : ℂ) ^ 2 / (cK F 2 : ℂ)))
      ?_ fun z hz => by rw [hG0, hB z hz, mul_div_assoc]
    apply DifferentiableOn.const_add
    apply DifferentiableOn.mul_const
    exact _root_.GlobalTheory.QHolo.qholo F 𝔞 𝔟
  · refine ⟨Za', hZa', fun z hz => ⟨(_root_.GlobalTheory.HeckeTwoExp.bOne_zero_qExpansion F 𝔞 𝔟 z hz).1, ?_⟩⟩
    rw [hG0, mul_add, add_div, _root_.GlobalTheory.HeckeTwoConst.constant_term F 𝔞 _ D Za Za' rfl (mul_inv_cancel_right _ _) hZa hZa' hFEa,
      (_root_.GlobalTheory.HeckeTwoExp.bOne_zero_qExpansion F 𝔞 𝔟 z hz).2]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomEqZeroOfIsConnOfIsEt
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {k : Type} [Field k]


omit [Field k] in
theorem mem_augIdeal_iff' {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A] (a : A) :
    a ∈ augIdeal R A ↔ counit (R := R) a = 0 := by
  rw [augIdeal, RingHom.mem_ker, Bialgebra.counitAlgHom_apply]

theorem eq_zero_of_app_augIdeal {G H : PDivGroup p k} (f : G ⟶ H)
    (hf : ∀ n, ∀ a ∈ augIdeal k (H.A n), f.app n a = 0) : f = 0 := by
  refine Hom.ext (funext fun n => BialgHom.ext fun a => ?_)
  have hmem : a - algebraMap k (H.A n) (counit (R := k) a) ∈ augIdeal k (H.A n) := by
    rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
      ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  have h := hf n _ hmem
  rw [map_sub, AlgHomClass.commutes, sub_eq_zero] at h
  exact h

variable [Fact p.Prime] [CharP k p] [PerfectRing k p]

theorem exists_augIdeal_pow_eq {A : Type} [CommRing A] [Bialgebra k A] [Module.Finite k A]
    [IsReduced A] (r : ℕ) : ∀ a ∈ augIdeal k A, ∃ b ∈ augIdeal k A, a = b ^ p ^ r := by
  induction r with
  | zero => exact fun a ha => ⟨a, ha, by rw [pow_zero, pow_one]⟩
  | succ r ih =>
    intro a ha
    obtain ⟨b, hb, rfl⟩ := ih a ha
    obtain ⟨c, rfl⟩ := exists_pow_char_eq_of_isReduced_finite p k A b
    refine ⟨c, ?_, by rw [← pow_mul, ← pow_succ']⟩
    rw [mem_augIdeal_iff'] at hb ⊢
    rw [← Bialgebra.counitAlgHom_apply (R := k), map_pow, Bialgebra.counitAlgHom_apply] at hb
    exact pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 hb

theorem eq_zero_of_isConn_of_isEt {G H : PDivGroup p k} (hG : G.IsConn) (hH : H.IsEt)
    (f : G ⟶ H) : f = 0 := by
  refine eq_zero_of_app_augIdeal f fun n a ha => ?_
  haveI := hH n
  haveI : IsNoetherianRing (G.A n) := isNoetherian_of_tower k inferInstance
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical
    (IsNoetherian.noetherian (augIdeal k (G.A n)))).2 fun x hx => mem_nilradical.2 (hG n x hx)
  obtain ⟨b, hb, rfl⟩ := exists_augIdeal_pow_eq (A := H.A n) N a ha
  have hfb : f.app n b ∈ augIdeal k (G.A n) := by
    rw [mem_augIdeal_iff', CoalgHomClass.counit_comp_apply]
    exact (mem_augIdeal_iff' b).1 hb
  have hle : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h1 := Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hfb (p ^ N))
  rw [hN] at h1
  rw [map_pow]
  exact (Submodule.mem_bot _).1 h1

theorem eq_zero_of_isEt_of_isConn {G H : PDivGroup p k} (hG : G.IsConn) (hH : H.IsEt)
    (f : H ⟶ G) : f = 0 := by
  refine eq_zero_of_app_augIdeal f fun n a ha => ?_
  haveI := hH n
  exact ((hG n a ha).map (f.app n)).eq_zero

end PDivGroup

theorem PDivGroup.hom_eq_zero_of_isConn_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
      (G H : PDivGroup p k), G.IsConn → H.IsEt → (∀ f : G ⟶ H, f = 0) ∧ ∀ f : H ⟶ G, f = 0 :=
  fun _ _ _ _ _ _ _ _ hG hH =>
    ⟨PDivGroup.eq_zero_of_isConn_of_isEt hG hH, PDivGroup.eq_zero_of_isEt_of_isConn hG hH⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawIsLinear
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.LawDer.Linear

variable {R : Type} [CommRing R] {d : ℕ}


open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
theorem _root_.GlobalTheory.LawDer.Linear.invDer_linear : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ u : Fin d → R, (∀ F G : MvPowerSeries (Fin d) R, _root_.GlobalTheory.LawDer.invDer μ u (F + G) = _root_.GlobalTheory.LawDer.invDer μ u F + _root_.GlobalTheory.LawDer.invDer μ u G) ∧ (∀ (a : R) (F : MvPowerSeries (Fin d) R), _root_.GlobalTheory.LawDer.invDer μ u (a • F) = a • _root_.GlobalTheory.LawDer.invDer μ u F) ∧ ∀ a : R, _root_.GlobalTheory.LawDer.invDer μ u (C a) = 0 := by
  intro R _ d μ hμ u
  have hμs : HasSubst μ := hasSubst_of_constantCoeff_nilpotent fun i ↦ by simp [hμ i]
  have hzero : HasSubst (Sum.elim (fun i : Fin d ↦ (X i : MvPowerSeries (Fin d) R))
      fun _ : Fin d ↦ (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_nilpotent fun s ↦ by cases s <;> simp
  refine ⟨fun F G ↦ ?_, fun a F ↦ ?_, fun a ↦ ?_⟩
  · unfold _root_.GlobalTheory.LawDer.invDer _root_.GlobalTheory.LawDer.atZero
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [subst_add hμs, map_add (f := _), subst_add hzero, smul_add]
  · unfold _root_.GlobalTheory.LawDer.invDer _root_.GlobalTheory.LawDer.atZero
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [subst_smul hμs, Derivation.map_smul_of_tower, subst_smul hzero, smul_comm]
  · unfold _root_.GlobalTheory.LawDer.invDer _root_.GlobalTheory.LawDer.atZero
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [subst_C, pderiv_C]
    simpa using congrArg (u i • ·) (subst_C (a := Sum.elim
      (fun j : Fin d ↦ (X j : MvPowerSeries (Fin d) R))
      fun _ : Fin d ↦ (0 : MvPowerSeries (Fin d) R)) (0 : R))

end GlobalTheory.LawDer.Linear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawLeibniz
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LawDer

theorem atZero_subst_of_unit (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hc : ∀ i, constantCoeff (μ i) = 0)
    (hu : op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = fun i => X i)
    (F : MvPowerSeries (Fin d) R) : atZero (subst μ F) = F := by
  have hμ : HasSubst μ := hasSubst_of_constantCoeff_zero hc
  have hz : HasSubst (Sum.elim (fun i : Fin d => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by intro s; cases s <;> simp)
  unfold atZero
  rw [subst_comp_subst_apply hμ hz]
  have : (fun i => subst (Sum.elim (fun i : Fin d => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) (μ i))
      = fun i => X i := hu
  rw [this, subst_self]
  rfl

theorem invDer_mul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → ∀ (u : Fin d → R) (F G : MvPowerSeries (Fin d) R), invDer μ u (F * G) = invDer μ u F * G + F * invDer μ u G := by
  intro R _ d μ hc hu u F G
  have hμ : HasSubst μ := hasSubst_of_constantCoeff_zero hc
  have hz : HasSubst (Sum.elim (fun i : Fin d => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by intro s; cases s <;> simp)
  have hmul : ∀ H K : MvPowerSeries (Fin d ⊕ Fin d) R, atZero (H * K) = atZero H * atZero K := by
    intro H K; unfold atZero; exact subst_mul hz H K
  have h0 := atZero_subst_of_unit R d μ hc hu
  have key : ∀ i, atZero (MvPowerSeries.pderiv (Sum.inr i) (subst μ (F * G))) =
      atZero (MvPowerSeries.pderiv (Sum.inr i) (subst μ F)) * G + F * atZero (MvPowerSeries.pderiv (Sum.inr i) (subst μ G)) := by
    intro i
    rw [subst_mul hμ, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    unfold atZero
    rw [subst_add hz, subst_mul hz, subst_mul hz]
    have hF := h0 F; have hG := h0 G; unfold atZero at hF hG
    rw [hF, hG]; ring
  unfold invDer
  simp_rw [key, smul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

end GlobalTheory.LawDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAway
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem IsFrame.isLocalization_away {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O]
    [Algebra B Q] {θ : B →+* O} (h : IsFrame p Q θ) : IsLocalization.Away (p : B) Q := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, k, rfl⟩
    simpa [map_pow, map_natCast] using h.unit_p.pow k
  · intro q
    obtain ⟨k, b, hb⟩ := h.denom q
    refine ⟨⟨b, ⟨(p : B) ^ k, k, rfl⟩⟩, ?_⟩
    simp only [map_pow, map_natCast]
    rw [← hb, mul_comm]
  · intro x y hxy
    exact ⟨1, by simpa using h.inj hxy⟩

theorem frame_fraction_map : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∃ Θ : Q →+* C, ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b) := by
  intro p _ B O Q _ _ _ _ θ hQ C _ _ hC
  haveI := hQ.isLocalization_away
  refine ⟨IsLocalization.Away.lift (p : B) (g := (algebraMap O C).comp θ) ?_, fun b => ?_⟩
  · simpa [map_natCast] using hC.unit_p
  · exact IsLocalization.Away.lift_eq (p : B) _ b

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubSubstIntegralOfIntegralDifferentialStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_sub_subst_integral_of_integral_differential : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries (τ) (Fr p k)) (w : σ → MvPowerSeries τ k) (f : MvPowerSeries (σ) (Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, Red p (u i) (w i)) → (∀ i, Red p (v i) (w i)) → f ∈ quasiInt p k σ → subst u f - subst v f ∈ intBy p k τ p := by
  first | exact @GlobalTheory.Katz.subst_sub_subst_mem_intBy | exact GlobalTheory.Katz.subst_sub_subst_mem_intBy | (intros; apply GlobalTheory.Katz.subst_sub_subst_mem_intBy <;> assumption)
end

