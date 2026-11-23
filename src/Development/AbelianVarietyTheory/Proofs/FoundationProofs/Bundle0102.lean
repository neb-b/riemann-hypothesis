module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormPreservesDeltaPowerCondition
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.NormDelta

def conjM (γ : SL(2, ℤ)) (l : ℕ) (j k B : ℤ) (hB : (l : ℤ) * B = γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0)) : SL(2, ℤ) :=
  ⟨!![γ 0 0 + j * γ 1 0, B; l * γ 1 0, γ 1 1 - k * γ 1 0], by
    have hd := γ.2
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    change γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 at hd
    linear_combination hd - γ 1 0 * hB⟩

open scoped MatrixGroups in
private lemma toGQ_mul_ofSL_eq_ofSL_mul_toGQ (γ γ' : SL(2, ℤ)) (l : ℕ) (hl : 0 < l) (j k B : ℤ)
    (hB : (l : ℤ) * B = γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0))
    (hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![γ 0 0 + j * γ 1 0, B; l * γ 1 0, γ 1 1 - k * γ 1 0]) :
    _root_.GlobalTheory.KZ.toGQ !![1, j; 0, (l : ℤ)] * _root_.GlobalTheory.KZ.ofSL γ =
      _root_.GlobalTheory.KZ.ofSL γ' * _root_.GlobalTheory.KZ.toGQ !![1, k; 0, (l : ℤ)] := by
  have hdet : ∀ m : ℤ, 0 < (!![1, m; 0, (l : ℤ)]).det := by
    intro m
    simp only [Matrix.det_fin_two_of, one_mul, mul_zero, sub_zero]
    exact_mod_cast hl
  unfold _root_.GlobalTheory.KZ.toGQ _root_.GlobalTheory.KZ.ofSL
  rw [dite_eq_left (hdet j), dite_eq_left (hdet k)]
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i i'
  have h00 := congrFun (congrFun hγ' 0) 0
  have h01 := congrFun (congrFun hγ' 0) 1
  have h10 := congrFun (congrFun hγ' 1) 0
  have h11 := congrFun (congrFun hγ' 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at h00 h01 h10 h11
  have hBq : ((l : ℚ) * B = γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0)) := by exact_mod_cast hB
  fin_cases i <;> fin_cases i' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.toGLPos,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, h00, h01, h10, h11] <;>
    first | ring1 | linear_combination -hBq


open scoped MatrixGroups in
theorem _root_.GlobalTheory.NormDelta.norm_delta (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : _root_.GlobalTheory.KZ.Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ)
    (hn : 0 < n) (hlN : ¬ l ∣ N) (f : X.K) (hf : _root_.GlobalTheory.Glue.Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f)
    (hδ : ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, _root_.GlobalTheory.Glue.Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ f * X.sl (_root_.GlobalTheory.KZ.ofSL δ) f = g ^ (l ^ n)) :
    ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, _root_.GlobalTheory.Glue.Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧
        (∏ j ∈ Finset.range l, X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) *
          X.sl (_root_.GlobalTheory.KZ.ofSL δ) (∏ j ∈ Finset.range l, X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) = g ^ (l ^ n) := by
  intro δ hδN hδl
  obtain ⟨g, hg, hfg⟩ := hδ δ hδN hδl
  have hlp : l.Prime := Fact.out
  have hl0 : 0 < l := hlp.pos
  refine ⟨∏ j ∈ Finset.range l,
      X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g,
    _root_.GlobalTheory.normInv_gamma1 Ω ε X N l n hn g hg, ?_⟩
  rw [CongruenceSubgroup.Gamma1_mem] at hδN
  obtain ⟨-, -, hcN⟩ := hδN
  rw [CongruenceSubgroup.Gamma_mem] at hδl
  obtain ⟨ha', hb', hc', hd'⟩ := hδl
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at ha' hb' hc' hd'
  have hlpow : ∀ x : ℤ, ((x : ZMod (l ^ n)) = 0) → (l : ℤ) ∣ x := fun x hx =>
    (dvd_pow_self (l : ℤ) hn.ne').trans (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd x (l ^ n)).1 hx)
  obtain ⟨xa, hxa⟩ := hlpow (δ 0 0 + 1) (by push_cast; linear_combination -ha')
  obtain ⟨xd, hxd⟩ := hlpow (δ 1 1 + 1) (by push_cast; linear_combination -hd')
  obtain ⟨xb, hxb⟩ := hlpow (δ 0 1) (by linear_combination -hb')
  obtain ⟨xc, hxc⟩ := hlpow (δ 1 0) (by linear_combination -hc')
  have hcop : IsCoprime (N : ℤ) ((l : ℤ) ^ n) := by
    have := Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd hlp).2 hlN).symm
    exact_mod_cast Nat.isCoprime_iff_coprime.2 this
  have hcM : ((δ 1 0 : ℤ) : ZMod (N * l ^ n)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    refine hcop.mul_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hcN) ?_
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (δ 1 0) (l ^ n)).1 (by linear_combination -hc')
    exact_mod_cast this
  have hdetM : ((δ 0 0 : ℤ) : ZMod (N * l ^ n)) * (δ 1 1 : ℤ) = 1 := by
    have hdet := δ.2
    rw [Matrix.det_fin_two] at hdet
    have := congrArg (Int.cast : ℤ → ZMod (N * l ^ n)) hdet
    push_cast at this
    rw [hcM] at this
    simpa using this
  rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hB : (l : ℤ) * (xb + j * xd - j * xa - j * j * xc) =
      δ 0 1 + j * δ 1 1 - j * (δ 0 0 + j * δ 1 0) := by
    linear_combination -hxb - j * hxd + j * hxa + j * j * hxc
  have hη : _root_.GlobalTheory.NormDelta.conjM δ l j j _ hB * δ⁻¹ ∈ CongruenceSubgroup.Gamma1 (N * l ^ n) := by
    rw [CongruenceSubgroup.Gamma1_mem, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp only [_root_.GlobalTheory.NormDelta.conjM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons]
    push_cast
    rw [hcM]
    refine ⟨?_, ?_, ?_⟩ <;> first | ring1 | linear_combination hdetM
  have hsplit : _root_.GlobalTheory.KZ.ofSL (_root_.GlobalTheory.NormDelta.conjM δ l j j _ hB) =
      _root_.GlobalTheory.KZ.ofSL (_root_.GlobalTheory.NormDelta.conjM δ l j j _ hB * δ⁻¹) *
        _root_.GlobalTheory.KZ.ofSL δ := by
    rw [← map_mul, inv_mul_cancel_right]
  have hact : X.sl (_root_.GlobalTheory.KZ.ofSL δ)
      (X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) =
      X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)])
        (X.sl (_root_.GlobalTheory.KZ.ofSL δ) f) := by
    rw [← _root_.GlobalTheory.KZ.Tower.sl_mul,
      toGQ_mul_ofSL_eq_ofSL_mul_toGQ δ (_root_.GlobalTheory.NormDelta.conjM δ l j j _ hB) l hl0 j j _ hB rfl,
      _root_.GlobalTheory.KZ.Tower.sl_mul, hsplit,
      _root_.GlobalTheory.KZ.Tower.sl_mul, hf _ hη]
  rw [hact, ← map_mul, hfg, map_pow]

end GlobalTheory.NormDelta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTranslateNormProductEqOfDvd
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem toGQ_mul_pos' (m m' : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (h' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have hmm : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos h h'
  unfold toGQ
  rw [dite_eq_left hmm, dite_eq_left h, dite_eq_left h']
  apply Subtype.ext
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_mul] at *
  exact Matrix.map_mul (f := Int.castRingHom ℚ)

theorem sl_trans_of_lev {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (f : X.K)
    (hf : Lev X M f) (t : ℕ) : X.sl (toGQ !![1, ((t * M : ℕ) : ℤ); 0, 1]) f = f := by
  let γ : SL(2, ℤ) := ⟨!![1, ((t * M : ℕ) : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩
  have hγ : γ ∈ CongruenceSubgroup.Gamma M := by
    rw [CongruenceSubgroup.Gamma_mem]
    simp [γ]
  have e : toGQ !![1, ((t * M : ℕ) : ℤ); 0, 1] = ofSL γ := Betti.toGQ_sl γ
  rw [e]; exact hf γ hγ

theorem Nq_eq_of_dvd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M M' q : ℕ) (f : X.K), 0 < q → M ∣ M' → Nat.Coprime q M' → Lev X M f → Nq X M q f = Nq X M' q f := by
  intro Ω _ _ _ ε X M M' q f hq hdvd hcop hlev
  obtain ⟨e, rfl⟩ := hdvd
  have hqe : Nat.Coprime q e := Nat.Coprime.coprime_dvd_right (dvd_mul_left e M) hcop
  set g : ℕ → X.K := fun i => X.sl (toGQ !![1, ((i : ℤ) * (M : ℤ)); 0, (q : ℤ)]) f with hg
  have step : ∀ j : ℕ, X.sl (toGQ !![1, ((j : ℤ) * ((M * e : ℕ) : ℤ)); 0, (q : ℤ)]) f = g (j * e % q) := by
    intro j
    have hm : !![1, ((j : ℤ) * ((M * e : ℕ) : ℤ)); 0, (q : ℤ)] =
        !![1, (((j * e / q) * M : ℕ) : ℤ); 0, 1] * !![1, (((j * e % q : ℕ) : ℤ) * (M : ℤ)); 0, (q : ℤ)] := by
      have hd := Nat.mod_add_div (j * e) q
      generalize j * e % q = a at hd ⊢
      generalize j * e / q = b at hd ⊢
      have hdz : (a : ℤ) + (q : ℤ) * (b : ℤ) = (j : ℤ) * (e : ℤ) := by exact_mod_cast hd
      ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (M : ℤ) * hdz.symm
    have h1 : (0 : ℤ) < (!![1, (((j * e / q) * M : ℕ) : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two]
    have h2 : (0 : ℤ) < (!![1, (((j * e % q : ℕ) : ℤ) * (M : ℤ)); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two]; exact_mod_cast hq
    rw [hm, toGQ_mul_pos' _ _ h1 h2, X.sl_mul, sl_trans_of_lev X M f hlev]
  have hinj : Set.InjOn (fun j => j * e % q) (Finset.range q : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h' : a * e ≡ b * e [MOD q] := hab
    have := Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.gcd_comm] using hqe) h'
    simpa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  have himg : (Finset.range q).image (fun j => j * e % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨j, _, rfl⟩ := hx
      exact Nat.mod_lt _ hq
    · rw [Finset.card_image_of_injOn hinj]
  unfold Nq
  simp_rw [step]
  show ∏ j ∈ Finset.range q, g j = _
  rw [← Finset.prod_image (f := g) hinj, himg]

end GlobalTheory.KZ.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousPolyCocycleDiffCoboundaryOfEqOn
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

private theorem ent_gamma {K d : ℕ} (hd : d ∣ K) {δ : SL(2, ℤ)} (h : δ ∈ CongruenceSubgroup.Gamma K)
    (i j : Fin 2) :
    (((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod d) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod d) := by
  rw [CongruenceSubgroup.Gamma_mem] at h
  obtain ⟨h00, h01, h10, h11⟩ := h
  have key : ∀ x : ℤ, ∀ y : ZMod K, (x : ZMod K) = y → (x : ZMod d) = ZMod.castHom hd (ZMod d) y := by
    intro x y hxy; rw [← hxy, map_intCast]
  fin_cases i <;> fin_cases j
  · have := key _ _ h00; rw [map_one] at this; simpa using this
  · simpa using key _ _ h01
  · simpa using key _ _ h10
  · have := key _ _ h11; rw [map_one] at this; simpa using this

private theorem gamma_le {K d : ℕ} (hd : d ∣ K) {δ : SL(2, ℤ)} (h : δ ∈ CongruenceSubgroup.Gamma K) :
    δ ∈ CongruenceSubgroup.Gamma d := by
  rw [CongruenceSubgroup.Gamma_mem]
  have e := ent_gamma hd h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using e 0 0
  · simpa using e 0 1
  · simpa using e 1 0
  · simpa using e 1 1

theorem adj_of_near : ∀ (N l w n : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w →
    ∀ z z' : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)), IsCoc w (Gam N l) z → IsCoc w (Gam N l) z' →
    Near z z' → ∃ p : MvPolynomial (Fin 2) (ZMod (l ^ n)), p.IsHomogeneous w ∧
      ∀ γ ∈ Gam N l, z γ - z' γ = slP (γ : Matrix (Fin 2) (Fin 2) ℤ) p - p := by
  intro N l w n hN hl hl2 hlN hw z z' hz hz' hnear
  obtain ⟨M', hM', hM'eq⟩ := hnear
  obtain ⟨e, M, hlM, hMe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM'.ne' l hl.one_lt.ne'
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hMe; omega
    · exact h
  set a := max e n
  obtain ⟨c, hcG, hcomm, hcmod⟩ := _root_.GlobalTheory.KZ.exists_scalar_mod_level N l a M hN hl hl2 hlN hM hlM
  obtain ⟨L1, L2, L3, -, -, L6, L7⟩ := _root_.GlobalTheory.KZ.polySlash_laws (ZMod (l ^ n))
  let R := ZMod (l ^ n)
  let V := MvPolynomial (Fin 2) R
  let G := ↥(Gam N l)
  let ρ : G → V →ₗ[R] V := fun g => (slP ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).toLinearMap
  let S : Submodule R V := MvPolynomial.homogeneousSubmodule (Fin 2) R w
  let K := M * N * l ^ a
  let Δ : Subgroup G := (CongruenceSubgroup.Gamma K).subgroupOf (Gam N l)
  have hρmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v) := by
    intro g h v
    simp only [ρ, AlgHom.toLinearMap_apply, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact L1 _ _ v
  have hρone : ∀ v, ρ 1 v = v := by
    intro v
    simp only [ρ, AlgHom.toLinearMap_apply, OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one]
    exact L2 v
  have h2 : IsUnit (2 : R) := by
    have hc : Nat.Coprime 2 (l ^ n) :=
      Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2))
    exact_mod_cast (ZMod.isUnit_iff_coprime 2 (l ^ n)).mpr hc
  have hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S := by
    intro g v hv
    exact L3 _ w v hv
  have hΔn : Δ.Normal := by
    haveI := CongruenceSubgroup.Gamma_normal (M * N * l ^ a)
    exact Subgroup.normal_subgroupOf
  have hM'K : M' ∣ K := by
    rw [hMe]
    have := mul_dvd_mul (pow_dvd_pow l (le_max_left e n)) (dvd_mul_right M N)
    simpa [K, mul_comm, mul_assoc, mul_left_comm] using this
  have hnK : l ^ n ∣ K := Dvd.dvd.mul_left (pow_dvd_pow l (le_max_right e n)) _
  have hΔ : ∀ δ ∈ Δ, ∀ v, ρ δ v = v := by
    intro δ hδ v
    rw [Subgroup.mem_subgroupOf] at hδ
    simp only [ρ, AlgHom.toLinearMap_apply]
    rw [L6 _ 1 v (ent_gamma hnK hδ), L2 v]
  let c' : G := ⟨c, hcG⟩
  have hc1 : ∀ v ∈ S, ρ c' v = -v := by
    intro v hv
    simp only [ρ, AlgHom.toLinearMap_apply, c']
    have hent : ∀ i j, (((c : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : R) = (((-1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : R) := by
      intro i j
      have h1 := congrArg (ZMod.castHom (pow_dvd_pow l (le_max_right e n)) R) (hcmod i j)
      rw [map_intCast] at h1
      rw [h1]
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl, map_neg, map_one]; simp [Matrix.neg_apply]
      · simp [hij, Matrix.neg_apply, Matrix.one_apply]
    rw [L6 _ _ v hent, L7 w v hv, hw.neg_one_pow, neg_one_smul]
  have hc2 : ∀ g, c' * g * c'⁻¹ * g⁻¹ ∈ Δ := by
    intro g
    rw [Subgroup.mem_subgroupOf]
    exact hcomm g
  let zz : G → V := fun g => z g - z' g
  have hzS : ∀ g, zz g ∈ S := by
    intro g
    exact (hz.1 g g.2).sub (hz'.1 g g.2)
  have hzc : ∀ g h, zz (g * h) = ρ h (zz g) + zz h := by
    intro g h
    have hgh : ((g * h : G) : SL(2, ℤ)) = (g : SL(2, ℤ)) * h := rfl
    simp only [zz, ρ, AlgHom.toLinearMap_apply, map_sub]
    rw [hgh, hz.2 g g.2 h h.2, hz'.2 g g.2 h h.2]
    abel
  have hzΔ : ∀ δ ∈ Δ, zz δ = 0 := by
    intro δ hδ
    rw [Subgroup.mem_subgroupOf] at hδ
    simp only [zz]
    rw [hM'eq _ (gamma_le hM'K hδ), sub_self]
  obtain ⟨p, hpS, hp⟩ := _root_.GlobalTheory.KZ.H3.cocycle_isCoboundary_of_neg_central G R V ρ hρmul hρone h2 S hS Δ hΔn hΔ c' hc1 hc2 zz hzS hzc hzΔ
  refine ⟨p, hpS, fun γ hγ => ?_⟩
  exact hp ⟨γ, hγ⟩

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjugateSL2IntLaws
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.CjLaws

end GlobalTheory.KZ.CjLaws

open Matrix in
open scoped MatrixGroups TensorProduct in
private lemma mul_eq_cj_mul_of_exists {m : Matrix (Fin 2) (Fin 2) ℤ} {δ : SL(2, ℤ)}
    (h : ∃ δ' : SL(2, ℤ), m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m) :
    m * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
      (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m := by
  unfold _root_.GlobalTheory.KZ.H3.cj
  rw [dite_eq_left h]
  exact h.choose_spec

open Matrix in
open scoped MatrixGroups TensorProduct in
private lemma eq_of_mul_eq_mul_of_det_ne_zero {m δ₁ δ₂ : Matrix (Fin 2) (Fin 2) ℤ} (hm : m.det ≠ 0)
    (h : δ₁ * m = δ₂ * m) : δ₁ = δ₂ := by
  have h2 : δ₁ * m * adjugate m = δ₂ * m * adjugate m := by rw [h]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_one] at h2
  exact smul_right_injective _ hm h2

open Matrix in
open scoped MatrixGroups TensorProduct in
private lemma mul_eq_cj_mul_and_cj_mem_gamma (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ) (hm : 0 < m.det)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs)) :
    m * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
        (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧
      _root_.GlobalTheory.KZ.H3.cj m δ ∈ CongruenceSubgroup.Gamma M := by
  set d := m.det with hd
  have hd0 : d ≠ 0 := hm.ne'
  have hN : ((M * d.natAbs : ℕ) : ℤ) = (M : ℤ) * d := by
    push_cast
    rw [abs_of_pos hm]
  have hdvd : ∀ i j, ((M : ℤ) * d) ∣
      (δ : Matrix (Fin 2) (Fin 2) ℤ) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    rw [CongruenceSubgroup.Gamma_mem] at hδ
    obtain ⟨h00, h01, h10, h11⟩ := hδ
    intro i j
    rw [← hN, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    fin_cases i <;> fin_cases j <;> simp_all
  choose X hX using hdvd
  set D : Matrix (Fin 2) (Fin 2) ℤ := 1 + (M : ℤ) • (m * Matrix.of X * adjugate m) with hD
  have hδX : (δ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + ((M : ℤ) * d) • Matrix.of X := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← hX i j]
    ring
  have hDm : D * m = m * (δ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hD, hδX, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      adjugate_mul, ← Matrix.mul_assoc, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_add,
      Matrix.mul_one, Matrix.mul_smul, smul_smul]
  have hdetD : D.det = 1 := by
    have h := congrArg Matrix.det hDm
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one] at h
    exact mul_right_cancel₀ hd0 (by rw [h, one_mul])
  have hex : ∃ δ' : SL(2, ℤ),
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m :=
    ⟨⟨D, hdetD⟩, hDm.symm⟩
  have h1 := mul_eq_cj_mul_of_exists hex
  refine ⟨h1, ?_⟩
  have h2 : (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) = D :=
    eq_of_mul_eq_mul_of_det_ne_zero hd0 (by rw [← h1, hDm])
  rw [CongruenceSubgroup.Gamma_mem, h2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hD, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;>
    push_cast <;> simp

open Matrix in
open scoped MatrixGroups TensorProduct in
theorem _root_.GlobalTheory.KZ.cj_laws : (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ), 0 < m.det →
    ∀ δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs),
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧
        _root_.GlobalTheory.KZ.H3.cj m δ ∈ CongruenceSubgroup.Gamma M) ∧
    (∀ γ δ : SL(2, ℤ), _root_.GlobalTheory.KZ.H3.cj (γ : Matrix (Fin 2) (Fin 2) ℤ) δ = γ * δ * γ⁻¹) ∧
    (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (δ δ' : SL(2, ℤ)), 0 < m.det →
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m →
        ∀ z ∈ _root_.GlobalTheory.KZ.Hs,
          _root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.toGQ m) (_root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.ofSL δ) z) =
            _root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.ofSL δ')
              (_root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.toGQ m) z)) := by
  refine ⟨mul_eq_cj_mul_and_cj_mem_gamma, fun γ δ => ?_, fun m δ δ' hm h => ?_⟩
  · have hex : ∃ δ' : SL(2, ℤ), (γ : Matrix (Fin 2) (Fin 2) ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
        (δ' : Matrix (Fin 2) (Fin 2) ℤ) * γ :=
      ⟨γ * δ * γ⁻¹, by simp [Matrix.mul_assoc, Matrix.adjugate_mul]⟩
    have h1 := mul_eq_cj_mul_of_exists hex
    apply Subtype.ext
    refine eq_of_mul_eq_mul_of_det_ne_zero (m := (γ : Matrix (Fin 2) (Fin 2) ℤ)) (by simp) ?_
    rw [← h1]
    simp [Matrix.mul_assoc, Matrix.adjugate_mul]
  · intro z hz
    obtain ⟨-, hmul, -, -, hcoe, hhom⟩ := _root_.GlobalTheory.KZ.mob_laws
    have hδ : (0 : ℤ) < (δ : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
    have hδ' : (0 : ℤ) < (δ' : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
    rw [← hmul _ _ z hz, ← hmul _ _ z hz, ← hcoe, ← hcoe, ← hhom _ _ hm hδ, ← hhom _ _ hδ' hm, h]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfFiniteComplexAutomorphismOrbit
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FinOrbit

theorem exists_algEquiv_shift (E : Subfield ℂ) (z : ℂ) (hz : Transcendental E z) (k : ℕ) :
    ∃ g : ℂ ≃ₐ[E] ℂ, g z = z + k := by
  classical
  have hind : AlgebraicIndepOn E id ({z} : Set ℂ) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using hz
  obtain ⟨B, hzB, hB⟩ := exists_isTranscendenceBasis_superset hind
  have hzB' : z ∈ B := hzB rfl
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let b0 : B := ⟨z, hzB'⟩
  let f : B → MvPolynomial B E := fun i => if i = b0 then MvPolynomial.X i + (k : MvPolynomial B E)
    else MvPolynomial.X i
  let f' : B → MvPolynomial B E := fun i => if i = b0 then MvPolynomial.X i - (k : MvPolynomial B E)
    else MvPolynomial.X i
  let n : MvPolynomial B E ≃ₐ[E] MvPolynomial B E :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval f) (MvPolynomial.aeval f')
      (by ext i; by_cases h : i = b0 <;> simp [f, f', h])
      (by ext i; by_cases h : i = b0 <;> simp [f, f', h])
  let e := (hB.1.aevalEquiv.symm.trans (n.trans hB.1.aevalEquiv))
  let g0 := IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv
  have hcomm : ∀ c : E, g0 (algebraMap E ℂ c) = algebraMap E ℂ c := by
    intro c
    rw [IsScalarTower.algebraMap_apply E (Algebra.adjoin E (Set.range ((↑) : B → ℂ))) ℂ,
      IsAlgClosure.equivOfEquiv_algebraMap]
    simp
  refine ⟨AlgEquiv.ofRingEquiv (f := g0) hcomm, ?_⟩
  have h1 : algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.X b0)) = z := by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  show g0 z = z + k
  conv_lhs => rw [← h1]
  rw [IsAlgClosure.equivOfEquiv_algebraMap]
  have : e.toRingEquiv (hB.1.aevalEquiv (MvPolynomial.X b0))
      = hB.1.aevalEquiv (MvPolynomial.X b0 + (k : MvPolynomial B E)) := by
    simp [e, n, f]
  rw [this, map_add (f := _), map_natCast, map_add (f := _), map_natCast, h1]

theorem isAlgebraic_of_finite_orbit :
    ∀ (E : Subfield ℂ) (x : ℂ), (Set.range fun g : ℂ ≃ₐ[E] ℂ => g x).Finite → IsAlgebraic E x := by
  intro E x hfin
  by_contra hx
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => x + (k : ℂ)) _ _ hfin
  · intro a b hab
    simpa using hab
  · intro k
    obtain ⟨g, hg⟩ := exists_algEquiv_shift E x hx k
    exact ⟨g, hg⟩

end GlobalTheory.FinOrbit
end

