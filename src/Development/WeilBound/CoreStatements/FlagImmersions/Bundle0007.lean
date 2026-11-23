module

public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0004
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.AltEqZero
section
noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.M5

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def lower (a : Ψ → Fin N → ℕ) (τ : Ψ) (l : Fin N) (m : ℕ) : Ψ → Fin N → ℕ :=
  fun τ' c => if τ' = τ ∧ c = l then a τ' c - m else a τ' c

theorem alt_pk (a : Ψ → Fin N → ℕ) (τ : Ψ) (m : ℕ) (G : RP Ψ N) :
    alt a (pk τ m * G) = ∑ l, if m ≤ a τ l then alt (lower a τ l m) G else 0 := by
  have h1 : ∀ σ : Ψ → Equiv.Perm (Fin N), (pk τ m * G).coeff (expo a σ) =
      ∑ l, if m ≤ a τ l then G.coeff (expo (lower a τ l m) σ) else 0 := by
    intro σ
    rw [← Equiv.sum_comp (σ τ), pk, Finset.sum_mul, coeff_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [X_pow_eq_monomial, coeff_monomial_mul', one_mul]
    have e1 : (Finsupp.single (τ, i) m ≤ expo a σ) ↔ m ≤ a τ (σ τ i) := by
      rw [Finsupp.single_le_iff]; simp [expo]
    have e2 : expo a σ - Finsupp.single (τ, i) m = expo (lower a τ (σ τ i) m) σ := by
      ext ⟨t, b⟩
      simp only [expo, lower, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.equivFunOnFinite_symm_apply_apply,
        Finsupp.single_apply, Prod.mk.injEq]
      by_cases ht : t = τ
      · subst ht
        by_cases hb : b = i
        · subst hb; simp
        · have : ¬ i = b := fun h => hb h.symm
          simp [hb, this]
      · have : ¬ τ = t := fun h => ht h.symm
        simp [ht, this]
    rw [e2]
    by_cases h : m ≤ a τ (σ τ i)
    · rw [if_pos (e1.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (e1.mp h')), if_neg h]
  simp only [alt, h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem alt_perm (a : Ψ → Fin N → ℕ) (π : Ψ → Equiv.Perm (Fin N)) (G : RP Ψ N) :
    alt a G = (∏ τ, ((Equiv.Perm.sign (π τ) : ℤ) : ℝ)) * alt (fun τ c => a τ (π τ c)) G := by
  unfold alt
  rw [← Equiv.sum_comp (Equiv.mulLeft π), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    simp

theorem alt_swap (a b : Ψ → Fin N → ℕ) (τ : Ψ) (p q : Fin N) (hpq : p ≠ q) (G : RP Ψ N)
    (h1 : ∀ c, b τ c = a τ (Equiv.swap p q c)) (h2 : ∀ t, t ≠ τ → b t = a t) :
    alt a G = - alt b G := by
  rw [alt_perm a (Function.update 1 τ (Equiv.swap p q)) G]
  have e : (fun t c => a t (Function.update (1 : Ψ → Equiv.Perm (Fin N)) τ (Equiv.swap p q) t c)) = b := by
    funext t c
    by_cases ht : t = τ
    · subst ht; simp [h1]
    · simp [ht, h2 t ht]
  rw [e, Finset.prod_eq_single τ]
  · simp [Equiv.Perm.sign_swap hpq]
  · intro t _ ht; simp [ht]
  · simp

theorem alt_eq_zero (a : Ψ → Fin N → ℕ) (τ : Ψ) (p q : Fin N) (hpq : p ≠ q) (h : a τ p = a τ q)
    (G : RP Ψ N) : alt a G = 0 := by
  have := alt_swap a a τ p q hpq G (fun c => by
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, h]
    · rw [h2, h]
    · rfl) (fun _ _ => rfl)
  linarith

theorem alt_pk_zero (a : Ψ → Fin N → ℕ) (τ : Ψ) (ha : ∀ c : Fin N, a τ c = N - 1 - (c : ℕ)) (m : ℕ) (hm : 1 ≤ m)
    (G : RP Ψ N) : alt a (pk τ m * G) = 0 := by
  rw [alt_pk]
  refine Finset.sum_eq_zero fun l _ => ?_
  split_ifs with h
  · rw [ha] at h
    have hl := l.isLt
    have hne : l ≠ ⟨l + m, by omega⟩ := fun e => by
      have := congrArg Fin.val e; simp at this; omega
    refine alt_eq_zero _ τ l ⟨l + m, by omega⟩ hne ?_ G
    simp only [lower, true_and, if_true, if_neg hne.symm, ha]
    omega
  · rfl

theorem alt_rho_pk (τ : Ψ) (m : ℕ) (hm : 1 ≤ m) (G : RP Ψ N) : alt rho (pk τ m * G) = 0 :=
  alt_pk_zero rho τ (fun _ => rfl) m hm G

theorem col_sum (τ : Ψ) (k m : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (hm : 1 ≤ m) (G : RP Ψ N) (l : Fin N) :
    (∑ c, if m ≤ bump τ c k τ l then alt (lower (bump τ c k) τ l m) G else 0) =
      if (l : ℕ) + m < N then 0 else if m = k then alt rho G else 0 := by
  have hl := l.isLt
  split_ifs with h1 h2
  · set l' : Fin N := ⟨l + m, h1⟩ with hl'
    have hv : (l' : ℕ) = l + m := rfl
    have hne : l ≠ l' := fun e => by
      have := congrArg Fin.val e; omega
    rw [Finset.sum_eq_add l l' hne]
    · rw [if_pos (by simp [bump]; omega), if_pos (by simp [bump]; omega)]
      rw [alt_swap (lower (bump τ l k) τ l m) (lower (bump τ l' k) τ l m) τ l l' hne G]
      · ring
      · intro c
        rw [Equiv.swap_apply_def]
        split_ifs with c1 c2
        · subst c1
          simp [lower, bump, hne, hne.symm]; omega
        · subst c2
          simp [lower, bump, hne, hne.symm]; omega
        · simp [lower, bump, c1, c2]
      · intro t ht
        funext c
        simp [lower, bump, ht]
    · intro c _ hc
      split_ifs with h
      · refine alt_eq_zero _ τ l l' hne ?_ G
        simp [lower, bump, hne.symm, hc.1.symm, hc.2.symm]; omega
      · rfl
    · simp
    · simp
  · subst h2
    rw [Finset.sum_eq_single l]
    · rw [if_pos (by simp [bump])]
      congr 1
      funext t c
      simp only [lower, bump, rho]
      split_ifs <;> omega
    · intro c _ hc
      rw [if_neg]
      simp [bump, hc.symm]; omega
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with h
    · by_cases hc : l = c
      · subst hc
        simp only [bump, true_and, if_true] at h
        set q : Fin N := ⟨N - 1 - (N - 1 - l + k - m), by omega⟩ with hq
        have hv : (q : ℕ) = N - 1 - (N - 1 - l + k - m) := rfl
        have hne : l ≠ q := fun e => by
          have := congrArg Fin.val e; omega
        refine alt_eq_zero _ τ l q hne ?_ G
        simp only [lower, bump, true_and, if_true, if_neg hne.symm]
        omega
      · exfalso
        simp [bump, hc] at h; omega
    · rfl

theorem lam_pk (τ τ' : Ψ) (k m : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N) (G : RP Ψ N) :
    lam τ k (pk τ' m * G) = if τ' = τ ∧ m = k then (k : ℝ) * alt rho G else 0 := by
  by_cases ht : τ' = τ
  · subst ht
    simp only [lam, alt_pk, true_and]
    rw [Finset.sum_comm]
    simp only [col_sum τ' k m hk hkN hm G]
    by_cases h : m = k
    · subst h
      simp only [if_true]
      rw [Fin.sum_univ_eq_sum_range (fun l => if l + m < N then 0 else alt rho G) N, Finset.sum_ite,
        Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
      have : (Finset.range N).filter (fun l => ¬ l + m < N) = Finset.Ico (N - m) N := by
        ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [this, Nat.card_Ico]
      congr 2; omega
    · simp [h]
  · rw [if_neg (fun h => ht h.1)]
    refine Finset.sum_eq_zero fun c _ => alt_pk_zero _ τ' (fun c' => ?_) m hm G
    simp [bump, ht]

end RootFieldNumerics.M5
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.CoeffShift
section
noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.M5

theorem coeff_lin {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (a : ι →₀ ℕ) (n : ℕ) (h : ∑ x, a x = n) :
    AddMonoidAlgebra.coeff ((∑ x, w x • (X x : MvPolynomial ι ℝ)) ^ n) a =
      (n.factorial : ℝ) * ∏ x, (((a x).factorial : ℝ)⁻¹ * w x ^ a x) := by
  rw [MvPolynomial.coeff_linearCombination_X_pow_of_fintype,
    Finsupp.sum_fintype a (fun _ m => m) (fun _ => rfl)]
  rw [if_pos h, Finsupp.prod_fintype a (fun r m => w r ^ m) (fun _ => pow_zero _),
    ← Finsupp.multinomial_of_support_subset (Finset.subset_univ _),
    Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hpos : (∏ x, ((a x).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun x _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hspec : (∏ x, ((a x).factorial : ℝ)) * (Nat.multinomial Finset.univ a : ℝ) =
      (n.factorial : ℝ) := by
    rw [← h]
    exact_mod_cast Nat.multinomial_spec Finset.univ a
  rw [← hspec]
  generalize (∏ x, ((a x).factorial : ℝ)) = F at hpos ⊢
  generalize (Nat.multinomial Finset.univ a : ℝ) = M
  generalize (∏ x, w x ^ a x) = P
  calc M * P = (F * F⁻¹) * (M * P) := by rw [mul_inv_cancel₀ hpos, one_mul]
    _ = F * M * (F⁻¹ * P) := by ring

theorem coeff_shift {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (x0 : ι) (s n : ℕ) (a : ι →₀ ℕ)
    (h : ∑ x, a x = n + s) :
    AddMonoidAlgebra.coeff (X x0 ^ s * (∑ x, (-w x) • (X x : MvPolynomial ι ℝ)) ^ n) a =
      (-1) ^ n * (n.factorial : ℝ) * (s.factorial : ℝ) *
        (∏ x, (Polynomial.C (((a x).factorial : ℝ)⁻¹) *
          (Polynomial.C (w x) + if x = x0 then Polynomial.X else 0) ^ a x)).coeff s := by
  have hrhs : (∏ x, (Polynomial.C (((a x).factorial : ℝ)⁻¹) *
      (Polynomial.C (w x) + if x = x0 then Polynomial.X else 0) ^ a x)).coeff s =
      (∏ x ∈ Finset.univ.erase x0, (((a x).factorial : ℝ)⁻¹ * w x ^ a x)) *
        (((a x0).factorial : ℝ)⁻¹ * (w x0 ^ (a x0 - s) * ((a x0).choose s : ℝ))) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x0)]
    have hrest : ∏ x ∈ Finset.univ.erase x0, (Polynomial.C (((a x).factorial : ℝ)⁻¹) *
        (Polynomial.C (w x) + if x = x0 then Polynomial.X else 0) ^ a x) =
        Polynomial.C (∏ x ∈ Finset.univ.erase x0, (((a x).factorial : ℝ)⁻¹ * w x ^ a x)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [if_neg (Finset.ne_of_mem_erase hx), add_zero, map_mul, map_pow]
    rw [hrest, Polynomial.coeff_mul_C, if_pos (rfl : x0 = x0), add_comm, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_add_C_pow]
    ring
  rw [hrhs, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul']
  by_cases hs : s ≤ a x0
  · rw [if_pos (Finsupp.single_le_iff.mpr hs), one_mul]
    have e4 : (a - Finsupp.single x0 s) x0 = a x0 - s := by
      rw [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
    have e3 : ∀ x ∈ Finset.univ.erase x0, (a - Finsupp.single x0 s) x = a x := by
      intro x hx
      rw [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
        if_neg (Finset.ne_of_mem_erase hx).symm, tsub_zero]
    have e1 := Finset.add_sum_erase Finset.univ (fun x => a x) (Finset.mem_univ x0)
    have e2 := Finset.add_sum_erase Finset.univ (fun x => (a - Finsupp.single x0 s) x)
      (Finset.mem_univ x0)
    have e3' : ∑ x ∈ Finset.univ.erase x0, (a - Finsupp.single x0 s) x =
        ∑ x ∈ Finset.univ.erase x0, a x := Finset.sum_congr rfl e3
    rw [e4, e3'] at e2
    have hsum : ∑ x, (a - Finsupp.single x0 s) x = n := by omega
    rw [RootFieldNumerics.M5.coeff_lin (fun x => -w x) _ n hsum,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ x0), e4]
    have hrest : ∏ x ∈ Finset.univ.erase x0,
        ((((a - Finsupp.single x0 s) x).factorial : ℝ)⁻¹ * (-w x) ^ (a - Finsupp.single x0 s) x) =
        (-1) ^ (∑ x ∈ Finset.univ.erase x0, a x) *
          ∏ x ∈ Finset.univ.erase x0, (((a x).factorial : ℝ)⁻¹ * w x ^ a x) := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [e3 x hx, neg_pow (w x)]
      ring
    rw [hrest]
    have hsign : ((-1 : ℝ)) ^ n = (-1) ^ (a x0 - s) * (-1) ^ (∑ x ∈ Finset.univ.erase x0, a x) := by
      rw [← pow_add]
      congr 1
      omega
    have hfac : (s.factorial : ℝ) * (((a x0).factorial : ℝ)⁻¹ * ((a x0).choose s : ℝ)) =
        ((a x0 - s).factorial : ℝ)⁻¹ := by
      have hA : ((a x0).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hB : (s.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hD : ((a x0 - s).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      rw [Nat.cast_choose ℝ hs]
      field_simp <;> ring
    rw [hsign, neg_pow (w x0)]
    linear_combination (-((-1 : ℝ) ^ (a x0 - s) * (-1) ^ (∑ x ∈ Finset.univ.erase x0, a x) *
      (n.factorial : ℝ) * (∏ x ∈ Finset.univ.erase x0, (((a x).factorial : ℝ)⁻¹ * w x ^ a x)) *
      w x0 ^ (a x0 - s))) * hfac
  · rw [if_neg fun h' => hs (Finsupp.single_le_iff.mp h'), Nat.choose_eq_zero_of_lt (not_le.mp hs)]
    simp

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def vv (u : Wt Ψ N) (x0 : Ψ × Fin N) (τ : Ψ) (b : Fin N) : Polynomial ℝ :=
  Polynomial.C (u τ b) + if (τ, b) = x0 then Polynomial.X else 0

theorem linRoot_eq (u : Wt Ψ N) : linRoot u = ∑ x : Ψ × Fin N, (-u x.1 x.2) • (X x : RP Ψ N) := by
  unfold GlobalTheory.CompanionTheory.Ar.Top.linRoot
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_neg, neg_mul]

theorem alt_pow (a : Ψ → Fin N → ℕ) (u : Wt Ψ N) (x0 : Ψ × Fin N) (s n : ℕ) (h : ∑ τ, ∑ c, a τ c = n + s) :
    alt a (X x0 ^ s * linRoot u ^ n) =
      (-1) ^ n * (n.factorial : ℝ) * (s.factorial : ℝ) * (∏ τ, gdet (a τ) (vv u x0 τ)).coeff s := by
  have hdet : ∀ τ, RootFieldNumerics.M5.gdet (a τ) (RootFieldNumerics.M5.vv u x0 τ) =
      ∑ π : Equiv.Perm (Fin N), Polynomial.C ((Equiv.Perm.sign π : ℤ) : ℝ) *
        ∏ c, (Polynomial.C (((a τ (π c)).factorial : ℝ)⁻¹) *
          RootFieldNumerics.M5.vv u x0 τ c ^ a τ (π c)) := by
    intro τ
    unfold RootFieldNumerics.M5.gdet
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun π _ => ?_
    simp only [Matrix.of_apply, map_intCast]
  have hsum : ∀ σ : Ψ → Equiv.Perm (Fin N), ∑ x : Ψ × Fin N, RootFieldNumerics.M5.expo a σ x = n + s := by
    intro σ
    rw [← h, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [RootFieldNumerics.M5.expo, Finsupp.equivFunOnFinite_symm_apply_apply]
    exact Equiv.sum_comp (σ τ) (a τ)
  have hq : ∀ σ : Ψ → Equiv.Perm (Fin N),
      (∏ x : Ψ × Fin N, Polynomial.C (((RootFieldNumerics.M5.expo a σ x).factorial : ℝ)⁻¹) *
        (Polynomial.C (u x.1 x.2) + if x = x0 then Polynomial.X else 0) ^ RootFieldNumerics.M5.expo a σ x) =
      ∏ τ, ∏ c, (Polynomial.C (((a τ (σ τ c)).factorial : ℝ)⁻¹) *
        RootFieldNumerics.M5.vv u x0 τ c ^ a τ (σ τ c)) := by
    intro σ
    rw [Fintype.prod_prod_type]
    simp only [RootFieldNumerics.M5.expo, Finsupp.equivFunOnFinite_symm_apply_apply,
      RootFieldNumerics.M5.vv]
  rw [RootFieldNumerics.M5.linRoot_eq]
  unfold RootFieldNumerics.M5.alt
  simp only [hdet]
  rw [Fintype.prod_sum, Polynomial.finsetSum_coeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [RootFieldNumerics.M5.coeff_shift (fun x : Ψ × Fin N => u x.1 x.2) x0 s n
      (RootFieldNumerics.M5.expo a σ) (hsum σ), hq σ, Finset.prod_mul_distrib,
    show (∏ τ, Polynomial.C ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) =
      Polynomial.C (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) from (map_prod Polynomial.C _ _).symm,
    Polynomial.coeff_C_mul]
  ring

theorem sum_rho : ∑ τ : Ψ, ∑ c : Fin N, rho τ c = dimFl Ψ N := by
  have hinner : ∀ τ : Ψ, ∑ c : Fin N, RootFieldNumerics.M5.rho τ c = N * (N - 1) / 2 := by
    intro τ
    simp only [RootFieldNumerics.M5.rho]
    rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N,
      Finset.sum_range_reflect (fun i => i) N, Finset.sum_range_id]
  unfold GlobalTheory.CompanionTheory.Ar.Top.dimFl
  rw [Finset.sum_congr rfl fun τ _ => hinner τ, Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem sum_bump (τ : Ψ) (c : Fin N) (k : ℕ) : ∑ τ' : Ψ, ∑ c' : Fin N, bump τ c k τ' c' = dimFl Ψ N + k := by
  have hsplit : ∀ τ' c', RootFieldNumerics.M5.bump τ c k τ' c' =
      RootFieldNumerics.M5.rho τ' c' + if τ' = τ ∧ c' = c then k else 0 := fun _ _ => rfl
  simp only [hsplit, Finset.sum_add_distrib, RootFieldNumerics.M5.sum_rho, add_right_inj]
  rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp),
    Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
  simp

end RootFieldNumerics.M5
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.IntersectionMultilinearOneSlot
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in
theorem hermLine_ext {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  simp only at ha hh
  subst ha hh
  rfl


open Classical in
noncomputable def indLine (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι where
  a := 0
  h z := if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then 1 else 0
  pos z hz := by rw [if_pos hz]; exact one_pos
  smul c z hc := by
    have : (∀ k, ∃ i, c k * z ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
      simp [hc]
    simp only [this]
    simp

theorem indLine_smooth : IsSmoothHerm (indLine ι) :=
  (contDiffOn_const (c := (1 : ℝ))).congr fun _ hz => if_pos hz

theorem tensor_indLine {A B : HermLine ι} (ha : A.a = B.a)
    (hh : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A.h z = B.h z) :
    A.tensor (indLine ι) = B.tensor (indLine ι) := by
  refine hermLine_ext (by simp [HermLine.tensor, ha]) (funext fun z => ?_)
  by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · show A.h z * _ = B.h z * _
    rw [hh z hz]
  · have : (indLine ι).h z = 0 := if_neg hz
    show A.h z * _ = B.h z * _
    rw [this, mul_zero, mul_zero]

theorem additive_congr (φ : HermLine ι → ℝ)
    (hφ : ∀ A B, IsSmoothHerm A → IsSmoothHerm B → φ (A.tensor B) = φ A + φ B)
    {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (ha : A.a = B.a)
    (hh : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A.h z = B.h z) : φ A = φ B := by
  have h1 := hφ A _ hA indLine_smooth
  have h2 := hφ B _ hB indLine_smooth
  rw [tensor_indLine ha hh] at h1
  linarith

theorem combLine_single {J : Type} [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (j : J) :
    combLine ℓ (Pi.single j 1) = ℓ j := by
  refine hermLine_ext ?_ (funext fun z => ?_)
  · show ∑ i, (Pi.single j 1 : J → ℤ) i • (ℓ i).a = _
    rw [Finset.sum_eq_single j] <;> simp +contextual
  · show ∏ i, (ℓ i).h z ^ (Pi.single j 1 : J → ℤ) i = _
    rw [Finset.prod_eq_single j] <;> simp +contextual

theorem tensor_smooth {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) := ContDiffOn.mul hA hB

theorem additive_comb (φ : HermLine ι → ℝ)
    (hφ : ∀ A B, IsSmoothHerm A → IsSmoothHerm B → φ (A.tensor B) = φ A + φ B)
    {J : Type} [Fintype J] (ℓ : J → HermLine ι) (hℓ : ∀ j, IsSmoothHerm (ℓ j)) (n : J → ℤ) :
    φ (combLine ℓ n) = ∑ j, (n j : ℝ) * φ (ℓ j) := by
  classical
  have hs : ∀ m, IsSmoothHerm (combLine ℓ m) := fun m => (combLine_smooth_conj_invariant K ι J ℓ m).1 hℓ
  let ψ : (J → ℤ) →+ ℝ := AddMonoidHom.mk' (fun m => φ (combLine ℓ m)) (fun m m' => by
    show φ _ = φ _ + φ _
    rw [← hφ _ _ (hs m) (hs m')]
    refine additive_congr φ hφ (hs _) (tensor_smooth (hs m) (hs m')) ?_ fun z hz => ?_
    · show ∑ i, (m + m') i • (ℓ i).a = ∑ i, m i • (ℓ i).a + ∑ i, m' i • (ℓ i).a
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    · show ∏ i, (ℓ i).h z ^ (m + m') i = (∏ i, (ℓ i).h z ^ m i) * ∏ i, (ℓ i).h z ^ m' i
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => zpow_add₀ ((ℓ i).pos z hz).ne' _ _)
  have hn : n = ∑ j, n j • (Pi.single j 1 : J → ℤ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  show ψ n = _
  conv_lhs => rw [hn]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, zsmul_eq_mul]
  show _ * φ (combLine ℓ (Pi.single j 1)) = _
  rw [combLine_single]

end

end Ii

open Ii in
theorem intersection_multilinear_one_position : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (L : Fin d → HermLine ι) (k : Fin d) (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), IsArithVar P d → (∀ i, IsSmoothHerm (L i)) → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (Function.update L k (combLine ℓ n)) = ∑ j, (n j : ℝ) * II K ι P d (Function.update L k (ℓ j)) := by
  intro II hII K _ ι _ P d L k J _ ℓ n hP hL hℓ
  exact additive_comb (fun A => II K ι P d (Function.update L k A))
    (fun A B hA hB => hII.2.1 K ι P d L k A B hP hL hA hB) ℓ hℓ n

end RootFieldNumerics
end

