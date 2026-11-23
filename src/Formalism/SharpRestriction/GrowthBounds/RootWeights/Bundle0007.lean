module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalEigen
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diagonal_eigen (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]

theorem gl_rep_shifts_weights {E : GLOps n K V} (hE : IsGLRep E) : OperatorsShiftWeightsByRoots E := by
  intro a b ν x hx
  rw [mem_weightSpace_iff_diagonal_eigen] at hx ⊢
  intro c
  have h1 := congrArg (fun T : Module.End K V => T x) (hE.1 c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at h1
  rw [sub_eq_iff_eq_add] at h1
  rw [h1]
  simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb; simp
  · subst hca
    have : ¬ b = c := fun h => hcb h.symm
    simp [hcb, this]; module
  · subst hcb
    simp [hca]; module
  · have : ¬ b = c := fun h => hcb h.symm
    simp [hca, hcb, this]

theorem findim_weights_bounded [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) : WeightsBounded E := by
  classical
  have hfin : ∀ a, Set.Finite {t : ℤ | (E a a).HasEigenvalue (t : K)} := fun a =>
    (Module.End.finite_hasEigenvalue (E a a)).preimage
      (fun x _ y _ h => by exact_mod_cast h)
  have hT : Set.Finite (⋃ a, {t : ℤ | (E a a).HasEigenvalue (t : K)}) := Set.finite_iUnion hfin
  obtain ⟨m, hm⟩ := (hT.image Int.natAbs).bddAbove
  refine ⟨m, fun ν hν a => ?_⟩
  have hev : (E a a).HasEigenvalue ((ν a : ℤ) : K) := by
    rw [Module.End.hasEigenvalue_iff]
    obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff _ |>.mp hν
    rw [mem_weightSpace_iff_diagonal_eigen] at hx
    rw [Submodule.ne_bot_iff]
    exact ⟨x, Module.End.mem_eigenspace_iff.mpr (hx a), hx0⟩
  have := hm ⟨ν a, Set.mem_iUnion.mpr ⟨a, hev⟩, rfl⟩
  rw [Int.abs_eq_natAbs]
  exact_mod_cast this

theorem diagonal_list_prod_eigen_apply (E : GLOps n K V) (a : Fin n) (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) (k : ℕ) :
    (((List.range k).map fun j : ℕ => E a a - (j : K) • (1 : Module.End K V)).prod) x =
      (∏ j ∈ Finset.range k, ((ν a : K) - (j : K))) • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [(mem_weightSpace_iff_diagonal_eigen E ν x).mp hx a, ← sub_smul, map_smul, ih, smul_smul, mul_comm]

theorem binomial_diagonal_apply_weight [CharZero K] (E : GLOps n K V) (a : Fin n) (ν : Fin n → ℤ) (x : V)
    (hx : x ∈ weightSp E ν) (k : ℕ) :
    binomE E a k x = ((Ring.choose (ν a) k : ℤ) : K) • x := by
  have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hZ : (k.factorial : ℤ) * Ring.choose (ν a) k = ∏ j ∈ Finset.range k, (ν a - (j : ℤ)) := by
    rw [← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval,
      Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  have hK : (k.factorial : K) * ((Ring.choose (ν a) k : ℤ) : K) =
      ∏ j ∈ Finset.range k, ((ν a : K) - (j : K)) := by
    have := congrArg (fun t : ℤ => (t : K)) hZ
    push_cast at this
    exact this
  rw [binomE, LinearMap.smul_apply, diagonal_list_prod_eigen_apply E a ν x hx k, ← hK, smul_smul,
    ← mul_assoc, inv_mul_cancel₀ hk, one_mul]

def ActsByIntegralPolynomial (E : GLOps n K V) (a : Fin n) (g : ℤ → ℤ) : Prop :=
  ∃ u ∈ binomialDiagonalSubring E, ∀ ν, ∀ x ∈ weightSp E ν, u x = ((g (ν a) : ℤ) : K) • x

theorem binomial_polynomial_acts_by_choose [CharZero K] (E : GLOps n K V) (a : Fin n) (i : ℕ) :
    ActsByIntegralPolynomial E a (fun z => Ring.choose z i) := ⟨binomE E a i, Subring.subset_closure ⟨a, i, rfl⟩,
    fun ν x hx => binomial_diagonal_apply_weight E a ν x hx i⟩

theorem action_zero (E : GLOps n K V) (a : Fin n) : ActsByIntegralPolynomial E a (fun _ => 0) := ⟨0, Subring.zero_mem _, fun ν x _ => by simp⟩

theorem binomial_polynomial_action_add {E : GLOps n K V} {a : Fin n} {g h : ℤ → ℤ} (hg : ActsByIntegralPolynomial E a g) (hh : ActsByIntegralPolynomial E a h) :
    ActsByIntegralPolynomial E a (fun z => g z + h z) := by
  obtain ⟨u, hu, hux⟩ := hg
  obtain ⟨v, hv, hvx⟩ := hh
  refine ⟨u + v, Subring.add_mem _ hu hv, fun ν x hx => ?_⟩
  rw [LinearMap.add_apply, hux ν x hx, hvx ν x hx, ← add_smul]
  congr 1
  push_cast
  ring

theorem action_mul_const {E : GLOps n K V} {a : Fin n} {g : ℤ → ℤ} (hg : ActsByIntegralPolynomial E a g) (c : ℤ) :
    ActsByIntegralPolynomial E a (fun z => g z * c) := by
  obtain ⟨u, hu, hux⟩ := hg
  refine ⟨u * ((c : Module.End K V)), Subring.mul_mem _ hu (intCast_mem (binomialDiagonalSubring E) c), fun ν x hx => ?_⟩
  rw [Module.End.mul_apply, Module.End.intCast_apply, map_zsmul, hux ν x hx,
    ← Int.cast_smul_eq_zsmul K, smul_smul]
  congr 1
  push_cast
  ring

theorem action_finset_sum {E : GLOps n K V} {a : Fin n} {ι : Type*} (s : Finset ι) (g : ι → ℤ → ℤ)
    (hg : ∀ i ∈ s, ActsByIntegralPolynomial E a (g i)) : ActsByIntegralPolynomial E a (fun z => ∑ i ∈ s, g i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using action_zero E a
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact binomial_polynomial_action_add (hg i (Finset.mem_insert_self i s))
      (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem binomial_shifted_action [CharZero K] (E : GLOps n K V) (a : Fin n) (m k : ℕ) :
    ActsByIntegralPolynomial E a (fun z => Ring.choose (z + (m : ℤ)) k) := by
  have h : (fun z : ℤ => Ring.choose (z + (m : ℤ)) k) = fun z =>
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, Ring.choose z ij.1 * Ring.choose (m : ℤ) ij.2 := by
    funext z
    exact Ring.add_choose_eq k (Commute.all z (m : ℤ))
  rw [h]
  exact action_finset_sum _ _ fun ij _ => action_mul_const (binomial_polynomial_acts_by_choose E a ij.1) _

private theorem exists_binomial_transform_inverse (f : ℕ → ℤ) (M : ℕ) : ∃ d : ℕ → ℤ, ∀ N ≤ M,
    ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * d k = f N := by
  induction M with
  | zero =>
    refine ⟨fun _ => f 0, fun N hN => ?_⟩
    obtain rfl : N = 0 := Nat.le_zero.mp hN
    simp
  | succ M ih =>
    obtain ⟨d, hd⟩ := ih
    set s := ∑ j ∈ Finset.range (M + 1), ((M + 1).choose j : ℤ) * d j with hs
    refine ⟨fun k => if k = M + 1 then f (M + 1) - s else d k, fun N hN => ?_⟩
    beta_reduce
    rcases Nat.lt_or_ge N (M + 1) with h | h
    · have e : ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * (if k = M + 1 then f (M + 1) - s else d k)
          = ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * d k :=
        Finset.sum_congr rfl fun k hk => by rw [if_neg (by simp at hk; omega)]
      rw [e, hd N (by omega)]
    · obtain rfl : N = M + 1 := by omega
      rw [Finset.sum_range_succ]
      have e : ∑ k ∈ Finset.range (M + 1), ((M + 1).choose k : ℤ) *
          (if k = M + 1 then f (M + 1) - s else d k) = s := by
        rw [hs]
        exact Finset.sum_congr rfl fun k hk => by rw [if_neg (by simp at hk; omega)]
      rw [e]
      simp

theorem newton_interpolation_indicator (m : ℕ) (c : ℤ) : ∃ d : ℕ → ℤ, ∀ z : ℤ, |z| ≤ (m : ℤ) →
    ∑ k ∈ range (2 * m + 1), Ring.choose (z + (m : ℤ)) k * d k = if z = c then 1 else 0 := by
  obtain ⟨d, hd⟩ := exists_binomial_transform_inverse (fun N => if (N : ℤ) - (m : ℤ) = c then 1 else 0) (2 * m)
  refine ⟨d, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := abs_le.mp hz
  obtain ⟨N, hN⟩ : ∃ N : ℕ, z + (m : ℤ) = N := ⟨(z + m).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hN2 : N ≤ 2 * m := by omega
  rw [hN]
  have hc : ∀ k ∈ range (2 * m + 1), Ring.choose (N : ℤ) k * d k = (N.choose k : ℤ) * d k := by
    intro k _
    rw [Ring.choose_natCast]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_range_add_sum_Ico _ (show N + 1 ≤ 2 * m + 1 by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (N + 1) (2 * m + 1)) (fun k hk => by
      rw [Nat.choose_eq_zero_of_lt (by simp at hk; omega)]; simp), add_zero, hd N hN2]
  obtain rfl : z = (N : ℤ) - m := by omega
  rfl

theorem binomial_indicator_exists [CharZero K] (E : GLOps n K V) (a : Fin n) (m : ℕ)
    (hm : ∀ ν, weightSp E ν ≠ ⊥ → ∀ a, |ν a| ≤ (m : ℤ)) (c : ℤ) :
    ∃ u ∈ binomialDiagonalSubring E, ∀ ν, ∀ x ∈ weightSp E ν, u x = if ν a = c then x else 0 := by
  obtain ⟨d, hd⟩ := newton_interpolation_indicator m c
  obtain ⟨u, hu, hux⟩ := action_finset_sum (E := E) (a := a) (range (2 * m + 1))
    (fun k z => Ring.choose (z + (m : ℤ)) k * d k)
    (fun k _ => action_mul_const (binomial_shifted_action E a m k) (d k))
  refine ⟨u, hu, fun ν x hx => ?_⟩
  rw [hux ν x hx]
  by_cases h0 : weightSp E ν = ⊥
  · have : x = 0 := by rw [h0] at hx; exact (Submodule.mem_bot K).mp hx
    subst this
    simp
  · simp only [hd (ν a) (hm ν h0 a)]
    split_ifs <;> simp

theorem weight_projections_integral_findim [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) : WeightProjectionsIntegralBinomial E := by
  obtain ⟨m, hm⟩ := findim_weights_bounded E
  have h := fun (μ : Fin n → ℤ) (a : Fin n) => binomial_indicator_exists E a m hm (μ a)
  choose u hu hux using h
  refine ⟨fun μ => ((List.finRange n).map (u μ)).prod, fun μ => ?_, fun μ ν x hx => ?_⟩
  · apply Subring.list_prod_mem
    intro y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
    exact hu μ a
  · have key : ∀ L : List (Fin n),
        (L.map (u μ)).prod x = if ∀ a ∈ L, ν a = μ a then x else 0 := by
      intro L
      induction L with
      | nil => simp
      | cons b L ih =>
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
        by_cases hL : ∀ a ∈ L, ν a = μ a
        · rw [if_pos hL, hux μ b ν x hx]
          by_cases hb : ν b = μ b
          · rw [if_pos hb, if_pos (fun a ha => by rcases List.mem_cons.mp ha with rfl | ha; exacts [hb, hL a ha])]
          · rw [if_neg hb, if_neg (fun h => hb (h b (List.mem_cons.mpr (Or.inl rfl))))]
        · rw [if_neg hL, map_zero, if_neg (fun h => hL fun a ha => h a (List.mem_cons_of_mem _ ha))]
    show ((List.finRange n).map (u μ)).prod x = _
    rw [key]
    by_cases h : ν = μ
    · subst h
      simp
    · rw [if_neg h, if_neg]
      intro h'
      exact h (funext fun a => h' a (List.mem_finRange a))

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.PolarizationDividedPowerSumSucc
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section v2dpAbs

variable {R : Type*} [CommRing R] {σ ι : Type*} [DecidableEq ι]

def dividedPowerExponent (src dst : ι → σ) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : σ →₀ ℕ :=
  (m - Finsupp.mapDomain src f) + Finsupp.mapDomain dst f

def dividedPowerCoefficient (sg : ι → R) (src : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : R :=
  ∏ l ∈ s, sg l ^ (f l) * ((m (src l)).choose (f l) : R)

def dividedPowerMonomialTerm (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : MvPolynomial σ R :=
  monomial (dividedPowerExponent src dst m f) (dividedPowerCoefficient sg src s m f)

def dividedPowerMonomialSum (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (k : ℕ) (m : σ →₀ ℕ) : MvPolynomial σ R :=
  ∑ f ∈ Finset.finsuppAntidiag s k, dividedPowerMonomialTerm sg src dst s m f

def polarizationDerivation (sg : ι → R) (src dst : ι → σ) (l : ι) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  sg l • ((LinearMap.mulLeft R (X (dst l))) ∘ₗ (pderiv (src l)).toLinearMap)

theorem polarization_dividedPowerTerm (sg : ι → R) (src dst : ι → σ) (hs : Function.Injective src) (hd : ∀ l l', dst l' ≠ src l)
    (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) (l : ι) (hl : l ∈ s) :
    polarizationDerivation sg src dst l (dividedPowerMonomialTerm sg src dst s m f) =
      (f l + 1) • dividedPowerMonomialTerm sg src dst s m (f + Finsupp.single l 1) := by
  classical
  have h1 : Finsupp.mapDomain src f (src l) = f l := Finsupp.mapDomain_apply_of_injective hs f l
  have h2 : ∀ g : ι →₀ ℕ, Finsupp.mapDomain dst g (src l) = 0 := fun g =>
    Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨l', h⟩; exact hd l l' h)
  have hexp : Finsupp.single (dst l) 1 + (dividedPowerExponent src dst m f - Finsupp.single (src l) 1) =
      dividedPowerExponent src dst m (f + Finsupp.single l 1) := by
    ext v
    simp only [dividedPowerExponent, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.add_apply,
      Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hv : src l = v
    · subst hv
      have h3 := hd l l
      simp only [h1, h2, h3, if_true, if_false]
      omega
    · simp only [hv, if_false]
      omega
  have he : dividedPowerExponent src dst m f (src l) = m (src l) - f l := by
    simp [dividedPowerExponent, h1, h2]
  have hcf : sg l * (dividedPowerCoefficient sg src s m f * ((dividedPowerExponent src dst m f (src l) : ℕ) : R)) =
      ((f l + 1 : ℕ) : R) * dividedPowerCoefficient sg src s m (f + Finsupp.single l 1) := by
    rw [he]
    unfold dividedPowerCoefficient
    rw [← Finset.mul_prod_erase s _ hl, ← Finset.mul_prod_erase s _ hl]
    have h4 : ∏ x ∈ s.erase l, sg x ^ ((f + Finsupp.single l 1 : ι →₀ ℕ) x) *
        ((m (src x)).choose ((f + Finsupp.single l 1 : ι →₀ ℕ) x) : R) =
        ∏ x ∈ s.erase l, sg x ^ (f x) * ((m (src x)).choose (f x) : R) := by
      apply Finset.prod_congr rfl
      intro x hx
      have hx' : x ≠ l := (Finset.mem_erase.1 hx).1
      simp [hx'.symm]
    rw [h4]
    have hc : ((m (src l)).choose (f l + 1) : R) * ((f l + 1 : ℕ) : R) =
        ((m (src l)).choose (f l) : R) * ((m (src l) - f l : ℕ) : R) := by
      exact_mod_cast congrArg (Nat.cast (R := R)) (Nat.choose_succ_right_eq (m (src l)) (f l))
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, pow_succ]
    generalize (∏ x ∈ s.erase l, sg x ^ (f x) * ((m (src x)).choose (f x) : R)) = Er
    linear_combination (-(sg l ^ f l * sg l * Er)) * hc
  simp only [polarizationDerivation, dividedPowerMonomialTerm, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, pderiv_monomial]
  rw [X, monomial_mul, hexp, one_mul, smul_monomial, smul_eq_mul, hcf, ← nsmul_eq_mul, map_nsmul]

theorem finsuppAntidiag_succ_reindex {N : Type*} [AddCommMonoid N] (s : Finset ι) (k : ℕ) (l : ι) (hl : l ∈ s)
    (F : (ι →₀ ℕ) → N) :
    ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • F g =
      ∑ f ∈ Finset.finsuppAntidiag s k, (f l + 1) • F (f + Finsupp.single l 1) := by
  have hL : ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • F g =
      ∑ g ∈ (Finset.finsuppAntidiag s (k + 1)).filter (fun g => g l ≠ 0), (g l) • F g := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro g _ h h0
    apply h
    simp [h0]
  rw [hL]
  symm
  apply Finset.sum_nbij' (fun f => f + Finsupp.single l 1) (fun g => g - Finsupp.single l 1)
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hf ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hf.1]
      simp [Finset.sum_add_distrib, Finsupp.single_apply, hl]
    · intro x hx
      rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
      · exact hf.2 h
      · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
        exact hl
    · simp
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hg ⊢
    have hle : Finsupp.single l 1 ≤ g := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hg.2)
    have hg' : g - Finsupp.single l 1 + Finsupp.single l 1 = g := tsub_add_cancel_of_le hle
    refine ⟨?_, ?_⟩
    · have hsum : ∑ x ∈ s, (g - Finsupp.single l 1 : ι →₀ ℕ) x + ∑ x ∈ s, (Finsupp.single l 1 : ι →₀ ℕ) x =
          ∑ x ∈ s, g x := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun x _ => by rw [← Finsupp.add_apply, hg'])
      have h1 : ∑ x ∈ s, (Finsupp.single l 1 : ι →₀ ℕ) x = 1 := by
        simp [Finsupp.single_apply, hl]
      have h2 : ∑ x ∈ s, g x = k + 1 := hg.1.1
      have h3 : ∑ x ∈ s, (g - Finsupp.single l 1 : ι →₀ ℕ) x = k := by omega
      exact h3
    · intro x hx
      apply hg.1.2
      rw [Finsupp.mem_support_iff] at hx ⊢
      intro h0
      apply hx
      simp [h0]
  · intro f _
    simp
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hg
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hg.2))
  · intro f _
    simp

theorem polarization_dividedPowerSum_succ (sg : ι → R) (src dst : ι → σ) (hs : Function.Injective src) (hd : ∀ l l', dst l' ≠ src l)
    (s : Finset ι) (m : σ →₀ ℕ) (k : ℕ) :
    (∑ l ∈ s, polarizationDerivation sg src dst l) (dividedPowerMonomialSum sg src dst s k m) = (k + 1) • dividedPowerMonomialSum sg src dst s (k + 1) m := by
  have h1 : (∑ l ∈ s, polarizationDerivation sg src dst l) (dividedPowerMonomialSum sg src dst s k m) =
      ∑ l ∈ s, ∑ f ∈ Finset.finsuppAntidiag s k, polarizationDerivation sg src dst l (dividedPowerMonomialTerm sg src dst s m f) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun l _ => map_sum _ _ _)
  have h2 : ∀ l ∈ s, ∑ f ∈ Finset.finsuppAntidiag s k, polarizationDerivation sg src dst l (dividedPowerMonomialTerm sg src dst s m f) =
      ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • dividedPowerMonomialTerm sg src dst s m g := by
    intro l hl
    rw [finsuppAntidiag_succ_reindex s k l hl (dividedPowerMonomialTerm sg src dst s m)]
    exact Finset.sum_congr rfl (fun f _ => polarization_dividedPowerTerm sg src dst hs hd s m f l hl)
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_comm]
  unfold dividedPowerMonomialSum
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← Finset.sum_smul, (Finset.mem_finsuppAntidiag.1 hg).1]

theorem dividedPowerMonomialSum_zero (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) :
    dividedPowerMonomialSum sg src dst s 0 m = monomial m 1 := by
  simp [dividedPowerMonomialSum, dividedPowerMonomialTerm, dividedPowerExponent, dividedPowerCoefficient, Finset.finsuppAntidiag_zero]

end v2dpAbs

end Formalism.MainNotions.G.GLWeightTheory
end
end

