module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.PdvrExt
section
namespace PositivityTheory.HtPt.Pdvr

open Polynomial IsLocalRing

theorem exists_root (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (q : (ResidueField V)[X]) (hm : q.Monic) (hq : Irreducible q) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : V →+* R) (_ : IsLocalHom f), Function.Injective f ∧
      ∃ a, (q.map (ResidueField.map f)).IsRoot a := by
  obtain ⟨P, hP, hdeg, hPm⟩ := lifts_and_degree_eq_and_monic
    ((mem_lifts q).mpr (map_surjective (residue V) residue_surjective q)) hm
  have hPi : Irreducible P :=
    Monic.irreducible_of_irreducible_map (residue V) P hPm (hP ▸ hq)
  have : IsDomain (AdjoinRoot P) := AdjoinRoot.isDomain_of_prime hPi.prime
  have hinj : Function.Injective (AdjoinRoot.of P) :=
    AdjoinRoot.of.injective_of_degree_ne_zero (hdeg ▸ (degree_pos_of_irreducible hq).ne')
  have : Module.Finite V (AdjoinRoot P) := hPm.finite_adjoinRoot
  have hmax : (Ideal.map (AdjoinRoot.of P) (maximalIdeal V)).IsMaximal := by
    apply Ideal.Quotient.maximal_of_isField
    have : Fact (Irreducible (P.map (residue V))) := ⟨hP ▸ hq⟩
    have h1 : IsField (AdjoinRoot (P.map (residue V))) := Field.toIsField _
    exact MulEquiv.isField h1
      (AdjoinRoot.quotEquivQuotMap P (maximalIdeal V)).toRingEquiv.toMulEquiv
  have huniq : ∀ M : Ideal (AdjoinRoot P), M.IsMaximal →
      M = Ideal.map (AdjoinRoot.of P) (maximalIdeal V) := by
    intro M hM
    have h1 : (M.comap (algebraMap V (AdjoinRoot P))).IsMaximal := by
      letI := hM
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (algebraMap V (AdjoinRoot P)) (by
          intro x
          exact Algebra.IsIntegral.isIntegral x) M
    have h2 := eq_maximalIdeal h1
    refine (hmax.eq_of_le hM.ne_top ?_).symm
    rw [Ideal.map_le_iff_le_comap, ← h2]
    exact le_rfl
  have : IsLocalRing (AdjoinRoot P) := .of_unique_max_ideal ⟨_, hmax, huniq⟩
  have hme : maximalIdeal (AdjoinRoot P) = Ideal.map (AdjoinRoot.of P) (maximalIdeal V) :=
    huniq _ inferInstance
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hme' : maximalIdeal (AdjoinRoot P) = Ideal.span {AdjoinRoot.of P π} := by
    rw [hme, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (AdjoinRoot P) := by
    rw [isField_iff_maximalIdeal_eq, hme', Ideal.span_singleton_eq_bot]
    exact fun h => hπ.ne_zero (hinj (h.trans (map_zero _).symm))
  have : IsNoetherianRing (AdjoinRoot P) := IsNoetherianRing.of_finite V _
  have hdvr : IsDiscreteValuationRing (AdjoinRoot P) :=
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot P) hnf).out 1 5).mpr
      (show (maximalIdeal (AdjoinRoot P)).IsPrincipal from ⟨_, hme'⟩)
  have hloc : IsLocalHom (AdjoinRoot.of P) := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have : AdjoinRoot.of P a ∈ maximalIdeal (AdjoinRoot P) :=
      hme ▸ Ideal.mem_map_of_mem _ h
    exact this ha
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, hdvr, AdjoinRoot.of P, hloc, hinj,
    residue _ (AdjoinRoot.root P), ?_⟩
  rw [← hP, Polynomial.map_map, ResidueField.map_comp_residue, IsRoot.def, eval_map,
    ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

theorem exists_splits (n : ℕ) : ∀ (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (q : (ResidueField V)[X]), q.natDegree = n →
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : V →+* R) (_ : IsLocalHom f), Function.Injective f ∧
      (q.map (ResidueField.map f)).Splits := by
  induction n with
  | zero =>
    intro V _ _ _ q hq
    exact ⟨V, inferInstance, inferInstance, inferInstance, RingHom.id V, inferInstance,
      Function.injective_id, (Splits.of_natDegree_eq_zero hq).map _⟩
  | succ n ih =>
    intro V _ _ _ q hq
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at hq
    have hnu : ¬ IsUnit q := not_isUnit_of_natDegree_pos q (by omega)
    obtain ⟨g, hgm, hgi, hgd⟩ := exists_monic_irreducible_factor q hnu
    obtain ⟨R, _, _, _, f, _, hf, a, ha⟩ := exists_root V g hgm hgi
    have hr : (q.map (ResidueField.map f)).IsRoot a := ha.dvd (Polynomial.map_dvd _ hgd)
    obtain ⟨q', hq'⟩ := dvd_iff_isRoot.mpr hr
    have hq1 : q.map (ResidueField.map f) ≠ 0 := Polynomial.map_ne_zero hq0
    have hd : q'.natDegree = n := by
      have h1 := congrArg natDegree hq'
      have h2 : q' ≠ 0 := by
        rintro rfl
        exact hq1 (by rw [hq', mul_zero])
      rw [natDegree_map, natDegree_mul (X_sub_C_ne_zero a) h2, natDegree_X_sub_C] at h1
      omega
    obtain ⟨S, _, _, _, f', _, hf', hs⟩ := ih R q' hd
    refine ⟨S, inferInstance, inferInstance, inferInstance, f'.comp f, inferInstance,
      hf'.comp hf, ?_⟩
    rw [ResidueField.map_comp, ← Polynomial.map_map, hq', Polynomial.map_mul]
    exact ((Splits.X_sub_C a).map _).mul hs

theorem exists_complete (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : V →+* R) (_ : IsLocalHom f), IsAdicComplete (maximalIdeal R) R ∧
      Function.Injective f := by
  classical
  let R := AdicCompletion (maximalIdeal V) V
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let ϖ : R := algebraMap V R π
  have hme : maximalIdeal R = Ideal.span {ϖ} := by
    refine AdicCompletion.maximalIdeal_eq_map.trans ?_
    refine (congrArg (Ideal.map (algebraMap V R)) hπ.maximalIdeal_eq).trans ?_
    rw [Ideal.map_span, Set.image_singleton]
  have hreg : ∀ r : V, r ≠ 0 → ∀ x : R, algebraMap V R r * x = 0 → x = 0 := by
    intro r hr x hx
    have h1 : IsSMulRegular R r :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
    apply h1
    change r • x = r • (0 : R)
    rw [smul_zero, Algebra.smul_def, hx]
  have hfac : ∀ x : R, x ≠ 0 → ∃ (n : ℕ) (u : Rˣ), ϖ ^ n * u = x := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ ϖ ^ n ∣ x := by
      by_contra h
      push Not at h
      apply hx
      refine IsHausdorff.haus' (I := maximalIdeal R) x fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hme, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      exact h n
    have h0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h, pow_zero] at this
      exact this (one_dvd _)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have h1 : ϖ ^ n ∣ x := not_not.mp (Nat.find_min hex (by omega))
    obtain ⟨y, rfl⟩ := h1
    have hy : IsUnit y := by
      by_contra h
      have h2 : y ∈ maximalIdeal R := h
      rw [hme, Ideal.mem_span_singleton] at h2
      have h3 := Nat.find_spec hex
      rw [hn, pow_succ] at h3
      exact h3 (mul_dvd_mul_left _ h2)
    exact ⟨n, hy.unit, rfl⟩
  have : NoZeroDivisors R := ⟨fun {a b} hab => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      obtain ⟨n, u, rfl⟩ := hfac a ha
      have h1 : algebraMap V R (π ^ n) * (u * b) = 0 := by
        rw [map_pow, ← mul_assoc]
        exact hab
      have h2 := hreg _ (pow_ne_zero n hπ.ne_zero) _ h1
      exact (Units.mul_right_eq_zero u).mp h2⟩
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  have hinj : Function.Injective (algebraMap V R) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h
    exact one_ne_zero (hreg a h 1 (by rw [ha, zero_mul]))
  have hϖ0 : ϖ ≠ 0 := fun h => hπ.ne_zero (hinj (h.trans (map_zero _).symm))
  have hϖ : Irreducible ϖ := by
    refine Prime.irreducible ((Ideal.span_singleton_prime hϖ0).mp ?_)
    rw [← hme]
    infer_instance
  have hdvr : IsDiscreteValuationRing R :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨ϖ, hϖ, fun {x} hx => hfac x hx⟩
  exact ⟨R, inferInstance, inferInstance, hdvr, algebraMap V R, inferInstance,
    (inferInstance : IsAdicComplete (maximalIdeal R) R), hinj⟩

end PositivityTheory.HtPt.Pdvr
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RaCarry
section
open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Ra

theorem carry : ∀ (p f : ℕ), 2 ≤ p → 0 < f → ∀ (y : ℕ → NNReal), (∀ n, y (n + f) = y n) → (∀ n, y n ≤ 1) → (∀ n, y n ^ p ≤ y (n + 1)) → ∀ (e : Fin f → ℕ) (j : ℕ), 2 ≤ ∑ n, e n → (∑ n : Fin f, e n * p ^ (n : ℕ)) ≡ p ^ (j + 1) [MOD (p ^ f - 1)] → ∏ n : Fin f, y n ^ e n ≤ y j ^ p := by
  intro p f hp hf y hper hle1 hstep e j he hcong
  have hperm : ∀ a c, y (a + f * c) = y a := by
    intro a c
    induction c with
    | zero => simp
    | succ c ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]
  have hiter : ∀ a k, y a ^ (p ^ k) ≤ y (a + k) := by
    intro a k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ← Nat.add_assoc]
      exact (pow_le_pow_left₀ zero_le ih p).trans (hstep _)
  obtain ⟨q, s, hs, hj⟩ : ∃ q s, s < f ∧ j = s + f * q :=
    ⟨j / f, j % f, Nat.mod_lt _ hf, (Nat.mod_add_div j f).symm⟩
  have hk : ∀ n : Fin f, ∃ k c m c', k + m = f - 1 ∧ (n : ℕ) + k = s + f * c ∧
      m + (j + 1) = n + f * c' := by
    intro n
    have hn := n.isLt
    by_cases h : (n : ℕ) ≤ s
    · refine ⟨s - n, 0, f - 1 - (s - n), q + 1, by omega, by omega, ?_⟩
      rw [hj, Nat.mul_succ]
      omega
    · refine ⟨s + f - n, 1, f - 1 - (s + f - n), q, by omega, by omega, ?_⟩
      rw [hj]
      omega
  choose k c m c' hkm hkc hmc using hk
  have hyk : ∀ n : Fin f, y n ^ (p ^ k n) ≤ y j := by
    intro n
    have := hiter n (k n)
    rw [hkc, hperm] at this
    rw [hj, hperm]
    exact this
  have hpos : 1 ≤ p := by omega
  have hN : p ^ f - 1 + 1 = p ^ f := Nat.sub_add_cancel (Nat.one_le_pow _ _ hpos)
  have hT1 : (∑ n : Fin f, e n * p ^ m n) ≡ 1 [MOD (p ^ f - 1)] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have hc := (ZMod.natCast_eq_natCast_iff _ _ _).2 hcong
    push_cast at hc ⊢
    set u : ZMod (p ^ f - 1) := (p : ZMod (p ^ f - 1)) with hu
    have huf : u ^ f = 1 := by
      rw [hu, ← Nat.cast_pow, ← hN, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    have hper' : ∀ a c, u ^ (a + f * c) = u ^ a := by
      intro a c
      rw [pow_add, pow_mul, huf, one_pow, mul_one]
    have hunit : IsUnit (u ^ (j + 1)) := by
      refine IsUnit.pow _ (isUnit_iff_exists_inv.2 ⟨u ^ (f - 1), ?_⟩)
      rw [← pow_succ', Nat.sub_add_cancel hf, huf]
    have hmul : (∑ n : Fin f, (e n : ZMod (p ^ f - 1)) * u ^ m n) * u ^ (j + 1) = u ^ (j + 1) := by
      refine (Finset.sum_mul _ _ _).trans ((Finset.sum_congr rfl fun n _ => ?_).trans hc)
      rw [mul_assoc, ← pow_add, hmc, hper']
    have h0 : ((∑ n : Fin f, (e n : ZMod (p ^ f - 1)) * u ^ m n) - 1) * u ^ (j + 1) = 0 := by
      rw [sub_mul, hmul, one_mul, sub_self]
    exact sub_eq_zero.1 (hunit.mul_left_eq_zero.1 h0)
  have hT2 : 2 ≤ ∑ n : Fin f, e n * p ^ m n :=
    le_trans he (Finset.sum_le_sum fun n _ => Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
  have hTf : p ^ f ≤ ∑ n : Fin f, e n * p ^ m n := by
    have hd := (Nat.modEq_iff_dvd' (by omega : 1 ≤ ∑ n : Fin f, e n * p ^ m n)).1 hT1.symm
    have hle := Nat.le_of_dvd (by omega) hd
    generalize p ^ f = P at *
    generalize ∑ n : Fin f, e n * p ^ m n = T at *
    omega
  have hP : 0 < p ^ (f - 1) := pow_pos (by omega) _
  refine (pow_le_pow_iff_left₀ zero_le zero_le hP.ne').1 ?_
  calc (∏ n : Fin f, y n ^ e n) ^ p ^ (f - 1)
      = ∏ n : Fin f, (y n ^ p ^ k n) ^ (e n * p ^ m n) := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun n _ => ?_
        rw [← pow_mul, ← pow_mul]
        congr 1
        rw [← hkm n, pow_add]
        ring
    _ ≤ ∏ n : Fin f, y j ^ (e n * p ^ m n) :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le) fun n _ => pow_le_pow_left₀ zero_le (hyk n) _
    _ = y j ^ (∑ n : Fin f, e n * p ^ m n) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ y j ^ p ^ f := pow_le_pow_of_le_one zero_le (hle1 j) hTf
    _ = (y j ^ p) ^ p ^ (f - 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 2
        omega

end PositivityTheory.HtPt.Ra
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RaTlog
section
open scoped Matrix TensorProduct
open Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

open Polynomial

def logPoly {O : Type} [CommRing O] (p : ℕ) (c : ℕ → O) : O[X] :=
  ∑ k ∈ Finset.Ico 1 p, C ((-1) ^ (k - 1) * c k) * X ^ k

lemma logPoly_deriv {O : Type} [CommRing O] (p : ℕ) (hp : 1 ≤ p) (c : ℕ → O)
    (hc : ∀ k, 1 ≤ k → k < p → c k * k = 1) :
    (1 + X) * derivative (logPoly p c) = 1 - (-X) ^ (p - 1) := by
  have h1 : derivative (logPoly p c) = ∑ i ∈ Finset.range (p - 1), (-X : O[X]) ^ i := by
    rw [logPoly, derivative_sum, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [derivative_C_mul_X_pow, mul_assoc, hc _ (by omega) (by omega), mul_one,
      show 1 + i - 1 = i by omega, neg_pow (X : O[X])]
    simp
  rw [h1, ← mul_neg_geom_sum, sub_neg_eq_add]

lemma logPoly_dvd {O : Type} [CommRing O] [IsDomain O] [CharZero O] (p : ℕ) (hp : 1 ≤ p)
    (c : ℕ → O) (hc : ∀ k, 1 ≤ k → k < p → c k * k = 1) (a : ℕ) :
    X ^ p ∣ (logPoly p c).comp ((1 + X) ^ a - 1) - C (a : O) * logPoly p c := by
  set P := (logPoly p c).comp ((1 + X) ^ a - 1) - C (a : O) * logPoly p c with hP
  set s : O[X] := (1 + X) ^ a - 1 with hs
  have hXs : X ∣ s := by
    have := sub_dvd_pow_sub_pow (1 + X : O[X]) 1 a
    simpa using this
  have hd := logPoly_deriv p hp c hc
  have hd2 : (1 + s) * (derivative (logPoly p c)).comp s = 1 - (-s) ^ (p - 1) := by
    have := congrArg (fun q => q.comp s) hd
    simpa using this
  have hds : (1 + X) * derivative s = C (a : O) * (1 + s) := by
    rw [hs]
    rcases a with _ | a
    · simp
    · simp only [derivative_sub, derivative_one, sub_zero, derivative_pow_succ, derivative_add,
        derivative_X, zero_add, mul_one, add_sub_cancel]
      push_cast
      ring
  have hP' : (1 + X) * derivative P = C (a : O) * ((-X) ^ (p - 1) - (-s) ^ (p - 1)) := by
    rw [hP, derivative_sub, derivative_comp, derivative_C_mul]
    linear_combination ((derivative (logPoly p c)).comp s) * hds + C (a : O) * hd2 - C (a : O) * hd
  have hdv : X ^ (p - 1) ∣ (1 + X) * derivative P := by
    rw [hP']
    exact Dvd.dvd.mul_left (dvd_sub (pow_dvd_pow_of_dvd (dvd_neg.2 dvd_rfl) _)
      (pow_dvd_pow_of_dvd (dvd_neg.2 hXs) _)) _
  have hcop : IsCoprime (X ^ (p - 1) : O[X]) (1 + X) :=
    IsCoprime.pow_left ⟨-1, 1, by ring⟩
  have hdv2 := X_pow_dvd_iff.1 (hcop.dvd_of_dvd_mul_left hdv)
  refine X_pow_dvd_iff.2 fun d hdp => ?_
  rcases d with _ | d
  · have hL : X ∣ logPoly p c := by
      refine Finset.dvd_sum fun k hk => Dvd.dvd.mul_left (dvd_pow_self _ ?_) _
      have := (Finset.mem_Ico.1 hk).1
      omega
    refine X_dvd_iff.1 (dvd_sub ?_ (hL.mul_left _))
    obtain ⟨q, hq⟩ := hL
    rw [hq, mul_comp, X_comp]
    exact hXs.mul_right _
  · have := hdv2 d (by omega)
    rw [coeff_derivative] at this
    exact (mul_eq_zero.1 this).resolve_right (by exact_mod_cast Nat.succ_ne_zero d)

section Val

variable {K : Type} [Field K] (v : Valuation K NNReal)

lemma val_nat_le (k : ℕ) : v (k : K) ≤ 1 := (natCast_mem v.integer k : (k : K) ∈ v.integer)

lemma val_nat_eq (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) (k : ℕ) (h1 : 1 ≤ k) (h2 : k < p) :
    v (k : K) = 1 := by
  by_contra hne
  have hlt : v (k : K) < 1 := lt_of_le_of_ne (val_nat_le v k) hne
  have hc : Nat.Coprime p k := (Nat.coprime_of_lt_prime (by omega) h2 Fact.out)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  have hab' : (a : K) * p + b * k = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab
  have ha : v (a : K) ≤ 1 := (intCast_mem v.integer a : (a : K) ∈ v.integer)
  have hb : v (b : K) ≤ 1 := (intCast_mem v.integer b : (b : K) ∈ v.integer)
  have : v ((a : K) * p + b * k) < 1 := by
    refine v.map_add_lt ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right ha zero_le hp
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right hb zero_le hlt
  rw [hab', map_one] at this
  exact lt_irrefl _ this

lemma val_root (p : ℕ) (hp : p ≠ 0) {x : K} (hx : x ^ p = 1) : v x = 1 := by
  have : v x ^ p = 1 := by rw [← map_pow, hx, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le hp).1 this

lemma val_pow_sub_one {x : K} (hx : v x = 1) (k : ℕ) : v (x ^ k - 1) ≤ v (x - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : x ^ (k + 1) - 1 = x * (x ^ k - 1) + (x - 1) := by ring
    rw [this]
    refine v.map_add_le ?_ le_rfl
    rw [map_mul, hx, one_mul]; exact ih

lemma val_prim (p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    v (ζ - 1) ^ (p - 1) = v (p : K) := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have h := congrArg v hζ.prod_one_sub_pow_eq_order
  rw [map_prod] at h
  push_cast
  rw [← h, Finset.prod_congr rfl (g := fun _ => v (ζ - 1))]
  · simp
  intro k hk
  have hk' := Finset.mem_range.1 hk
  have hc : Nat.Coprime (k + 1) (n + 1) :=
    (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
  have h2 := hζ.pow_of_coprime _ hc
  rw [v.map_sub_swap]
  refine le_antisymm (val_pow_sub_one v (val_root v _ hp.ne_zero hζ.pow_eq_one) _) ?_
  obtain ⟨i, -, hi⟩ := h2.eq_pow_of_pow_eq_one hζ.pow_eq_one
  conv_lhs => rw [← hi]
  exact val_pow_sub_one v (val_root v _ hp.ne_zero h2.pow_eq_one) _

def tl (p : ℕ) (x : K) : K := ∑ k ∈ Finset.Ico 1 p, (-1) ^ (k - 1) * (x - 1) ^ k / (k : K)

lemma tl_one (p : ℕ) : tl p (1 : K) = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  have := (Finset.mem_Ico.1 hk).1
  rw [sub_self, zero_pow (by omega)]; simp

lemma val_tl_pow [CharZero K] (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {x : K} (hx : v x = 1)
    (a : ℕ) : v (tl p (x ^ a) - tl p x * a) ≤ v (x - 1) ^ p := by
  classical
  let c : ℕ → v.integer := fun k => if h : v (k : K) = 1 then ⟨(k : K)⁻¹, by
    rw [Valuation.mem_integer_iff, map_inv₀, h, inv_one]⟩ else 0
  have hc' : ∀ k, 1 ≤ k → k < p → (c k : K) = (k : K)⁻¹ := by
    intro k h1 h2
    simp only [c, dif_pos (val_nat_eq v p hp k h1 h2)]
  have hc : ∀ k, 1 ≤ k → k < p → c k * k = 1 := by
    intro k h1 h2
    ext
    have : (k : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    push_cast
    rw [hc' k h1 h2, inv_mul_cancel₀ this]
  have hev : ∀ t : v.integer, (((logPoly p c).eval t : v.integer) : K) = tl p (1 + (t : K)) := by
    intro t
    rw [logPoly, eval_finsetSum, tl]
    push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    push_cast
    rw [hc' k h1 h2, add_sub_cancel_left]; ring
  obtain ⟨q, hq⟩ := logPoly_dvd p (Fact.out : p.Prime).one_le c hc a
  have hx1 : x - 1 ∈ v.integer := by
    apply sub_mem _ (one_mem _)
    rw [Valuation.mem_integer_iff, hx]
  let t : v.integer := ⟨x - 1, hx1⟩
  have h := congrArg (fun r : v.integer[X] => ((r.eval t : v.integer) : K)) hq
  simp only [eval_sub, eval_comp, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one] at h
  push_cast at h
  rw [hev, hev] at h
  push_cast at h
  have ht : (t : K) = x - 1 := rfl
  rw [ht, add_sub_cancel, add_sub_cancel, mul_comm (a : K)] at h
  rw [h, map_mul, map_pow]
  exact mul_le_of_le_one_right zero_le (q.eval t).2

lemma val_prim_lt (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) < 1 := by
  by_contra h
  have := one_le_pow₀ (n := p - 1) (not_lt.1 h)
  rw [val_prim v p hζ] at this
  exact absurd hp (not_lt.2 this)

lemma val_prim_pos (p : ℕ) [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : 0 < v (ζ - 1) :=
  (v.pos_iff).2 (sub_ne_zero.2 (hζ.ne_one (Fact.out : p.Prime).one_lt))

lemma val_prim_pow_le (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) ^ p ≤ v (p : K) := by
  rw [← val_prim v p hζ]
  exact pow_le_pow_of_le_one zero_le (val_prim_lt v p hp hζ).le (Nat.sub_le _ _)

lemma val_prim_pow_lt (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (k : ℕ) (hk : 1 < k) : v (ζ - 1) ^ k < v (ζ - 1) :=
  pow_lt_self_of_lt_one₀ (val_prim_pos v p hζ) (val_prim_lt v p hp hζ) hk

lemma val_tl_prim (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (tl p ζ) = v (ζ - 1) := by
  rw [tl, Finset.sum_eq_sum_Ico_succ_bot (Fact.out : p.Prime).one_lt]
  simp only [Nat.sub_self, pow_zero, pow_one, one_mul, Nat.cast_one, div_one]
  refine v.map_add_eq_of_lt_left (v.map_sum_lt (val_prim_pos v p hζ).ne' fun k hk => ?_)
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
  rw [map_div₀, val_nat_eq v p hp k (by omega) h2, div_one, map_mul, map_pow, map_pow,
    Valuation.map_neg, map_one, one_pow, one_mul]
  exact val_prim_pow_lt v p hp hζ k (by omega)

lemma val_tl_add [CharZero K] (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {x y : K}
    (hx : x ^ p = 1) (hy : y ^ p = 1) : v (tl p (x * y) - tl p x - tl p y) ≤ v (p : K) := by
  have hpp : p.Prime := Fact.out
  by_cases h1 : x = 1
  · simp [h1, tl_one]
  have hζ : IsPrimitiveRoot x p := by
    have := orderOf_eq_prime hx h1
    rw [← this]; exact IsPrimitiveRoot.orderOf x
  have : NeZero p := ⟨hpp.ne_zero⟩
  obtain ⟨b, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy
  have hv := val_root v p hpp.ne_zero hx
  have : tl p (x * x ^ b) - tl p x - tl p (x ^ b) =
      (tl p (x ^ (b + 1)) - tl p x * (b + 1 : ℕ)) - (tl p (x ^ b) - tl p x * b) := by
    rw [pow_succ']; push_cast; ring
  rw [this]
  exact (v.map_sub_le (val_tl_pow v p hp hv _) (val_tl_pow v p hp hv _)).trans
    (val_prim_pow_le v p hp hζ)

end Val

end PositivityTheory.HtPt.Ra
end
end

