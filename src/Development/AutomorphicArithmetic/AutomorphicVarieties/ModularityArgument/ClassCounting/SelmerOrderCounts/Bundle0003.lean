module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.NumberTheory.Multiplicity

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.PCount
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem card_tors (W : Type) [AddCommGroup W] [Finite W] (l : ℤ) (s : ℕ) :
    Nat.card (Submodule.torsionBy ℤ W (l ^ s)) ≤ Nat.card {w : W // l • w = 0} ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    let T := Submodule.torsionBy ℤ W (l ^ (s + 1))
    let m : T →ₗ[ℤ] W := l • T.subtype
    have hr : LinearMap.range m ≤ Submodule.torsionBy ℤ W (l ^ s) := by
      rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_torsionBy_iff]
      have hw := (Submodule.mem_torsionBy_iff _ _).1 w.2
      change l ^ s • (l • (w : W)) = 0
      rw [smul_smul, ← pow_succ]
      exact hw
    have h1 : Nat.card T = Nat.card (T ⧸ LinearMap.ker m) * Nat.card (LinearMap.ker m) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker m).toAddSubgroup
    rw [Nat.card_congr m.quotKerEquivRange.toEquiv] at h1
    have h2 : Nat.card (LinearMap.range m) ≤ Nat.card (Submodule.torsionBy ℤ W (l ^ s)) :=
      Nat.card_le_card_of_injective (Submodule.inclusion hr) (Submodule.inclusion_injective hr)
    have h3 : Nat.card (LinearMap.ker m) ≤ Nat.card {w : W // l • w = 0} :=
      Nat.card_le_card_of_injective (fun k => ⟨((k : T) : W), k.2⟩)
        (fun a b hab => by
          have h := congrArg Subtype.val hab
          apply Subtype.ext
          apply Subtype.ext
          exact h)
    calc Nat.card T = Nat.card (LinearMap.range m) * Nat.card (LinearMap.ker m) := h1
      _ ≤ Nat.card (Submodule.torsionBy ℤ W (l ^ s)) * Nat.card {w : W // l • w = 0} :=
          Nat.mul_le_mul h2 h3
      _ ≤ Nat.card {w : W // l • w = 0} ^ s * Nat.card {w : W // l • w = 0} :=
          Nat.mul_le_mul_right _ ih
      _ = Nat.card {w : W // l • w = 0} ^ (s + 1) := (pow_succ _ _).symm

theorem UpperTheory.V.ZK.Ct.pCount :
    ∀ (W Z : Type) [AddCommGroup W] [AddCommGroup Z] [Finite W] (f : W →ₗ[ℤ] Z) (l s g : ℕ) (u : ℤ), l.Prime → ¬(l : ℤ) ∣ u → (∀ w, f w = 0 → (u * (l : ℤ) ^ s) • w = 0) → Nat.card {w : W // (l : ℤ) • w = 0} ≤ l ^ g → l ^ (Nat.card W).factorization l ≤ Nat.card (LinearMap.range f) * l ^ (s * g) := by
  intro W Z _ _ _ f l s g u hl hlu hker hW
  haveI := Fact.mk hl
  let K := LinearMap.ker f
  let gm : K →ₗ[ℤ] K := ((l : ℤ) ^ s) • LinearMap.id
  haveI : Finite (LinearMap.range f) := Finite.of_surjective _ f.surjective_rangeRestrict
  have hWc : Nat.card W = Nat.card (LinearMap.range f) * Nat.card K := by
    have h : Nat.card W = Nat.card (W ⧸ LinearMap.ker f) * Nat.card (LinearMap.ker f) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup
    rwa [Nat.card_congr f.quotKerEquivRange.toEquiv] at h
  have hKc : Nat.card K = Nat.card (LinearMap.range gm) * Nat.card (LinearMap.ker gm) := by
    have h : Nat.card K = Nat.card (K ⧸ LinearMap.ker gm) * Nat.card (LinearMap.ker gm) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker gm).toAddSubgroup
    rwa [Nat.card_congr gm.quotKerEquivRange.toEquiv] at h
  have hR0 : Nat.card (LinearMap.range f) ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hRg0 : Nat.card (LinearMap.range gm) ≠ 0 := Nat.card_pos.ne'
  have hKg0 : Nat.card (LinearMap.ker gm) ≠ 0 := Nat.card_pos.ne'
  have hcop : ¬ l ∣ Nat.card (LinearMap.range gm) := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' l hd
    have hux : u • x = 0 := by
      rcases x with ⟨y, k, rfl⟩
      apply Subtype.ext
      apply Subtype.ext
      change u • ((l : ℤ) ^ s • ((k : K) : W)) = 0
      rw [smul_smul]
      exact hker _ k.2
    have hdv := addOrderOf_dvd_iff_zsmul_eq_zero.2 hux
    rw [hx] at hdv
    exact hlu hdv
  have hvK : (Nat.card K).factorization l = (Nat.card (LinearMap.ker gm)).factorization l := by
    rw [hKc, Nat.factorization_mul hRg0 hKg0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hcop, zero_add]
  have hA : Nat.card (LinearMap.ker gm) ≤ l ^ (s * g) := by
    calc Nat.card (LinearMap.ker gm) ≤ Nat.card (Submodule.torsionBy ℤ W ((l : ℤ) ^ s)) :=
          Nat.card_le_card_of_injective
            (fun a => ⟨((a : K) : W), by
              rw [Submodule.mem_torsionBy_iff]
              exact congrArg Subtype.val (LinearMap.mem_ker.1 a.2)⟩)
            (fun a b hab => by
              have h := congrArg Subtype.val hab
              apply Subtype.ext
              apply Subtype.ext
              exact h)
      _ ≤ Nat.card {w : W // (l : ℤ) • w = 0} ^ s := card_tors W l s
      _ ≤ (l ^ g) ^ s := Nat.pow_le_pow_left hW s
      _ = l ^ (s * g) := by rw [← pow_mul, mul_comm]
  have hR : l ^ (Nat.card (LinearMap.range f)).factorization l ≤ Nat.card (LinearMap.range f) :=
    Nat.ordProj_le l hR0
  have hKl : l ^ (Nat.card (LinearMap.ker gm)).factorization l ≤ Nat.card (LinearMap.ker gm) :=
    Nat.ordProj_le l hKg0
  rw [hWc, Nat.factorization_mul hR0 hK0, Finsupp.add_apply, pow_add, hvK]
  exact Nat.mul_le_mul hR (hKl.trans hA)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.PermDet
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem permDet_weight {X : Type} [Fintype X] [DecidableEq X] (π : Equiv.Perm X) (n : ℕ)
    (h : ∀ (k : ℕ) (x : X), (π ^ k) x = x ↔ n ∣ k) (ζ : ℂ) (hζ : ζ ^ n = 1) (hζ0 : ζ ≠ 0) :
    ∃ c : X → ℂ, (∀ x, c x ≠ 0) ∧ ∀ x, c (π x) = ζ * c x := by
  classical
  let S := Equiv.Perm.SameCycle.setoid π
  have hk : ∀ x : X, ∃ k : ℕ, (π ^ k) (Quotient.out (Quotient.mk S x)) = x := fun x => by
    have hr : π.SameCycle (Quotient.out (Quotient.mk S x)) x := Quotient.mk_out (s := S) x
    obtain ⟨i, _, hi⟩ := hr.exists_pow_eq'
    exact ⟨i, hi⟩
  choose k hk using hk
  have hsame : ∀ y : X, ∀ p q : ℕ, (π ^ p) y = (π ^ q) y → ζ ^ p = ζ ^ q := by
    intro y p q hpq
    wlog hle : p ≤ q generalizing p q
    · exact (this q p hpq.symm (by omega)).symm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hfix : (π ^ d) ((π ^ p) y) = (π ^ p) y := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm]
      exact hpq.symm
    obtain ⟨m, rfl⟩ := (h d _).1 hfix
    rw [pow_add, pow_mul, hζ, one_pow, mul_one]
  refine ⟨fun x => ζ ^ k x, fun x => pow_ne_zero _ hζ0, fun x => ?_⟩
  have hq : Quotient.mk S (π x) = Quotient.mk S x :=
    Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl π x))
  have e1 := hk (π x)
  rw [hq] at e1
  have e2 : (π ^ (k x + 1)) (Quotient.out (Quotient.mk S x)) = π x := by
    rw [pow_succ', Equiv.Perm.mul_apply, hk x]
  show ζ ^ k (π x) = ζ * ζ ^ k x
  rw [← pow_succ']
  exact hsame _ _ _ (e1.trans e2.symm)

private theorem permDet_twist {X : Type} [Fintype X] [DecidableEq X] (π : Equiv.Perm X)
    (ζ a : ℂ) (c : X → ℂ) (hc0 : ∀ x, c x ≠ 0) (hc : ∀ x, c (π x) = ζ * c x) :
    (a • (1 : Matrix X X ℂ) - ζ • π.permMatrix ℂ).det = (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det := by
  have key : Matrix.diagonal c * (a • (1 : Matrix X X ℂ) - ζ • π.permMatrix ℂ) =
      (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ) * Matrix.diagonal c := by
    ext i j
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.diagonal_mul, Matrix.mul_diagonal, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Matrix.one_apply]
    by_cases h2 : π i = j
    · subst h2
      rw [hc]
      by_cases h1 : i = π i
      · have e := hc i
        rw [← h1] at e
        have hz : ζ = 1 := mul_right_cancel₀ (hc0 i) (e.symm.trans (one_mul _).symm)
        rw [if_pos h1, if_pos rfl, if_pos rfl, hz]
        ring
      · rw [if_neg h1, if_pos rfl, if_pos rfl]
        ring
    · rw [if_neg h2, if_neg h2]
      split_ifs with h1
      · subst h1
        ring
      · ring
  have hd : (Matrix.diagonal c).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun x _ => hc0 x
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm ((a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det)] at this
  exact mul_left_cancel₀ hd this

private theorem permDet_pow {X : Type} [Fintype X] [DecidableEq X] (π : Equiv.Perm X) (n : ℕ)
    (hn : 0 < n) (h : ∀ (k : ℕ) (x : X), (π ^ k) x = x ↔ n ∣ k) (a : ℂ) :
    (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det ^ n = (a ^ n - 1) ^ Fintype.card X := by
  classical
  have hpow : ∀ k : ℕ, (π.permMatrix ℂ) ^ k = (π ^ k).permMatrix ℂ := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.permMatrix_one]
    | succ k ih => rw [pow_succ', pow_succ, Matrix.permMatrix_mul, ih]
  have hπn : π ^ n = 1 := Equiv.ext fun x => (h n x).2 dvd_rfl
  have hPn : (π.permMatrix ℂ) ^ n = 1 := by rw [hpow, hπn, Matrix.permMatrix_one]
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨S, hS⟩ : ∃ S, S = Polynomial.nthRootsFinset n (1 : ℂ) := ⟨_, rfl⟩
  have hcard : S.card = n := by rw [hS]; exact hprim.card_nthRootsFinset
  have hmem : ∀ ζ ∈ S, ζ ^ n = 1 := fun ζ hζ => by
    rw [hS] at hζ
    exact (Polynomial.mem_nthRootsFinset hn 1).1 hζ
  have hpt : ∀ t : ℂ, ∏ ζ ∈ S, (a - ζ * t) = a ^ n - t ^ n := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp [Finset.prod_const, hcard, hn.ne']
    · have e := congrArg (Polynomial.eval (a / t)) (Polynomial.X_pow_sub_one_eq_prod hn hprim)
      rw [← hS] at e
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_prod, Polynomial.eval_C] at e
      have e2 : ∏ ζ ∈ S, (a - ζ * t) = ∏ ζ ∈ S, (t * (a / t - ζ)) :=
        Finset.prod_congr rfl fun ζ _ => by field_simp
      rw [e2, Finset.prod_mul_distrib, Finset.prod_const, hcard, ← e, div_pow]
      field_simp
  have hpoly : ∏ ζ ∈ S, (Polynomial.C a - Polynomial.C ζ * Polynomial.X) =
      Polynomial.C (a ^ n) - Polynomial.X ^ n := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    exact hpt t
  let f : Polynomial ℂ →* ℂ :=
    Matrix.detMonoidHom.comp (Polynomial.aeval (π.permMatrix ℂ)).toRingHom.toMonoidHom
  have hf : ∀ q, f q = (Polynomial.aeval (π.permMatrix ℂ) q).det := fun q => rfl
  have hdet := congrArg f hpoly
  rw [map_prod, hf] at hdet
  have hfac : ∀ ζ ∈ S, f (Polynomial.C a - Polynomial.C ζ * Polynomial.X) =
      (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det := by
    intro ζ hζ
    have hz0 : ζ ≠ 0 := by
      rintro rfl
      have := hmem 0 hζ
      rw [zero_pow hn.ne'] at this
      exact zero_ne_one this
    obtain ⟨c, hc0, hc⟩ := permDet_weight π n h ζ (hmem ζ hζ) hz0
    rw [hf, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact permDet_twist π ζ a c hc0 hc
  rw [Finset.prod_congr rfl hfac, Finset.prod_const, hcard] at hdet
  rw [hdet, map_sub, Polynomial.aeval_C, Polynomial.aeval_X_pow, hPn, Algebra.algebraMap_eq_smul_one]
  have e3 : (a ^ n • (1 : Matrix X X ℂ) - 1) = (a ^ n - 1) • (1 : Matrix X X ℂ) := by
    rw [sub_smul, one_smul]
  rw [e3, Matrix.det_smul, Matrix.det_one, mul_one]

theorem UpperTheory.V.ZK.Ct.permDet :
    ∀ (X : Type) [Fintype X] [DecidableEq X] (π : Equiv.Perm X) (n r : ℕ) (a : ℝ), 0 < n → 1 ≤ a → Fintype.card X = n * r → (∀ (k : ℕ) (x : X), (π ^ k) x = x ↔ n ∣ k) → |LinearMap.det (LinearMap.funLeft ℝ ℝ π - a • (LinearMap.id : (X → ℝ) →ₗ[ℝ] (X → ℝ)))| = (a ^ n - 1) ^ r := by
  intro X _ _ π n r a hn ha hcard h
  classical
  have hlin : LinearMap.funLeft ℝ ℝ π - a • (LinearMap.id : (X → ℝ) →ₗ[ℝ] (X → ℝ)) =
      Matrix.toLin' (π.permMatrix ℝ - a • (1 : Matrix X X ℝ)) := by
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.permMatrix_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    rfl
  rw [hlin, LinearMap.det_toLin']
  have hneg : π.permMatrix ℝ - a • (1 : Matrix X X ℝ) = -(a • (1 : Matrix X X ℝ) - π.permMatrix ℝ) := by
    rw [neg_sub]
  rw [hneg, Matrix.det_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hC := permDet_pow π n hn h (a : ℂ)
  have hmap : ((a • (1 : Matrix X X ℝ) - π.permMatrix ℝ).det : ℂ) =
      ((a : ℂ) • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det := by
    have e := RingHom.map_det Complex.ofRealHom (a • (1 : Matrix X X ℝ) - π.permMatrix ℝ)
    rw [Complex.ofRealHom_eq_coe] at e
    rw [e]
    congr 1
    ext i j
    simp [Matrix.one_apply, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  have hR : (a • (1 : Matrix X X ℝ) - π.permMatrix ℝ).det ^ n = ((a ^ n - 1) ^ r) ^ n := by
    apply Complex.ofReal_injective
    push_cast
    rw [hmap, hC, hcard, pow_mul']
  have hnn : 0 ≤ a ^ n - 1 := sub_nonneg.mpr (one_le_pow₀ ha)
  rw [← pow_left_inj₀ (abs_nonneg _) (pow_nonneg hnn r) hn.ne', ← abs_pow, hR,
    abs_of_nonneg (pow_nonneg (pow_nonneg hnn r) n)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.SelInj
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem selInj_delI_inj {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I)
    (v : I) (hv : D.delI v = 0) : v = 0 := by
  have h1 : D.gI v = (D.a : ℤ) • v := by
    have h := hv
    simp only [Dat.delI, LinearMap.sub_apply, sub_eq_zero] at h
    rw [h]
    simp
  have hp : ∀ k : ℕ, (D.gI ^ k) v = ((D.a : ℤ) ^ k) • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, h1, map_zsmul, ih, smul_smul, pow_succ, mul_comm]
  have hn := hp D.n
  rw [D.gI_pow] at hn
  change v = _ at hn
  apply D.tf ((D.a : ℤ) ^ D.n - 1) v
  · have h2 : (1 : ℤ) < (D.a : ℤ) ^ D.n := one_lt_pow₀ (by have := D.two_le; omega) D.n_pos.ne'
    omega
  · rw [sub_smul, one_smul, ← hn, sub_self]

private theorem selInj_tors_iff {Y : Type} [AddCommGroup Y] (t : Y) :
    t ∈ Submodule.torsion ℤ Y ↔ ∃ m : ℤ, m ≠ 0 ∧ m • t = 0 := by
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨m, hm⟩, h⟩
    exact ⟨m, nonZeroDivisors.ne_zero hm, h⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, h⟩

private theorem selInj_mem_mt {Y : Type} [AddCommGroup Y] (l : ℕ) (x : Y) :
    x ∈ mt Y l ↔ ∃ z : Y, ∃ t ∈ Submodule.torsion ℤ Y, (l : ℤ) • z + t = x := by
  simp only [Ct.mt, Submodule.mem_sup, LinearMap.mem_range]
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, t, ht, h⟩
    exact ⟨z, t, ht, by simpa using h⟩
  · rintro ⟨z, t, ht, h⟩
    exact ⟨_, ⟨z, rfl⟩, t, ht, by simpa using h⟩

theorem UpperTheory.V.ZK.Ct.selInj :
    ∀ (Y I : Type) [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I), ∀ l : ℕ, (l : ℤ) ∣ (D.a : ℤ) - 1 → 0 < l → Finite (D.SelInv l) → Nat.card {w : D.W // (l : ℤ) • w = 0} ≤ Nat.card (D.SelInv l) := by
  intro Y I _ _ D l hl hl0 hfin
  have hdel_apply : ∀ y, D.del y = D.g y - (D.a : ℤ) • y := by
    intro y
    simp [Dat.del]
  have hdelI_apply : ∀ v, D.delI v = D.gI v - (D.a : ℤ) • v := by
    intro v
    simp [Dat.delI]
  have htor : ∀ {y : Y} (m : ℤ), m ≠ 0 → m • y ∈ Submodule.torsion ℤ Y → y ∈ Submodule.torsion ℤ Y := by
    intro y m hm h
    obtain ⟨m', hm', h'⟩ := (selInj_tors_iff _).1 h
    exact (selInj_tors_iff y).2 ⟨m' * m, mul_ne_zero hm' hm, by rw [mul_smul, h']⟩
  have hdt : ∀ t ∈ Submodule.torsion ℤ Y, D.d t = 0 := by
    intro t ht
    obtain ⟨m, hm, h⟩ := (selInj_tors_iff t).1 ht
    exact D.tf m _ hm (by rw [← map_zsmul, h, map_zero])
  have hdd : ∀ y, D.d (D.del y) = D.delI (D.d y) := by
    intro y
    rw [hdel_apply, hdelI_apply, map_sub, map_zsmul, D.comm]
  have hdelt : ∀ t ∈ Submodule.torsion ℤ Y, D.del t ∈ Submodule.torsion ℤ Y := by
    intro t ht
    obtain ⟨m, hm, h⟩ := (selInj_tors_iff t).1 ht
    exact (selInj_tors_iff _).2 ⟨m, hm, by rw [← map_zsmul, h, map_zero]⟩
  have key : ∀ w : {w : D.W // (l : ℤ) • w = 0}, ∃ u : D.U, Submodule.Quotient.mk u = w.1 ∧
      ∃ y : Y, ∃ t ∈ Submodule.torsion ℤ Y, (l : ℤ) • (u : Y) = D.del y + t := by
    rintro ⟨w, hw⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    refine ⟨u, rfl, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hw
    have hw' : (l : ℤ) • (u : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y := hw
    obtain ⟨a', ⟨y, rfl⟩, t, ht, h⟩ := Submodule.mem_sup.1 hw'
    exact ⟨y, t, ht, h.symm⟩
  choose u hu y t ht hyt using key
  have hsel : ∀ w, (Submodule.Quotient.mk (y w) : Y ⧸ Ct.mt Y l) ∈ D.SelInv l := by
    intro w
    obtain ⟨c, hc⟩ := hl
    refine ⟨y w, rfl, ?_, ?_⟩
    · rw [selInj_mem_mt]
      refine ⟨(u w : Y) + c • y w, -t w, neg_mem (ht w), ?_⟩
      rw [smul_add, hyt w, hdel_apply, smul_smul, ← hc, sub_smul, one_smul]
      abel
    · obtain ⟨i, hi⟩ := (u w).2
      refine ⟨i, ?_⟩
      have e := congrArg D.d (hyt w)
      rw [map_zsmul, map_add (f := _), hdt _ (ht w), add_zero, hdd, ← hi] at e
      rw [← sub_eq_zero]
      apply selInj_delI_inj D
      rw [map_sub, map_zsmul, ← e, sub_self]
  let f : {w : D.W // (l : ℤ) • w = 0} → D.SelInv l := fun w => ⟨_, hsel w⟩
  apply Nat.card_le_card_of_injective f
  intro w w' hww
  have hq : (Submodule.Quotient.mk (y w) : Y ⧸ Ct.mt Y l) = Submodule.Quotient.mk (y w') :=
    congrArg Subtype.val hww
  rw [Submodule.Quotient.eq, selInj_mem_mt] at hq
  obtain ⟨z, t0, ht0, hz⟩ := hq
  apply Subtype.ext
  rw [← hu w, ← hu w', Submodule.Quotient.eq]
  show ((u w : Y) - (u w' : Y)) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y
  have e2 : D.del (y w) - D.del (y w') = (l : ℤ) • D.del z + D.del t0 := by
    rw [← map_sub, ← hz, map_add (f := _), map_zsmul]
  have hs : (u w : Y) - u w' - D.del z ∈ Submodule.torsion ℤ Y := by
    refine htor (l : ℤ) (by exact_mod_cast hl0.ne') ?_
    have e : (l : ℤ) • ((u w : Y) - u w' - D.del z) = D.del t0 + (t w - t w') := by
      rw [smul_sub, smul_sub, hyt w, hyt w',
        show D.del (y w) = (l : ℤ) • D.del z + D.del t0 + D.del (y w') by rw [← e2]; abel]
      abel
    rw [e]
    exact add_mem (hdelt t0 ht0) (sub_mem (ht w) (ht w'))
  rw [show (u w : Y) - u w' = D.del z + ((u w : Y) - u w' - D.del z) by abel]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) hs
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TorsionExponentBound
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem padic_val_one_add_pow_sub_one (l c m : ℕ) (hl : l.Prime) (hc : 1 ≤ c) (h2 : l = 2 → 2 ≤ c)
    (hm : m ≠ 0) : padicValNat l ((1 + l ^ c) ^ m - 1) = c + padicValNat l m := by
  simp only [Nat.padicValNat_def]
  haveI := Fact.mk hl
  have hpow1 : 1 ≤ l ^ c := Nat.one_le_pow c l hl.pos
  have hx1 : 1 < 1 + l ^ c := by omega
  have hdvd : l ∣ (1 + l ^ c) - 1 := by
    rw [Nat.add_sub_cancel_left]
    exact dvd_pow_self l (by omega)
  have hnd : ¬ l ∣ 1 + l ^ c := by
    intro h
    rw [add_comm] at h
    have := (Nat.dvd_add_right (dvd_pow_self l (by omega : c ≠ 0))).1 h
    exact hl.one_lt.ne' (Nat.dvd_one.1 this)
  rcases hl.eq_two_or_odd' with rfl | hodd
  · obtain ⟨d, rfl⟩ : ∃ d, c = d + 2 := ⟨c - 2, by have := h2 rfl; omega⟩
    have h4 : 2 ^ (d + 2) = 4 * 2 ^ d := by ring
    have h := padicValNat.pow_two_sub_pow (x := 1 + 2 ^ (d + 2)) (y := 1) hx1 hdvd hnd
      (n := 2 * m) (by omega) (even_two_mul m)
    rw [one_pow] at h
    have hA : multiplicity 2 (1 + 2 ^ (d + 2) + 1) = 1 := by
      have e : 1 + 2 ^ (d + 2) + 1 = 2 * (1 + 2 * 2 ^ d) := by rw [h4]; ring
      rw [e, Nat.multiplicity_mul (by norm_num) (by omega), Nat.multiplicity_self (by norm_num),
        (Nat.multiplicity_eq_zero_iff.mpr (Or.inr (Or.inr (by omega))))]
    have hB : multiplicity 2 (1 + 2 ^ (d + 2) - 1) = d + 2 := by
      rw [Nat.add_sub_cancel_left, Nat.multiplicity_prime_pow]
    have hC : multiplicity 2 (2 * m) = 1 + multiplicity 2 m := by
      rw [Nat.multiplicity_mul (by norm_num) hm, Nat.multiplicity_self (by norm_num)]
    have hxm : 1 < (1 + 2 ^ (d + 2)) ^ m := Nat.one_lt_pow hm hx1
    obtain ⟨b, hb⟩ : ∃ b, (1 + 2 ^ (d + 2)) ^ m = b + 1 := ⟨_ - 1, (Nat.sub_add_cancel hxm.le).symm⟩
    have hmod : (1 + 2 ^ (d + 2)) ^ m % 4 = 1 := by
      rw [Nat.pow_mod, h4]
      have : (1 + 4 * 2 ^ d) % 4 = 1 := by omega
      rw [this, one_pow]
      rfl
    have hD : multiplicity 2 ((1 + 2 ^ (d + 2)) ^ m + 1) = 1 := by
      obtain ⟨q, hq⟩ : ∃ q, (1 + 2 ^ (d + 2)) ^ m + 1 = 2 * (2 * q + 1) :=
        ⟨((1 + 2 ^ (d + 2)) ^ m + 1) / 4, by omega⟩
      rw [hq, Nat.multiplicity_mul (by norm_num) (by omega), Nat.multiplicity_self (by norm_num),
        (Nat.multiplicity_eq_zero_iff.mpr (Or.inr (Or.inr (by omega))))]
    have hfac : (1 + 2 ^ (d + 2)) ^ (2 * m) - 1 =
        ((1 + 2 ^ (d + 2)) ^ m - 1) * ((1 + 2 ^ (d + 2)) ^ m + 1) := by
      rw [pow_mul', hb, Nat.add_sub_cancel]
      have : (b + 1) ^ 2 = b * (b + 1 + 1) + 1 := by ring
      rw [this, Nat.add_sub_cancel]
    rw [hfac, Nat.multiplicity_mul (by omega) (by omega), hD, hA, hB, hC] at h
    omega
  · have := padicValNat.pow_sub_pow hodd hx1 hdvd hnd hm
    rwa [one_pow, Nat.add_sub_cancel_left, Nat.multiplicity_prime_pow] at this

theorem UpperTheory.V.ZK.Ct.lte :
    ∀ l c ν E : ℕ, l.Prime → 1 ≤ c → (l = 2 → 2 ≤ c) → c ≤ ν → 1 ≤ E → 2 ≤ (1 + l ^ c) ^ E ∧ ((1 + l ^ c) ^ E - 1).factorization l = c + E.factorization l ∧ (((1 + l ^ c) ^ E) ^ l ^ (ν - c) - 1).factorization l = ν + E.factorization l := by
  intro l c ν E hl hc h2 hcν hE
  haveI := Fact.mk hl
  have hE0 : E ≠ 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · have : 2 ≤ 1 + l ^ c := by have := Nat.one_le_pow c l hl.pos; omega
    exact this.trans (Nat.le_self_pow hE0 _)
  · rw [Nat.factorization_def _ hl, Nat.factorization_def _ hl]
    simpa only [← Nat.padicValNat_def] using padic_val_one_add_pow_sub_one l c E hl hc h2 hE0
  · have hval := padic_val_one_add_pow_sub_one l c (E * l ^ (ν - c)) hl hc h2
      (mul_ne_zero hE0 (pow_ne_zero _ hl.ne_zero))
    simp only [Nat.padicValNat_def] at hval
    rw [Nat.factorization_def _ hl, Nat.factorization_def _ hl, ← pow_mul, hval,
      Nat.multiplicity_mul hE0 (pow_ne_zero _ hl.ne_zero), Nat.multiplicity_prime_pow]
    omega
end

