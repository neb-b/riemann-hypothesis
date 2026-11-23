module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0003
public import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.HasUniqueFixedPoint

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

private theorem exists_subring_iff_ge_zero : ∃ R : Subring C, ∀ a, a ∈ R ↔ V.Ge 0 a := by
  refine ⟨{ carrier := {a | V.Ge 0 a}
            mul_mem' := ?_
            one_mem' := ?_
            add_mem' := ?_
            zero_mem' := ?_
            neg_mem' := ?_ }, fun a => Iff.rfl⟩
  · intro a b ha hb
    have ha' : ((0 : ℝ) : WithTop ℝ) ≤ V.v a := ha
    have hb' : ((0 : ℝ) : WithTop ℝ) ≤ V.v b := hb
    show ((0 : ℝ) : WithTop ℝ) ≤ V.v (a * b)
    rw [AddValuation.map_mul]
    rw [WithTop.coe_zero] at ha' hb' ⊢
    exact add_nonneg ha' hb'
  · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 1
    rw [AddValuation.map_one, WithTop.coe_zero]
  · intro a b ha hb
    have ha' : ((0 : ℝ) : WithTop ℝ) ≤ V.v a := ha
    have hb' : ((0 : ℝ) : WithTop ℝ) ≤ V.v b := hb
    show ((0 : ℝ) : WithTop ℝ) ≤ V.v (a + b)
    exact le_trans (le_min ha' hb') (V.v.map_add a b)
  · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
    rw [AddValuation.map_zero]
    exact le_top
  · intro a ha
    have ha' : ((0 : ℝ) : WithTop ℝ) ≤ V.v a := ha
    show ((0 : ℝ) : WithTop ℝ) ≤ V.v (-a)
    rw [AddValuation.map_neg]
    exact ha'

theorem VF.Ge.prod {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.Ge 0 (∏ i ∈ s, f i) := by
  obtain ⟨R, hR⟩ := exists_subring_iff_ge_zero (V := V)
  exact (hR _).1 (prod_mem fun i hi => (hR _).2 (h i hi))

theorem det_int (M : Matrix I I C) (h : ∀ i j, V.Ge 0 (M i j)) : V.Ge 0 M.det := by
  obtain ⟨R, hR⟩ := exists_subring_iff_ge_zero (V := V)
  have hM : M = (Matrix.of fun a b => (⟨M a b, (hR _).2 (h a b)⟩ : R)).map R.subtype := by
    ext a b
    rfl
  rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (hR _).1 (Subtype.mem _)

theorem inv_unit_int {a : C} (h : V.v a = 0) : V.Ge 0 a⁻¹ := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at h
    exact WithTop.top_ne_zero h
  have e : V.v a + V.v a⁻¹ = 0 := by
    rw [← AddValuation.map_mul, mul_inv_cancel₀ ha, AddValuation.map_one]
  rw [h, zero_add] at e
  show ((0 : ℝ) : WithTop ℝ) ≤ V.v a⁻¹
  rw [e, WithTop.coe_zero]

theorem inv_int (M : Matrix I I C) (h : ∀ i j, V.Ge 0 (M i j)) (hd : V.v M.det = 0) :
    ∀ i j, V.Ge 0 (M⁻¹ i j) := by
  obtain ⟨R, hR⟩ := exists_subring_iff_ge_zero (V := V)
  have hadj : ∀ i j, V.Ge 0 (M.adjugate i j) := by
    have hM : M = (Matrix.of fun a b => (⟨M a b, (hR _).2 (h a b)⟩ : R)).map R.subtype := by
      ext a b
      rfl
    intro i j
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    exact (hR _).1 (Subtype.mem _)
  intro i j
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (hR _).1 (mul_mem ((hR _).2 (inv_unit_int hd)) ((hR _).2 (hadj i j)))

namespace Cart

variable (X : Cart V d I J)

variable {X} {L : (I ⊕ J → C) → ℕ → I ⊕ J → C}

end Cart

namespace Sys

variable {X : Cart V d I J} (S : Sys X)

theorem mem (c : I) : S.cur c ∈ X.Ty := (S.curve c).1

theorem pure (c : I) : ∀ (i : ℕ) n, X.ty n ≠ X.ty (Sum.inl c) + i → S.cur c i n = 0 := (S.curve c).2.2

theorem cur_zero_inl (c k : I) : S.cur c 0 (Sum.inl k) = S.tan c k := by
  rw [(S.curve c).2.1]
  rfl

theorem be_zero (c : I) (κ : J) : S.cur c 0 (Sum.inr κ) = 0 := by
  rw [(S.curve c).2.1]
  rfl

def U : Matrix I I C := Matrix.of S.tan

theorem U_int (c k : I) : V.Ge 0 (S.U c k) := by
  have := X.t2 _ (S.mem c) 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) (Sum.inl k)
  rw [S.cur_zero_inl] at this
  exact this

theorem U_det_ne : S.U.det ≠ 0 := by
  intro h0
  have := S.unimod
  change V.v S.U.det = 0 at this
  rw [h0, AddValuation.map_zero] at this
  exact WithTop.top_ne_zero this

def co (h : I ⊕ J → C) (b : I) : C := ∑ k, h (Sum.inl k) * S.U⁻¹ k b

theorem co_int {h : I ⊕ J → C} (hh : ∀ n, V.Ge 0 (h n)) (b : I) : V.Ge 0 (S.co h b) := by
  obtain ⟨R, hR⟩ := exists_subring_iff_ge_zero (V := V)
  have hinv := inv_int S.U (fun i j => S.U_int i j) S.unimod
  show V.Ge 0 (∑ k, h (Sum.inl k) * S.U⁻¹ k b)
  exact (hR _).1 (sum_mem fun k _ => mul_mem ((hR _).2 (hh _)) ((hR _).2 (hinv k b)))

theorem co_spec (h : I ⊕ J → C) (k : I) : ∑ b, S.co h b * S.U b k = h (Sum.inl k) := by
  have hU : S.U⁻¹ * S.U = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have e : ∀ j, ∑ b, S.U⁻¹ j b * S.U b k = (1 : Matrix I I C) j k := fun j => by
    rw [← hU, Matrix.mul_apply]
  simp only [co, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, e, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Sys

private theorem ge_zero_l_pow_mul_of_mem_Ty (X : Cart V d I J) :
    ∀ (i : ℕ) (x : ℕ → I ⊕ J → C), x ∈ X.Ty → ∀ n, V.Ge 0 ((V.l : C) ^ i * x i n) := by
  intro i
  induction i with
  | zero =>
    intro x hx n
    rw [pow_zero, one_mul]
    exact X.t2 x hx 0 (fun j hj => absurd hj (Nat.not_lt_zero _)) n
  | succ i ih =>
    intro x hx n
    have h := ih (Fs V.l x) (X.F_mem x hx) n
    simp only [Fs] at h
    rw [pow_succ, mul_assoc]
    exact h

private theorem ge_neg_of_ge_zero_l_pow_mul (i : ℕ) (y : C) (h : V.Ge 0 ((V.l : C) ^ i * y)) : V.Ge (-(i : ℝ)) y := by
  unfold VF.Ge at *
  rw [AddValuation.map_mul, AddValuation.map_pow, V.v_l] at h
  have hi : (i • (1 : WithTop ℝ)) = ((i : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]
  rw [hi] at h
  by_cases hy : V.v y = ⊤
  · rw [hy]
    exact le_top
  · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hy
    rw [← ht] at h ⊢
    rw [← WithTop.coe_add] at h
    have h' := WithTop.coe_le_coe.mp h
    exact WithTop.coe_le_coe.mpr (by linarith)

theorem lattice_inclusion_forms_injective (X : Cart V d I J) : LatticeInclusionFormsInjective X := by
  intro S c i n
  exact ge_neg_of_ge_zero_l_pow_mul i _ (ge_zero_l_pow_mul_of_mem_Ty X i _ (S.mem c) n)

private theorem ge_mono' {w w' : ℝ} {a : C} (h : V.Ge w a) (hw : w' ≤ w) : V.Ge w' a :=
  le_trans (WithTop.coe_le_coe.mpr hw) h

theorem eq16 (X : Cart V d I J) : Eq16 X := by
  intro a u x hx i hi
  rcases Nat.lt_or_ge i 2 with h2 | h2
  · obtain rfl : i = 1 := by omega
    refine ⟨fun k => ?_, fun κ => ?_⟩
    · rw [hx.2 k]
      show ((_ : ℝ) : WithTop ℝ) ≤ V.v 0
      rw [AddValuation.map_zero]
      exact le_top
    · exact ge_mono' (hx.bound_one _) (by norm_num)
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    refine ⟨fun k => ge_mono' (hx.bound j _) (by push_cast; linarith),
      fun κ => ge_mono' (hx.bound j _) (by push_cast; linarith [le_max_right (1 : ℝ) ((j : ℝ) + 2 - 1)])⟩

theorem sysExists (X : Cart V d I J) : SysExists X := by
  intro u hu hty hdet
  have hc : ∀ c, ∃ x, X.IsCurve (X.ty (Sum.inl c)) (u c) x := fun c => by
    obtain ⟨x, hx, h0, hp⟩ := X.t4 (X.ty (Sum.inl c)) (u c) (hu c) (fun k hk => hty c k hk)
    exact ⟨x, hx, h0, hp⟩
  choose cur hcur using hc
  exact ⟨⟨u, cur, hcur, hdet⟩, rfl⟩

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
section
noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds

open Formalism.BaseCaseIdentities (OrdGE NoConst)

section Gen

variable {k : Type*} [Field k] {Z B : Type*}

structure Contr (Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)) : Prop where
  noConst : ∀ t, NoConst (Ψ t)
  contr : ∀ (t t' : B → MvPowerSeries Z k) (n : ℕ), NoConst t → NoConst t' →
    (∀ c, OrdGE (n + 1) (t c - t' c)) → ∀ b, OrdGE (n + 2) (Ψ t b - Ψ t' b)

namespace Contr

variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)

include H

theorem noConst_iterate {t : B → MvPowerSeries Z k} (ht : NoConst t) (n : ℕ) :
    NoConst (Ψ^[n] t) := by
  cases n with
  | zero => simpa using ht
  | succ n =>
    rw [Function.iterate_succ_apply']
    exact H.noConst _

theorem iterate_close {a b : B → MvPowerSeries Z k} (ha : NoConst a) (hb : NoConst b) (n : ℕ) :
    ∀ c, OrdGE (n + 1) (Ψ^[n] a c - Ψ^[n] b c) := by
  induction n with
  | zero =>
    intro c A hA
    simp only [Function.iterate_zero, id_eq, map_sub, ha c A hA, hb c A hA, sub_zero]
  | succ n ih =>
    intro c
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact H.contr _ _ n (H.noConst_iterate ha n) (H.noConst_iterate hb n) ih c

omit H in
theorem noConst_zero : NoConst (0 : B → MvPowerSeries Z k) := by
  intro c A _
  simp

def fixPt (_H : Contr Ψ) : B → MvPowerSeries Z k := fun c A => coeff A (Ψ^[A.degree] 0 c)

theorem coeff_iterate_zero (c : B) (A : Z →₀ ℕ) {n : ℕ} (hn : A.degree ≤ n) :
    coeff A (Ψ^[n] 0 c) = coeff A (H.fixPt c) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e : coeff A (H.fixPt c) = coeff A (Ψ^[A.degree] 0 c) := rfl
  have h1 := H.iterate_close (a := Ψ^[j] 0) (b := 0) (H.noConst_iterate noConst_zero j)
    noConst_zero A.degree c A (Nat.lt_succ_self _)
  rw [map_sub, sub_eq_zero] at h1
  rw [Function.iterate_add_apply, e]
  exact h1

theorem fixPt_close (n : ℕ) (c : B) : OrdGE (n + 1) (H.fixPt c - Ψ^[n] 0 c) := by
  intro A hA
  rw [map_sub, ← H.coeff_iterate_zero c A (Nat.lt_succ_iff.mp hA), sub_self]

theorem noConst_fixPt : NoConst H.fixPt := by
  intro c A hA
  have h := H.fixPt_close 0 c A hA
  simpa using h

theorem fix_fixPt : Ψ H.fixPt = H.fixPt := by
  funext c
  ext A
  have h1 := H.contr H.fixPt (Ψ^[A.degree] 0) A.degree H.noConst_fixPt
    (H.noConst_iterate noConst_zero _) (fun c' => H.fixPt_close A.degree c') c A (by omega)
  rw [map_sub, sub_eq_zero, ← Function.iterate_succ_apply' Ψ A.degree 0] at h1
  rw [h1, H.coeff_iterate_zero c A (Nat.le_succ _)]

theorem exists_unique : ∃! t : B → MvPowerSeries Z k, NoConst t ∧ Ψ t = t := by
  refine ⟨H.fixPt, ⟨H.noConst_fixPt, H.fix_fixPt⟩, ?_⟩
  rintro t ⟨ht, hft⟩
  funext c
  ext A
  have h1 := H.iterate_close ht H.noConst_fixPt A.degree c A (Nat.lt_succ_self _)
  rw [Function.iterate_fixed hft, Function.iterate_fixed H.fix_fixPt, map_sub, sub_eq_zero] at h1
  exact h1

end Contr

theorem noConst_iff (t : B → MvPowerSeries Z k) :
    NoConst t ↔ ∀ c, MvPowerSeries.constantCoeff (t c) = 0 := by
  constructor
  · intro h c
    have h0 := h c 0 (by simp)
    simpa using h0
  · intro h c A hA
    have hA0 : A.degree = 0 := by omega
    have hA1 : A = 0 := by
      first
      | exact (Finsupp.degree_eq_zero_iff A).mp hA0
      | exact Finsupp.degree_eq_zero_iff.mp hA0
      | simpa using hA0
    subst hA1
    simpa using h c

end Gen

section Main

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {X : Cart V d I J}

namespace Sys

variable (S : Sys X)

def Mt : Matrix I I C := Matrix.of S.tan

theorem al_zero (c x : I) : S.al c 0 x = S.Mt c x := by
  have h := S.3 c
  unfold Cart.IsCurve at h
  unfold Sys.al
  rw [h.2.1]
  rfl

theorem det_ne : S.Mt.det ≠ 0 := by
  intro h
  have h5 := S.4
  change V.v S.Mt.det = 0 at h5
  rw [h, AddValuation.map_zero] at h5
  simp at h5

def Rr (t : I → MvPowerSeries I C) (x : I) (μ : I →₀ ℕ) : C :=
  ∑ s ∈ Finset.range μ.degree, ∑ c : I, S.al c (s + 1) x * coeff μ (t c ^ (V.l ^ (s + 1)))

def dl (x : I) (μ : I →₀ ℕ) : C := if μ = Finsupp.single x 1 then 1 else 0

def Ps (t : I → MvPowerSeries I C) : I → MvPowerSeries I C := fun c μ =>
  Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹ c

theorem coeff_Ps (t : I → MvPowerSeries I C) (c : I) (μ : I →₀ ℕ) :
    coeff μ (S.Ps t c) = Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹ c := rfl

theorem two_le_pow (s : ℕ) : 2 ≤ V.l ^ (s + 1) := by
  first
  | exact V.3.two_le.trans (Nat.le_self_pow (Nat.succ_ne_zero s) _)
  | exact le_trans V.3.two_le (Nat.le_self_pow (by omega) _)
  | calc 2 ≤ V.l := V.3.two_le
      _ = V.l ^ 1 := (pow_one _).symm
      _ ≤ V.l ^ (s + 1) := Nat.pow_le_pow_right V.3.pos (by omega)

theorem contr : Contr S.Ps := by
  refine ⟨?_, ?_⟩
  · intro t c A hA
    have hA0 : A.degree = 0 := by omega
    rw [coeff_Ps]
    have : (fun x => dl x A - S.Rr t x A) = (0 : I → C) := by
      funext x
      have h1 : dl (C := C) x A = 0 := by
        unfold dl
        rw [if_neg]
        intro h
        rw [h, Finsupp.degree_single] at hA0
        omega
      have h2 : S.Rr t x A = 0 := by
        unfold Rr
        rw [hA0]
        simp
      simp [h1, h2]
    rw [this, Matrix.zero_vecMul]
    rfl
  · intro t t' n ht ht' h b A hA
    rw [map_sub, coeff_Ps, coeff_Ps, sub_eq_zero]
    have : (fun x => dl x A - S.Rr t x A) = (fun x => dl x A - S.Rr t' x A) := by
      funext x
      congr 1
      unfold Rr
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ => ?_
      have hN := two_le_pow (V := V) s
      have := Formalism.BaseCaseIdentities.OrdGE.pow_sub_pow (ht c) (ht' c) (h c) (N := V.l ^ (s + 1)) (by omega) A
        (by omega)
      rw [map_sub, sub_eq_zero] at this
      rw [this]
    rw [this]

theorem eqn_eq (t : I → MvPowerSeries I C) (x : I) (μ : I →₀ ℕ) :
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ c : I,
        S.al c s x * MvPowerSeries.coeff μ (t c ^ (V.l ^ s))) =
      Matrix.vecMul (fun c => coeff μ (t c)) S.Mt x + S.Rr t x μ := by
  rw [Finset.sum_range_succ', add_comm (Matrix.vecMul _ _ _)]
  congr 1
  all_goals first
    | rfl
    | (show _ = ∑ c, coeff μ (t c) * S.Mt c x
       exact Finset.sum_congr rfl fun c _ => by rw [S.al_zero c x, pow_zero, pow_one, mul_comm])

theorem isT_iff (t : I → MvPowerSeries I C) : S.IsT t ↔ NoConst t ∧ S.Ps t = t := by
  have hdet : IsUnit S.Mt.det := isUnit_iff_ne_zero.mpr S.det_ne
  have key : ∀ μ : I →₀ ℕ, ((∀ x, Matrix.vecMul (fun c => coeff μ (t c)) S.Mt x + S.Rr t x μ = dl x μ) ↔
      (fun c => coeff μ (t c)) = Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹) := by
    intro μ
    constructor
    · intro h
      have h' : Matrix.vecMul (fun c => coeff μ (t c)) S.Mt = fun x => dl x μ - S.Rr t x μ := by
        funext x
        exact eq_sub_of_add_eq (h x)
      rw [← h', Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
    · intro h x
      rw [h, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
      simp
  rw [Sys.IsT, noConst_iff]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · funext c
    ext μ
    rw [S.coeff_Ps]
    have hk := (key μ).mp (fun x => by rw [← S.eqn_eq t x μ]; exact h x μ)
    exact (congrFun hk c).symm
  · intro x μ
    rw [S.eqn_eq t x μ]
    refine (key μ).mpr ?_ x
    funext c
    rw [← S.coeff_Ps, h]

end Sys

theorem tExistsUnique (X : Cart V d I J) : TExistsUnique X := by
  intro S
  obtain ⟨t, ⟨h1, h2⟩, hu⟩ := S.contr.exists_unique
  exact ⟨t, (S.isT_iff t).mpr ⟨h1, h2⟩, fun t' ht' => hu t' ((S.isT_iff t').mp ht')⟩

end Main

end Formalism.L2.FormalSeriesBounds
end
end

