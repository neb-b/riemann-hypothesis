module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.AltInv
section
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds.AltInv

variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))

def IntC (x : C) : Prop := 0 ≤ v x

def IntS {σ : Type*} (f : MvPowerSeries σ C) : Prop := ∀ μ, IntC v (coeff μ f)

variable {v}

theorem intC_zero : IntC v 0 := by
  unfold IntC
  simp
theorem intC_one : IntC v 1 := by
  unfold IntC
  simp
theorem intC_add {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x + y) :=
  le_trans (le_min hx hy) (v.map_add x y)
theorem intC_neg {x : C} (hx : IntC v x) : IntC v (-x) := by
  unfold IntC at *
  rwa [AddValuation.map_neg]
theorem intC_mul {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x * y) := by
  unfold IntC at *
  rw [AddValuation.map_mul]
  exact add_nonneg hx hy
theorem intC_sub {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x - y) := by
  rw [sub_eq_add_neg]
  exact intC_add hx (intC_neg hy)
theorem intC_natCast (n : ℕ) : IntC v (n : C) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact intC_zero
  | succ n ih =>
    rw [Nat.cast_succ]
    exact intC_add ih intC_one
theorem intC_intCast (n : ℤ) : IntC v (n : C) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, Int.cast_natCast]
    exact intC_natCast n
  | negSucc n =>
    rw [Int.cast_negSucc]
    exact intC_neg (intC_natCast _)
theorem intC_sum {ι : Type*} (s : Finset ι) {f : ι → C} (h : ∀ i ∈ s, IntC v (f i)) :
    IntC v (∑ i ∈ s, f i) :=
  Finset.sum_induction _ (IntC v) (fun _ _ => intC_add) intC_zero h
theorem intC_prod {ι : Type*} (s : Finset ι) {f : ι → C} (h : ∀ i ∈ s, IntC v (f i)) :
    IntC v (∏ i ∈ s, f i) :=
  Finset.prod_induction _ (IntC v) (fun _ _ => intC_mul) intC_one h
theorem intC_finsum {ι : Type*} {f : ι → C} (h : ∀ i, IntC v (f i)) : IntC v (∑ᶠ i, f i) := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs]
    exact intC_sum _ fun i _ => h i
  · rw [finsum_of_infinite_support hs]
    exact intC_zero

variable {σ τ : Type*}

theorem intS_mul {f g : MvPowerSeries σ C} (hf : IntS v f) (hg : IntS v g) : IntS v (f * g) := by
  intro μ
  rw [coeff_mul]
  exact intC_sum _ fun p _ => intC_mul (hf _) (hg _)

theorem intS_one : IntS v (1 : MvPowerSeries σ C) := by
  intro μ
  rw [coeff_one]
  split_ifs
  · exact intC_one
  · exact intC_zero

theorem intS_pow {f : MvPowerSeries σ C} (hf : IntS v f) (n : ℕ) : IntS v (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact intS_one
  | succ n ih =>
    rw [pow_succ]
    exact intS_mul ih hf

theorem intS_prod {ι : Type*} (s : Finset ι) {f : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS v (f i)) :
    IntS v (∏ i ∈ s, f i) :=
  Finset.prod_induction _ (IntS v) (fun _ _ => intS_mul) intS_one h

private theorem hasSubst_lemma [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) :
    HasSubst a :=
  ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩

theorem intS_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha0 : ∀ s, constantCoeff (a s) = 0)
    (ha : ∀ s, IntS v (a s)) {γ : MvPowerSeries σ C} (hγ : IntS v γ) : IntS v (subst a γ) := by
  have hsub : HasSubst a := hasSubst_lemma ha0
  intro μ
  rw [coeff_subst hsub]
  refine intC_finsum fun d => ?_
  rw [smul_eq_mul]
  exact intC_mul (hγ d) (intS_prod _ (fun s _ => intS_pow (ha s) _) μ)

def LowLt {σ : Type*} (K : ℕ) (f : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, μ.degree < K → IntC v (coeff μ f)

def OrdV {σ : Type*} (D : ℕ) (f : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, μ.degree < D → coeff μ f = 0

private theorem degree_add_lemma_2 (a b : σ →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  first
  | exact map_add _ a b
  | exact Finsupp.sum_add_index' (h := fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)

theorem low_mul {E D D' : ℕ} {f g : MvPowerSeries σ C} (hf : OrdV D f) (hf' : LowLt (v := v) (E + D) f)
    (hg : OrdV D' g) (hg' : LowLt (v := v) (E + D') g) :
    OrdV (D + D') (f * g) ∧ LowLt (v := v) (E + (D + D')) (f * g) := by
  constructor
  · intro μ hμ
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg : p.1.degree + p.2.degree = μ.degree := by rw [← hp, degree_add_lemma_2]
    by_cases h1 : p.1.degree < D
    · rw [hf p.1 h1, zero_mul]
    · rw [hg p.2 (by omega), mul_zero]
  · intro μ hμ
    rw [coeff_mul]
    refine intC_sum _ fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg : p.1.degree + p.2.degree = μ.degree := by rw [← hp, degree_add_lemma_2]
    by_cases h1 : p.1.degree < D
    · rw [hf p.1 h1, zero_mul]
      exact intC_zero
    · by_cases h2 : p.2.degree < D'
      · rw [hg p.2 h2, mul_zero]
        exact intC_zero
      · exact intC_mul (hf' p.1 (by omega)) (hg' p.2 (by omega))

theorem low_one (E : ℕ) : OrdV 0 (1 : MvPowerSeries σ C) ∧ LowLt (v := v) E (1 : MvPowerSeries σ C) :=
  ⟨fun _ hμ => absurd hμ (Nat.not_lt_zero _), fun μ _ => intS_one μ⟩

theorem low_pow {E D : ℕ} {f : MvPowerSeries σ C} (hf : OrdV D f) (hf' : LowLt (v := v) (E + D) f) (n : ℕ) :
    OrdV (n * D) (f ^ n) ∧ LowLt (v := v) (E + n * D) (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.zero_mul, Nat.add_zero]
    exact low_one E
  | succ n ih =>
    rw [pow_succ, Nat.add_mul, Nat.one_mul]
    exact low_mul ih.1 ih.2 hf hf'

theorem low_prod {E : ℕ} {t : σ → MvPowerSeries σ C} (ht : ∀ s, OrdV 1 (t s))
    (ht' : ∀ s, LowLt (v := v) (E + 1) (t s)) (S : Finset σ) (d : σ → ℕ) :
    OrdV (∑ s ∈ S, d s) (∏ s ∈ S, t s ^ d s) ∧ LowLt (v := v) (E + ∑ s ∈ S, d s) (∏ s ∈ S, t s ^ d s) := by
  refine Finset.induction_on S ?_ ?_
  · rw [Finset.sum_empty, Finset.prod_empty, Nat.add_zero]
    exact low_one E
  · intro a S ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hp := low_pow (ht a) (ht' a) (d a)
    rw [Nat.mul_one] at hp
    exact low_mul hp.1 hp.2 ih.1 ih.2

theorem deg_one_single (d : σ →₀ ℕ) (h : d.degree = 1) : ∃ y, d = Finsupp.single y 1 := by
  have hdeg : ∑ i ∈ d.support, d i = 1 := h
  have h1 : ∀ x ∈ d.support, d x = 1 := by
    intro x hx
    have hle := Finset.single_le_sum (f := fun i => d i) (fun i _ => Nat.zero_le _) hx
    have h0 : d x ≠ 0 := Finsupp.mem_support_iff.1 hx
    omega
  have hcard : d.support.card = 1 := by
    rw [← hdeg, Finset.sum_congr rfl h1]
    simp
  obtain ⟨y, hy⟩ := Finset.card_eq_one.1 hcard
  refine ⟨y, Finsupp.ext fun x => ?_⟩
  by_cases hx : x = y
  · subst hx
    rw [Finsupp.single_eq_same]
    exact h1 x (by rw [hy]; exact Finset.mem_singleton_self x)
  · have hxs : x ∉ d.support := by
      rw [hy]
      simpa using hx
    have hdx : d x = 0 := by
      by_contra h'
      exact hxs (Finsupp.mem_support_iff.2 h')
    rw [hdx, Finsupp.single_apply, if_neg (Ne.symm hx)]

theorem intC_det {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n C) (hA : ∀ i j, IntC v (A i j)) :
    IntC v A.det := by
  rw [Matrix.det_apply]
  refine intC_sum _ fun s _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  exact intC_mul (intC_intCast _) (intC_prod _ fun i _ => hA _ _)

end Formalism.L2.FormalSeriesBounds.AltInv
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.GeNatCast
section
namespace Formalism.L2.FormalSeriesBounds

open Finset

noncomputable section

structure VF (C : Type*) [Field C] where
  v : AddValuation C (WithTop ℝ)
  l : ℕ
  l_prime : l.Prime
  v_l : v (l : C) = 1

variable {C : Type*} [Field C]

namespace VF

variable (V : VF C)

def Ge (w : ℝ) (a : C) : Prop := (w : WithTop ℝ) ≤ V.v a

variable {V}

theorem Ge.mono {w w' : ℝ} {a : C} (h : V.Ge w a) (hw : w' ≤ w) : V.Ge w' a := le_trans (WithTop.coe_le_coe.mpr hw) h

theorem Ge.zero (w : ℝ) : V.Ge w (0 : C) := by
  show ((w : ℝ) : WithTop ℝ) ≤ V.v 0
  rw [AddValuation.map_zero]
  exact le_top

theorem Ge.add {w : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w b) : V.Ge w (a + b) := le_trans (le_min ha hb) (V.v.map_add a b)

theorem Ge.neg {w : ℝ} {a : C} (ha : V.Ge w a) : V.Ge w (-a) := by
  show ((w : ℝ) : WithTop ℝ) ≤ V.v (-a)
  rw [AddValuation.map_neg]
  exact ha

theorem Ge.sub {w : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w b) : V.Ge w (a - b) := by
  rw [sub_eq_add_neg]
  exact Ge.add ha (Ge.neg hb)

theorem Ge.sum {ι : Type*} {s : Finset ι} {f : ι → C} {w : ℝ} (h : ∀ i ∈ s, V.Ge w (f i)) :
    V.Ge w (∑ i ∈ s, f i) := Finset.sum_induction f (fun x => V.Ge w x) (fun _ _ ha hb => Ge.add ha hb) (Ge.zero w) h

theorem Ge.mul {w w' : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w' b) : V.Ge (w + w') (a * b) := by
  show ((w + w' : ℝ) : WithTop ℝ) ≤ V.v (a * b)
  rw [AddValuation.map_mul, WithTop.coe_add]
  exact add_le_add ha hb

theorem Ge.one : V.Ge 0 (1 : C) := by
  show ((0 : ℝ) : WithTop ℝ) ≤ V.v 1
  rw [AddValuation.map_one]
  exact le_of_eq WithTop.coe_zero

theorem Ge.pow {a : C} (ha : V.Ge 0 a) (n : ℕ) : V.Ge 0 (a ^ n) := by
  induction n with
  | zero => simpa using (Ge.one (V := V))
  | succ n ih =>
    rw [pow_succ]
    simpa using Ge.mul ih ha

theorem Ge.mul_int {w : ℝ} {a b : C} (ha : V.Ge 0 a) (hb : V.Ge w b) : V.Ge w (a * b) := by
  simpa using Ge.mul ha hb

theorem ge_l : V.Ge 1 (V.l : C) := (le_of_eq WithTop.coe_one).trans V.v_l.symm.le

theorem l_ne_zero : (V.l : C) ≠ 0 := by
  intro h
  have h1 := V.v_l
  rw [h, AddValuation.map_zero] at h1
  simp at h1

theorem ge_natCast (n : ℕ) : V.Ge 0 (n : C) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Ge.zero 0
  | succ n ih => rw [Nat.cast_succ]; exact Ge.add ih Ge.one

theorem Ge.of_l_mul {w : ℝ} {a : C} (h : V.Ge w ((V.l : C) * a)) : V.Ge (w - 1) a := by
  have h0 : ((w : ℝ) : WithTop ℝ) ≤ 1 + V.v a := by
    have h2 : ((w : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C) * a) := h
    rwa [AddValuation.map_mul, V.v_l] at h2
  show (((w - 1) : ℝ) : WithTop ℝ) ≤ V.v a
  by_cases hva : V.v a = ⊤
  · rw [hva]; exact le_top
  · obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.mp hva
    rw [← hx] at h0 ⊢
    have h' : w ≤ 1 + x := by exact_mod_cast h0
    exact WithTop.coe_le_coe.mpr (by linarith)

theorem Ge.l_mul {w : ℝ} {a : C} (h : V.Ge w a) : V.Ge (1 + w) ((V.l : C) * a) := by
  show ((1 + w : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C) * a)
  rw [AddValuation.map_mul, V.v_l, WithTop.coe_add, WithTop.coe_one]
  exact add_le_add le_rfl h

theorem Ge.l_inv_mul {w : ℝ} {a : C} (h : V.Ge w a) : V.Ge (w - 1) ((V.l : C)⁻¹ * a) := by
  apply Ge.of_l_mul
  rwa [← mul_assoc, mul_inv_cancel₀ l_ne_zero, one_mul]

end VF

section Ops

variable {N : Type*}

def teich (l : ℕ) (c : C) (x : ℕ → N → C) : ℕ → N → C := fun i n => c ^ (l ^ i) * x i n

def Vpow (s : ℕ) (x : ℕ → N → C) : ℕ → N → C := fun i n => if i < s then 0 else x (i - s) n

def Fs (l : ℕ) (x : ℕ → N → C) : ℕ → N → C := fun i n => (l : C) * x (i + 1) n

def sumV (y : ℕ → ℕ → N → C) : ℕ → N → C := fun i n => ∑ s ∈ range (i + 1), y s (i - s) n

def const0 (h : N → C) : ℕ → N → C := fun i n => if i = 0 then h n else 0

end Ops

structure Cart (V : VF C) (d : ℕ) (I J : Type*) where

  ty : I ⊕ J → ZMod d
  Ty : AddSubgroup (ℕ → I ⊕ J → C)
  teich_mem : ∀ c, V.Ge 0 c → ∀ x ∈ Ty, teich V.l c x ∈ Ty
  V_mem : ∀ x ∈ Ty, Vpow 1 x ∈ Ty
  F_mem : ∀ x ∈ Ty, Fs V.l x ∈ Ty
  sumV_mem : ∀ y : ℕ → ℕ → I ⊕ J → C, (∀ s, y s ∈ Ty) → sumV y ∈ Ty

  t2 : ∀ x ∈ Ty, ∀ s, (∀ i < s, x i = 0) → ∀ n, V.Ge 0 (x s n)

  t3 : ∀ ζ : J → C, (∀ j, V.Ge 0 (ζ j)) → const0 (Sum.elim 0 ζ) ∈ Ty

  t4 : ∀ (a : ZMod d) (u : I → C), (∀ c, V.Ge 0 (u c)) → (∀ c, ty (Sum.inl c) ≠ a → u c = 0) →
    ∃ x ∈ Ty, x 0 = Sum.elim u 0 ∧ ∀ (i : ℕ) n, ty n ≠ a + i → x i n = 0

end

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyJointDef
section
namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

def JointEigSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C], IsAlgClosed C → ∀ (n q : ℕ), 2 ≤ q →
    ∀ (T : Set (Matrix (Fin n) (Fin n) C)), (∀ t ∈ T, t ^ q = t) → (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) →
    ∀ v : Fin n → C, ∃ (m : ℕ) (w : Fin m → Fin n → C), v = ∑ j, w j ∧
      ∀ j, ∀ t ∈ T, ∃ c : C, Matrix.mulVec t (w j) = c • w j

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePSplitDef
section
namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePSplit

open Polynomial

def SplitSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (O : Type) [CommRing O] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : O →+* Matrix (Fin n) (Fin n) C) (P : Matrix (Fin n) (Fin n) C) (em : ι → (O →+* C)),
    P * P = P → (∀ x, P * M x = M x * P) → Function.Injective em →
    (∀ x, Polynomial.aeval (M x) (∏ c, (X - Polynomial.C (em c x))) * P = 0) →
    ∀ v : Fin n → C, ∃ w : ι → (Fin n → C), Matrix.mulVec P v = ∑ c, w c ∧ ∀ c x, Matrix.mulVec (M x) (w c) = em c x • w c

end RowTiePSplit

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrPl
section
set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

def tauX {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE] {R : Type} [CommRing R] [Algebra ℤ_[l] R] (τ : OE →+* R) :
    (ℤ_[l] ⊗[ℤ] OE) →ₐ[ℤ_[l]] R :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[l] R) τ.toIntAlgHom (fun _ _ => Commute.all _ _)

def EmbX {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE] {R : Type} [CommRing R] [Algebra ℤ_[l] R]
    (e : ℤ_[l] ⊗[ℤ] OE) : Set (OE →+* R) := {τ | tauX τ e = 1}

def PlaceX (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] (R : Type) [CommRing R] [Algebra ℤ_[l] R] (d : ℕ)
    (em : ZMod d → OE →+* R) : Prop :=
  ∃ e : ℤ_[l] ⊗[ℤ] OE, e * e = e ∧ e ≠ 0 ∧ (∀ f : ℤ_[l] ⊗[ℤ] OE, f * f = f → f * e = f → f = 0 ∨ f = e) ∧
    ∃ (_ : NeZero (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))))
      (t : Fin (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))) ≃ EmbX (R := R) e)
      (jj : ZMod d ≃ Fin (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))),
      (∀ a, jj (a + 1) = jj a + 1) ∧ (∀ a, ((t (jj a) : EmbX (R := R) e) : OE →+* R) = em a) ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))) ℤ_[l]
          (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)),
        IsUnit (Matrix.det (Matrix.of fun i j =>
          tauX ((t j : EmbX (R := R) e) : OE →+* R) (b i : ℤ_[l] ⊗[ℤ] OE)))

def PlaceCriterionOfIdempotent : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R] [Algebra ℤ_[l] R],
    (l : R) ∈ maximalIdeal R → ¬ ((l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) →
    ∀ (d : ℕ) [NeZero d] (em : ZMod d → OE →+* R),
      (∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) →
      (∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) →
      (∃ ε : OE, (∃ y, ε * ε - ε = (l : OE) * y) ∧ (∀ a, em a ε - 1 ∈ maximalIdeal R) ∧
        ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y) → PlaceX l OE R d em

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
end
end

