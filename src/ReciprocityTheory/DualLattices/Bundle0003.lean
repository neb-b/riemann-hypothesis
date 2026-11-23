module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.RankMapLeRank
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.RankA

variable {S : Type} [CommRing S]

lemma col_mem_range {m n : Type} [Fintype n] [DecidableEq n] (A : Matrix m n S) (y : n) :
    (fun x => A x y) ∈ LinearMap.range A.mulVecLin :=
  ⟨Pi.single y 1, by ext x; simp⟩

lemma factor_of_basis {m n ι : Type} [Fintype ι] (A : Matrix m n S)
    (M : Submodule S (m → S)) (b : Module.Basis ι S M) (hA : ∀ y, (fun x => A x y) ∈ M) :
    A = (Matrix.of fun x l => (b l : m → S) x) *
      Matrix.of fun l y => b.repr ⟨fun x => A x y, hA y⟩ l := by
  ext x y
  have h := congrArg (fun z : M => (z : m → S) x) (b.sum_repr ⟨fun x => A x y, hA y⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [← h]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

lemma rank_map_le [StrongRankCondition S] {K : Type} [Field K] (f : S →+* K) {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n S) [Module.Free S (LinearMap.range A.mulVecLin)]
    [Module.Finite S (LinearMap.range A.mulVecLin)] :
    (A.map f).rank ≤ Module.finrank S (LinearMap.range A.mulVecLin) := by
  obtain ⟨N, hN, P, Q, hPQ⟩ : ∃ N, N = Module.finrank S (LinearMap.range A.mulVecLin) ∧
      ∃ (P : Matrix m (Fin N) S) (Q : Matrix (Fin N) n S), A = P * Q :=
    ⟨_, rfl, _, _, factor_of_basis A _ (Module.finBasis S _) (col_mem_range A)⟩
  rw [← hN]
  have h : A.map f = P.map f * Q.map f := by rw [hPQ, Matrix.map_mul]
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))

lemma sum_finrank {ι m : Type} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    [StrongRankCondition S] (e : m → Matrix ι ι S)
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hsum : ∑ i, e i = 1)
    [∀ i, Module.Free S (LinearMap.range (e i).mulVecLin)]
    [∀ i, Module.Finite S (LinearMap.range (e i).mulVecLin)] :
    ∑ i, Module.finrank S (LinearMap.range (e i).mulVecLin) = Fintype.card ι := by
  let M : m → Submodule S (ι → S) := fun i => LinearMap.range (e i).mulVecLin
  have hmem : ∀ i j (y : M j), e i *ᵥ (y : ι → S) = if i = j then (y : ι → S) else 0 := by
    intro i j y
    obtain ⟨z, hz⟩ := y.2
    simp only [Matrix.mulVecLin_apply] at hz
    rw [← hz, mulVec_mulVec, horth]
    split_ifs with h
    · subst h; rfl
    · exact zero_mulVec _
  have hsum' : ∀ x : ι → S, ∑ i, e i *ᵥ x = x := by
    intro x
    rw [← Matrix.sum_mulVec, hsum, one_mulVec]
  let E : (ι → S) ≃ₗ[S] ((i : m) → M i) :=
    { toFun := fun x i => ⟨e i *ᵥ x, x, rfl⟩
      map_add' := fun x y => by ext i : 1; apply Subtype.ext; simp [mulVec_add]
      map_smul' := fun c x => by ext i : 1; apply Subtype.ext; simp [mulVec_smul]
      invFun := fun y => ∑ i, (y i : ι → S)
      left_inv := fun x => hsum' x
      right_inv := fun y => by
        ext i : 1; apply Subtype.ext
        simp only [Matrix.mulVec_sum, hmem, Finset.sum_ite_eq, Finset.mem_univ, if_true] }
  have h1 := E.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype] at h1
  exact h1.symm

lemma free_range_idem [IsLocalRing S] {ι : Type} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι S)
    (he : e * e = e) :
    Module.Free S (LinearMap.range e.mulVecLin) ∧ Module.Finite S (LinearMap.range e.mulVecLin) := by
  let s : (ι → S) →ₗ[S] LinearMap.range e.mulVecLin := e.mulVecLin.rangeRestrict
  have hs : s ∘ₗ (LinearMap.range e.mulVecLin).subtype = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨_, y, rfl⟩ := x
    simp [s, Matrix.mulVec_mulVec, he]
  have : Module.Projective S (LinearMap.range e.mulVecLin) :=
    Module.Projective.of_split (LinearMap.range e.mulVecLin).subtype s hs
  have : Module.Finite S (LinearMap.range e.mulVecLin) :=
    Module.Finite.of_surjective s (LinearMap.surjective_rangeRestrict _)
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

end ReciprocityTheory.PGsh.Up.RankA
end
end

-- bundled from ReciprocityTheory.DualLattices.TensorSpan
section
noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]

def intFun (X : Type) : Submodule R (X → C) where
  carrier := {f | ∀ x, ∃ r : R, algebraMap R C r = f x}
  add_mem' := by
    rintro f g hf hg x
    obtain ⟨r, hr⟩ := hf x
    obtain ⟨s, hs⟩ := hg x
    exact ⟨r + s, by simp [hr, hs]⟩
  zero_mem' := fun _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c f hf x
    obtain ⟨r, hr⟩ := hf x
    exact ⟨c * r, by simp [hr, Algebra.smul_def]⟩

def tensorSpan {X : Type} (M : Submodule R (X → C)) : Submodule R (X × X → C) :=
  Submodule.span R {F | ∃ g ∈ M, ∃ h ∈ M, F = fun p => g p.1 * h p.2}

def IsLat {X : Type} [Fintype X] [DecidableEq X] (M : Submodule R (X → C)) : Prop :=
  ∃ B : Matrix X X C, IsUnit B.det ∧ M = Submodule.span R (Set.range fun j x => B x j)

def HasColen (v : Valuation C NNReal) {X : Type} [Fintype X] [DecidableEq X]
    (M : Submodule R (X → C)) (c : NNReal) : Prop :=
  ∃ B : Matrix X X C, M = Submodule.span R (Set.range fun j x => B x j) ∧ v B.det = c

def addPull (N : Type) [AddCommGroup N] : (N → C) →ₗ[R] (N × N → C) :=
  LinearMap.funLeft R C (fun p : N × N => p.1 + p.2)

structure HopfOrder (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] where
  carrier : Submodule R (N → C)
  lat : IsLat R carrier
  le_int : carrier ≤ intFun R N
  one_mem : (1 : N → C) ∈ carrier
  mul_mem : ∀ f g, f ∈ carrier → g ∈ carrier → f * g ∈ carrier
  comul : ∀ f ∈ carrier, addPull R N f ∈ tensorSpan R carrier
  antipode : ∀ f ∈ carrier, (fun x => f (-x)) ∈ carrier

variable {R}

def dualLat {X : Type} [Fintype X] (M : Submodule R (X → C)) : Submodule R (X → C) where
  carrier := {u | ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a}
  add_mem' := by
    rintro u w hu hw f hf
    obtain ⟨r, hr⟩ := hu f hf
    obtain ⟨s, hs⟩ := hw f hf
    exact ⟨r + s, by simp [hr, hs, add_mul, Finset.sum_add_distrib]⟩
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c u hu f hf
    obtain ⟨r, hr⟩ := hu f hf
    refine ⟨c * r, ?_⟩
    simp only [map_mul, hr, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, mul_assoc]

def fourier {N H : Type} [Fintype N] (e : H → N → C) :
    (N → C) →ₗ[R] (H → C) where
  toFun u h := ∑ a, u a * e h a
  map_add' u w := by ext h; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by ext h; simp [Algebra.smul_def, Finset.mul_sum, mul_assoc]

def augIdeal {X : Type} [AddCommGroup X] (M : Submodule R (X → C)) : Submodule R (X → C) :=
  M ⊓ LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : X => C) 0)

def resK {N : Type} [AddCommGroup N] (K : AddSubgroup N) : (N → C) →ₗ[R] (K → C) :=
  LinearMap.funLeft R C (fun k : K => (k : N))

def pullQ {N : Type} [AddCommGroup N] (K : AddSubgroup N) : (N ⧸ K → C) →ₗ[R] (N → C) :=
  LinearMap.funLeft R C (QuotientAddGroup.mk : N → N ⧸ K)

def extK {N : Type} [AddCommGroup N] (K : AddSubgroup N) [DecidablePred (· ∈ K)] :
    (K → C) →ₗ[R] (N → C) where
  toFun u a := if h : a ∈ K then u ⟨a, h⟩ else 0
  map_add' u w := by ext a; by_cases h : a ∈ K <;> simp [h]
  map_smul' c u := by ext a; by_cases h : a ∈ K <;> simp [h]

def pushQ {N : Type} [AddCommGroup N] [Fintype N] (K : AddSubgroup N)
    [DecidableEq (N ⧸ K)] : (N → C) →ₗ[R] (N ⧸ K → C) where
  toFun u c := ∑ a ∈ Finset.univ.filter (fun a : N => (a : N ⧸ K) = c), u a
  map_add' u w := by ext c; simp [Finset.sum_add_distrib]
  map_smul' c u := by ext d; simp [Finset.smul_sum]

end ReciprocityTheory.PGsh.L2
end
end

-- bundled from ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
section
namespace ReciprocityTheory.PGsh

open MvPowerSeries

noncomputable section

variable {C : Type*} [Field C]

def IsIntV (v : AddValuation C (WithTop ℝ)) (x : C) : Prop := 0 ≤ v x

def MvIsInt (v : AddValuation C (WithTop ℝ)) {σ : Type*} (f : MvPowerSeries σ C) : Prop :=
  ∀ α, IsIntV v (coeff α f)

def PsIsInt (v : AddValuation C (WithTop ℝ)) (f : PowerSeries C) : Prop :=
  ∀ n, IsIntV v (PowerSeries.coeff n f)

theorem v_eq_zero_of_pow_eq_one {v : AddValuation C (WithTop ℝ)} {z : C} {N : ℕ} (hN : N ≠ 0)
    (hz : z ^ N = 1) : v z = 0 := by
  have h1 : N • v z = 0 := by rw [← AddValuation.map_pow, hz, AddValuation.map_one]
  generalize v z = x at h1 ⊢
  induction x using WithTop.recTopCoe with
  | top =>
    exfalso
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
    rw [succ_nsmul, WithTop.add_top] at h1
    exact WithTop.top_ne_zero h1
  | coe r =>
    rw [← WithTop.coe_nsmul] at h1
    have h2 : N • r = 0 := WithTop.coe_eq_zero.mp h1
    rw [nsmul_eq_mul] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (Nat.cast_eq_zero.mp h) hN
    · rw [h]; rfl

structure LogFGL (v : AddValuation C (WithTop ℝ)) (d : ℕ) where
  lg : Fin d → MvPowerSeries (Fin d) C
  lg_const : ∀ a, constantCoeff (lg a) = 0
  lg_lin : ∀ a b, coeff (Finsupp.single b 1) (lg a) = if a = b then 1 else 0
  F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) C
  F_int : ∀ a, MvIsInt v (F a)
  F_const : ∀ a, constantCoeff (F a) = 0
  lg_F : ∀ a, subst F (lg a) =
    subst (fun b => X (Sum.inl b)) (lg a) + subst (fun b => X (Sum.inr b)) (lg a)

def IsCurve (v : AddValuation C (WithTop ℝ)) {d : ℕ} (ga : Fin d → PowerSeries C) : Prop :=
  ∀ a, PowerSeries.constantCoeff (ga a) = 0 ∧ PsIsInt v (ga a)

def tangent {d : ℕ} (ga : Fin d → PowerSeries C) : Fin d → C :=
  fun a => PowerSeries.coeff 1 (ga a)

def rescaleCurve {d : ℕ} (x : C) (ga : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => PowerSeries.rescale x (ga a)

namespace LogFGL

variable {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)

def lgCurve (ga : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => subst ga (G.lg a)

def add (ga gb : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => subst (Sum.elim ga gb) (G.F a)

def sumList (G : LogFGL v d) : List (Fin d → PowerSeries C) → (Fin d → PowerSeries C)
  | [] => 0
  | g :: l => G.add g (sumList G l)

def sumF {m : ℕ} (g : Fin m → Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  G.sumList (List.ofFn g)

def nsmulF (G : LogFGL v d) : ℕ → (Fin d → PowerSeries C) → (Fin d → PowerSeries C)
  | 0, _ => 0
  | n + 1, ga => G.add ga (nsmulF G n ga)

def lc (p : ℕ) (ga : Fin d → PowerSeries C) (n : ℕ) : Fin d → C :=
  fun a => PowerSeries.coeff (p ^ n) (G.lgCurve ga a)

def IsPTypical (p : ℕ) (ga : Fin d → PowerSeries C) : Prop :=
  ∀ a m, (∀ n, m ≠ p ^ n) → PowerSeries.coeff m (G.lgCurve ga a) = 0

def IsOfType (p : ℕ) {h : ℕ} (ty : Fin d → ZMod h) (i : ZMod h)
    (ga : Fin d → PowerSeries C) : Prop :=
  G.IsPTypical p ga ∧ ∀ (n : ℕ) a, ty a ≠ i + (n : ZMod h) → G.lc p ga n a = 0

end LogFGL

structure MuAction {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d) (p h : ℕ)
    (ty : Fin d → ZMod h) where
  mul : C → Fin d → MvPowerSeries (Fin d) C
  mul_int : ∀ z, z ^ (p ^ h - 1) = 1 → ∀ a, MvIsInt v (mul z a)
  mul_const : ∀ z a, constantCoeff (mul z a) = 0
  lg_mul : ∀ z, z ^ (p ^ h - 1) = 1 → ∀ a,
    subst (mul z) (G.lg a) = (z ^ (p ^ (ty a).val)) • G.lg a

def expComp [CharZero C] (Ω : C) (lg : PowerSeries C) : PowerSeries C :=
  PowerSeries.mk fun m => ∑ n ∈ Finset.range (m + 1),
    Ω ^ n / (n.factorial : C) * PowerSeries.coeff m (lg ^ n)

def lgSum {d M : ℕ} (p : ℕ) (c : Fin d → ℕ → Fin d → C)
    (t : Fin d → MvPowerSeries (Fin M) C) (b : Fin d) : MvPowerSeries (Fin M) C :=
  fun α => ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n b * coeff α (t a ^ (p ^ n))

def OrdGe (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ) (g : MvPowerSeries (Fin M) C)
    (r : ℝ) : Prop :=
  ∀ α : Fin M →₀ ℕ, (((r - ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) ≤ v (coeff α g)

def radius (p : ℕ) (k : ℤ) : ℝ := (1 + (p : ℝ) ^ (-(2 * k + 1))) / ((p : ℝ) ^ 2 - 1)

end

end ReciprocityTheory.PGsh
end

