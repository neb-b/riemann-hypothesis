module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LoweringPartRightActionInlInr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.EqZeroOfFockInnerSelfRe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistHW

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.BlockDegreeAntitone
section
noncomputable section

open MvPolynomial FockH1Action

namespace PI.FJMF

def BlockAntitone : Prop := ∀ (σ : Type) (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι →
  ∀ (α : Fin m → ℕ) (P : MvPolynomial σ ℂ), P ≠ 0 → (∀ a b : Fin m, a < b → PI.FJM.bRow ι a b P = 0) →
    (∀ e ∈ P.support, ∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) → Antitone α

section Block

variable {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ)

theorem bRow_apply' (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b P = ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (b, k)) P := by
  simp [PI.FJM.bRow, LinearMap.sum_apply, Module.End.mul_apply]

theorem pd_X_mul [DecidableEq σ] (l v : σ) (Q : MvPolynomial σ ℂ) :
    pderiv l (X v * Q) = X v * pderiv l Q + (if v = l then Q else 0) := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, Pi.single_apply]
  split_ifs <;> simp

theorem sum_ite_row [DecidableEq σ] (hι : Function.Injective ι) (b : Fin m) (k : Fin n) (G : Fin n → MvPolynomial σ ℂ) :
    ∑ j : Fin n, (if ι (b, j) = ι (b, k) then G j else 0) = G k := by
  simp [hι.eq_iff]

theorem EF_expand (hι : Function.Injective ι) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b (PI.FJM.bRow ι b a P) =
      (∑ k : Fin n, ∑ j : Fin n, X (ι (a, k)) * (X (ι (b, j)) * pderiv (ι (b, k)) (pderiv (ι (a, j)) P))) +
        ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (a, k)) P := by
  classical
  rw [bRow_apply' ι a b, bRow_apply' ι b a]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, pd_X_mul, Finset.sum_add_distrib, sum_ite_row ι hι, mul_add, Finset.mul_sum]

private theorem pderiv_pderiv_comm' {σ : Type} (i j : σ) (p : MvPolynomial σ ℂ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  have h : ⁅(pderiv i : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)),
      (pderiv j : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X, Derivation.zero_apply]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have := congrArg (fun D => D p) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at this
  exact sub_eq_zero.1 this

theorem comm_eq (hι : Function.Injective ι) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b (PI.FJM.bRow ι b a P) - PI.FJM.bRow ι b a (PI.FJM.bRow ι a b P) =
      ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (a, k)) P - ∑ k : Fin n, X (ι (b, k)) * pderiv (ι (b, k)) P := by
  rw [EF_expand ι hι a b, EF_expand ι hι b a]
  have hS : (∑ k : Fin n, ∑ j : Fin n,
      X (ι (b, k)) * (X (ι (a, j)) * pderiv (ι (a, k)) (pderiv (ι (b, j)) P))) =
      ∑ k : Fin n, ∑ j : Fin n, X (ι (a, k)) * (X (ι (b, j)) * pderiv (ι (b, k)) (pderiv (ι (a, j)) P)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [pderiv_pderiv_comm' (ι (a, j)) (ι (b, k)) P]
    ring
  rw [hS]
  abel

theorem euler_row (a : Fin m) (c : ℕ) (P : MvPolynomial σ ℂ)
    (hP : ∀ e ∈ P.support, ∑ k : Fin n, e (ι (a, k)) = c) :
    ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (a, k)) P = (c : ℂ) • P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.mul_sum, X_mul_pderiv_monomial]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← Finset.sum_smul, hP e he]
  exact (Nat.cast_smul_eq_nsmul ℂ c _).symm

end Block

section Inner

variable {σ : Type}

theorem inner_zero_right (P : MvPolynomial σ ℂ) : fockInner P 0 = 0 := by
  unfold fockInner
  simp

theorem inner_sum_right {ι : Type*} (t : Finset ι) (P : MvPolynomial σ ℂ) (f : ι → MvPolynomial σ ℂ) :
    fockInner P (∑ i ∈ t, f i) = ∑ i ∈ t, fockInner P (f i) := by
  induction t using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, inner_zero_right]
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, FockRaiseLowInner.fockInner_add_right, ih]

theorem inner_conj (P Q : MvPolynomial σ ℂ) : fockInner Q P = starRingEnd ℂ (fockInner P Q) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [FockRaiseLowInner.fockInner_eq_sum_left Q P (P.support ∪ Q.support) Finset.subset_union_right,
    FockRaiseLowInner.fockInner_eq_sum_left P Q (P.support ∪ Q.support) Finset.subset_union_left, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, map_mul, Complex.conj_conj, FockRaiseLowInner.wt_conj]
  ring

theorem inner_sum_left {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ ℂ) (Q : MvPolynomial σ ℂ) :
    fockInner (∑ i ∈ t, f i) Q = ∑ i ∈ t, fockInner (f i) Q := by
  induction t using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, FockRaiseLowInner.fockInner_zero_left]
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, FockRaiseLowInner.fockInner_add_left, ih]

theorem inner_X_left (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner (X l * P) Q = fockInner P (pderiv l Q) := by
  rw [inner_conj Q (X l * P), FockRaiseLowInner.fockInner_mul_X, inner_conj P (pderiv l Q), Complex.conj_conj]

theorem inner_pd_left (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner (pderiv l P) Q = fockInner P (X l * Q) := by
  rw [inner_conj Q (pderiv l P), ← inner_X_left l Q P, inner_conj P (X l * Q), Complex.conj_conj]

end Inner

theorem bRow_adj {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (x y : MvPolynomial σ ℂ) :
    fockInner (PI.FJM.bRow ι b a x) y = fockInner x (PI.FJM.bRow ι a b y) := by
  rw [bRow_apply' ι b a x, bRow_apply' ι a b y, inner_sum_left, inner_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_X_left, inner_pd_left]

theorem block_degree_antitone : BlockAntitone := by
  intro σ m n ι hι α P hP hE hdeg a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · have hc := comm_eq ι hι a b P
    rw [hE a b h, map_zero, sub_zero, euler_row ι a (α a) P (fun e he => hdeg e he a),
      euler_row ι b (α b) P (fun e he => hdeg e he b)] at hc
    have hadj := bRow_adj ι a b P (PI.FJM.bRow ι b a P)
    rw [hc, ← sub_smul, FockRaiseLowInner.fockInner_smul_right] at hadj
    have h1 := PI.FockOneDegW.Inner.fockInner_self_re_nonneg (PI.FJM.bRow ι b a P)
    rw [hadj] at h1
    have hre := PI.FockOneDegW.Inner.fockInner_self_re_nonneg P
    have him := PI.FockOneDegW.Inner.fockInner_self_im P
    have hpos : 0 < (fockInner P P).re := lt_of_le_of_ne hre
      (fun h0 => hP (PI.FockOneDegW.Inner.eq_zero_of_fockInner_self_re P h0.symm))
    rw [Complex.mul_re, him, mul_zero, sub_zero] at h1
    simp only [Complex.sub_re, Complex.natCast_re] at h1
    have hlt : (α b : ℝ) ≤ α a := by nlinarith
    exact_mod_cast hlt

end PI.FJMF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.GlobalTheory
section
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJM

def nP {n : ℕ} (f : Fin n → ℚ) : ℕ := (Finset.univ.filter fun i => 0 < f i).card

def nN {n : ℕ} (f : Fin n → ℚ) : ℕ := (Finset.univ.filter fun i => f i < 0).card

theorem nP_le_nW {n : ℕ} (f : Fin n → ℚ) : nP f ≤ n := by
  unfold nP
  exact (Finset.card_filter_le _ _).trans (Finset.card_fin n).le

theorem nN_le {n : ℕ} (f : Fin n → ℚ) : nN f ≤ n := by
  unfold nN
  exact (Finset.card_filter_le _ _).trans (Finset.card_fin n).le

section Blocks

variable (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)

def leftWeightFirst : Fin p → ℚ := fun i => nu1 p q r s μ (.inl i)
def leftWeightSecond : Fin q → ℚ := fun j => nu1 p q r s μ (.inr j)
def rightWeightFirst : Fin r → ℚ := fun k => nu2 p q r s μ' (.inl k)
def rightWeightSecond : Fin s → ℚ := fun l => nu2 p q r s μ' (.inr l)

def ιA : Fin (nP (leftWeightFirst p q r s μ)) × Fin (nP (rightWeightFirst p q r s μ')) → Ln p q r s := fun x =>
  (.inl (Fin.castLE (nP_le_nW _) x.1), .inl (Fin.castLE (nP_le_nW _) x.2))

def ιB : Fin (nN (leftWeightFirst p q r s μ)) × Fin (nN (rightWeightSecond p q r s μ')) → Ln p q r s := fun x =>
  (.inl (Fin.rev (Fin.castLE (nN_le _) x.1)), .inr (Fin.rev (Fin.castLE (nN_le _) x.2)))

def ιC : Fin (nP (leftWeightSecond p q r s μ)) × Fin (nP (rightWeightSecond p q r s μ')) → Ln p q r s := fun x =>
  (.inr (Fin.castLE (nP_le_nW _) x.1), .inr (Fin.castLE (nP_le_nW _) x.2))

def ιD : Fin (nN (leftWeightSecond p q r s μ)) × Fin (nN (rightWeightFirst p q r s μ')) → Ln p q r s := fun x =>
  (.inr (Fin.rev (Fin.castLE (nN_le _) x.1)), .inl (Fin.rev (Fin.castLE (nN_le _) x.2)))

def αA : Fin (nP (leftWeightFirst p q r s μ)) → ℕ := fun i => ⌊leftWeightFirst p q r s μ (Fin.castLE (nP_le_nW _) i)⌋₊
def βA : Fin (nP (rightWeightFirst p q r s μ')) → ℕ := fun k => ⌊rightWeightFirst p q r s μ' (Fin.castLE (nP_le_nW _) k)⌋₊
def αB : Fin (nN (leftWeightFirst p q r s μ)) → ℕ := fun i => ⌊-leftWeightFirst p q r s μ (Fin.rev (Fin.castLE (nN_le _) i))⌋₊
def βB : Fin (nN (rightWeightSecond p q r s μ')) → ℕ := fun l => ⌊-rightWeightSecond p q r s μ' (Fin.rev (Fin.castLE (nN_le _) l))⌋₊
def αC : Fin (nP (leftWeightSecond p q r s μ)) → ℕ := fun j => ⌊leftWeightSecond p q r s μ (Fin.castLE (nP_le_nW _) j)⌋₊
def βC : Fin (nP (rightWeightSecond p q r s μ')) → ℕ := fun l => ⌊rightWeightSecond p q r s μ' (Fin.castLE (nP_le_nW _) l)⌋₊
def αD : Fin (nN (leftWeightSecond p q r s μ)) → ℕ := fun j => ⌊-leftWeightSecond p q r s μ (Fin.rev (Fin.castLE (nN_le _) j))⌋₊
def βD : Fin (nN (rightWeightFirst p q r s μ')) → ℕ := fun k => ⌊-rightWeightFirst p q r s μ' (Fin.rev (Fin.castLE (nN_le _) k))⌋₊

def vLine : Pol p q r s :=
  shapeProd (Matrix.of fun i k => (X (ιA p q r s μ μ' (i, k)) : Pol p q r s)) (List.ofFn (αA p q r s μ)) *
  shapeProd (Matrix.of fun i k => (X (ιB p q r s μ μ' (i, k)) : Pol p q r s)) (List.ofFn (αB p q r s μ)) *
  shapeProd (Matrix.of fun i k => (X (ιC p q r s μ μ' (i, k)) : Pol p q r s)) (List.ofFn (αC p q r s μ)) *
  shapeProd (Matrix.of fun i k => (X (ιD p q r s μ μ' (i, k)) : Pol p q r s)) (List.ofFn (αD p q r s μ))

end Blocks

def IsBlockHighestWeight {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ) (α : Fin m → ℕ) (β : Fin n → ℕ) (P : MvPolynomial σ ℂ) : Prop :=
  (∀ a b : Fin m, a < b → bRow ι a b P = 0) ∧ (∀ c d : Fin n, c < d → bCol ι c d P = 0) ∧
  (∀ e ∈ P.support, (∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) ∧ (∀ k, ∑ i : Fin m, e (ι (i, k)) = β k)) ∧
  (∀ i, 0 < α i) ∧ (∀ k, 0 < β k)

def HypA : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  IsBlockHighestWeight (ιA p q r s μ μ') (αA p q r s μ) (βA p q r s μ') P
def HypB : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  IsBlockHighestWeight (ιB p q r s μ μ') (αB p q r s μ) (βB p q r s μ') P
def HypC : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  IsBlockHighestWeight (ιC p q r s μ μ') (αC p q r s μ) (βC p q r s μ') P
def HypD : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  IsBlockHighestWeight (ιD p q r s μ μ') (αD p q r s μ) (βD p q r s μ') P

def CoverJ : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  ∀ e ∈ P.support, ∀ l : Ln p q r s, e l ≠ 0 →
    l ∈ Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') ∪ Set.range (ιC p q r s μ μ') ∪
      Set.range (ιD p q r s μ μ')

def SqFacts {m n : ℕ} (α : Fin m → ℕ) (β : Fin n → ℕ) : Prop :=
  m = n ∧ Antitone α ∧ ∀ (i : Fin m) (k : Fin n), (i : ℕ) = k → α i = β k

def BlockFacts (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Prop :=
  SqFacts (αA p q r s μ) (βA p q r s μ') ∧ SqFacts (αB p q r s μ) (βB p q r s μ') ∧
  SqFacts (αC p q r s μ) (βC p q r s μ') ∧ SqFacts (αD p q r s μ) (βD p q r s μ')

def SegFacts (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Prop :=
  (∀ i i' : Fin p, i < i' → 0 < nu1 p q r s μ (.inl i') → 0 < nu1 p q r s μ (.inl i)) ∧
  (∀ i i' : Fin p, i < i' → nu1 p q r s μ (.inl i) < 0 → nu1 p q r s μ (.inl i') < 0) ∧
  (∀ j j' : Fin q, j < j' → 0 < nu1 p q r s μ (.inr j') → 0 < nu1 p q r s μ (.inr j)) ∧
  (∀ j j' : Fin q, j < j' → nu1 p q r s μ (.inr j) < 0 → nu1 p q r s μ (.inr j') < 0) ∧
  (∀ k k' : Fin r, k < k' → 0 < nu2 p q r s μ' (.inl k') → 0 < nu2 p q r s μ' (.inl k)) ∧
  (∀ k k' : Fin r, k < k' → nu2 p q r s μ' (.inl k) < 0 → nu2 p q r s μ' (.inl k') < 0) ∧
  (∀ l l' : Fin s, l < l' → 0 < nu2 p q r s μ' (.inr l') → 0 < nu2 p q r s μ' (.inr l)) ∧
  (∀ l l' : Fin s, l < l' → nu2 p q r s μ' (.inr l) < 0 → nu2 p q r s μ' (.inr l') < 0)

def IntFacts (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Prop :=
  (∀ a, ((⌊nu1 p q r s μ a⌋ : ℤ) : ℚ) = nu1 p q r s μ a) ∧ (∀ c, ((⌊nu2 p q r s μ' c⌋ : ℤ) : ℚ) = nu2 p q r s μ' c)

def ShapeFromFacts : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
  BlockFacts p q r s μ μ' → SegFacts p q r s μ μ' → IntFacts p q r s μ μ' → JointShape p q r s μ μ'

end PI.FJM
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.IsDiagonalBlockIndexRightOfPositiveRoot
section
open MvPolynomial FockH1Action PI.FJM

noncomputable section

namespace PI.FJMX

variable {p q r s : ℕ}

def leftPositiveIndicator (x : Ix p q) : Ln p q r s → ℕ := fun v => if v.1 = x ∧ linePos v = true then 1 else 0

def leftNegativeIndicator (x : Ix p q) : Ln p q r s → ℕ := fun v => if v.1 = x ∧ linePos v = false then 1 else 0

def rightPositiveIndicator (y : Ix r s) : Ln p q r s → ℕ := fun v => if v.2 = y ∧ linePos v = true then 1 else 0

def rightNegativeIndicator (y : Ix r s) : Ln p q r s → ℕ := fun v => if v.2 = y ∧ linePos v = false then 1 else 0

theorem weight_fin (w : Ln p q r s → ℕ) (m : Ln p q r s →₀ ℕ) :
    Finsupp.weight w m = ∑ v, m v * w v := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [smul_eq_mul]

theorem monomialLeftWeight_eq_weight_sub (m : Ln p q r s →₀ ℕ) (x : Ix p q) :
    wt1 m x = (Finsupp.weight (leftPositiveIndicator x) m : ℤ) - (Finsupp.weight (leftNegativeIndicator x) m : ℤ) := by
  classical
  rw [weight_fin, weight_fin, wt1]
  push_cast
  rw [← Finset.sum_sub_distrib, Fintype.sum_prod_type, Finset.sum_eq_single x]
  · apply Finset.sum_congr rfl
    intro c _
    cases h : linePos (x, c) <;> simp [leftPositiveIndicator, leftNegativeIndicator, h]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    simp [leftPositiveIndicator, leftNegativeIndicator, hb]
  · simp

theorem monomialRightWeight_eq_weight_sub (m : Ln p q r s →₀ ℕ) (y : Ix r s) :
    wt2 m y = (Finsupp.weight (rightPositiveIndicator y) m : ℤ) - (Finsupp.weight (rightNegativeIndicator y) m : ℤ) := by
  classical
  rw [weight_fin, weight_fin, wt2]
  push_cast
  rw [← Finset.sum_sub_distrib, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single y]
  · cases h : linePos (a, y) <;> simp [rightPositiveIndicator, rightNegativeIndicator, h]
  · intro c _ hc
    simp [rightPositiveIndicator, rightNegativeIndicator, hc]
  · simp

theorem leftAction_diagonal_of (hW : FormWt1) (P : Pol p q r s) (x : Ix p q) (W : ℤ)
    (h : ∀ m, AddMonoidAlgebra.coeff P m ≠ 0 → wt1 m x = W) :
    fockAct1 p q r s (Eab x x) P = ((((W : ℚ) + sh1 p q r s x : ℚ)) : ℂ) • P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have e : monomial m (AddMonoidAlgebra.coeff P m) = AddMonoidAlgebra.coeff P m • monomial m (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, hW, h m (mem_support_iff.1 hm), smul_comm]

theorem rightAction_diagonal_of (hW : FormWt2) (P : Pol p q r s) (y : Ix r s) (W : ℤ)
    (h : ∀ m, AddMonoidAlgebra.coeff P m ≠ 0 → wt2 m y = W) :
    fockAct2 p q r s (Eab y y) P = ((((W : ℚ) + sh2 p q r s y : ℚ)) : ℂ) • P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have e : monomial m (AddMonoidAlgebra.coeff P m) = AddMonoidAlgebra.coeff P m • monomial m (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, hW, h m (mem_support_iff.1 hm), smul_comm]

theorem mem_wtSub1 (hW : FormWt1) (P : Pol p q r s) (μ : Ix p q → ℚ)
    (h : ∀ x, ∃ W : ℤ, (W : ℚ) + sh1 p q r s x = μ x ∧ ∀ m, AddMonoidAlgebra.coeff P m ≠ 0 → wt1 m x = W) :
    P ∈ wtSub (fockAct1 p q r s) μ := by
  simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x
  obtain ⟨W, hWx, hm⟩ := h x
  rw [LinearMap.sub_apply, leftAction_diagonal_of hW P x W hm, hWx]
  simp

theorem mem_wtSub2 (hW : FormWt2) (P : Pol p q r s) (μ : Ix r s → ℚ)
    (h : ∀ y, ∃ W : ℤ, (W : ℚ) + sh2 p q r s y = μ y ∧ ∀ m, AddMonoidAlgebra.coeff P m ≠ 0 → wt2 m y = W) :
    P ∈ wtSub (fockAct2 p q r s) μ := by
  simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y
  obtain ⟨W, hWy, hm⟩ := h y
  rw [LinearMap.sub_apply, rightAction_diagonal_of hW P y W hm, hWy]
  simp

theorem posC_ne {n m : ℕ} (x y : Ix n m) (h : posC x y) : x ≠ y := by
  cases x <;> cases y <;> simp only [posC] at h <;> first | exact h.elim | (intro e; simp at e; omega)

theorem isDiagonalBlockIndex_left_of_positiveRoot (x y : Ix p q) (h : posC x y) (c : Ix r s) : linePos (x, c) = linePos (y, c) := by
  cases x <;> cases y <;> cases c <;> simp only [posC] at h <;> first | exact h.elim | rfl

theorem isDiagonalBlockIndex_right_of_positiveRoot (x y : Ix r s) (h : posC x y) (a : Ix p q) : linePos (a, x) = linePos (a, y) := by
  cases x <;> cases y <;> cases a <;> simp only [posC] at h <;> first | exact h.elim | rfl

theorem hwVec_hom (w : Ln p q r s → ℕ) (a b c d : List ℤ) (d1 d2 d3 d4 : ℕ)
    (h1 : IsWeightedHomogeneous w (shapeProd (varMat (fun i : Fin p => (Sum.inl i : Ix p q))
      (fun k : Fin r => (Sum.inl k : Ix r s))) (posPart a)) d1)
    (h2 : IsWeightedHomogeneous w (shapeProd (varMat (fun i : Fin p => (Sum.inl (Fin.rev i) : Ix p q))
      (fun l : Fin s => (Sum.inr (Fin.rev l) : Ix r s))) (negPart b)) d2)
    (h3 : IsWeightedHomogeneous w (shapeProd (varMat (fun j : Fin q => (Sum.inr j : Ix p q))
      (fun l : Fin s => (Sum.inr l : Ix r s))) (posPart c)) d3)
    (h4 : IsWeightedHomogeneous w (shapeProd (varMat (fun j : Fin q => (Sum.inr (Fin.rev j) : Ix p q))
      (fun k : Fin r => (Sum.inl (Fin.rev k) : Ix r s))) (negPart d)) d4) :
    IsWeightedHomogeneous w (hwVec p q r s a b c d) (d1 + d2 + d3 + d4) := by
  unfold hwVec
  exact ((h1.mul h2).mul h3).mul h4

theorem wtVec1 (a b c d : List ℤ) (hd : ShapeData p q r s a b c d) (x : Ix p q) :
    ∃ W : ℤ, (W : ℚ) + sh1 p q r s x = wtOf1 p q r s a b c d x ∧
      ∀ m, AddMonoidAlgebra.coeff (hwVec p q r s a b c d) m ≠ 0 → wt1 m x = W := by
  obtain ⟨ha, hc, hb, hdd, hpa, hpb, hpc, hpd, h1, h2, h3, h4⟩ := hd
  cases x with
  | inl i₀ =>
    have hP := hwVec_hom (p := p) (q := q) (r := r) (s := s) (leftPositiveIndicator (Sum.inl i₀)) a b c d _ 0 0 0
      (shapeProd_hom_row _ _ _ i₀ (fun i k => by simp [leftPositiveIndicator, linePos]) _ (posPart_pw a hpa))
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftPositiveIndicator, linePos]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftPositiveIndicator]) _)
    have hN := hwVec_hom (p := p) (q := q) (r := r) (s := s) (leftNegativeIndicator (Sum.inl i₀)) a b c d 0 _ 0 0
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [leftNegativeIndicator, linePos]) _)
      (shapeProd_hom_row _ _ _ (Fin.rev i₀) (fun i l => by simp [leftNegativeIndicator, linePos, Fin.rev_eq_iff]) _
        (negPart_pw b hpb))
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftNegativeIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftNegativeIndicator]) _)
    refine ⟨((posPart a).getD i₀ 0 : ℤ) - ((negPart b).getD (Fin.rev i₀).val 0 : ℤ), ?_, ?_⟩
    · have hv : (Fin.rev i₀).val = p - 1 - i₀.val := by simp [Fin.val_rev]; omega
      simp only [wtOf1, ofBlocks]
      rw [pad_getD a b p h1 ha hb i₀.val i₀.isLt, hv]
      push_cast
      ring
    · intro m hm
      rw [monomialLeftWeight_eq_weight_sub, hP hm, hN hm]
      simp
  | inr j₀ =>
    have hP := hwVec_hom (p := p) (q := q) (r := r) (s := s) (leftPositiveIndicator (Sum.inr j₀)) a b c d 0 0 _ 0
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [leftPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftPositiveIndicator]) _)
      (shapeProd_hom_row _ _ _ j₀ (fun j l => by simp [leftPositiveIndicator, linePos]) _ (posPart_pw c hpc))
      (shapeProd_hom_zero _ _ _ (fun j k => by simp [leftPositiveIndicator, linePos]) _)
    have hN := hwVec_hom (p := p) (q := q) (r := r) (s := s) (leftNegativeIndicator (Sum.inr j₀)) a b c d 0 0 0 _
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [leftNegativeIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftNegativeIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun j l => by simp [leftNegativeIndicator, linePos]) _)
      (shapeProd_hom_row _ _ _ (Fin.rev j₀) (fun j k => by simp [leftNegativeIndicator, linePos, Fin.rev_eq_iff]) _
        (negPart_pw d hpd))
    refine ⟨((posPart c).getD j₀ 0 : ℤ) - ((negPart d).getD (Fin.rev j₀).val 0 : ℤ), ?_, ?_⟩
    · have hv : (Fin.rev j₀).val = q - 1 - j₀.val := by simp [Fin.val_rev]; omega
      simp only [wtOf1, ofBlocks]
      rw [pad_getD c d q h2 hc hdd j₀.val j₀.isLt, hv]
      push_cast
      ring
    · intro m hm
      rw [monomialLeftWeight_eq_weight_sub, hP hm, hN hm]
      simp

theorem wtVec2 (a b c d : List ℤ) (hd : ShapeData p q r s a b c d) (y : Ix r s) :
    ∃ W : ℤ, (W : ℚ) + sh2 p q r s y = wtOf2 p q r s a b c d y ∧
      ∀ m, AddMonoidAlgebra.coeff (hwVec p q r s a b c d) m ≠ 0 → wt2 m y = W := by
  obtain ⟨ha, hc, hb, hdd, hpa, hpb, hpc, hpd, h1, h2, h3, h4⟩ := hd
  cases y with
  | inl k₀ =>
    have hP := hwVec_hom (p := p) (q := q) (r := r) (s := s) (rightPositiveIndicator (Sum.inl k₀)) a b c d _ 0 0 0
      (shapeProd_hom_col _ _ _ k₀ (fun i k => by simp [rightPositiveIndicator, linePos]) _ (posPart_pw a hpa))
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [rightPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun j l => by simp [rightPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun j k => by simp [rightPositiveIndicator, linePos]) _)
    have hN := hwVec_hom (p := p) (q := q) (r := r) (s := s) (rightNegativeIndicator (Sum.inl k₀)) a b c d 0 0 0 _
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [rightNegativeIndicator, linePos]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [rightNegativeIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun j l => by simp [rightNegativeIndicator]) _)
      (shapeProd_hom_col _ _ _ (Fin.rev k₀) (fun j k => by simp [rightNegativeIndicator, linePos, Fin.rev_eq_iff]) _
        (negPart_pw d hpd))
    refine ⟨((posPart a).getD k₀ 0 : ℤ) - ((negPart d).getD (Fin.rev k₀).val 0 : ℤ), ?_, ?_⟩
    · have hv : (Fin.rev k₀).val = r - 1 - k₀.val := by simp [Fin.val_rev]; omega
      simp only [wtOf2, ofBlocks]
      rw [pad_getD a d r h3 ha hdd k₀.val k₀.isLt, hv]
      push_cast
      ring
    · intro m hm
      rw [monomialRightWeight_eq_weight_sub, hP hm, hN hm]
      simp
  | inr l₀ =>
    have hP := hwVec_hom (p := p) (q := q) (r := r) (s := s) (rightPositiveIndicator (Sum.inr l₀)) a b c d 0 0 _ 0
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [rightPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [rightPositiveIndicator, linePos]) _)
      (shapeProd_hom_col _ _ _ l₀ (fun j l => by simp [rightPositiveIndicator, linePos]) _ (posPart_pw c hpc))
      (shapeProd_hom_zero _ _ _ (fun j k => by simp [rightPositiveIndicator]) _)
    have hN := hwVec_hom (p := p) (q := q) (r := r) (s := s) (rightNegativeIndicator (Sum.inr l₀)) a b c d 0 _ 0 0
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [rightNegativeIndicator]) _)
      (shapeProd_hom_col _ _ _ (Fin.rev l₀) (fun i l => by simp [rightNegativeIndicator, linePos, Fin.rev_eq_iff]) _
        (negPart_pw b hpb))
      (shapeProd_hom_zero _ _ _ (fun j l => by simp [rightNegativeIndicator, linePos]) _)
      (shapeProd_hom_zero _ _ _ (fun j k => by simp [rightNegativeIndicator]) _)
    refine ⟨((posPart c).getD l₀ 0 : ℤ) - ((negPart b).getD (Fin.rev l₀).val 0 : ℤ), ?_, ?_⟩
    · have hv : (Fin.rev l₀).val = s - 1 - l₀.val := by simp [Fin.val_rev]; omega
      simp only [wtOf2, ofBlocks]
      rw [pad_getD c b s h4 hc hb l₀.val l₀.isLt, hv]
      push_cast
      ring
    · intro m hm
      rw [monomialRightWeight_eq_weight_sub, hP hm, hN hm]
      simp

theorem vecHW1_of (hW : FormWt1) (hR : FormRaise1) : VecHW1 := by
  intro p q r s a b c d hd
  refine Submodule.mem_inf.2 ⟨mem_wtSub1 hW _ _ (wtVec1 a b c d hd), ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x y hxy
  rw [hR p q r s x y (posC_ne x y hxy), leftRootOperator_eq_derivation x y (posC_ne x y hxy) (isDiagonalBlockIndex_left_of_positiveRoot x y hxy)]
  exact vecRaise1 a b c d x y hxy

theorem vecHW2_of (hW : FormWt2) (hR : FormRaise2) : VecHW2 := by
  intro p q r s a b c d hd
  refine Submodule.mem_inf.2 ⟨mem_wtSub2 hW _ _ (wtVec2 a b c d hd), ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x y hxy
  rw [hR p q r s x y (posC_ne x y hxy), rightRootOperator_eq_derivation x y (posC_ne x y hxy) (isDiagonalBlockIndex_right_of_positiveRoot x y hxy)]
  exact vecRaise2 a b c d x y hxy

end PI.FJMX
end
end

