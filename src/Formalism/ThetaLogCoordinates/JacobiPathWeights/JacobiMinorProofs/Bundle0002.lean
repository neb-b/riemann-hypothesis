module

public import Mathlib
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementP
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.Bundle0004
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.Bundle0001

@[expose] public section

-- bundled from Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.NormIndexCountBound
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace Count

theorem antitone_of_step {n : ℕ} {f : Fin n → ℤ}
    (h : ∀ m m' : Fin n, m.val + 1 = m'.val → f m' ≤ f m) : Antitone f := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ hab
  change a ≤ b at hab
  revert hb
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ k hak ih => intro hb; exact (h ⟨k, by omega⟩ ⟨k + 1, hb⟩ rfl).trans (ih (by omega))

theorem antitone_upper {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip ν μ b) : Antitone ν :=
  antitone_of_step fun m m' hm => (h.2.1 m m' hm).trans (h.1 m)

theorem antitone_lower {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip ν μ b) : Antitone μ :=
  antitone_of_step fun m m' hm => (h.1 m').trans (h.2.1 m m' hm)

def Step {n : ℕ} (v : Bool) (b : ℕ) (μ ν : Fin n → ℤ) : Prop :=
  if v then HStrip ν μ b else HStrip μ ν b

def succs {n : ℕ} (v : Bool) (b : ℕ) (μ : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  if v then stripsUp μ b else stripsDown μ b

theorem mem_succs (hS : StripsMem) {n : ℕ} (v : Bool) (b : ℕ) (μ ν : Fin n → ℤ) :
    ν ∈ succs v b μ ↔ Step v b μ ν := by
  unfold succs Step
  cases v
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact (hS n μ ν b).2
  · simp only [↓reduceIte]; exact (hS n μ ν b).1

theorem Step.antitone {n : ℕ} {v : Bool} {b : ℕ} {μ ν : Fin n → ℤ} (h : Step v b μ ν) : Antitone ν := by
  unfold Step at h
  cases v
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact antitone_lower h
  · simp only [↓reduceIte] at h; exact antitone_upper h

theorem sum_succs (hP : GTPieri) {n : ℕ} (v : Bool) (b : ℕ) (μ : Fin n → ℤ) (hμ : Antitone μ) :
    ∑ ν ∈ succs v b μ, dGT n ν = dGT n μ * (n + b - 1).choose b := by
  unfold succs
  cases v
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact (hP n μ b hμ).2
  · simp only [↓reduceIte]; exact (hP n μ b hμ).1

def baseEquiv (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ) :
    ContIdx n N N isVec B μ₀ ≃ {I : ℤ → Finset (Fin n) // IsStd μ₀ I} where
  toFun x := ⟨x.1.2, by
    have h := x.2.2.2.2
    rw [x.2.1] at h
    exact h⟩
  invFun I := ⟨(Function.update 0 N μ₀, I.1), by
    refine ⟨by simp, ?_, ?_, by simpa using I.2⟩
    · intro j hj
      have : j ≠ N := by omega
      simp [Function.update_of_ne this]
    · intro j h1 h2
      omega⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext j
      by_cases hj : j = N
      · subst hj
        simpa using x.2.1.symm
      · have : j < N ∨ N < j := by omega
        simp [Function.update_of_ne hj, x.2.2.1 j this]
    · rfl
  right_inv I := rfl

def nextW (hS : StripsMem) {n i N : ℕ} (hi : i < N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ)
    (x : ContIdx n i N isVec B μ₀) : {ν // ν ∈ succs (isVec i) (B i) μ₀} :=
  ⟨x.1.1 (i + 1), by
    rw [mem_succs hS]
    have h := x.2.2.2.1 i le_rfl hi
    rw [x.2.1] at h
    exact h⟩

def fibreEquiv (hS : StripsMem) {n i N : ℕ} (hi : i < N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ)
    (ν : {ν // ν ∈ succs (isVec i) (B i) μ₀}) :
    {x : ContIdx n i N isVec B μ₀ // nextW hS hi isVec B μ₀ x = ν} ≃ ContIdx n (i + 1) N isVec B ν.1 where
  toFun x := ⟨(Function.update x.1.1.1 i 0, x.1.1.2), by
    have hν : x.1.1.1 (i + 1) = ν.1 := congrArg Subtype.val x.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Function.update_of_ne (show i + 1 ≠ i by omega)] using hν
    · intro j hj
      by_cases hji : j = i
      · subst hji; simp
      · simpa [Function.update_of_ne hji] using x.1.2.2.1 j (by omega)
    · intro j h1 h2
      have e1 : j ≠ i := by omega
      have e2 : j + 1 ≠ i := by omega
      simpa [Function.update_of_ne e1, Function.update_of_ne e2] using x.1.2.2.2.1 j (by omega) h2
    · have e1 : N ≠ i := by omega
      simpa [Function.update_of_ne e1] using x.1.2.2.2.2⟩
  invFun y := ⟨⟨(Function.update y.1.1 i μ₀, y.1.2), by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro j hj
      have e1 : j ≠ i := by omega
      simpa [Function.update_of_ne e1] using y.2.2.1 j (by omega)
    · intro j h1 h2
      by_cases hji : j = i
      · subst hji
        have e2 : j + 1 ≠ j := by omega
        have h := (mem_succs hS _ _ _ _).1 ν.2
        simpa [Function.update_of_ne e2, y.2.1, Step] using h
      · have e2 : j + 1 ≠ i := by omega
        simpa [Function.update_of_ne hji, Function.update_of_ne e2] using y.2.2.2.1 j (by omega) h2
    · have e1 : N ≠ i := by omega
      simpa [Function.update_of_ne e1] using y.2.2.2.2⟩, by
    apply Subtype.ext
    have e2 : i + 1 ≠ i := by omega
    simpa [nextW, Function.update_of_ne e2] using y.2.1⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · funext j
      by_cases hji : j = i
      · subst hji
        simpa using x.1.2.1.symm
      · simp [Function.update_of_ne hji]
    · rfl
  right_inv y := by
    apply Subtype.ext
    apply Prod.ext
    · funext j
      by_cases hji : j = i
      · subst hji
        simpa using (y.2.2.1 j (by omega)).symm
      · simp [Function.update_of_ne hji]
    · rfl

theorem norm_index_count_bound (hS : StripsMem) (hP : GTPieri) (hC : StdCountGT) (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) :
    ∀ (k i : ℕ), i + k = N → ∀ μ₀ : Fin n → ℤ, Antitone μ₀ →
      Finite (ContIdx n i N isVec B μ₀) ∧
      Nat.card (ContIdx n i N isVec B μ₀) = dGT n μ₀ * ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by
  intro k
  induction k with
  | zero =>
    intro i hi μ₀ hμ
    simp only [add_zero] at hi
    subst hi
    obtain ⟨hfin, hcard⟩ := hC n μ₀ hμ
    have e := baseEquiv n i isVec B μ₀
    refine ⟨Finite.of_equiv _ e.symm, ?_⟩
    rw [Nat.card_congr e, hcard, Finset.Ico_self, Finset.prod_empty, mul_one]
  | succ k ih =>
    intro i hi μ₀ hμ
    have hiN : i < N := by omega
    have e : ContIdx n i N isVec B μ₀ ≃
        Σ ν : {ν // ν ∈ succs (isVec i) (B i) μ₀}, ContIdx n (i + 1) N isVec B ν.1 :=
      (Equiv.sigmaFiberEquiv (nextW hS hiN isVec B μ₀)).symm.trans
        (Equiv.sigmaCongrRight fun ν => fibreEquiv hS hiN isVec B μ₀ ν)
    have hν : ∀ ν : {ν // ν ∈ succs (isVec i) (B i) μ₀}, Antitone ν.1 :=
      fun ν => Step.antitone ((mem_succs hS _ _ _ _).1 ν.2)
    have ihν := fun ν : {ν // ν ∈ succs (isVec i) (B i) μ₀} => ih (i + 1) (by omega) ν.1 (hν ν)
    haveI : ∀ ν : {ν // ν ∈ succs (isVec i) (B i) μ₀}, Finite (ContIdx n (i + 1) N isVec B ν.1) :=
      fun ν => (ihν ν).1
    refine ⟨Finite.of_equiv _ e.symm, ?_⟩
    have hsum : ∑ ν : {ν // ν ∈ succs (isVec i) (B i) μ₀}, Nat.card (ContIdx n (i + 1) N isVec B ν.1) =
        (∑ ν ∈ succs (isVec i) (B i) μ₀, dGT n ν) *
          ∏ l ∈ Finset.Ico (i + 1) N, (n + B l - 1).choose (B l) := by
      rw [Finset.sum_mul, ← Finset.sum_coe_sort (succs (isVec i) (B i) μ₀)]
      exact Finset.sum_congr rfl fun ν _ => (ihν ν).2
    rw [Nat.card_congr e, Nat.card_sigma, hsum, sum_succs hP _ _ _ hμ,
      Finset.prod_eq_prod_Ico_succ_bot hiN]
    ring

theorem dGT_zero (n : ℕ) : dGT n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : gtBox (0 : Fin (n + 1) → ℤ) = {0} := by
      ext κ
      simp [gtBox, Fintype.mem_piFinset, funext_iff]
    show ∑ κ ∈ gtBox (0 : Fin (n + 1) → ℤ), dGT n κ = 1
    rw [h, Finset.sum_singleton, ih]

theorem antitone_of_rules {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ} (h0 : Antitone (μ 0))
    (h : ∀ j < N, if isVec j then HStrip (μ (j + 1)) (μ j) (B j) else HStrip (μ j) (μ (j + 1)) (B j)) :
    ∀ i ≤ N, Antitone (μ i) := by
  intro i hi
  cases i with
  | zero => exact h0
  | succ j =>
    have hj := h j (by omega)
    split_ifs at hj
    · exact antitone_upper hj
    · exact antitone_lower hj

def pathEquiv (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) : PathIdx n N isVec B ≃ ContIdx n 0 N isVec B 0 :=
  Equiv.subtypeEquivRight fun x => by
    constructor
    · rintro ⟨⟨h0, _, h2⟩, h3, h4⟩
      exact ⟨h0, fun j hj => h3 j (by omega), fun j _ hj => h2 j hj, h4⟩
    · rintro ⟨h0, h1, h2, h3⟩
      have h2' : ∀ j < N, if isVec j then HStrip (x.1 (j + 1)) (x.1 j) (B j)
          else HStrip (x.1 j) (x.1 (j + 1)) (B j) := fun j hj => h2 j (Nat.zero_le _) hj
      refine ⟨⟨h0, antitone_of_rules (by rw [h0]; exact fun _ _ _ => le_rfl) h2', h2'⟩,
        fun j hj => h1 j (Or.inr hj), h3⟩

end Count

theorem countCont_of : StripsMem → GTPieri → StdCountGT → CountCont := by
  intro hS hP hC n i N isVec B μ₀ hiN hμ
  exact Count.norm_index_count_bound hS hP hC n N isVec B (N - i) i (by omega) μ₀ hμ

theorem countPAll_of : CountCont → CountPAll := by
  intro hCC n N isVec B
  unfold CountP
  obtain ⟨-, hcard⟩ := hCC n 0 N isVec B 0 (Nat.zero_le N) (fun _ _ _ => le_rfl)
  rw [Nat.card_congr (Count.pathEquiv n N isVec B), hcard, Count.dGT_zero, one_mul, Finset.range_eq_Ico]

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

-- bundled from Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.PathBasisOfCount
section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace MinorDeterminantBasis

section Abstract

variable {σ X : Type} [Fintype X] [DecidableEq X]

def cmat (m : X → σ →₀ ℕ) (F : X → MvPolynomial σ ℤ) : Matrix X X ℤ :=
  Matrix.of fun x y => AddMonoidAlgebra.coeff (F x) (m y)

theorem expand (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m) (S : Type) [CommRing S] (x : X) :
    MvPolynomial.map (Int.castRingHom S) (F x) =
      ∑ y, ((cmat m F).map (Int.castRingHom S)) x y • monomial (m y) (1 : S) := by
  classical
  ext d
  rw [coeff_map, MvPolynomial.coeff_sum]
  simp only [coeff_smul, coeff_monomial, Matrix.map_apply, cmat, Matrix.of_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  by_cases hd : d ∈ Set.range m
  · obtain ⟨y₀, rfl⟩ := hd
    rw [Finset.sum_eq_single y₀]
    · simp
    · intro y _ hy
      rw [if_neg (hm.ne hy)]
    · simp
  · have h0 : AddMonoidAlgebra.coeff (F x) d = 0 := by
      by_contra h
      exact hd (hF x d (mem_support_iff.mpr h))
    rw [h0, map_zero, Finset.sum_eq_zero]
    intro y _
    rw [if_neg]
    rintro rfl
    exact hd ⟨y, rfl⟩

private theorem sum_smul_sum_smul_eq_sum_mul_smul {S : Type} [CommRing S] (M : Matrix X X S) (e : X → MvPolynomial σ S)
    (g : X → S) : ∑ x, g x • ∑ y, M x y • e y = ∑ y, (∑ x, g x * M x y) • e y := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem rows_indep (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m) (S : Type) [CommRing S]
    (h : LinearIndependent S fun x => MvPolynomial.map (Int.castRingHom S) (F x)) :
    LinearIndependent S ((cmat m F).map (Int.castRingHom S)).row := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  apply h g
  simp only [expand m hm F hF S, sum_smul_sum_smul_eq_sum_mul_smul]
  have hy : ∀ y, ∑ x, g x * ((cmat m F).map (Int.castRingHom S)) x y = 0 := by
    intro y
    have := congrFun hg y
    simpa [Finset.sum_apply, Matrix.row] using this
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [hy y, zero_smul]

theorem det_unit (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m)
    (hp : ∀ p : ℕ, ∀ _ : Fact p.Prime,
      LinearIndependent (ZMod p) fun x => MvPolynomial.map (Int.castRingHom (ZMod p)) (F x)) :
    IsUnit (cmat m F).det := by
  rw [Int.isUnit_iff_natAbs_eq]
  by_contra hne
  obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd hne
  haveI : Fact p.Prime := ⟨hpp⟩
  have hrows := rows_indep m hm F hF (ZMod p) (hp p ⟨hpp⟩)
  have hu : IsUnit ((cmat m F).map (Int.castRingHom (ZMod p))) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp (by simpa [Matrix.row] using hrows)
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
  apply hu
  have hdet : ((cmat m F).map (Int.castRingHom (ZMod p))).det = Int.castRingHom (ZMod p) (cmat m F).det :=
    (RingHom.map_det _ _).symm
  rw [hdet, eq_intCast]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (Int.ofNat_dvd_left.mpr hpd)

theorem basis_of (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m)
    (hp : ∀ p : ℕ, ∀ _ : Fact p.Prime,
      LinearIndependent (ZMod p) fun x => MvPolynomial.map (Int.castRingHom (ZMod p)) (F x))
    (R : Type) [CommRing R] :
    LinearIndependent R (fun x => MvPolynomial.map (Int.castRingHom R) (F x)) ∧
    Submodule.span R (Set.range fun x => MvPolynomial.map (Int.castRingHom R) (F x)) =
      Submodule.span R (Set.range fun y => monomial (m y) (1 : R)) := by
  classical
  set M := (cmat m F).map (Int.castRingHom R) with hM
  have hdet : IsUnit M.det := by
    have h1 := (det_unit m hm F hF hp).map (Int.castRingHom R)
    rw [RingHom.map_det] at h1
    exact h1
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  have hMN : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  have he : LinearIndependent R fun y => (monomial (m y) (1 : R) : MvPolynomial σ R) := by
    have h1 := (MvPolynomial.basisMonomials σ R).linearIndependent.comp m hm
    simpa [Function.comp_def, MvPolynomial.coe_basisMonomials] using h1
  have hexp : ∀ x, MvPolynomial.map (Int.castRingHom R) (F x) =
      ∑ y, M x y • (monomial (m y) (1 : R) : MvPolynomial σ R) := expand m hm F hF R
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [hexp, sum_smul_sum_smul_eq_sum_mul_smul] at hg
    have h0 := Fintype.linearIndependent_iff.mp he _ hg
    have hv : Matrix.vecMul g M = 0 := funext fun y => by
      simpa [Matrix.vecMul, dotProduct] using h0 y
    have h2 := congrArg (fun v => Matrix.vecMul v M⁻¹) hv
    simp only [Matrix.vecMul_vecMul, hMN, Matrix.vecMul_one, Matrix.zero_vecMul] at h2
    exact congrFun h2
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      dsimp only
      rw [hexp]
      exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      have key : ∑ x, M⁻¹ y x • MvPolynomial.map (Int.castRingHom R) (F x) =
          (monomial (m y) (1 : R) : MvPolynomial σ R) := by
        simp only [hexp, sum_smul_sum_smul_eq_sum_mul_smul]
        have h1 : ∀ z, ∑ x, M⁻¹ y x * M x z = (1 : Matrix X X R) y z := fun z => by
          rw [← hNM, Matrix.mul_apply]
        simp only [h1, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
      dsimp only
      rw [← key]
      exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)

end Abstract

def expSet (n N : ℕ) (B : ℕ → ℕ) : Set (ℕ × Fin n →₀ ℕ) :=
  {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then B i else 0}

theorem psi_map (R : Type) [CommRing R] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    {I : ℤ → Finset (Fin n)} (hμ : IsPath n isVec B μ N) (hI : IsIndex (μ N) I) :
    psiPath R isVec μ N I = MvPolynomial.map (Int.castRingHom R) (psiPath ℤ isVec μ N I) := by
  have hfin := (pathProductDegrees ℤ n N isVec B μ I hμ hI).1
  have h := (MvPolynomial.map (Int.castRingHom R) :
    MvPolynomial (ℕ × Fin n) ℤ →+* MvPolynomial (ℕ × Fin n) R).toMonoidHom.map_finprod hfin
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h
  unfold psiPath
  rw [h]
  congr 1
  funext c
  rw [A1hw.map_pathWord]
  simp [map_X]

private theorem weight_indicator_fst_eq_sum {n : ℕ} (i : ℕ) (d : ℕ × Fin n →₀ ℕ) :
    Finsupp.weight (fun x : ℕ × Fin n => if x.1 = i then 1 else 0) d = ∑ a, d (i, a) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d₁ d₂ h₁ h₂ =>
    rw [map_add (f := _), h₁, h₂]
    simp [Finset.sum_add_distrib]
  | single x k =>
    obtain ⟨j, b⟩ := x
    rw [Finsupp.weight_single]
    by_cases hj : j = i
    · subst hj
      simp [Finsupp.single_apply, Prod.ext_iff]
    · simp [Finsupp.single_apply, Prod.ext_iff, hj]

theorem psi_support (hr : PolBRank) {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    {I : ℤ → Finset (Fin n)} (hμ : IsPath n isVec B μ N) (hI : IsIndex (μ N) I) :
    ∀ d ∈ (psiPath ℤ isVec μ N I).support, d ∈ expSet n N B := by
  intro d hd i
  rw [← weight_indicator_fst_eq_sum]
  exact (pathProductDegrees ℤ n N isVec B μ I hμ hI).2 i (mem_support_iff.mp hd)

end MinorDeterminantBasis

open MinorDeterminantBasis

theorem path_basis_of_count : LemmaA2indep → PathIdxFinite → PolBRank → PathBasisOfCount := by
  classical
  intro hA hF hR n N isVec B hC R _
  haveI := hF n N isVec B
  letI := Fintype.ofFinite (PathIdx n N isVec B)
  obtain ⟨hcard, hfin, hspan⟩ := hR n N B
  haveI : Finite (expSet n N B) := hfin.to_subtype
  have hce : Nat.card (PathIdx n N isVec B) = Nat.card (expSet n N B) := by
    rw [hC, Nat.card_coe_set_eq, ← hcard]
    rfl
  obtain ⟨e⟩ := Finite.card_eq.mp hce
  let m : PathIdx n N isVec B → ℕ × Fin n →₀ ℕ := fun x => (e x : ℕ × Fin n →₀ ℕ)
  have hm : Function.Injective m := Subtype.val_injective.comp e.injective
  have hFs : ∀ x : PathIdx n N isVec B, ∀ d ∈ (psiPath ℤ isVec x.1.1 N x.1.2).support,
      d ∈ Set.range m := by
    intro x d hd
    have h1 := psi_support hR x.2.1 x.2.2.2.1 d hd
    exact ⟨e.symm ⟨d, h1⟩, by simp [m]⟩
  have hfun : ∀ (S : Type) [CommRing S], (fun x : PathIdx n N isVec B =>
      MvPolynomial.map (Int.castRingHom S) (psiPath ℤ isVec x.1.1 N x.1.2)) =
      fun x => psiPath S isVec x.1.1 N x.1.2 := fun S _ =>
    funext fun x => (psi_map S x.2.1 x.2.2.2.1).symm
  have hp : ∀ p : ℕ, ∀ _ : Fact p.Prime, LinearIndependent (ZMod p) fun x : PathIdx n N isVec B =>
      MvPolynomial.map (Int.castRingHom (ZMod p)) (psiPath ℤ isVec x.1.1 N x.1.2) := by
    intro p hpp
    rw [hfun]
    exact hA (ZMod p) n N isVec B
  obtain ⟨h1, h2⟩ := basis_of m hm (fun x => psiPath ℤ isVec x.1.1 N x.1.2) hFs hp R
  rw [hfun] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  rw [hspan R]
  congr 1
  ext f
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨m y, (e y).2, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨e.symm ⟨d, hd⟩, by simp [m]⟩

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

