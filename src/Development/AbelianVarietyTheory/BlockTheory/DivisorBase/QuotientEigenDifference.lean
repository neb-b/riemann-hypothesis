module

public import Mathlib

@[expose] public section

open scoped NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

noncomputable section Defs

variable {C : Type} [Field C] (w : Valuation C ℝ≥0)

noncomputable def addVal (ℓ c : C) : ℝ := Real.log (w c : ℝ) / Real.log (w ℓ : ℝ)

def HasVal (ℓ c : C) (y : ℝ) : Prop := c ≠ 0 ∧ addVal w ℓ c = y

def IsLatticeBasis {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n : ℕ} (x : Fin n → W)
    (X : Submodule w.valuationSubring W) : Prop :=
  LinearIndependent C x ∧ Submodule.span w.valuationSubring (Set.range x) = X

def HasLength (ℓ : C) {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] (X X' : Submodule w.valuationSubring W) (t : ℝ) :
    Prop :=
  X' ≤ X ∧ ∃ (n : ℕ) (x x' : Fin n → W) (M : Matrix (Fin n) (Fin n) C),
    IsLatticeBasis w x X ∧ IsLatticeBasis w x' X' ∧ (∀ i, x' i = ∑ j, M i j • x j) ∧
      HasVal w ℓ M.det t

def DetRel (ℓ : C) {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (X : Submodule w.valuationSubring (Fin (p + q) → C))
    (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F))
    (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) : Prop :=
  ∃ (x : Fin (p + q) → Fin (p + q) → C) (u : Fin p → Fin (p + q) → C)
    (m : Fin q → Fin (p + q) → C) (c : C),
    IsLatticeBasis w x X ∧ IsLatticeBasis w (fun i => F.mkQ (u i)) L ∧ IsLatticeBasis w m M ∧
      (∀ i, m i ∈ F) ∧ HasVal w ℓ c y ∧
      (Matrix.of x).det = c * (Matrix.of (Fin.append u m)).det

variable {w}

def eigenSub {S : Type} [DecidableEq S] {W : S → Type} [∀ s, AddCommGroup (W s)]
    [∀ s, Module w.valuationSubring (W s)] (X : Submodule w.valuationSubring (∀ s, W s))
    (τ : S) : Submodule w.valuationSubring (W τ) :=
  X.comap (LinearMap.single w.valuationSubring W τ)

def eigenQuot {S : Type} {W : S → Type} [∀ s, AddCommGroup (W s)]
    [∀ s, Module w.valuationSubring (W s)] (X : Submodule w.valuationSubring (∀ s, W s))
    (τ : S) : Submodule w.valuationSubring (W τ) :=
  X.map (LinearMap.proj τ)

def freeLattice {S : Type} (a : S → w.valuationSubring) (r : ℕ) :
    Submodule w.valuationSubring (S → Fin r → C) where
  carrier := {x | ∀ i, ∃ f : Polynomial w.valuationSubring, ∀ s,
    x s i = ((f.eval (a s) : w.valuationSubring) : C)}
  zero_mem' := fun _ => ⟨0, fun _ => by simp⟩
  add_mem' := by
    intro x y hx hy i
    obtain ⟨f, hf⟩ := hx i
    obtain ⟨g, hg⟩ := hy i
    exact ⟨f + g, fun s => by simp [hf s, hg s]⟩
  smul_mem' := by
    intro c x hx i
    obtain ⟨f, hf⟩ := hx i
    exact ⟨Polynomial.C c * f, fun s => by simp [hf s, Algebra.smul_def]⟩

def unif {S : Type} {r : ℕ} (a : S → w.valuationSubring) (x : S → Fin r → C) :
    S → Fin r → C := fun s => (a s : C) • x s

def filSpace {S : Type} {r : ℕ} (Fil : Submodule w.valuationSubring (S → Fin r → C)) (s : S) :
    Submodule C (Fin r → C) :=
  Submodule.span C (eigenQuot (W := fun _ => Fin r → C) Fil s : Set (Fin r → C))

def quotMap {r : ℕ} (F : Submodule C (Fin r → C)) :
    (Fin r → C) →ₗ[w.valuationSubring] ((Fin r → C) ⧸ F) :=
  F.mkQ.restrictScalars w.valuationSubring

def lie {S : Type} {r : ℕ} (H Fil : Submodule w.valuationSubring (S → Fin r → C)) :
    Submodule w.valuationSubring (∀ s, (Fin r → C) ⧸ filSpace Fil s) :=
  H.map (LinearMap.pi fun s => quotMap (filSpace Fil s) ∘ₗ LinearMap.proj s)

def dualLie {S : Type} [DecidableEq S] {r : ℕ}
    (β : (S → Fin r → C) →ₗ[C] (S → Fin r → C) →ₗ[C] C)
    (Fil H' Fil' : Submodule w.valuationSubring (S → Fin r → C)) (τ : S) :
    Submodule w.valuationSubring (Fin r → C) where
  carrier := {x | x ∈ filSpace Fil τ ∧ ∀ y : Fin r → C,
    (filSpace Fil' τ).mkQ y ∈ eigenSub (lie H' Fil') τ →
      β (Pi.single τ x) (Pi.single τ y) ∈ w.valuationSubring}
  zero_mem' := ⟨zero_mem _, fun y _ => by simp⟩
  add_mem' := by
    rintro x x' ⟨hx, h⟩ ⟨hx', h'⟩
    refine ⟨add_mem hx hx', fun y hy => ?_⟩
    rw [Pi.single_add, map_add (f := _), LinearMap.add_apply]
    exact add_mem (h y hy) (h' y hy)
  smul_mem' := by
    rintro c x ⟨hx, h⟩
    refine ⟨Submodule.smul_mem _ (c : C) hx, fun y hy => ?_⟩
    have : (Pi.single τ (c • x) : S → Fin r → C) = (c : C) • (Pi.single τ x : S → Fin r → C) :=
      Pi.single_smul' τ (c : C) x
    rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_mem c.2 (h y hy)

structure IsFiltration {S : Type} {r : ℕ} (a : S → w.valuationSubring)
    (Fil : Submodule w.valuationSubring (S → Fin r → C)) : Prop where
  le : Fil ≤ freeLattice a r
  stable : ∀ x ∈ Fil, unif a x ∈ Fil
  saturated : ∀ x ∈ freeLattice a r, ∀ c : w.valuationSubring, c ≠ 0 → c • x ∈ Fil → x ∈ Fil

structure IsDualDatum {S : Type} {r : ℕ} (a : S → w.valuationSubring)
    (β : (S → Fin r → C) →ₗ[C] (S → Fin r → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin r → C)) : Prop where
  fil : IsFiltration a Fil
  fil' : IsFiltration a Fil'
  adjoint : ∀ x y, β (unif a x) y = β x (unif a y)
  perfect_left : ∀ x, x ∈ freeLattice a r ↔
    ∀ y ∈ freeLattice a r, β x y ∈ w.valuationSubring
  perfect_right : ∀ y, y ∈ freeLattice a r ↔
    ∀ x ∈ freeLattice a r, β x y ∈ w.valuationSubring
  ann_left : ∀ x ∈ freeLattice a r, (x ∈ Fil ↔ ∀ y ∈ Fil', β x y = 0)
  ann_right : ∀ y ∈ freeLattice a r, (y ∈ Fil' ↔ ∀ x ∈ Fil, β x y = 0)

def diffGen {S : Type} [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (τ : S) :
    w.valuationSubring := ∏ s ∈ Finset.univ.erase τ, (a τ - a s)

def flatLattice {S : Type} {r : ℕ} (a : S → w.valuationSubring) (τ : S)
    (d : w.valuationSubring) : Submodule w.valuationSubring (Fin r → C) :=
  (eigenQuot (W := fun _ => Fin r → C) (freeLattice a r) τ).map
    (LinearMap.lsmul w.valuationSubring (Fin r → C) d)

end Defs

section Stmt

variable {C : Type} [Field C] (w : Valuation C ℝ≥0) (ℓ : C)

def TypeOne : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (β : (S → Fin (p + q) → C) →ₗ[C] (S → Fin (p + q) → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S),
    Function.Injective a → IsDualDatum a β Fil Fil' →
    (∀ s, Module.finrank C (filSpace Fil s) = q) →
    let H := freeLattice a (p + q)
    let vd := addVal w ℓ (diffGen a τ : C)
    let HH := flatLattice (r := p + q) a τ (diffGen a τ)
    let FilSub := eigenSub (W := fun _ => Fin (p + q) → C) Fil τ
    let FilQuot := eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ
    HH = eigenSub (W := fun _ => Fin (p + q) → C) H τ ∧
    DetRel w ℓ (filSpace Fil τ) HH (eigenSub (lie H Fil) τ) (dualLie β Fil H Fil' τ)
      ((q : ℝ) * vd) ∧
    HH ⊓ LinearMap.ker (quotMap (filSpace Fil τ)) = FilSub ∧
    ∃ t : ℝ, HasLength w ℓ FilQuot FilSub t ∧
      HasLength w ℓ (eigenSub (lie H Fil) τ) (HH.map (quotMap (filSpace Fil τ)))
        ((q : ℝ) * vd - t) ∧
      0 ≤ (q : ℝ) * vd - t ∧ (q : ℝ) * vd - t ≤ (q : ℝ) * vd

def TypeTwo : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (β : (S → Fin (p + q) → C) →ₗ[C] (S → Fin (p + q) → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ τ' : S),
    τ ≠ τ' → (∀ s, s = τ ∨ s = τ') →
    HasVal w ℓ ((a τ : C) - (a τ' : C)) (1 / 2) → IsDualDatum a β Fil Fil' →
    Module.finrank C (filSpace Fil τ) = q → Module.finrank C (filSpace Fil τ') = p →
    let H := freeLattice a (p + q)
    let HH := flatLattice (r := p + q) a τ 1
    let FilSub := eigenSub (W := fun _ => Fin (p + q) → C) Fil τ
    let FilQuot := eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ
    HH = eigenQuot (W := fun _ => Fin (p + q) → C) H τ ∧
    DetRel w ℓ (filSpace Fil τ) HH (eigenSub (lie H Fil) τ) (dualLie β Fil H Fil' τ)
      (-((q : ℝ) / 2)) ∧
    HH.map (quotMap (filSpace Fil τ)) = eigenQuot (lie H Fil) τ ∧
    (∃ la : ℝ, HasLength w ℓ (eigenQuot (lie H Fil) τ) (eigenSub (lie H Fil) τ) la ∧
      0 ≤ la ∧ la ≤ (q : ℝ) / 2 ∧
      HasLength w ℓ (HH ⊓ LinearMap.ker (quotMap (filSpace Fil τ))) FilQuot
        ((q : ℝ) / 2 - la)) ∧
    ∃ t : ℝ, HasLength w ℓ FilQuot FilSub t ∧ t ≤ (q : ℝ) / 2

def Unramified : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (β : (S → Fin (p + q) → C) →ₗ[C] (S → Fin (p + q) → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S),
    (∀ s, s = τ) → IsDualDatum a β Fil Fil' →
    Module.finrank C (filSpace Fil τ) = q →
    let H := freeLattice a (p + q)
    DetRel w ℓ (filSpace Fil τ) (flatLattice (r := p + q) a τ 1) (eigenSub (lie H Fil) τ)
      (dualLie β Fil H Fil' τ) 0

def ValuedFieldThreeCases : Prop := TypeOne w ℓ ∧ TypeTwo w ℓ ∧ Unramified w ℓ

end Stmt

def Stmt : Prop :=
  ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ValuedFieldThreeCases w ℓ

noncomputable section Example

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

end Example

end GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference
