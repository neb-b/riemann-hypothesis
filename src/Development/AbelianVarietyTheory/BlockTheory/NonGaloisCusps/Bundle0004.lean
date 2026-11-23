module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleSignatures
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures

open GlobalTheory.BK PowerSeries

structure Admissible (l e N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ) : Prop where
  frob_mem : ∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig
  zero_mem_Sig : (0 : ZMod e) ∈ Sig
  card_Sig : Sig.card ≤ N
  two_le : 2 ≤ N
  range_U : ∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ (H : ℤ)
  zero_mem_U : (0 : ℤ) ∈ U
  card_U : U.card ≤ N + 1
  one_le : 1 ≤ η
  lt : η < H
  large : 40 * (H * N ^ 2 + N ^ 3) < l

def cOne (l : ℕ) {e : ℕ} (η : ℕ) (Sig : Finset (ZMod e)) : ℕ := η * (maxPeriod l Sig + 1)

def ZetaBound : Prop :=
  ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
    (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), Admissible l e N η H Sig U →
    ∀ D : BKDat O K l e a ι η H, D.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) →
    ∀ y' ∈ D.Y', ∀ m ∈ D.Minv, D.Mon (y' + D.phi m) = 0 →
      (l : K) ^ cOne l η Sig • D.zeta (y' + D.phi m) ∈ D.MM

section Basic₂

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}
  {D : BKDat O K l e a ι η H}

omit [NeZero e]

theorem add_phi_mem_Y {y' m : Vec K a ι} (hy : y' ∈ D.Y') (hm : m ∈ D.Minv) :
    y' + D.phi m ∈ D.Y :=
  add_mem (D.desc.Y'_le_Y η hy)
    ⟨D.upper _ (D.phi_mem_L hm.1), fun g => by rw [D.desc.act_phi, hm.2 g]⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents

open PowerSeries GlobalTheory.BK

def eW (N r : ℕ) : ℕ := 2 * (N - 1) * r

def eL (N η : ℕ) : ℕ := (N + 1) * η

def c₁ (η r : ℕ) : ℕ := η * (r + 1)

def c₂ (N η r : ℕ) : ℕ := c₁ η r + eW N r

def kExp (N η r : ℕ) : ℕ := c₂ N η r + η + eL N η + eW N r

structure Numerics (l e N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ) : Prop where
  frob_mem : ∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig
  zero_mem_Sig : (0 : ZMod e) ∈ Sig
  card_Sig : Sig.card ≤ N
  two_le : 2 ≤ N
  range_U : ∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ H
  zero_mem_U : (0 : ℤ) ∈ U
  card_U : U.card ≤ N + 1
  one_le : 1 ≤ η
  lt : η < H
  large : 40 * (H * N ^ 2 + N ^ 3) < l

section

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {ι₀ ι₁ ι₂ : Type} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁]
  [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] {η H : ℕ}
  {D₀ : BKDat O K l e a ι₀ η H} {D₁ : BKDat O K l e a ι₁ η H} {D₂ : BKDat O K l e a ι₂ η H}

def Hyp (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (N : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ) : Prop :=
  IsExactTriple F.toHom G.toHom ∧ Numerics l e N η H Sig U ∧
    D₁.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) ∧ ∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))

def Lifts (G : BKHom D₁ D₂) (k : ℕ) (y₂' m₂ : Vec K a ι₂) : Prop :=
  ∃ y' ∈ D₁.Y', ∃ m ∈ D₁.Minv, D₁.Mon (y' + D₁.phi m) = 0 ∧
    G.app (y' + D₁.phi m) = (l : K) ^ k • (y₂' + D₂.phi m₂)

end

def Lifting : Prop :=
  ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] [CompleteSpace K] (ι₀ ι₁ ι₂ : Type) [Fintype ι₀] [DecidableEq ι₀]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] (η H : ℕ)
    (D₀ : BKDat O K l e a ι₀ η H) (D₁ : BKDat O K l e a ι₁ η H) (D₂ : BKDat O K l e a ι₂ η H)
    (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (N : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ),
    Hyp F G N Sig U → ∀ y₂' ∈ D₂.Y', ∀ m₂ ∈ D₂.Minv, D₂.Mon (y₂' + D₂.phi m₂) = 0 →
      Lifts G (kExp N η (maxPeriod l Sig)) y₂' m₂

end GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction

open PowerSeries GlobalTheory.BK

def shifts (U : Finset ℤ) (η : ℕ) : Finset ℤ := Finset.image₂ (· + ·) U (Finset.Icc 1 (η : ℤ))

def polyR (l e : ℕ) (U : Finset ℤ) (η : ℕ) : Polynomial ℤ :=
  ∏ n ∈ (shifts U η).erase 0, (Polynomial.X - Polynomial.C (n * e * l))

def polyR₁ (l e : ℕ) (U : Finset ℤ) (η : ℕ) : Polynomial ℤ := (polyR l e U η).divX

theorem X_mul_polyR₁ (l e : ℕ) (U : Finset ℤ) (η : ℕ) :
    Polynomial.X * polyR₁ l e U η = polyR l e U η - Polynomial.C ((polyR l e U η).eval 0) := by
  rw [polyR₁, mul_comm, ← Polynomial.coeff_zero_eq_eval_zero]
  exact eq_sub_of_add_eq (Polynomial.divX_mul_X_add _)

theorem mem_shifts {U : Finset ℤ} {η : ℕ} {n : ℤ} :
    n ∈ shifts U η ↔ ∃ i ∈ U, ∃ k : ℤ, (1 ≤ k ∧ k ≤ η) ∧ i + k = n := by
  rw [shifts, Finset.mem_image₂]
  simp only [Finset.mem_Icc]

section Clauses

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ} (D : BKDat O K l e a ι η H)

def FiniteFree : Prop := Module.Free O D.Z ∧ Module.Finite O D.Z

def Localisation : Prop :=
  Function.Injective (Descent.quotToPol D.toPhiMod η) ∧
  (∀ w : D.Pol, w ∈ D.PolEta η ↔
    ∃ n : ℕ, (l : K) ^ n • w ∈ LinearMap.range (Descent.quotToPol D.toPhiMod η)) ∧
  (D.desc.actQuot η).invariants.map (Descent.quotToPol D.toPhiMod η) = D.Z ∧
  ∀ w : D.Pol, w ∈ D.Zl ↔ ∃ n : ℕ, (l : K) ^ n • w ∈ D.Z

def Integral : Prop := ∀ w ∈ D.Z, D.Lc w ∈ D.Z

def Semisimple (U : Finset ℤ) : Prop :=
  D.LcZ.IsSemisimple ∧
  (∀ μ : K, D.LcZ.HasEigenvalue μ → ∃ n ∈ shifts U η, μ = ((n * e * l : ℤ) : K)) ∧
  ⨆ n ∈ shifts U η, D.LcZ.eigenspace ((n * e * l : ℤ) : K) = ⊤

def Image (U : Finset ℤ) : Prop :=
  (∀ w ∈ LinearMap.range D.LcZ, Polynomial.aeval D.LcZ (polyR l e U η) w = 0 ∧
    (((polyR l e U η).eval 0 : ℤ) : K) • w =
      -D.LcZ (Polynomial.aeval D.LcZ (polyR₁ l e U η) w)) ∧
  ∀ W : Submodule K D.Zl, W ≤ W.comap D.LcZ → LinearMap.range D.LcZ ⊓ W = W.map D.LcZ

def IntegralImage (U : Finset ℤ) : Prop :=
  ∀ (c : ℤ), ∀ w ∈ LinearMap.range D.LcZ, (l : K) ^ c • (w : D.Pol) ∈ D.Z →
    ∃ z : D.Zl, (l : K) ^ c • (z : D.Pol) ∈ D.Z ∧
      (((polyR l e U η).eval 0 : ℤ) : K) • w = D.LcZ z

def Divisible : Prop :=
  (∀ w ∈ D.Z, ∃ z ∈ D.Z, (l : K) ^ η • w = D.vPol z) ∧
  ∀ y ∈ D.Y, (l : K) ^ η • y ∈ D.Y' ⊔ D.Minv

def IntegralityComputation : Prop :=
  (∀ m ∈ D.MM, ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), m = p + f) ∧
  (∀ f ∈ D.FilMM (10 * H), Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man) ∧
  ∀ y ∈ D.EM η, ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), E K l e ^ (2 * H) • D.EN y = p + f

end Clauses

def Valuation (l e : ℕ) (U : Finset ℤ) (η N : ℕ) : Prop :=
  (∀ n ∈ shifts U η, |n| < l) ∧
  (polyR l e U η).eval 0 ≠ 0 ∧
  padicValInt l ((polyR l e U η).eval 0) = ((shifts U η).erase 0).card ∧
  ((shifts U η).erase 0).card ≤ U.card * η ∧ U.card * η ≤ (N + 1) * η

section Basic₂

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {η H : ℕ}

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds

open PowerSeries GlobalTheory.BK

section Ring

variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ)

def SHigh : Ideal (S O K e) :=
  (Ideal.span {(X : K⟦X⟧) ^ (l * e)}).comap (S O K e).val

variable {O K l e} in
theorem mem_SHigh {f : S O K e} : f ∈ SHigh O K l e ↔ (X : K⟦X⟧) ^ (l * e) ∣ (f : K⟦X⟧) := by
  rw [SHigh, Ideal.mem_comap, Ideal.mem_span_singleton]
  rfl

structure RingModHigh : Prop where
  N_stable : ∀ f ∈ SHigh O K l e, ∃ g ∈ SHigh O K l e, (g : K⟦X⟧) = N K (f : K⟦X⟧)
  eq_add : ∀ f : K⟦X⟧, f ∈ S O K e ↔ ∃ g ∈ A O K, ∃ h ∈ SHigh O K l e, f = g + (h : K⟦X⟧)
  inter_eq : ∀ f : K⟦X⟧, (f ∈ A O K ∧ ∃ h ∈ SHigh O K l e, (h : K⟦X⟧) = f) ↔
    ∃ g ∈ A O K, f = ((X : K⟦X⟧) ^ e) ^ l * g

end Ring

section Degrees

variable {e : ℕ}

def degrees (Sig : Finset (ZMod e)) (c : ZMod e) (m m' : ℕ) : Finset ℕ :=
  (Sig ×ˢ Finset.Ico m m').image fun p => (c - p.1).val + p.2 * e

def D₁ (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ) : Finset ℕ := degrees Sig c 0 A'

def D₂ (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ) : Finset ℕ := degrees Sig c A' (2 * A')

def rootPoly (T : Finset ℕ) : Polynomial ℤ := ∏ i ∈ T, (Polynomial.X - Polynomial.C (i : ℤ))

def P₁ (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ) : Polynomial ℤ := rootPoly (D₁ Sig c A')

def P₂ (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ) : Polynomial ℤ := rootPoly (D₂ Sig c A')

structure DegreeBounds (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ) : Prop where
  lt_of_mem₁ : ∀ i ∈ D₁ Sig c A', i < e * A'
  mem_Ico₂ : ∀ j ∈ D₂ Sig c A', e * A' ≤ j ∧ j < 2 * e * A'
  monic₁ : (P₁ Sig c A').Monic
  monic₂ : (P₂ Sig c A').Monic
  disjoint_roots : Disjoint (P₁ Sig c A').roots (P₂ Sig c A').roots
  card₁ : (D₁ Sig c A').card ≤ Sig.card * A'
  card₂ : (D₂ Sig c A').card ≤ Sig.card * A'

end Degrees

section Modules

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def MMHigh (P : PhiMod O K l e a ι) : Submodule O (Vec K a ι) :=
  (SHigh O K l e • P.MM).restrictScalars O

def mulL (P : PhiMod O K l e a ι) (f : K⟦X⟧) : Submodule O (Vec K a ι) :=
  (P.L.restrictScalars O).map ((mulV K a ι f).restrictScalars O)

theorem mem_mulL {P : PhiMod O K l e a ι} {f : K⟦X⟧} {x : Vec K a ι} :
    x ∈ mulL P f ↔ ∃ y ∈ P.L, f • y = x := by
  simp only [mulL, Submodule.mem_map, Submodule.restrictScalars_mem, LinearMap.restrictScalars_apply,
    mulV_apply]

abbrev uL (P : PhiMod O K l e a ι) (i : ℕ) : Submodule O (Vec K a ι) := mulL P (X ^ i)

abbrev vL (P : PhiMod O K l e a ι) (n : ℕ) : Submodule O (Vec K a ι) := mulL P ((X ^ e) ^ n)

abbrev part (W : Submodule K (Vec K a ι)) (V : Submodule O (Vec K a ι)) : Submodule O (Vec K a ι) :=
  V ⊓ W.restrictScalars O

variable [Fact l.Prime]

structure ModHigh (P : PhiMod O K l e a ι) (W : Submodule K (Vec K a ι)) : Prop where
  MM_eq : part W (P.MM.restrictScalars O) = part W (P.L.restrictScalars O) ⊔ part W (MMHigh P)
  inter_eq : part W (P.L.restrictScalars O) ⊓ part W (MMHigh P) = part W (vL P l)
  conn_MM : ∀ x ∈ part W (P.MM.restrictScalars O), P.conn x ∈ part W (P.MM.restrictScalars O)
  conn_high : ∀ x ∈ part W (MMHigh P), P.conn x ∈ part W (MMHigh P)
  conn_uL : ∀ i : ℕ, ∀ x ∈ part W (uL P i) ⊔ part W (MMHigh P),
    P.conn x ∈ part W (uL P i) ⊔ part W (MMHigh P)
  conn_graded : ∀ i : ℕ, i < l * e → ∀ x ∈ part W (uL P i),
    P.conn x - i • x ∈ part W (uL P (i + 1)) ⊔ part W (MMHigh P)

def ImageStable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)
    (W : Submodule K (Vec K a κ)) : Prop :=
  ∀ x ∈ part W (F.imL.restrictScalars O) ⊔ part W (MMHigh Q),
    Q.conn x ∈ part W (F.imL.restrictScalars O) ⊔ part W (MMHigh Q)

variable [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a]

structure RaisesDegree {P : PhiMod O K l e a ι} (Δ : Descent P) (Sig : Finset (ZMod e)) (c : ZMod e)
    (A' : ℕ) : Prop where
  graded_eq_zero : ∀ i : ℕ, (¬ ∃ c' ∈ Sig, ∃ n : ℕ, i = (c - c').val + n * e) →
    part (Δ.isotypic c) (uL P i) ≤ uL P (i + 1)
  aeval₁ : ∀ x ∈ part (Δ.isotypic c) (P.L.restrictScalars O),
    Polynomial.aeval P.conn (P₁ Sig c A') x ∈ vL P A' ⊔ MMHigh P
  aeval₂ : ∀ x ∈ part (Δ.isotypic c) (vL P A'),
    Polynomial.aeval P.conn (P₂ Sig c A') x ∈ vL P (2 * A') ⊔ MMHigh P

end Modules

section Statement

variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]

def Reduction : Prop :=
  RingModHigh O K l e ∧
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H),
    ModHigh D.toPhiMod ⊤ ∧
    (∀ ζ x, D.desc.act (TameGal.inertia ζ) (D.conn x) = D.conn (D.desc.act (TameGal.inertia ζ) x)) ∧
    ∀ c : ZMod e, ModHigh D.toPhiMod (D.desc.isotypic c)) ∧
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (η H : ℕ)
    (B₁ : BKDat O K l e a ι η H) (B₂ : BKDat O K l e a κ η H) (F : BKHom B₁ B₂),
    (∀ x ∈ B₁.MM, F.app x ∈ B₂.MM ∧ F.app (B₁.conn x) = B₂.conn (F.app x)) ∧
    ImageStable F.toHom ⊤ ∧ ∀ c : ZMod e, ImageStable F.toHom (B₂.desc.isotypic c)

def Degrees : Prop :=
  ∀ (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ), 2 * A' ≤ l →
    DegreeBounds Sig c A' ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H),
      (∀ τ, D.desc.chars τ ⊆ (Sig : Set (ZMod e))) → RaisesDegree D.desc Sig c A'

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds

open GlobalTheory.BK PowerSeries

def C₀ : ℕ := 40

structure Bounds (l e : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ) (N η H : ℕ) : Prop where

  frob_mem : ∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig

  zero_mem_Sig : (0 : ZMod e) ∈ Sig
  card_Sig : Sig.card ≤ N
  two_le : 2 ≤ N

  range_U : ∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ (H : ℤ)
  zero_mem_U : (0 : ℤ) ∈ U
  card_U : U.card ≤ N + 1
  one_le : 1 ≤ η
  lt : η < H

  large : C₀ * (H * N ^ 2 + N ^ 3) < l

def rho (l : ℕ) {e : ℕ} (Sig : Finset (ZMod e)) (N : ℕ) : ℕ := 2 * (N - 1) * maxPeriod l Sig

def KillsCoker {V₁ V₂ : Type} [AddCommGroup V₂] (f : V₁ → V₂) (n : ℕ) (W₁ : Set V₁) (W₂ : Set V₂) : Prop :=
  ∀ y ∈ W₂, ∃ x ∈ W₁, f x = n • y

section

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

def KillsAll {D₁ : BKDat O K l e a ι η H} {D₂ : BKDat O K l e a κ η H} (F : BKHom D₁ D₂) (n : ℕ) :
    Prop :=
  KillsCoker F.app n D₁.L D₂.L ∧
  KillsCoker F.app n D₁.M D₂.M ∧
  KillsCoker F.app n (D₁.EM η) (D₂.EM η) ∧
  KillsCoker F.app n D₁.Minv D₂.Minv ∧
  KillsCoker F.app n D₁.Y D₂.Y ∧
  KillsCoker F.app n D₁.Y' D₂.Y'


omit [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] in
theorem killsCoker_M_iff {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q) (n : ℕ) :
    KillsCoker F.app n P.M Q.M ↔ ∀ q : F.coker, n • q = 0 := by
  constructor
  · intro h q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, hx, hxy⟩ := h y y.2
    rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨x, hx, hxy⟩
  · intro h y hy
    have h1 := h (Submodule.Quotient.mk ⟨y, hy⟩)
    rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    exact h1

end

def Stmt : Prop :=
  ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
    (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Sig : Finset (ZMod e)) (U : Finset ℤ) (N η H : ℕ), Bounds l e Sig U N η H →
    ∀ (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H),
      D₁.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) → (∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))) →
      ∀ F : BKHom D₁ D₂, IsFiniteLength (A O K) F.coker →
        KillsAll F (l ^ rho l Sig N)

end GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds
end
end

