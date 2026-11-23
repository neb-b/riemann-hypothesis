module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
section
open Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JR

class Unram (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] : Prop where
  charZero : CharZero F
  ultraF : IsUltrametricDist F
  ultraE : IsUltrametricDist E
  lcF : LocallyCompactSpace F
  lcE : LocallyCompactSpace E
  finrank_eq : Module.finrank F E = 2
  star_fix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x
  star_ne : ∃ y : E, star y ≠ y
  norm_star : ∀ y : E, ‖star y‖ = ‖y‖
  unram : ∀ y : E, ∃ x : F, ‖y‖ = ‖x‖

def eta {F : Type} [NormedField F] (x : F) : ℂ := by
  classical exact if ∃ y : F, ‖x‖ = ‖y‖ ^ 2 then 1 else -1

def IsStdChar {F : Type} [NormedField F] (ψ : AddChar F ℂ) : Prop :=
  (∀ x : F, ‖x‖ ≤ 1 → ψ x = 1) ∧ ∃ x : F, ψ x ≠ 1 ∧ ∀ y : F, ‖y‖ < 1 → ‖x * y‖ ≤ 1

def IsTest {X : Type} [TopologicalSpace X] (f : X → ℂ) : Prop := IsLocallyConstant f ∧ HasCompactSupport f

abbrev Gl (r : ℕ) (k : Type) : Type := Matrix (Fin r) (Fin r) k × (Fin r → k) × (Fin r → k) × k

abbrev Inv (r : ℕ) (k : Type) : Type := (Fin r → k) × (Fin r → k) × k

section Alg
variable {r : ℕ} {k : Type} [CommRing k]

def act (g : GL (Fin r) k) (Y : Gl r k) : Gl r k :=
  ((g : Matrix (Fin r) (Fin r) k) * Y.1 * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k),
    (g : Matrix (Fin r) (Fin r) k) *ᵥ Y.2.1,
    Y.2.2.1 ᵥ* ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k), Y.2.2.2)

def mom (Y : Gl r k) (i : ℕ) : k := Y.2.2.1 ⬝ᵥ ((Y.1 ^ i) *ᵥ Y.2.1)

def inv (Y : Gl r k) : Inv r k := (fun i => Y.1.charpoly.coeff i, fun i => mom Y i, Y.2.2.2)

def Bm (Y : Gl r k) : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => ((Y.1 ^ (j : ℕ)) *ᵥ Y.2.1) i

def Cm (Y : Gl r k) : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => (Y.2.2.1 ᵥ* (Y.1 ^ (i : ℕ))) j

def companion (p : Fin r → k) : Matrix (Fin r) (Fin r) k :=
  Matrix.of fun i j => if (j : ℕ) + 1 = r then - p i else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

def sec (a : Inv r k) : Gl r k := (companion a.1, fun i => if (i : ℕ) = 0 then 1 else 0, a.2.1, a.2.2)

def hankel (a : Inv r k) : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => mom (sec a) ((i : ℕ) + (j : ℕ))

def Delta (a : Inv r k) : k := (hankel a).det

def full (Y : Gl r k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks Y.1 (Matrix.of fun i (_ : Fin 1) => Y.2.1 i) (Matrix.of fun (_ : Fin 1) j => Y.2.2.1 j)
      (Matrix.of fun _ _ => Y.2.2.2))

def lastDet (Y : Gl r k) : k :=
  (Matrix.of fun (i j : Fin (r + 1)) => (Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ (i : ℕ))) j).det

def Inv.map {k' : Type} [CommRing k'] (φ : k →+* k') (a : Inv r k) : Inv r k' :=
  (fun i => φ (a.1 i), fun i => φ (a.2.1 i), φ a.2.2)

end Alg

abbrev Hn (r : ℕ) (F E : Type) [CommRing E] [StarRing E] : Type :=
  selfAdjoint (Matrix (Fin r) (Fin r) E) × (Fin r → E) × F

section Herm
variable {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]

def Hn.toGl (X : Hn r F E) : Gl r E := (X.1.1, X.2.1, star X.2.1, algebraMap F E X.2.2)

def actU (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : Hn r F E :=
  (⟨g.1 * X.1.1 * star g.1, IsSelfAdjoint.conjugate X.1.2 g.1⟩, g.1 *ᵥ X.2.1, X.2.2)

def HasInv (X : Hn r F E) (a : Inv r F) : Prop := inv X.toGl = a.map (algebraMap F E)

end Herm

section Orb
variable {r : ℕ} {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def omega (Y : Gl r F) : ℂ := eta (lastDet Y)

def glO (r : ℕ) (F : Type) [NormedField F] : Set (GL (Fin r) F) :=
  {g | ∀ i j, ‖(g : Matrix (Fin r) (Fin r) F) i j‖ ≤ 1 ∧ ‖((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j‖ ≤ 1}

def uO (r : ℕ) (E : Type) [NormedField E] [StarRing E] : Set (Matrix.unitaryGroup (Fin r) E) :=
  {g | ∀ i j, ‖g.1 i j‖ ≤ 1}

structure Meas (r : ℕ) (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E] where
  [mG : MeasurableSpace (GL (Fin r) F)]
  [bG : BorelSpace (GL (Fin r) F)]
  [mU : MeasurableSpace (Matrix.unitaryGroup (Fin r) E)]
  [bU : BorelSpace (Matrix.unitaryGroup (Fin r) E)]
  [mF : MeasurableSpace F]
  [bF : BorelSpace F]
  [mE : MeasurableSpace E]
  [bE : BorelSpace E]
  μG : Measure (GL (Fin r) F)
  μU : Measure (Matrix.unitaryGroup (Fin r) E)
  μF : Measure F
  μE : Measure E
  haarG : μG.IsHaarMeasure
  haarU : μU.IsHaarMeasure
  haarF : μF.IsAddHaarMeasure
  haarE : μE.IsAddHaarMeasure
  volG : μG (glO r F) = 1
  volU : μU (uO r E) = 1
  volF : μF (Metric.closedBall 0 1) = 1
  volE : μE (Metric.closedBall 0 1) = 1

def orbG (M : Meas r F E) (f' : Gl r F → ℂ) (Y : Gl r F) : ℂ :=
  letI := M.mG
  ∫ g, f' (act g Y) * omega (act g Y) ∂M.μG

def orbU (M : Meas r F E) (f : Hn r F E → ℂ) (X : Hn r F E) : ℂ :=
  letI := M.mU
  ∫ g, f (actU g X) ∂M.μU

def MatchAt (M : Meas r F E) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ) (a : Inv r F) : Prop :=
  (∀ X : Hn r F E, HasInv X a → orbG M f' (sec a) = orbU M f X) ∧
    ((¬ ∃ X : Hn r F E, HasInv X a) → orbG M f' (sec a) = 0)

def Match (M : Meas r F E) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ) : Prop :=
  ∀ a : Inv r F, Delta a ≠ 0 → MatchAt M f' f a

def fourG (M : Meas r F E) (ψ : AddChar F ℂ) (f' : Gl r F → ℂ) (Y : Gl r F) : ℂ :=
  letI := M.mF
  ∫ b', ∫ c', f' (Y.1, b', c', Y.2.2.2) * ψ (c' ⬝ᵥ Y.2.1 + Y.2.2.1 ⬝ᵥ b')
    ∂(Measure.pi fun _ : Fin r => M.μF) ∂(Measure.pi fun _ : Fin r => M.μF)

def fourU (M : Meas r F E) (ψ : AddChar F ℂ) (f : Hn r F E → ℂ) (X : Hn r F E) : ℂ :=
  letI := M.mE
  ∫ c, f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE)

def unitG (r : ℕ) (F : Type) [NormedField F] : Gl r F → ℂ :=
  Set.indicator {Y | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1} 1

def unitU (r : ℕ) (F E : Type) [NormedField F] [NormedField E] [StarRing E] : Hn r F E → ℂ :=
  Set.indicator {X | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} 1

end Orb

def FourierMatch (r : ℕ) : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    ∀ (f' : Gl r F → ℂ) (f : Hn r F E → ℂ), IsTest f' → IsTest f → Match M f' f →
      Match M (fourG M ψ f') (fourU M ψ f)

def UnitMatch (r : ℕ) : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (M : Meas r F E), Match M (unitG r F) (unitU r F E)

end GlobalTheory.JR
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
section
namespace GlobalTheory.PsChar

variable {M A : Type*} [Monoid M] [CommRing A]

noncomputable def alt (T : M → A) : (n : ℕ) → (Fin n → M) → A
  | 0, _ => 1
  | n + 1, x => T (x 0) * alt T n (Fin.tail x) - ∑ i : Fin n, alt T n (Function.update (Fin.tail x) i (x 0 * Fin.tail x i))

structure IsPsChar (d : ℕ) (T : M → A) : Prop where
  one : T 1 = d
  comm : ∀ x y, T (x * y) = T (y * x)
  alt_eq_zero : ∀ x : Fin (d + 1) → M, alt T (d + 1) x = 0

theorem map_alt {B : Type*} [CommRing B] (f : A →+* B) (T : M → A) :
    ∀ (n : ℕ) (x : Fin n → M), f (alt T n x) = alt (fun g => f (T g)) n x
  | 0, _ => by simp [alt]
  | n + 1, x => by simp [alt, map_alt f T n]

end GlobalTheory.PsChar
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset

section Basic

variable {F : Type*} [NormedField F] {m : Type*} [Fintype m]

def Integral (x : m → F) : Prop := ∀ i, ‖x i‖ ≤ 1

def gsum (q D : ℕ) (M : ℕ → Matrix m m F) (x : m → F) : m → F :=
  ∑ n ∈ range (D + 1), (M n).mulVec (fun i => x i ^ q ^ n)

variable [DecidableEq m]

structure Normal (N : ℕ) (M : ℕ → Matrix m m F) : Prop where
  int : ∀ n i j, ‖M n i j‖ ≤ 1
  top : M N = 1
  small : ∀ n, N < n → ∀ i j, ‖M n i j‖ < 1

end Basic

def GLOnto (N : ℕ) : Prop :=
  ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → N ≤ D →
    ∀ M : ℕ → Matrix m m F, Normal N M → ∀ b : m → F, Integral b →
      ∃ x : m → F, Integral x ∧ gsum (p ^ e) D M x = b

def GLCount (N : ℕ) : Prop :=
  ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → N ≤ D →
    ∀ M : ℕ → Matrix m m F, Normal N M → (M 0).det ≠ 0 →
      Nat.card {x : m → F // Integral x ∧ gsum (p ^ e) D M x = 0} = (p ^ e) ^ (Fintype.card m * N)

section Win

variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

def pw (k : ℤ) (x : F) : F :=
  if 0 ≤ k then x ^ p ^ k.toNat else ((frobeniusEquiv F p).symm)^[(-k).toNat] x

def Orth {h : ℕ} (lam : Fin h → F) : Prop :=
  ∀ (c : Fin h → ℤ) (j : Fin h), ¬ (p : ℤ) ∣ c j → ‖lam j‖ ≤ ‖∑ i, (c i : F) * lam i‖

def term {h : ℕ} (ϖ : F) (lam : Fin h → F) (x : Fin h → F) (r j : Fin h) (n : ℤ) : F :=
  lam j * ϖ ^ (-n) * pw p ((r : ℤ) + n * h) (x j)

def rowT {h : ℕ} (ϖ : F) (lam : Fin h → F) (K : ℕ) (x : Fin h → F) (r : Fin h) : F :=
  ∑ j, ∑ n ∈ Icc (-(K : ℤ)) K, term p ϖ lam x r j n

end Win

def MooreNorm : Prop :=
  ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ)
    (lam : Fin h → F), Antitone (fun j => ‖lam j‖) → Orth p lam →
    ‖(Matrix.of fun r j : Fin h => lam j ^ p ^ (r : ℕ)).det‖ = ∏ j : Fin h, ‖lam j‖ ^ p ^ (h - 1 - (j : ℕ))

def WinThm : Prop :=
  ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime]
    [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F), 0 < h → ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam : Fin h → F, (∀ j, lam j ≠ 0) →
    Antitone (fun j => ‖lam j‖) → Orth p lam → (∀ i j, ‖lam i‖ < p * ‖lam j‖) →
    ∃ (ρ τ : Fin h → ℝ) (K : ℕ), (∀ j, 0 < ρ j ∧ ρ j < 1) ∧ (∀ r, 0 < τ r) ∧
      (∀ x : Fin h → F, (∀ j, ‖x j‖ ≤ ρ j) → ∀ (r j : Fin h) (n : ℤ),
        ‖term p ϖ lam x r j n‖ ≤ τ r ∧ ((K : ℤ) < |n| → ‖term p ϖ lam x r j n‖ ≤ τ r / p)) ∧
      (∀ b : Fin h → F, (∀ r, ‖b r‖ ≤ τ r) → ∃ x : Fin h → F, (∀ j, ‖x j‖ ≤ ρ j) ∧ ∀ r, rowT p ϖ lam K x r = b r) ∧
      (∃ x : Fin h → F, (∀ j, ‖x j‖ ≤ ρ j) ∧ (∃ j, ρ j ^ p ^ h < ‖x j‖) ∧ ∀ r, rowT p ϖ lam K x r = 0)

end GlobalTheory.PMonE

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwConj
section
open Matrix

noncomputable section

namespace GlobalTheory.Tw

variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

def Phi (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (i : ℕ) + (j : ℕ) + 1 = n then (-1) ^ (i : ℕ) else 0

def theta (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := Phi n R * (g⁻¹)ᴴ * (Phi n R)ᵀ

def nrm (δ : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := δ * theta δ

def twConj (x δ : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := x⁻¹ * δ * theta x

def Reg (δ : Matrix (Fin n) (Fin n) R) : Prop := IsUnit δ ∧ (nrm δ).charpoly.Separable

def cent (δ : Matrix (Fin n) (Fin n) R) : Set (Matrix (Fin n) (Fin n) R) := {g | IsUnit g ∧ g * δ = δ * theta g}

def adj (δ g : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := δ * Phi n R * gᴴ * (Phi n R)ᵀ * δ⁻¹

end GlobalTheory.Tw
end
end

