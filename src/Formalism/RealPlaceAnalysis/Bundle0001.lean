module

public import Mathlib

@[expose] public section

-- bundled from Formalism.RealPlaceAnalysis.Complexify
section
open Matrix

noncomputable section

namespace Formalism.REAL

def Jm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => if ε a then 1 else -1

def inUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  gᴴ * Jm ε * g = Jm ε

def inG {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Xᴴ * Jm ε + Jm ε * X = 0

def inK {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  inG ε X ∧ X * Jm ε = Jm ε * X

def inP {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  inG ε X ∧ X * Jm ε = -(Jm ε * X)

def Kset {n : ℕ} (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Jm ε = Jm ε * g}

def hs {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖g i j‖ ^ 2

lemma Jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  cases ε a <;> norm_num

lemma Jm_conjTranspose {n : ℕ} (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  apply congrArg Matrix.diagonal
  funext a
  change star (if ε a then (1 : ℂ) else -1) = _
  cases h : ε a <;> simp [h, star_neg, star_one]

def UJ {n : ℕ} (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | inUJ ε (g : Matrix (Fin n) (Fin n) ℂ)}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq, inUJ, Units.val_mul, Matrix.conjTranspose_mul] at *
    calc (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε *
          ((g : Matrix (Fin n) (Fin n) ℂ) * h)
        = (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hg, hh]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, inUJ, Units.val_one, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq, inUJ] at *
    have h1 : ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
        (g : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    have h2 : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ) = 1 := Units.mul_inv g
    calc ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        = ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
          ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * g) *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by rw [hg]
      _ = Jm ε := by
          rw [show ∀ A B C D E : Matrix (Fin n) (Fin n) ℂ, A * (B * C * D) * E = (A * B) * C * (D * E)
            from fun A B C D E => by simp only [Matrix.mul_assoc], h1, h2, Matrix.one_mul, Matrix.mul_one]

def UJClosed : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g}

def ExpUJ : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ), inG ε X →
    ∀ t : ℝ, inUJ ε (NormedSpace.exp ((t : ℂ) • X))

def KFacts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    (∀ g ∈ Kset ε, inUJ ε g) ∧ IsCompact (Kset ε) ∧ Jm ε ∈ Kset ε ∧
    (∀ X, inK ε X → NormedSpace.exp X ∈ Kset ε) ∧
    (∀ g, g ∈ Kset ε ↔ (inUJ ε g ∧ g ∈ Matrix.unitaryGroup (Fin n) ℂ))

def PChar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ),
    (inP ε X ↔ (Xᴴ = X ∧ X * Jm ε = -(Jm ε * X))) ∧
    (inP ε X → Jm ε * X * Jm ε = -X)

def Polar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    (∀ g, inUJ ε g → ∃ k X, k ∈ Kset ε ∧ inP ε X ∧ g = k * NormedSpace.exp X) ∧
    (∀ k k' X X', k ∈ Kset ε → k' ∈ Kset ε → inP ε X → inP ε X' →
      k * NormedSpace.exp X = k' * NormedSpace.exp X' → k = k' ∧ X = X') ∧
    (∃ L : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
      ContinuousOn L {g | inUJ ε g} ∧
      ∀ g, inUJ ε g → inP ε (L g) ∧ g * NormedSpace.exp (-L g) ∈ Kset ε)

def HSBall : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    (∀ R : ℝ, IsCompact {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g ∧ hs g ≤ R}) ∧
    (∀ g k, k ∈ Kset ε → hs (g * k) = hs g ∧ hs (k * g) = hs g)

def UJInv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
    g * (Jm ε * gᴴ * Jm ε) = 1 ∧ (Jm ε * gᴴ * Jm ε) * g = 1

def OneParam : Prop :=
  ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ),
    NormedSpace.exp (((s + t : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)

def BallOpen : Prop :=
  ∀ (n : ℕ) (R : ℝ), (n : ℝ) < R →
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U ∧
      ∀ g ∈ U, hs g < R

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.StatementA
section
open scoped InnerProductSpace TensorProduct
open Finset

noncomputable section

namespace Formalism.REAL

def GlRel {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, E a b * E c d - E c d * E a b =
    (if b = c then E a d else 0) - (if d = a then E c b else 0)

def sgn {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : ℝ := if ε a = ε b then 1 else -1

def IsUnitary {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Prop :=
  ∀ (a b : Fin n) (x y : V), ⟪E a b x, y⟫_ℂ = (sgn ε a b : ℂ) * ⟪x, E b a y⟫_ℂ

def Cas {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : A :=
  ∑ a, ∑ b, E a b * E b a

def CasK {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → A) : A :=
  ∑ a, ∑ b, if ε a = ε b then E a b * E b a else 0

def IsWeight {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V) : Prop :=
  ∀ a, E a a w = (μ a : ℂ) • w

def KHighest {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V) : Prop :=
  IsWeight E μ w ∧ ∀ a b, a < b → ε a = ε b → E a b w = 0

def rhoC {n : ℕ} (ε : Fin n → Bool) : Fin n → ℝ := fun a =>
  (((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) -
    ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ)) / 2

def rhoN {n : ℕ} (ε : Fin n → Bool) : Fin n → ℝ := fun a =>
  (((univ.filter fun b => a < b ∧ ε b ≠ ε a).card : ℝ) -
    ((univ.filter fun b => b < a ∧ ε b ≠ ε a).card : ℝ)) / 2

def dot {n : ℕ} (u v : Fin n → ℝ) : ℝ := ∑ a, u a * v a

def nsq {n : ℕ} (u : Fin n → ℝ) : ℝ := dot u u

def root {n : ℕ} (a b : Fin n) : Fin n → ℝ := Pi.single a 1 - Pi.single b 1

def WDCas : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V),
    GlRel E → IsUnitary ε E → KHighest ε E μ w →
    ⟪w, Cas E w⟫_ℂ = (((nsq (μ + rhoC ε) - nsq (rhoC ε)) * ‖w‖ ^ 2 -
      ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b w‖ ^ 2) : ℝ) : ℂ)

def RhoStd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a : Fin n), rhoC ε a + rhoN ε a = ((n : ℝ) - 1) / 2 - (a : ℝ)

def SumSq : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (w : V),
    IsUnitary ε E →
    (((∑ a, ∑ b, ‖E a b w‖ ^ 2 : ℝ)) : ℂ) = ⟪w, (2 • CasK ε E - Cas E) w⟫_ℂ

def CasKHighest : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V),
    GlRel E → KHighest ε E μ w →
    CasK ε E w = ((nsq (μ + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • w

def CasCentral : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → A), GlRel E →
    (∀ c d, Cas E * E c d = E c d * Cas E) ∧
    (∀ c d, ε c = ε d → CasK ε E * E c d = E c d * CasK ε E)

def tens {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W) :
    Fin n → Fin n → Module.End ℂ (V ⊗[ℂ] W) :=
  fun a b => TensorProduct.map (E a b) LinearMap.id + TensorProduct.map LinearMap.id (F a b)

def Om {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) : Module.End ℂ (V ⊗[ℂ] W) :=
  ∑ a, ∑ b, if ε a = ε b then TensorProduct.map (E a b) (F b a) else 0

def adj {n : ℕ} (a b : Fin n) : Module.End ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  LinearMap.mulLeft ℂ (Matrix.single a b (1 : ℂ)) - LinearMap.mulRight ℂ (Matrix.single a b (1 : ℂ))

def OmEigen : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (a b : Fin n), a ≠ b →
    ((nsq (lam + rhoN ε - rhoC ε + root a b + rhoC ε) - nsq (rhoC ε)) - (n : ℝ) -
      (nsq (lam + rhoN ε - rhoC ε + rhoC ε) - nsq (rhoC ε))) / 2 =
      (lam a + rhoN ε a) - (lam b + rhoN ε b) + 1 - (n : ℝ) / 2

def UGap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (g : ℝ) (a b : Fin n),
    a < b → ε a ≠ ε b → g ≤ lam a - lam b →
    g - 2 * (n : ℝ) ≤ (lam a + rhoN ε a) - (lam b + rhoN ε b) + 1 - (n : ℝ) / 2

def GrowthIter : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (X : Module.End ℂ V)
    (U : ℕ → Submodule ℂ V) (B C : ℝ), 0 ≤ B → 0 ≤ C →
    (∀ (j : ℕ), ∀ w ∈ U j, X w ∈ U (j + 1) ∧ ‖X w‖ ≤ C * (B + j) * ‖w‖) →
    ∀ (j k : ℕ), ∀ w ∈ U j, ‖(X ^ k) w‖ ≤ C ^ k * (B + j + k) ^ k * ‖w‖

def TaylorRadius : Prop :=
  ∀ (C m t : ℝ), 0 ≤ C → 0 ≤ m → 0 ≤ t → C * t * Real.exp 1 < 1 →
    Summable (fun k : ℕ => (C * t) ^ k * (m + k) ^ k / (k.factorial : ℝ))

def volU : ℕ → ℝ
  | 0 => 1
  | i + 1 => volU i * (2 * Real.pi ^ (i + 1) / (i.factorial : ℝ))

end Formalism.REAL
end
end

