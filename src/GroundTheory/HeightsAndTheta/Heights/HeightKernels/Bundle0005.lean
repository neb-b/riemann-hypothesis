module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.GlobalFields.TateThesis.LatticePoissonBasic

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootsOfUnityDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RootsOfUnityDenseAlt

open Complex

theorem rootsOfUnity_infinite :
    {z : ℂ | ∃ k : ℕ, 0 < k ∧ z ^ k = 1}.Infinite := by
  have hprim : ∀ m : ℕ,
      IsPrimitiveRoot (exp (2 * Real.pi * I / ((m + 1 : ℕ) : ℂ))) (m + 1) :=
    fun m => Complex.isPrimitiveRoot_exp (m + 1) (Nat.succ_ne_zero m)
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => exp (2 * Real.pi * I / ((m + 1 : ℕ) : ℂ))) ?_ ?_
  · intro a b hab
    have ha := hprim a
    have hb := hprim b
    simp only at hab
    rw [hab] at ha
    have := IsPrimitiveRoot.unique ha hb
    omega
  · intro m
    exact ⟨m + 1, Nat.succ_pos m, (hprim m).pow_eq_one⟩

end RootsOfUnityDenseAlt

theorem RootsOfUnityDense.proof : RootsOfUnityDense.Statement := by
  intro n P hP
  refine MvPolynomial.funext_set (p := P) (q := 0)
    (fun _ => {z : ℂ | ∃ k : ℕ, 0 < k ∧ z ^ k = 1})
    (fun _ => RootsOfUnityDenseAlt.rootsOfUnity_infinite) ?_
  intro x hx
  rw [map_zero]
  exact hP x fun i => hx i (Set.mem_univ i)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def hermChartPot {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (y : Fin e → ℂ) : ℝ :=
  Real.log (Real.sqrt (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ
    (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re)

def chartMass {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : ℝ :=
  ∫ y : Fin e → ℂ, maDensity (fun _ : Fin e => hermChartPot M) y

def ChartMassInvariant.Statement : Prop :=
  ∀ (e : ℕ) (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef →
    chartMass M = chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory
open scoped FourierTransform

noncomputable section

def gaussLattice {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) :
    Submodule ℤ (EuclideanSpace ℝ (Fin g)) :=
  Submodule.span ℤ (Set.range fun i : Fin g => WithLp.toLp 2 (B *ᵥ Pi.single i 1))

def gaussShellConst (n : ℕ) : ℝ :=
  3 ^ n * √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π))

def GaussSqrt.Statement : Prop :=
  ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → ∃ B : Matrix (Fin g) (Fin g) ℝ, Bᵀ * B = Y

def GaussLatticeIsLattice.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    DiscreteTopology (gaussLattice B) ∧ ∀ [DiscreteTopology (gaussLattice B)], IsZLattice ℝ (gaussLattice B)

def GaussLatticeCovolume.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    ZLattice.covolume (gaussLattice B) = |B.det|

def GaussLatticeCoords.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    (∀ k : Fin g → ℤ, WithLp.toLp 2 (B *ᵥ intVec k) ∈ gaussLattice B) ∧
    (∀ x ∈ gaussLattice B, ∃ k : Fin g → ℤ, x = WithLp.toLp 2 (B *ᵥ intVec k)) ∧
    Function.Injective fun k : Fin g → ℤ => B *ᵥ intVec k

def GaussFourierSelf.Statement : Prop :=
  ∀ (g : ℕ) (w : EuclideanSpace ℝ (Fin g)),
    𝓕 (fun x : EuclideanSpace ℝ (Fin g) => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)) w =
      ((Real.exp (-π * ‖w‖ ^ 2) : ℝ) : ℂ)

def GaussPoissonBound.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 → ∀ a : Fin g → ℝ,
    Summable (fun k : Fin g → ℤ =>
      Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a))))) ∧
    Summable (fun μ : GroundTheory.Global.dualLattice (gaussLattice B) =>
      Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)) ∧
    ∑' k : Fin g → ℤ, Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a)))) ≤
      |B.det|⁻¹ * ∑' μ : GroundTheory.Global.dualLattice (gaussLattice B),
        Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)

def GaussDualMin.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    ∀ μ ∈ GroundTheory.Global.dualLattice (gaussLattice B), μ ≠ 0 →
      ∃ l : Fin g → ℤ, l ≠ 0 ∧ qf (Bᵀ * B)⁻¹ (intVec l) ≤ ‖μ‖ ^ 2

def GaussDetFactor.Statement : Prop :=
  ∀ (g : ℕ) (Y B : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → Bᵀ * B = (1 / 2 : ℝ) • Y →
    |B.det|⁻¹ = √2 ^ g * Y.det ^ (-(1 / 2 : ℝ))

def GaussPoissonDual.Statement : Prop :=
  ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ), Y.PosDef → 0 < ρ →
    (∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)) → ∀ u : Fin g → ℝ,
      Summable (fun k : Fin g → ℤ => Real.exp (-(π / 2) * qf Y (intVec k + u))) ∧
      ∃ Λ : Submodule ℤ (EuclideanSpace ℝ (Fin g)), (∀ v ∈ Λ, v ≠ 0 → ρ ≤ ‖v‖) ∧
        ∑' k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u)) ≤
          √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) *
            ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)

def GaussPacking.Statement : Prop :=
  ∀ (n : ℕ) (s : Finset (EuclideanSpace ℝ (Fin n))) (δ r : ℝ), 0 < δ → 0 ≤ r →
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ ‖x - y‖) → (∀ x ∈ s, ‖x‖ ≤ r) →
    (s.card : ℝ) ≤ (1 + 2 * r / δ) ^ n

def GaussTermBound.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ m : ℕ,
    ((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2) ≤
      √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ))

def GaussShell.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (δ : ℝ), 0 < δ →
    (∀ v ∈ Λ, v ≠ 0 → δ ≤ ‖v‖) → ∀ (F : Finset Λ) (m : ℕ),
      ∑ μ ∈ F.filter (fun μ : Λ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊ = m),
          Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
        gaussShellConst n * (1 + 1 / δ) ^ n * Real.exp (-(m : ℝ))

def GaussShellSum.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (δ : ℝ), 0 < δ →
    (∀ v ∈ Λ, v ≠ 0 → δ ≤ ‖v‖) →
      Summable (fun μ : Λ => Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)) ∧
      ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
        2 * gaussShellConst n * (1 + 1 / δ) ^ n

def GaussConstant.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → √2 ^ n * (2 * gaussShellConst n) ≤ (72 * Real.exp 4 * n) ^ ((n : ℝ) / 2)

abbrev gaussUnit : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (Pi.single 0 1)

theorem gaussUnit_norm : ‖gaussUnit‖ = 1 := by
  simp [gaussUnit]

theorem mem_gaussLattice_one {x : EuclideanSpace ℝ (Fin 1)} :
    x ∈ gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ) ↔ ∃ a : ℤ, a • gaussUnit = x := by
  have h : (Set.range fun i : Fin 1 => WithLp.toLp 2 ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
      Pi.single i 1)) = {gaussUnit} := by
    rw [Set.range_unique, Matrix.one_mulVec]
    rfl
  rw [gaussLattice, h, Submodule.mem_span_singleton]

theorem gaussLattice_one_min : ∀ v ∈ gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ), v ≠ 0 →
    (1 : ℝ) ≤ ‖v‖ := by
  intro v hv hv0
  obtain ⟨a, rfl⟩ := mem_gaussLattice_one.1 hv
  have ha : a ≠ 0 := by rintro rfl; exact hv0 (zero_smul _ _)
  rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, gaussUnit_norm, mul_one, Real.norm_eq_abs]
  exact_mod_cast Int.one_le_abs ha

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsInvertibleIdealIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def InvertibleIdealIndex.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L) (M : AddSubgroup L) (ι : Type) [Fintype ι]
    (a : ι → L),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) →
    (∀ i, a i ∈ M) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * a i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) →
      (Module.finrank ℚ L : ℝ) * Real.log (genIndex M B.toAddSubgroup) =
        (Module.finrank ℤ B : ℝ) *
          Real.log (genIndex (Submodule.span (𝓞 L) (Set.range a)).toAddSubgroup
            (1 : Submodule (𝓞 L) L).toAddSubgroup)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def symplOmega {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (u v : l ⊕ l → R) : R :=
  u ⬝ᵥ (J l R *ᵥ v)

def symplCons {R : Type*} {n : ℕ} (p q : R) (w : Fin n ⊕ Fin n → R) :
    Fin (n + 1) ⊕ Fin (n + 1) → R :=
  Sum.elim (vecCons p fun j => w (Sum.inl j)) (vecCons q fun j => w (Sum.inr j))

def symplTail {R : Type*} {n : ℕ} (u : Fin (n + 1) ⊕ Fin (n + 1) → R) : Fin n ⊕ Fin n → R :=
  fun x => u (Sum.map Fin.succ Fin.succ x)

def symplExt {R : Type*} [Zero R] {n : ℕ} (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) R :=
  Matrix.of (Sum.elim (vecCons (symplCons α β 0) fun i => symplCons 0 0 (Q (Sum.inl i)))
    (vecCons (symplCons γ δ 0) fun i => symplCons 0 0 (Q (Sum.inr i))))

def symplReduce {n : ℕ} (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fun a b => H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) -
    H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) * H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) /
      H (Sum.inl 0) (Sum.inl 0)

def symplGram {l : Type*} [Fintype l] (P : Matrix l l ℤ) (G : Matrix l l ℝ) : Matrix l l ℝ :=
  P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ

def SymplOmegaMem.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (l : Type) [Fintype l] [DecidableEq l]
    (M : Matrix (l ⊕ l) (l ⊕ l) R),
    M ∈ symplecticGroup l R ↔ ∀ x y, symplOmega (M x) (M y) = J l R x y

def SymplCons.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ),
    (∀ u : Fin (n + 1) ⊕ Fin (n + 1) → R,
      symplCons (u (Sum.inl 0)) (u (Sum.inr 0)) (symplTail u) = u) ∧
    ∀ (p q p' q' : R) (w w' : Fin n ⊕ Fin n → R),
      symplOmega (symplCons p q w) (symplCons p' q' w') = q * p' - p * q' + symplOmega w w'

def SymplExtMem.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R),
    α * δ - β * γ = 1 → Q ∈ symplecticGroup (Fin n) R →
    symplExt α β γ δ Q ∈ symplecticGroup (Fin (n + 1)) R

def SymplExtVecMul.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (α β γ δ p q : R)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (w : Fin n ⊕ Fin n → R),
    symplCons p q w ᵥ* symplExt α β γ δ Q = symplCons (p * α + q * γ) (p * β + q * δ) (w ᵥ* Q)

def SymplTwoRow.Statement : Prop :=
  ∀ (n : ℕ) (c d x y : ℤ), x * c + y * d = 1 →
    ∃ P ∈ symplecticGroup (Fin (n + 1 + 1)) ℤ, P (Sum.inl 0) = symplCons c 0 (symplCons d 0 0)

def SymplGcd.Statement : Prop :=
  ∀ a b : ℤ, ∃ c a' b' x y : ℤ, a = c * a' ∧ b = c * b' ∧ x * a' + y * b' = 1

def SymplOrbit.Statement : Prop :=
  ∀ (n : ℕ) (v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ),
    ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, ∃ m : ℤ, v = m • P (Sum.inl 0)

def SymplQuadDiag.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∃ (O : Matrix ι ι ℝ) (lam : ι → ℝ), (∀ i, 0 < lam i) ∧ |O.det| = 1 ∧ ∏ i, lam i = G.det ∧
      ∀ x : ι → ℝ, qf G x = ∑ i, lam i * (O *ᵥ x) i ^ 2

def SymplBoxVolume.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ), A.det ≠ 0 →
    (∀ i, 0 < a i) →
    MeasureTheory.volume {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} =
      ENNReal.ofReal ((∏ i, 2 * a i) / |A.det|)

def SymplMinkowskiBox.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ), |A.det| = 1 →
    (∀ i, 0 < a i) → 1 < ∏ i, a i →
    ∃ v : ι → ℤ, v ≠ 0 ∧ ∀ i, |(A *ᵥ intVec v) i| < a i

def SymplMinExists.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∃ m : ℝ, IsLeast {t | ∃ v : ι → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} m

def SymplMinBound.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef → G.det = 1 →
    ∀ m : ℝ, IsLeast {t | ∃ v : ι → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} m → m ≤ Fintype.card ι

def SymplShortPrim.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∀ (v w : ι → ℤ) (m : ℤ), v = m • w → v ≠ 0 →
    (∀ u : ι → ℤ, u ≠ 0 → qf G (intVec v) ≤ qf G (intVec u)) → m = 1 ∨ m = -1

def SymplGramMem.Statement : Prop :=
  ∀ (n : ℕ) (P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    P ∈ symplecticGroup (Fin n) ℤ → G ∈ symplecticGroup (Fin n) ℝ → G.PosDef →
    symplGram P G ∈ symplecticGroup (Fin n) ℝ ∧ (symplGram P G).PosDef ∧
      (∀ Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ,
        symplGram (Q * P) G = symplGram Q (symplGram P G)) ∧
      ∀ x, symplGram P G x x = qf G (intVec (P x))

def SymplFirstRow.Statement : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    G ∈ symplecticGroup (Fin (n + 1)) ℝ → G.PosDef →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      0 < ρsq ∧ ρsq ≤ 2 * ((n : ℝ) + 1) ∧
      ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, symplGram P G (Sum.inl 0) (Sum.inl 0) = ρsq

def SymplReduceMem.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    H ∈ symplecticGroup (Fin (n + 1)) ℝ → H (Sum.inl 0) (Sum.inl 0) ≠ 0 →
    symplReduce H ∈ symplecticGroup (Fin n) ℝ

def SymplReducePosDef.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    H.PosDef → (symplReduce H).PosDef

def SymplReduceConj.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    (symplExt 1 0 0 1 Q * H * (symplExt 1 0 0 1 Q)ᵀ) (Sum.inl 0) (Sum.inl 0) =
        H (Sum.inl 0) (Sum.inl 0) ∧
      symplReduce (symplExt 1 0 0 1 Q * H * (symplExt 1 0 0 1 Q)ᵀ) = Q * symplReduce H * Qᵀ

def SymplDetSchur.Statement : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ), A 0 0 ≠ 0 →
    A.det = A 0 0 * (Matrix.of fun i j : Fin n => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0).det

def SymplReduceStep.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ),
    H (Sum.inl 0) (Sum.inl 0) ≠ 0 → Q ∈ symplecticGroup (Fin n) ℤ →
    ∃ Q' ∈ symplecticGroup (Fin (n + 1)) ℤ,
      symplGram Q' H (Sum.inl 0) (Sum.inl 0) = H (Sum.inl 0) (Sum.inl 0) ∧
      (symplGram Q' H).toBlocks₁₁.det =
        H (Sum.inl 0) (Sum.inl 0) * (symplGram Q (symplReduce H)).toBlocks₁₁.det

def SymplStep.Statement : Prop :=
  ∀ (n : ℕ) (B : ℝ) (G : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    G ∈ symplecticGroup (Fin (n + 1)) ℝ → G.PosDef →
    (∀ H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, H ∈ symplecticGroup (Fin n) ℝ → H.PosDef →
      ∃ P ∈ symplecticGroup (Fin n) ℤ, (symplGram P H).toBlocks₁₁.det ≤ B) →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      0 < ρsq ∧ ρsq ≤ 2 * ((n : ℝ) + 1) ∧
      ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, symplGram P G (Sum.inl 0) (Sum.inl 0) = ρsq ∧
        (symplGram P G).toBlocks₁₁.det ≤ ρsq * B

def SymplDetBound.Statement : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    G ∈ symplecticGroup (Fin n) ℝ → G.PosDef →
    ∃ P ∈ symplecticGroup (Fin n) ℤ, (symplGram P G).toBlocks₁₁.det ≤ (2 * (n : ℝ)) ^ n

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

noncomputable section

def thetaSummand {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ)
    (k : Fin g → ℤ) : ℂ :=
  Complex.exp (π * Complex.I *
      ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ
        (periodMatrix X Y *ᵥ fun i => ((intVec k i + a i : ℝ) : ℂ))) +
    2 * π * Complex.I * ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ (z + fun i => (b i : ℂ))))

def torusChar {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ i, (m i : ℂ) * (u i : ℂ))

def ThetaSummandNorm.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ) (k : Fin g → ℤ), Y.IsSymm →
    ‖thetaSummand X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k‖ *
        exp (-π * qf Y u₁) = exp (-π * qf Y (intVec k + a + u₁))

def ThetaNormMajorant.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ), Y.PosDef →
    thetaNorm X Y a b u₁ u₂ ≤ ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁))

def ThetaCharIntegral.Statement : Prop :=
  ∀ (g : ℕ) (m : Fin g → ℤ),
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, torusChar m u = if m = 0 then 1 else 0

def ThetaCubeParseval.Statement : Prop :=
  ∀ (g : ℕ) (c : (Fin g → ℤ) → ℂ), Summable (fun k => ‖c k‖) →
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, ‖∑' k, c k * torusChar k u‖ ^ 2 = ∑' k, ‖c k‖ ^ 2

def ThetaInnerMean.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ : Fin g → ℝ), Y.PosDef →
    ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1, thetaNorm X Y a b u₁ u₂ ^ 2 =
      ∑' k : Fin g → ℤ, exp (-(2 * π) * qf Y (intVec k + a + u₁))

def ThetaMean.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ), Y.PosDef →
    (∫ u₁ in Set.Icc (0 : Fin g → ℝ) 1, ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1,
        thetaNorm X Y a b u₁ u₂ ^ 2) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ))

def ThetaFirstCoordSplit.Statement : Prop :=
  ∀ (g : ℕ) [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) (a u₁ : Fin g → ℝ), Y.PosDef → 0 < ρ →
    Y⁻¹ 0 0 = ρ ^ 2 →
    ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) ≤
      exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2) *
        ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + (a + u₁)))

def ThetaConstants.Statement : Prop :=
  ∀ C₃ : ℝ, 0 < C₃ → ∃ C : ℝ, 0 < C ∧
    ∀ (g : ℕ) (ρ d : ℝ), 1 ≤ g → 0 < ρ → 0 < d → ρ ^ 2 ≤ 2 * g → d⁻¹ ≤ ρ ^ 2 * (2 * g) ^ (g - 1) →
      (C₃ * g) ^ ((g : ℝ) / 2) * d ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g ≤
        ((2 : ℝ) ^ g * d) ^ (-(1 / 4 : ℝ)) * exp (g * log (1 + 1 / ρ) + C * g * log (2 * g))

end

end GroundTheory.Heights₂.Heights
end

