module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.Dec

def AutFinite : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g →
    ∀ (N : InfinitePlace I.F → ℕ → ℕ) (c : ∀ v m, Fin (N v m) → ℂ)
      (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (τ : Kinf I → (W →L[ℂ] W)),
      IsURep τ →
      FiniteDimensional ℂ (Submodule.span ℂ {f : I.GA → ℂ | IsSmoothMG I g f ∧
        (∀ v m x, (zOp I v m)^[N v m] f x = ∑ i, c v m i * (zOp I v m)^[i.val] f x) ∧
        ∃ L : W →ₗ[ℂ] (I.GA → ℂ), (∀ (k : Kinf I) w x, L (τ k w) x = L w (x * (fun v => (k v : UJ (I.ε v)), 1))) ∧
          f ∈ LinearMap.range L})

def CoefCusp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntIrr ε σ → ∀ u v : H, IsKFin ε σ u → IsKFin ε σ v →
    ∀ W, IsIsoC ε W → ∀ ν : Measure (UJ ε), IsHaarSub (NW ε W) ν → ∀ x y : UJ ε,
      Integrable (fun m => ⟪v, σ (umat (x * m * y)) u⟫_ℂ) ν ∧ ∫ m, ⟪v, σ (umat (x * m * y)) u⟫_ℂ ∂ν = 0

def ProjAbs : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g x, ‖σ g x‖ = ‖x‖) → (∀ x, Continuous fun g => σ g x) →
    ∀ d : ℝ, 0 < d →
    (∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) →
    ∀ w : H, ‖w‖ = 1 → Integrable (fun g => ⟪w, σ g w⟫_ℂ) μ →
      (∀ g : G, star (phG d σ w g⁻¹) = phG d σ w g) ∧
      (∀ x y : G, ∫ g, phG d σ w g * phG d σ w (x⁻¹ * g⁻¹ * y) ∂μ = ⟪w, σ x w⟫_ℂ * phG d σ w y) ∧
      ∀ (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]
        (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) →
        (∃ P : Hp →L[ℂ] Hp, IsOpIntG μ π (phG d σ w) P) ∧
        ∀ P : Hp →L[ℂ] Hp, IsOpIntG μ π (phG d σ w) P →
          IsStarProjection P ∧
          (∀ x : G, P ∘L π x ∘L P = ⟪w, σ x w⟫_ℂ • P) ∧
          (∀ v ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp), ‖v‖ = 1 →
            (∀ g : G, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) ∧
            ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u)) ∧
          ((LinearMap.range (P : Hp →ₗ[ℂ] Hp) : Submodule ℂ Hp) : Set Hp) =
            {v | ∃ io : H →L[ℂ] Hp, (∀ g : G, io ∘L σ g = π g ∘L io) ∧ v = io w}

def TensorRep : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d →
    IsURep B.σs ∧ IsIrr B.σs ∧ IsFdegG (muInf B.I) B.σs (∏ v, d v) ∧ ‖B.tens B.w‖ = 1 ∧
      ∀ g, ph B d g = ((∏ v, d v : ℝ) : ℂ) * star ⟪B.tens B.w, B.σs g (B.tens B.w)⟫_ℂ

def PhMaj : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → LocDec B h →
    Continuous (ph B d) ∧ (∀ g, ‖ph B d g‖ ≤ majPh B d h g) ∧
    ∀ s : ℝ, 0 ≤ s → (∀ v, rkR (B.I.ε v) = 0 ∨ 8 * Real.sqrt (rkR (B.I.ε v)) * (s + 4 * B.I.n * rkR (B.I.ε v)) < h) →
      Integrable (fun g => majPh B d h g * Real.exp (s * dSum B.I g)) (muInf B.I)

def GlobalProj : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → Integrable (ph B d) (muInf B.I) →
    IsOrthProjOnto B.Re (LinearMap.range (B.Re : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) ∧
    (∀ g : B.I.Ginf, B.Re.comp (B.R (g, 1)) = (B.R (g, 1)).comp B.Re) ∧
    (∃ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T) ∧
    ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T →
      IsOrthProjOnto T (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) ∧
      (∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, T (A (B.tens B.w)) = A (B.tens B.w)) ∧
      (∀ y, T y = y → ∃! A, A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re ∧ A (B.tens B.w) = y) ∧
      (FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → FiniteDimensional ℂ (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund))) ∧
      Module.finrank ℂ (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) = B.D

def CountRat : Prop :=
  ∀ (I : AutInst) (x y : I.GA) (r : InfinitePlace I.F → ℝ), 1 ≤ I.n → (∀ v, 0 ≤ r v) →
    {γ ∈ I.GFset | (x⁻¹ * γ * y).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * γ * y).1 v)) ≤ r v}.Finite ∧
    (({γ ∈ I.GFset | (x⁻¹ * γ * y).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * γ * y).1 v)) ≤ r v}.ncard : ℕ) : ℝ) ≤
      (3 * Real.sqrt I.n / (tau1 I x * tau1 I y)) ^ (2 * I.n ^ 2 * I.f) * Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v)

def TauLip : Prop :=
  ∀ I : AutInst, 1 ≤ I.n → (∀ x, 0 < tau1 I x) ∧ Continuous (tau1 I) ∧ (∀ γ ∈ I.GFset, ∀ x, tau1 I (γ * x) = tau1 I x) ∧
    ∀ x g : I.GA, g.2 ∈ I.Kset → |Real.log (tau1 I (x * g)) - Real.log (tau1 I x)| ≤ dSum I g.1 / I.f

def ConvolutionSmoothL2 : Prop :=
  ∀ (B : RowsAut) (g : ℕ), 1 ≤ B.I.n → 1 ≤ g → ∀ a : B.I.Ginf → ℂ, SmoothInf B.I a → HasCompactSupport a →
    ∃ C : ℝ, ∀ y : B.I.L2 B.μf B.fund, (∀ k ∈ B.I.Kg g, B.R (1, k) y = y) →
      ∀ T, IsOpOf (muInf B.I) (fun x => B.R (x, 1)) a T →
        ∃ f : B.I.GA → ℂ, IsSmoothMG B.I g f ∧ Continuous f ∧
          (∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * ‖y‖) ∧
          (T y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] f

def KernelA : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h →
    (∀ x y : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * y)‖) ∧
      ∑' γ : B.I.GFset, ‖phe B d (x⁻¹ * γ.1 * y)‖ ≤
        kerC B d * (tau1 B.I x * tau1 B.I y)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) ∧
    Continuous (fun p : B.I.GA × B.I.GA => kern B.I (phe B d) p.1 p.2) ∧
    (∀ γ ∈ B.I.GFset, ∀ x y, kern B.I (phe B d) (γ * x) y = kern B.I (phe B d) x y ∧
      kern B.I (phe B d) x (γ * y) = kern B.I (phe B d) x y) ∧
    ∀ x y, kern B.I (phe B d) y x = star (kern B.I (phe B d) x y)

def KernelB : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h →
    FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T →
    ∃ (y : Fin B.D → B.I.L2 B.μf B.fund) (Fc : Fin B.D → B.I.GA → ℂ), Orthonormal ℂ y ∧
      Submodule.span ℂ (Set.range y) = LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund) ∧
      (∀ i, Continuous (Fc i) ∧ (∀ γ ∈ B.I.GFset, ∀ x, Fc i (γ * x) = Fc i x) ∧
        (y i : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] Fc i) ∧
      (∀ x z, kern B.I (phe B d) x z = ∑ i, Fc i x * star (Fc i z)) ∧
      IntegrableOn (fun x => kern B.I (phe B d) x x) B.fund (B.I.muA B.μf) ∧
      ∫ x in B.fund, kern B.I (phe B d) x x ∂(B.I.muA B.μf) = (B.D : ℂ) ∧
      ∀ (c : Fin B.D → ℂ) (x : B.I.GA), ‖∑ i, c i * Fc i x‖ ^ 2 ≤
        (∑ i, ‖c i‖ ^ 2) * (kerC B d * (tau1 B.I x)⁻¹ ^ (4 * B.I.n ^ 2 * B.I.f))

def WeilVanish : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) (ν : Measure G),
    IsClosed (N : Set G) → IsHaarSub (N : Set G) ν →
    ∀ F φ : G → ℂ, Measurable F → Measurable φ → (∀ m ∈ N, ∀ y, F (m * y) = F y) →
      Integrable (fun y => F y * φ y) μ → (∀ y, ∫ m, φ (m * y) ∂ν = 0) →
      ∫ y, F y * φ y ∂μ = 0

def NearUnip : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (c : ℝ), 0 < c → c ≤ 1 / 10 ^ 5 → 1 ≤ B.I.n →
    4 * B.I.n < B.g₀ →
    (Ideal.span {(B.g₀ : 𝓞 B.I.E)}).IsRadical →
    ∀ ep δ : ℝ, ep = c / ((B.I.n : ℝ) ^ 8 * (B.I.f : ℝ) ^ 2) → δ = 3 * Real.sqrt (B.I.n * ep) →
      (∀ x γ : B.I.GA, IsNear B d ep x γ →
        (B.I.fmat γ.2 - 1) ^ B.I.n = 0 ∧ (∀ v, (uMat (γ.1 v) - 1) ^ B.I.n = 0) ∧ γ ∈ nearSet B.I x δ) ∧
      δ < 1 / 4 ∧ ∀ q : ℕ, q ^ 2 ≤ B.I.n → δ * q * B.I.n * B.I.f ≤ 1 / 100

end GlobalTheory.Dec
end
end

-- bundled from Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.DSId

def IsHCDS {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  IsSqIntIrr ε σ ∧ HasInfChar ε (fun a => (lam a : ℂ)) σ ∧ (∃! S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S) ∧
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
      ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b) ∧ μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b

def DSClass : Prop :=
  ∀ n : ℕ, ∃ (H : (Fin n → Bool) → (Fin n → ℝ) → Type) (_ : ∀ ε lam, NormedAddCommGroup (H ε lam))
    (_ : ∀ ε lam, InnerProductSpace ℂ (H ε lam)) (π : ∀ ε lam, Matrix (Fin n) (Fin n) ℂ → (H ε lam →L[ℂ] H ε lam)),
    (∀ ε lam, IsHCParam lam → IsHCDS ε lam (π ε lam)) ∧
    ∀ (ε : Fin n → Bool) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsSqIntIrr ε σ' →
      ∃ (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ), IsHCParam mu ∧ (∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) ∧
        UEquiv (ε ∘ s) (fun g => σ' (g.submatrix s.symm s.symm)) (π (ε ∘ s) mu)

def StrictLow : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) ∧
        ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → μ ≠ lowK ε lam →
          vNormSq ε (lowK ε lam) < vNormSq ε μ

def EigenfunctionFiniteCoefficients : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (χ : Fin n → ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), IsZEigen ε χ f → IsBiKFin ε f →
    MemLp (fun g : UJ ε => f (umat g)) 2 (muG ε) →
    ∃ (N : ℕ) (H : Fin N → Type) (_ : ∀ i, NormedAddCommGroup (H i)) (_ : ∀ i, InnerProductSpace ℂ (H i))
      (σ : ∀ i, Matrix (Fin n) (Fin n) ℂ → (H i →L[ℂ] H i)) (u v : ∀ i, H i),
      (∀ i, IsSqIntIrr ε (σ i)) ∧ ∀ g ∈ UJset ε, f g = ∑ i, ⟪v i, σ i g (u i)⟫_ℂ

def FormulaGap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
    ∀ h : ℝ, GapAtLeast ε lam h → 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h → ∀ w, IsHighestUnit ε lam σ w →
    ∀ X, inP ε X → ∀ u ∈ lowKSub ε lam σ, ∀ v ∈ lowKSub ε lam σ,
      ⟪v, σ (NormedSpace.exp X) u⟫_ℂ = (Module.finrank ℂ (lowKSub ε lam σ) : ℂ) *
        ∫ k' : KG ε, Phi lam ((toMK k')⁻¹ * NormedSpace.exp X * toMK k') *
          (⟪v, σ (toMK k') w⟫_ℂ * ⟪σ (toMK k') w, u⟫_ℂ) ∂(muK ε)

def DecGap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
    ∀ h : ℝ, GapAtLeast ε lam h → 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h → ∀ g ∈ UJset ε,
    ∀ u ∈ lowKSub ε lam σ, ∀ v ∈ lowKSub ε lam σ,
      ‖⟪v, σ g u⟫_ℂ‖ ≤ decHS h (rkR ε) (dHS g) * ‖u‖ * ‖v‖ ∧ ‖⟪v, σ g u⟫_ℂ‖ ≤ decE (rkR ε) h (dOp g) * ‖u‖ * ‖v‖

end GlobalTheory.DSId
end
end

-- bundled from Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas

open Formalism.MainNotions.S GlobalTheory.Count

def ResidueBound : Prop :=
  ∀ (k : Type) [Field k] [NumberField k], 2 ≤ Module.finrank ℚ k →
    dedekindZeta_residue k ≤ (Real.exp 1 * Real.log |(discr k : ℝ)| /
      (2 * ((Module.finrank ℚ k : ℝ) - 1))) ^ (Module.finrank ℚ k - 1)

def SameKindIsometric : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∀ (n : ℕ) (J J' : Matrix (Fin n) (Fin n) E), Jᴴ = J → J'ᴴ = J' → J.det ≠ 0 → J'.det ≠ 0 →
    (∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧
      ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) →
    (∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧
      ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J' *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) →
    (∀ φ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (J.map φ) p q ∧ Formalism.UG.HasSignature (J'.map φ) p q) →
    ∃ γ : GL (Fin n) E, (γ : Matrix (Fin n) (Fin n) E)ᴴ * J * (γ : Matrix (Fin n) (Fin n) E) = J'

def GenLinVolume : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j →
    glVol E j = ENNReal.ofReal (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j ^ 2) *
      ∏ l ∈ Finset.Icc 2 j, zetaE E l)

def VolumeStep : Prop :=
  ∀ (I : AutInst) (P Q : ℕ), HasSig I P Q → 3 ≤ I.n → ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∃ (I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E),
      (∀ y, e (star y) = star (e y)) ∧ I'.n + 1 = I.n ∧
      star x ⬝ᵥ (I.J *ᵥ x) = (if s then 1 else -1) ∧ star x ᵥ* (I.J * A) = 0 ∧ Aᴴ * I.J * A = I'.J.map e ∧
      HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) ∧
      ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
        (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure],
        IsGaugeAll I c → IsGaugeAll I' c' →
        gaugeVol I c μf / ENNReal.ofReal (volU I.n ^ I.f) =
          gaugeVol I' c' μf' / ENNReal.ofReal (volU I'.n ^ I.f) *
            ENNReal.ofReal (Formalism.HermitianLatticesTheory.massRatioRightSide I.E I.n)

def VolumeInvariant : Prop :=
  ∀ (I I' : AutInst) (p q : ℕ), SameField I I' → HasSig I p q → HasSig I' p q →
    ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
      (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure],
      IsGaugeAll I c → IsGaugeAll I' c' → gaugeVol I c μf = gaugeVol I' c' μf'

def VolumeRatio : Prop :=
  ∀ (I : AutInst) (p q p₀ q₀ : ℕ), HasSig I p q → p₀ ≤ p → q₀ ≤ q → 2 ≤ p₀ + q₀ →
    (∃ I₀ : AutInst, SameField I I₀ ∧ HasSig I₀ p₀ q₀) ∧
    ∀ I₀ : AutInst, SameField I I₀ → HasSig I₀ p₀ q₀ →
      ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
        (c₀ : InfinitePlace I₀.F → ℝ) (μ₀ : Measure I₀.Gf) [SigmaFinite μ₀] [μ₀.IsHaarMeasure],
        IsGaugeAll I c → IsGaugeAll I₀ c₀ →
        gaugeVol I c μf = gaugeVol I₀ c₀ μ₀ * ENNReal.ofReal (∏ M ∈ Finset.Ioc (p₀ + q₀) (p + q), rankFac I.E M)

def IwasawaFormula : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p →
    (univ.filter fun a => ε a = false).card = q →
    ∀ (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W →
    ∀ (c : ℝ) (μN μM μK : Measure (Formalism.REAL.UJ ε)), IsGauge ε c → IsGaugeSub (flagN ε W) (dimN n j) μN →
      IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM →
      μK (maxK ε)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ maxK ε, μK.map (fun g => k * g) = μK) →
      ∀ φ : Formalism.REAL.UJ ε → ENNReal, Measurable φ →
        ENNReal.ofReal c * ∫⁻ g, φ g ∂(Formalism.REAL.muG ε) =
          ENNReal.ofReal (cIw p q j) * ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) *
            ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN

def RadicalCovolume : Prop :=
  ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) →
    ∀ (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S →
    ∀ (ν : ∀ v, Measure (Formalism.REAL.UJ (I.ε v))) [∀ v, SigmaFinite (ν v)],
      (∀ v, IsGaugeSub (flagN (I.ε v) (flagAt I S v)) (dimN I.n j) (ν v)) →
      covol {g : I.Ginf | ∃ γ ∈ I.GFset, γ.1 = g ∧ xf⁻¹ * γ.2 * xf ∈ I.Kset ∧
          ∀ v, g v ∈ flagN (I.ε v) (flagAt I S v)} (Measure.pi ν)
          {g : I.Ginf | ∀ v, g v ∈ flagN (I.ε v) (flagAt I S v)} ≤
        ENNReal.ofReal ((2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ ((I.f : ℝ) * dimN I.n j / 2) *
          layerProd I.n I.f j
            (fun i => Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc)) id)

def UnfoldBound : Prop :=
  ∀ (I I₀ : AutInst) (p q : ℕ) (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∑ i, j i ≤ p →
    SameField I I₀ → HasSig I p q → HasSig I₀ (p - ∑ i, j i) (q - ∑ i, j i) →
    ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
      (c₀ : InfinitePlace I₀.F → ℝ) (μ₀ : Measure I₀.Gf) [SigmaFinite μ₀] [μ₀.IsHaarMeasure],
      IsGaugeAll I c → IsGaugeAll I₀ c₀ → ∀ B : Set (Fin a → ℝ), MeasurableSet B → B ⊆ simplexH a →
      ENNReal.ofReal (∏ v, c v) * covol I.GFset (I.muA μf) (typeSet I j B) / μf I.Kset ≤
        ENNReal.ofReal (cIw p q j ^ I.f * (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ ((I.f : ℝ) * dimN I.n j / 2)) *
          (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * glVol I.E (j i)) * gaugeVol I₀ c₀ μ₀ *
          ∫⁻ τ in B, ENNReal.ofReal (dens I.n I.f j τ)

def FlagMeasureBound : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund → ∀ (p q : ℕ), HasSig I p q → 2 * q + 2 ≤ I.n →
    ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q →
    ∀ B : Set (Fin a → ℝ), MeasurableSet B → B ⊆ simplexH a →
      MeasurableSet (typeSet I j B) ∧ 0 < I.muA μf fund ∧ I.muA μf fund < ⊤ ∧
      I.muA μf (typeSet I j B ∩ fund) / I.muA μf fund ≤
        ENNReal.ofReal (kapBd I.E p q j) * ∫⁻ τ in B, ENNReal.ofReal (dens I.n I.f j τ)

def ConstantBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∀ (p q a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → 15 ≤ Real.log (p + q : ℕ) → q ^ 2 ≤ p + q →
      Real.log (2 * Formalism.HermitianLatticesTheory.vInv E) ≤ Real.exp (p + q : ℕ) →
      Real.log (Formalism.HermitianLatticesTheory.fDeg E) ≤ Real.sqrt (p + q : ℕ) →
      kapBd E p q j ≤
        Real.exp (-(1 / 2 * (∑ i, j i : ℕ) * (p + q : ℕ) * Formalism.HermitianLatticesTheory.fDeg E * Real.log (p + q : ℕ)))

def NonzeroFlagBound : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund → ∀ (p q : ℕ), HasSig I p q → 15 ≤ Real.log I.n → q ^ 2 ≤ I.n →
      Real.log I.rd ≤ Real.exp I.n → Real.log I.f ≤ Real.sqrt I.n →
      I.muA μf ({x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund) / I.muA μf fund ≤
        ENNReal.ofReal (Real.exp (-(1 / 3 * I.n * I.f * Real.log I.n)))

def RankTwoClasses : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E →
    ((defClassNum E 2 : ENat) : ENNReal) ≤ ENNReal.ofReal
      (4 ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E) *
        (1 + Formalism.HermitianLatticesTheory.fDeg E * Real.log (2 * Formalism.HermitianLatticesTheory.vInv E)) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E))

def AbsoluteVolume : Prop :=
  ∀ (I : AutInst) (p q : ℕ), HasSig I p q → q ^ 2 ≤ I.n → 8 ≤ I.n →
    ∀ X : ℝ, 2 ≤ X → I.rd ≤ X → 2 * I.f * I.rd ≤ X ^ 2 →
    ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure],
      IsGaugeAll I c → gaugeVol I c μf ≤ ENNReal.ofReal (X ^ (I.n ^ 2 * I.f))

end GlobalTheory.FlagMeas
end
end

