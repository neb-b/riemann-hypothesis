module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Formalism.PairingDivisors.StatementN

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def archFactor (n : I → ℤ) (s : ℂ) : ℂ :=
  ∏ i, (2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2))

def IsCompletedL (χ : HChar E) (n : I → ℤ) (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ ∀ s : ℂ, 1 < s.re → ∃ L : ℂ, HasProd (eulerFactor χ s) L ∧ Λ s = archFactor n s * L

def BoundedInStrips (Λ : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a < b → ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Λ s‖ ≤ C

def CompletedLBoundedInStrips : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (χ : HChar E) (n : I → ℤ), IsUnitary χ → Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) →
      ∃ Λ : ℂ → ℂ, IsCompletedL χ n Λ ∧ BoundedInStrips Λ

theorem IsCompletedL.unique {χ : HChar E} {n : I → ℤ} {f g : ℂ → ℂ} (hf : IsCompletedL χ n f) (hg : IsCompletedL χ n g) :
    f = g :=
  entire_eq_of_halfPlane hf.1 hg.1 1 fun s hs => by
    obtain ⟨L, h1, h2⟩ := hf.2 s hs
    obtain ⟨L', h1', h2'⟩ := hg.2 s hs
    rw [h2, h2', h1.unique h1']

theorem IsCompletedL.eq_mul {χ : HChar E} {n : I → ℤ} {Λ L : ℂ → ℂ} (h : IsCompletedL χ n Λ) (hL : IsHeckeL χ L)
    {s : ℂ} (hs : 1 < s.re) : Λ s = archFactor n s * L s := by
  obtain ⟨L', h1, h2⟩ := h.2 s hs
  rw [h2, h1.unique (hL.2 s hs)]

theorem archFactor_two_mul (m : I → ℤ) (s : ℂ) : archFactor (fun i => 2 * m i) s = LInf m s := by
  unfold archFactor LInf
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (((|2 * m i| : ℤ) : ℂ)) / 2 = ((|m i| : ℤ) : ℂ) := by
    rw [abs_mul, abs_two]; push_cast; ring
  rw [this]

end GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] [DecidableEq I]

def cWt (E : Type) [Field E] [NumberField E] (k : ℕ) : ℝ :=
  ((k - 1).factorial : ℝ) ^ Module.finrank ℚ (maximalRealSubfield E) *
    |(discr (maximalRealSubfield E) : ℝ)| ^ (((k : ℝ) - 1) / 2)

def polydisc (I : Type) : Set (I → ℂ) := {z | ∀ i, ‖z i‖ < 1}

def defCoord (φ : I → E →+* ℂ) (z : I → ℂ) (x : E) (i : I) : ℂ := φ i x + z i * starRingEnd ℂ (φ i x)

def defTerm (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (σ : ℂ) (x : E) : ℂ :=
  ∏ i, ((defCoord φ z x i)⁻¹ ^ k * ((‖defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ))

def IsEisValue (φ : I → E →+* ℂ) (k : ℕ) (L : Set E) (z : I → ℂ) (G : ℂ) : Prop :=
  (k ≠ 2 → HasSum (fun q : modUnits L => ∏ i, (defCoord φ z q.1.out i)⁻¹ ^ k) G) ∧
  (k = 2 → ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {σ : ℂ | -1 / 2 < σ.re} ∧
    (∀ σ : ℂ, 0 < σ.re → HasSum (fun q : modUnits L => defTerm φ 2 z σ q.1.out) (H σ)) ∧ G = H 0)

def IsDefSum (φ : I → E →+* ℂ) (k : ℕ) (L : Set E) (g : (I → ℂ) → ℂ) : Prop :=
  ∀ z ∈ polydisc I, ∃ G : ℂ, IsEisValue φ k L z G ∧ g z = (cWt E k : ℂ) * G

def partialD (i : I) (g : (I → ℂ) → ℂ) : (I → ℂ) → ℂ := fun z => lineDeriv ℂ g z (Pi.single i 1)

def iterD (l : List I) (g : (I → ℂ) → ℂ) : (I → ℂ) → ℂ := l.foldr partialD g

def risingFactor (k : ℕ) (κ : I → ℕ) : ℂ := ∏ i, ((-1 : ℂ) ^ κ i * ∏ j ∈ Finset.range (κ i), ((k : ℂ) + j))

def DerivFormula (φ : I → E →+* ℂ) (k : ℕ) (L : Set E) : Prop :=
  (∃ g, IsDefSum φ k L g) ∧ ∀ g, IsDefSum φ k L g →
    DifferentiableOn ℂ g (polydisc I) ∧
    ∀ (κ : I → ℕ) (l : List I), (∀ i, l.count i = κ i) →
      (∀ S : ℂ → ℂ, IsLatSum φ k κ L S → iterD l g 0 = (cWt E k : ℂ) * risingFactor k κ * S 0) ∧
      (4 ≤ k → ∃ S₀ : ℂ,
        HasSum (fun q : modUnits L => ∏ i, ((φ i q.1.out)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i q.1.out)) ^ κ i)) S₀ ∧
        iterD l g 0 = (cWt E k : ℂ) * risingFactor k κ * S₀)

def lamInf (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (α : Eˣ) : ℂ :=
  ∏ i, ((φ i α) ^ (k + κ i) * (starRingEnd ℂ (φ i α))⁻¹ ^ κ i)

def Homothety (φ : I → E →+* ℂ) (k : ℕ) (L : Set E) : Prop :=
  ∀ (κ : I → ℕ) (α : Eˣ) (S : ℂ → ℂ), IsLatSum φ k κ L S →
    IsLatSum φ k κ ((fun x => (α : E) * x) '' L)
      (fun σ => (lamInf φ k κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) * S σ) ∧
    ∀ S' : ℂ → ℂ, IsLatSum φ k κ ((fun x => (α : E) * x) '' L) S' → S' 0 = (lamInf φ k κ α)⁻¹ * S 0

def lamFin (χ : HChar E) (s : ℕ) (y : (Af E)ˣ) : ℂ := (finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)

def ClassInvariance (φ : I → E →+* ℂ) (s : ℕ) : Prop :=
  ∀ (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (κ : I → ℕ) (χ : HChar E),
    IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ →
    ∀ (y y' : (Af E)ˣ) (S S' : ℂ → ℂ),
      (QuotientGroup.mk y : PicO (condQ 𝔣 Q)) = QuotientGroup.mk y' →
      IsLatSum φ (2 * s) κ (lattice (condQ 𝔣 Q) y) S → IsLatSum φ (2 * s) κ (lattice (condQ 𝔣 Q) y') S' →
      (lamFin χ s y)⁻¹ * S 0 = (lamFin χ s y')⁻¹ * S' 0

abbrev Coh (E : Type) [Field E] [NumberField E] : Type := E →ₗ[ℚ] ℂ

def eCl (φ : I → E →+* ℂ) (i : I) : Coh E := (φ i).toRatAlgHom.toLinearMap

def fCl (φ : I → E →+* ℂ) (i : I) : Coh E := (ComplexEmbedding.conjugate (φ i)).toRatAlgHom.toLinearMap

def plane (φ : I → E →+* ℂ) (i : I) : Submodule ℂ (Coh E) := Submodule.span ℂ {eCl φ i, fCl φ i}

variable [IsCMField E]

def riemann (ξ x y : E) : ℚ := Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E y)

def riemannCl (ξ x : E) : Coh E where
  toFun y := (riemann ξ x y : ℂ)
  map_add' y y' := by simp [riemann, mul_add]
  map_smul' a y := by
    have h : IsCMField.complexConj E (a • y) = a • IsCMField.complexConj E y := map_rat_smul _ a y
    simp only [riemann, h, mul_smul_comm, map_smul, RingHom.id_apply]
    simp [Rat.smul_def]

def IsDualForm (ξ : E) (B : LinearMap.BilinForm ℂ (Coh E)) : Prop :=
  ∀ x y : E, B (riemannCl ξ x) (riemannCl ξ y) = (riemann ξ x y : ℂ)

def pairing (ε : ℤˣ) (B : LinearMap.BilinForm ℂ (Coh E)) (a b : Coh E) : ℂ :=
  ((ε : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * B a b

def DualFormValue (φ : I → E →+* ℂ) : Prop :=
  ∀ ξ : E, ξ ≠ 0 → IsCMField.complexConj E ξ = -ξ →
    (∃! B, IsDualForm ξ B) ∧ ∀ B, IsDualForm ξ B → ∀ ε : ℤˣ,
      (∀ i j, i ≠ j → ∀ a ∈ plane φ i, ∀ b ∈ plane φ j, pairing ε B a b = 0) ∧
      ∀ i, pairing ε B (eCl φ i) (fCl φ i) = ((ε : ℤ) : ℂ) * (φ i ξ)⁻¹ / (2 * (Real.pi : ℂ) * Complex.I)

def DualFormBase (φ : I → E →+* ℂ) : Prop :=
  ∀ (d : ℕ) (δ : E), 0 < d → δ ^ 2 = -(d : E) → (∀ i, φ i δ = Complex.I * (Real.sqrt d : ℂ)) → ∀ η : ℤˣ,
    (∃! B, IsDualForm (((η : ℤ) : E) * δ⁻¹) B) ∧ ∀ B, IsDualForm (((η : ℤ) : E) * δ⁻¹) B → ∀ ε : ℤˣ,
      (∀ i j, i ≠ j → ∀ a ∈ plane φ i, ∀ b ∈ plane φ j, pairing ε B a b = 0) ∧
      ∀ i, pairing ε B (eCl φ i) (fCl φ i) = ((ε * η : ℤˣ) : ℤ) * ((Real.sqrt d / (2 * Real.pi) : ℝ) : ℂ)

def Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ),
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) → IsCMType φ →
    (∀ s : ℕ, 1 ≤ s →
      (∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
        DerivFormula φ (2 * s) (lattice c y) ∧ Homothety φ (2 * s) (lattice c y)) ∧
      ClassInvariance φ s) ∧
    DualFormValue φ ∧ DualFormBase φ

end GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open scoped nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport

section Quadratic

variable {K : Type} [Field K] [NumberField K]

def Fixes (φK : K →+* ℂ) (σ : ℂ ≃+* ℂ) : Prop := ∀ x : K, σ (φK x) = φK x

def IsInvIdealOf (t : (Af K)ˣ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Prop :=
  ∀ x : K, x ∈ 𝔞 ↔ ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) x) v) ≤ 1

def IsLatOf (φK : K →+* ℂ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (Λ : PeriodPair) : Prop :=
  (Λ.lattice : Set ℂ) = φK '' (𝔞 : Set K)

def jLat (Λ : PeriodPair) : ℂ := 1728 * Λ.g₂ ^ 3 / latDisc Λ

def nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ := ((FractionalIdeal.absNorm 𝔞 : ℚ) : ℝ)

def Equidistributed (φK : K →+* ℂ) (j₀ : ℂ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Prop :=
  IsAlgebraic ℚ j₀ ∧
  (∀ σ σ' : ℂ ≃+* ℂ, Fixes φK σ → Fixes φK σ' →
    (ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') ↔ σ j₀ = σ' j₀)) ∧
  ∀ L : IntermediateField ℚ ℂ, FiniteDimensional ℚ L → IsGalois ℚ L → (∀ x : K, φK x ∈ L) → j₀ ∈ L →
    ∀ C : ClassGroup (𝓞 K),
      Nat.card {τ : L →+* ℂ // ∃ σ : ℂ ≃+* ℂ, Fixes φK σ ∧ (∀ x : L, σ (x : ℂ) = τ x) ∧ ClassGroup.mk K (𝔞 σ) = C}
        * (2 * classNumber K) = Module.finrank ℚ L

end Quadratic

section CM

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def lamF (s : ℕ) (χ : HChar E) (y : (Af E)ˣ) : ℂ := (finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)

def IsConjWt (φ : I → E →+* ℂ) (σ : ℂ ≃+* ℂ) (κ κ' : I → ℕ) : Prop :=
  ∀ i j : I, (∀ x : E, σ (φ i x) = φ j x) → κ' j = κ i

def IsConjChar (φ : I → E →+* ℂ) (s : ℕ) (κ' : I → ℕ) (σ : ℂ ≃+* ℂ) (χ χ' : HChar E) : Prop :=
  (∀ y : (Af E)ˣ, lamF s χ' y = σ (lamF s χ y)) ∧ HasInf χ' φ (fun i => (κ' i : ℤ) + s)

def IsValSum (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E)))
    (χ : HChar E) (T : ℂ) : Prop :=
  IsFinSetSplitPlacesCoprimeConductor 𝔣 Q ∧ IsValChar φ s κ 𝔣 Q χ ∧ IsToricSum φ s κ (condQ 𝔣 Q) χ T

def IsConjSum (φ : I → E →+* ℂ) (s : ℕ) (κ' : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E)))
    (σ : ℂ ≃+* ℂ) (χ χ' : HChar E) (T' : ℂ) : Prop :=
  IsConjChar φ s κ' σ χ χ' ∧ IsToricSum φ s κ' (condQ 𝔣 Q) χ' T'

end CM

def upIdele (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] : (Af K)ˣ →* (Af E)ˣ :=
  Units.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K E).toMonoidHom

def TransportFor {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I]
    (d : ℕ) (φK : K →+* ℂ) (ΛK : PeriodPair) (t : (ℂ ≃+* ℂ) → (Af K)ˣ)
    (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : (ℂ ≃+* ℂ) → PeriodPair)
    (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) : Prop :=
  (∀ (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ), IsValSum φ s κ 𝔣 Q χ T →
    IsAlgebraic ℚ (beta E d s κ ΛK T) ∧
    ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∀ κ' : I → ℕ, IsConjWt φ σ κ κ' →
      ∀ (χ' : HChar E) (T' : ℂ), IsConjSum φ s κ' 𝔣 Q σ χ χ' T' →
        σ (beta E d s κ ΛK T) =
          ((C0 E d (2 * s) κ : ℂ) * ((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) : ℂ) ^ (∑ i, κ i))⁻¹ *
              (lamF s χ' (upIdele K E (t σ)))⁻¹ * T') ^ 12 / latDisc (Λ σ) ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i) ∧
        ‖σ (beta E d s κ ΛK T)‖ =
          (C0 E d (2 * s) κ * ‖T'‖) ^ 12 *
            ((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc (Λ σ)‖) ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i))⁻¹) ∧
  (∀ (Q₁ Q₂ : Finset (HeightOneSpectrum (OF E))) (χ₁ χ₂ : HChar E) (T₁ T₂ : ℂ),
    IsValSum φ s κ 𝔣 Q₁ χ₁ T₁ → IsValSum φ s κ 𝔣 Q₂ χ₂ T₂ → T₂ ≠ 0 →
    IsAlgebraic ℚ (T₁ / T₂) ∧
    ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∀ κ' : I → ℕ, IsConjWt φ σ κ κ' →
      ∀ (χ₁' χ₂' : HChar E) (T₁' T₂' : ℂ), IsConjSum φ s κ' 𝔣 Q₁ σ χ₁ χ₁' T₁' → IsConjSum φ s κ' 𝔣 Q₂ σ χ₂ χ₂' T₂' →
        T₂' ≠ 0 ∧
        σ (T₁ / T₂) = ((lamF s χ₁' (upIdele K E (t σ)))⁻¹ * T₁') / ((lamF s χ₂' (upIdele K E (t σ)))⁻¹ * T₂'))

def Transport : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ), 4 < d → Module.finrank ℚ K = 2 → discr K = -(d : ℤ) →
  ∀ (φK : K →+* ℂ) (ΛK : PeriodPair), IsLatOf φK 1 ΛK →
  ∃ (t : (ℂ ≃+* ℂ) → (Af K)ˣ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : (ℂ ≃+* ℂ) → PeriodPair),
    (∀ σ : ℂ ≃+* ℂ, Fixes φK σ →
      IsInvIdealOf (t σ) (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) ∧ IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) (Λ σ) ∧
        jLat (Λ σ) = σ (jLat ΛK)) ∧
    Equidistributed φK (jLat ΛK) 𝔞 ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] [Algebra K E], UnramFin E →
    ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ), 2 ≤ Fintype.card I → IsCMType φ →
      (∀ i, (φ i).comp (algebraMap K E) = φK) →
    ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)), 1 ≤ s → (∀ i, 1 ≤ κ i) → IsBaseCond 𝔣 →
      TransportFor d φK ΛK t 𝔞 Λ φ s κ 𝔣

theorem nrm_ne_zero {K : Type} [Field K] [NumberField K] (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  unfold nrm
  have : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := fun h =>
    𝔞.ne_zero (FractionalIdeal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast this

theorem lamF_ne_zero {E : Type} [Field E] [NumberField E] (s : ℕ) (χ : HChar E) (y : (Af E)ˣ) : lamF s χ y ≠ 0 := by
  have h : 0 < modF y := by
    unfold modF
    refine finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos ?_ _
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.pos_of_ne_zero this
  exact mul_ne_zero (Units.ne_zero _) (by exact_mod_cast (pow_pos h s).ne')

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
section
noncomputable section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory.CMVal

namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds

variable {E : Type} [Field E] [NumberField E]

def ValGe_vp (l : ℕ) (r : ℝ) (a : ℂ) : Prop :=
  ∀ (m : ℤ) (n : ℕ), 0 < n → r ≤ (m : ℝ) / n → IntAt l ((l : ℂ) ^ m * a ^ n)

def IsClassZeta (C : ClassGroup (OF E)) (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re →
    HasSum (fun 𝔞 : {𝔞 : (Ideal (OF E))⁰ // ClassGroup.mk0 𝔞 = C} =>
      ((Ideal.absNorm (𝔞.1 : Ideal (OF E)) : ℕ) : ℂ) ^ (-s)) (Z s)

def IsClassZetaVals (k : ℕ) (z : ClassGroup (OF E) → ℚ) : Prop :=
  ∀ C, ∃ Z : ℂ → ℂ, IsClassZeta C Z ∧ Z (1 - (k : ℂ)) = (z C : ℂ)

def cE_vp (l : ℕ) (z : ClassGroup (OF E) → ℚ) : ℕ :=
  Finset.univ.sup fun C => (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat

def delta_vp (E : Type) [Field E] [NumberField E] (l : ℕ) : ℝ :=
  (padicValInt l (discr E) : ℝ) / (Module.finrank ℚ E : ℝ)

def a0 (𝔣 : Ideal (OF E)) (l : ℕ) : ℕ :=
  sSup {n | ∃ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal ∧ expIn 𝔣 v = n}


open Classical in
def c_vp (𝔣 : Ideal (OF E)) (l : ℕ) : ℝ :=
  if ∃ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal ∧ v.asIdeal ∣ 𝔣 then (a0 𝔣 l : ℝ) else delta_vp E l

variable {I : Type} [Fintype I]


open Classical in
def n_vp (d s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (l : ℕ) : ℝ :=
  if c_vp 𝔣 l = 0 then 0
  else Formalism.PairingDivisionLocalBalance.nl ((2 * s * Fintype.card I : ℕ) : ℝ) (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) (c_vp 𝔣 l)
    ((if l = 2 then 1 else 0) + (if l = d then 1 / 2 else 0))

def IsFieldData (d : ℕ) (φ : I → E →+* ℂ) : Prop :=
  d.Prime ∧ 4 < d ∧ UnramFin E ∧ (∀ x : E, IsOfFinOrder x → ∏ i, φ i x = 1) ∧ (2 : ℤ) ∣ discr E ∧
    2 ≤ Fintype.card I ∧ IsCMType φ ∧ ∃ w : E, w ^ 2 = -(d : E) ∧ ∀ i, φ i w = Complex.I * (Real.sqrt d : ℝ)

def IsIntLattice (d : ℕ) (Λ : PeriodPair) : Prop :=
  ∀ x : ℂ, x ∈ Λ.lattice ↔ IsIntegral ℤ x ∧ ∃ a b : ℚ, x = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ))

def IsClassTerm (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E) (y : (Af E)ˣ) (T : ℂ) : Prop :=
  ∃ S : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y) S ∧ T = ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0

def IsPicChar (c : Ideal (OF E)) (ψ : HChar E) : Prop :=
  (∀ x : Eˣ, infPart ψ x = 1) ∧ ∀ u ∈ hatOUnits c, finPart ψ u = 1

def betaBound_vp (d s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (z : ClassGroup (OF E) → ℚ) (l : ℕ) : ℝ :=
  12 * ((cE_vp l z : ℝ) + n_vp d s κ 𝔣 l + (Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ : ℝ) * (a0 𝔣 l : ℝ))

def DenomBound (d s : ℕ) (φ : I → E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Λ : PeriodPair)
    (z : ClassGroup (OF E) → ℚ) (χ : HChar E) : Prop :=
  ∀ l : ℕ, l.Prime → ∀ Q : Finset (HeightOneSpectrum (OF E)), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    (∀ (y : (Af E)ˣ) (T : ℂ), IsClassTerm φ s κ (condQ 𝔣 Q) χ y T →
      ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (beta E d s κ Λ T)) ∧
    (∀ (ψ : HChar E) (T : ℂ), IsPicChar (condQ 𝔣 Q) ψ → IsToricSum φ s κ (condQ 𝔣 Q) (χ * ψ) T →
      ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (beta E d s κ Λ T))

def ToricDenominator : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I]
    (d : ℕ) (φ : I → E →+* ℂ) (s : ℕ), IsFieldData d φ → 1 ≤ s →
    ∃ z : ClassGroup (OF E) → ℚ, IsClassZetaVals (2 * s) z ∧
      ∀ (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Λ : PeriodPair) (χ : HChar E),
        IsBaseCond 𝔣 → IsIntLattice d Λ → IsValChar φ s κ 𝔣 ∅ χ → DenomBound d s φ κ 𝔣 Λ z χ

theorem expIn_le_two {𝔣 : Ideal (OF E)} (h : IsBaseCond 𝔣) (v : HeightOneSpectrum (OF E)) : expIn 𝔣 v ≤ 2 := by
  by_cases hv : v.asIdeal ∣ 𝔣
  · exact (h.2.2 v hv).2.1
  · rw [expIn, multiplicity_eq_zero_of_not_dvd hv]; omega

theorem expIn_le_maxConductorExponentOverPrime {𝔣 : Ideal (OF E)} (h : IsBaseCond 𝔣) {l : ℕ} {v : HeightOneSpectrum (OF E)}
    (hv : (l : OF E) ∈ v.asIdeal) : expIn 𝔣 v ≤ a0 𝔣 l :=
  le_csSup ⟨2, by rintro _ ⟨w, -, rfl⟩; exact expIn_le_two h w⟩ ⟨v, hv, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds
end
end

