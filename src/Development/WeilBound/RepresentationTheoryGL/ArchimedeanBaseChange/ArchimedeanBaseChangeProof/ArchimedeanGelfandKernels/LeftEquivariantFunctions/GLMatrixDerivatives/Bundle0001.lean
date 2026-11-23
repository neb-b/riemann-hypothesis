module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfSt
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.LfSt.ChainPf

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def DC {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) (Fr : Mat n → (V →L[ℂ] V))
    (f : Mat n → V) : Mat n → V :=
  fun x => ∑ p, ε (hb p) (Rd (hb p) f x + fderiv ℝ Fr 1 (hb p) (f x))

def kapL {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) (Fr k : Mat n → (V →L[ℂ] V))
    (y : Mat n) : V →L[ℂ] V :=
  ∑ p, ε (hb p) * (Ld (hb p) k y + fderiv ℝ Fr 1 (hb p) * k y)

def kapR {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) (Fr k : Mat n → (V →L[ℂ] V))
    (y : Mat n) : V →L[ℂ] V :=
  ∑ p, (-(Rd (hb p) k y) * ε (hb p) + k y * ε (hb p) * fderiv ℝ Fr 1 (hb p))

def DCinCE : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T → ∀ f ∈ CE E, DC ε Fr f ∈ CE E

def DCwave : Prop :=
  GelComm → ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T → ∀ u, IsWave E u →
    IsWave E fun t => DC ε Fr (u t)

def ParamInt : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ (g : ℝ → ℝ) (T : ℝ), IsBump g T →
    ContDiffOn ℝ ∞ (fun x => ∫ t, (g t : ℂ) • u t x) (GLs n) ∧
    ∀ X, ∀ x ∈ GLs n, Rd X (fun x' => ∫ t, (g t : ℂ) • u t x') x = ∫ t, (g t : ℂ) • Rd X (u t) x

def ZopDC : Prop :=
  GelComm → ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (h : Mat n → E.V), ContDiffOn ℝ ∞ h (GLs n) → ∀ w : List (Bool × ℕ),
      ContDiffOn ℝ ∞ (zOp w h) (GLs n) ∧ ∀ x ∈ GLs n, zOp w (DC ε Fr h) x = DC ε Fr (zOp w h) x

def ActDer : Prop :=
  Unimod → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), ContDiffOn ℝ ∞ k (GLs n) → PositivityTheory.RgBcC.Cpt k → ContDiffOn ℝ ∞ f (GLs n) →
    ContDiffOn ℝ ∞ (act μ E k f) (GLs n) ∧
    ∀ X, ∀ x ∈ GLs n, Rd X (act μ E k f) x = ∫ y : G n, Ld X k y.val (f (x * y.val)) ∂μ

def IBPAct : Prop :=
  Unimod → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), ContDiffOn ℝ ∞ k (GLs n) → PositivityTheory.RgBcC.Cpt k → ContDiffOn ℝ ∞ f (GLs n) →
    ∀ X, ∀ x ∈ GLs n, ∫ y : G n, k y.val (Rd X f (x * y.val)) ∂μ = -∫ y : G n, Rd X k y.val (f (x * y.val)) ∂μ

def KapEquiv : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T → ∀ (k : Mat n → (E.V →L[ℂ] E.V)),
    ContDiffOn ℝ ∞ k (GLs n) → (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂) →
    ContinuousOn (kapL ε Fr k) (GLs n) ∧ ContinuousOn (kapR ε Fr k) (GLs n) ∧
    ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ,
      kapL ε Fr k (y * k₂.1) = kapL ε Fr k y * E.ρ k₂ ∧ kapR ε Fr k (y * k₂.1) = kapR ε Fr k y * E.ρ k₂

end PositivityTheory.RgBcC.LfSt.ChainPf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate ComplexOrder

namespace PositivityTheory.RgBcC.LfSt

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def coords (H : Mat n) : Fin n × Fin n → ℝ := fun p => ((H * hb p).trace).re

def oPt (n : ℕ) : Fin n × Fin n → ℝ := coords 1

def Kf {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Fr k : Mat n → (V →L[ℂ] V)) (Γ T : V →L[ℂ] V) (d x y : Mat n) :
    V →L[ℂ] V :=
  Fr x * k (x⁻¹ * d * yᴴ⁻¹) * Γ * T * Fr y⁻¹

def Kc {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (σ : (Fin n × Fin n → ℝ) → Mat n) (c : ℝ)
    (Fr k : Mat n → (V →L[ℂ] V)) (Γ T : V →L[ℂ] V) (d : Mat n) (y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ)) : V →L[ℂ] V :=
  ((c : ℂ) * ((hOf y.2).det ^ n)⁻¹) • Kf Fr k Γ T d (σ y.1) (σ y.2)

def HbFacts : Prop :=
  ∀ n : ℕ, (∀ p, (hb p : Mat n).IsHermitian) ∧ (∀ p q : Fin n × Fin n, ((hb p : Mat n) * hb q).trace = if p = q then 1 else 0) ∧
    (∀ H : Mat n, H.IsHermitian → hOf (coords H) = H) ∧ (∀ v : Fin n × Fin n → ℝ, coords (hOf v) = v) ∧
    (∀ v : Fin n × Fin n → ℝ, (hOf v).IsHermitian) ∧ ∑ p, (hb p : Mat n) * hb p = (n : ℂ) • 1 ∧ ∑ p, (hb p : Mat n).trace • hb p = 1 ∧
    oPt n ∈ cone n

def FrameDer : Prop :=
  ∀ (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (σ : (Fin n × Fin n → ℝ) → Mat n) (F : Mat n → Z),
    ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) → ContDiffOn ℝ ∞ F (GLs n) →
    (∀ x ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, F (x * k.1) = F x) →
    ∀ v ∈ cone n, ∀ x ∈ GLs n, x * xᴴ = hOf v → ∀ X : Mat n, X.IsHermitian →
      fderiv ℝ (fun w => F (σ w)) v (coords ((2 : ℂ) • (x * X * xᴴ))) = fderiv ℝ F x (x * X)

def KChain : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (σ : (Fin n × Fin n → ℝ) → Mat n), ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContDiffOn ℝ ∞ k (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    (∀ y ∈ GLs n, Γ * k y = k y * Γ ∧
        ∑ p, ε (hb p) * (Ld (hb p) k y + fderiv ℝ Fr 1 (hb p) * k y) =
          ∑ p, (-(Rd (hb p) k y) * ε (hb p) + k y * ε (hb p) * fderiv ℝ Fr 1 (hb p))) →
    ∀ (d : Mat n), d ∈ GLs n → ∀ c : ℝ,
      ContDiffOn ℝ ∞ (Kc σ c Fr k Γ T d) (cone n ×ˢ cone n) ∧
      (∀ y ∈ cone n ×ˢ cone n, Γ * Kc σ c Fr k Γ T d y = Kc σ c Fr k Γ T d y * Γ) ∧
      ∀ y ∈ cone n ×ˢ cone n, ∑ i, ε (hb i) * fderiv ℝ (Kc σ c Fr k Γ T d) y (Pi.single i 1, 0) +
        ∑ i, fderiv ℝ (Kc σ c Fr k Γ T d) y (0, Pi.single i 1) * ε (hb i) = 0

def KSupp : Prop :=
  SuppSt → ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (σ : (Fin n × Fin n → ℝ) → Mat n),
    ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    ∀ (Fr k : Mat n → (V →L[ℂ] V)) (Γ T : V →L[ℂ] V) (R : ℝ), (∀ y ∈ GLs n, R < lg y → k y = 0) →
    ∀ (z : Fin n → ℂ), (∀ a, ‖z a‖ = 1) → (Function.Injective fun a => z a ^ 2) → ∀ c : ℝ,
      ∃ C ⊆ cone n, IsCompact C ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ cone n, v ∉ C →
        ∀ᶠ y in nhds (s • v + (1 - s) • oPt n, v), Kc σ c Fr k Γ T (diagonal z) y = 0

def End1 : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
      (σ : (Fin n × Fin n → ℝ) → Mat n) (c : ℝ), ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    (∀ F : Mat n → ℂ, ContinuousOn F (GLs n) → (∃ R, ∀ y ∈ GLs n, R < lg y → F y = 0) →
        (∀ y ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, F (y * k.1) = F y) →
        ∫ y : G n, F y.val ∂μ = c * ∫ v in cone n, F (σ v) * ((hOf v).det ^ n)⁻¹) →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContinuousOn k (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    (∀ y ∈ GLs n, Γ * k y = k y * Γ) → ∀ (d : G n) (R : ℝ),
    (∀ x ∈ GLs n, R < lg x → k (x⁻¹ * d.val * xᴴ⁻¹) = 0) →
      Integrable (fun x => phiOf E T k (tw x d)) μ ∧
      ∫ v in cone n, LinearMap.trace ℂ E.V ((Γ * S 1 * Kc σ c Fr k Γ T d.val (v, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
        ∫ x, phiOf E T k (tw x d) ∂μ

def End0 : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
      (σ : (Fin n × Fin n → ℝ) → Mat n) (c : ℝ), ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    (∀ F : Mat n → ℂ, ContinuousOn F (GLs n) → (∃ R, ∀ y ∈ GLs n, R < lg y → F y = 0) →
        (∀ y ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, F (y * k.1) = F y) →
        ∫ y : G n, F y.val ∂μ = c * ∫ v in cone n, F (σ v) * ((hOf v).det ^ n)⁻¹) →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ), ContinuousOn k (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    (∀ y ∈ GLs n, Γ * k y = k y * Γ) → (∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0) →
    (∀ χ, ∀ f ∈ CE E, IsEig χ f → ∀ x ∈ GLs n, act μ E k f x = val χ • f x) →
    ∀ (d : G n) (z : Fin n → ℂ), d.val = diagonal z → (∀ a, ‖z a‖ = 1) → (Function.Injective fun a => z a ^ 2) →
      ∫ v in cone n, LinearMap.trace ℂ E.V ((Γ * S 0 * Kc σ c Fr k Γ T d.val (oPt n, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
        val (infOf lam) * conj (weylChar lam fun a => z a ^ 2)

def LAsm : Prop := HbFacts → FrameDer → KChain → KSupp → End1 → End0 → Homot → ConeSt → LOf

end PositivityTheory.RgBcC.LfSt
end
end

