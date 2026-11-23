module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker

namespace GlobalTheory.WeilParts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def NonSplitAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) : Prop :=
  IsPlaceIdem D v ε ∧ ¬ ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε

def SuppPl (ε : AF D.host.F) (V : HSp D) (g : GA D V) : Prop :=
  ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (Formalism.L2.Theta.mt V g - 1) i j = (Formalism.L2.Theta.mt V g - 1) i j

def UnramAt (ε : AF D.host.F) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, algebraMap (AF D.host.F) (AE D) ε * ((x : AE D) - 1) = (x : AE D) - 1 →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def FixesVacAt (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) : Prop :=
  ∀ g h, SuppPl ε S g → SuppPl ε T h →
    (∀ u, u ∈ (latO S T ΛS ΛT fun w => w = v) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun w => w = v)) →
    ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ (latO S T ΛS ΛT fun w => w = v), heisO ψ S T u f = f) → om (g, h) f = f

def detPlus {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ) (a' : Matrix (Fin n) (Fin n) ℂ)
    (b : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ((1 / 2 : ℂ) • ((1 + sT ⊗ₖ sSᵀ) * (b ⊗ₖ a'ᵀ)) + (1 / 2 : ℂ) • (1 - sT ⊗ₖ sSᵀ)).det

def VacCharPlus (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ),
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ g ∈ GinfC S, ∀ h ∈ GinfC T,
      (∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt S g) = compAt θ τ (Formalism.L2.Theta.mt S g) * sS τ) →
      (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) →
      ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
        om (g, h) f = (∏ τ, detPlus (sS τ) (sT τ) (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h))) • f

structure IsUnitaryOnTheta (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop where
  pres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)
  cont : ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun p : GA D S × GA D T => om p f w
  unit : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ p f, IsThetaFunO ψ S T f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

structure IsFinWeil (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop extends IsUnitaryOnTheta ψ S T om where
  triv : ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ w₀ f, IsThetaFunO ψ S T f →
    om (g, h) (heisO ψ S T w₀ f) = heisO ψ S T (actO S T g h w₀) (om (g, h) f)
  split : ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ∀ f, IsThetaFunO ψ S T f → ℓ (om (g, h) f) = (r : ℂ) * (splitFacO χS χT x y : ℂ) * ℓ f
  inert : ∀ v ε, NonSplitAt D v ε → FixesVacAt ψ S T ΛS ΛT om v ε

structure IsInfWeil (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop extends IsUnitaryOnTheta ψ S T om where
  triv : ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ w₀ f, IsThetaFunO ψ S T f →
    om (g, h) (heisO ψ S T w₀ f) = heisO ψ S T (actO S T g h w₀) (om (g, h) f)
  vac : VacCharPlus ψ θ S T om

def IsEtaTilde (D : D7) (η : (AE D)ˣ →* Circle) : Prop :=
  IsHeckeChar D η ∧ UnramEverywhere D η ∧ ResEta D η 1 ∧ ∀ τ, HasInfExp D η τ (1 / 2)

end GlobalTheory.WeilParts

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
section
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {r g : ℕ}

structure IsMod (W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) : Prop where
  model : Formalism.L2.Pj.ModelW W hr X
  psi : ∀ τ : D.host.E →+* ℂ, τ ∈ X.Ψ ↔ ∃ ρ, τ = tauE D ρ
  kap : X.κ0 = -(2 * D.host.xi0)

def realM (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (τ : D.host.E →+* ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  if h : ∃ ρ, τ = tauE D ρ then compAt θ h.choose w else 0

def perC {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E r) (x : Frame X.Ψ r) (u : X.Ψ → Fin r → ℂ) :
    X.Ψ × Fin r → ℂ := fun p =>
  if (p.2 : ℕ) < X.p0 then hermC p.1.1 X.Gm (FD.col (mat x p.1) p.2) (u p.1) else ((mat x p.1)⁻¹ *ᵥ u p.1) p.2

def zOf (θ : InfFam D) (V W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) (idx : Fin g ≃ X.Ψ × Fin r)
    (x : Frame X.Ψ r) (w : WO V W) : Fin V.rank → Fin g → ℂ := fun b j =>
  perC X x (fun τ a => realM θ w τ.1 (Fin.cast hr.symm a) b) (idx j)

def Reads (θ : InfFam D) (V W : HSp D) (hr : W.rank = r) (X : Data D.host.E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (f : WO V W → ℂ) (φ : TF V.rank g)
    (x : Frame X.Ψ r) : Prop :=
  GlobalTheory.SW.IsSB φ ∧ ∀ w : WO V W, w.map (finPart D) = 0 →
    f w = cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
      thA X bas idx φ x (zOf θ V W hr X idx x w)

def colsR {E : Type} {m n : ℕ} (hr : m = r) (γ : Matrix (Fin m) (Fin n) E) : Matrix (Fin n) (Fin r) E :=
  fun b a => γ (Fin.cast hr.symm a) b

def IsFinOf (V W : HSp D) (γ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : WO V W) : Prop :=
  u.map (infPart D) = 0 ∧ u.map (finPart D) = (ratW W V γ).map (finPart D)

def IsONFr {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E r) (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnM X

def IsInvOf (W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) (x : Frame X.Ψ r)
    (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) : Prop :=
  ∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ →
    Matrix.reindex (finCongr hr) (finCongr hr) (s ρ) * mat x τ = -(mat x τ * sgnM X)

def frMove (θ : InfFam D) (W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) (h : GA D W) (x : Frame X.Ψ r) :
    Frame X.Ψ r := fun τ =>
  (Matrix.reindex (finCongr hr) (finCongr hr) (realM θ (Formalism.L2.Theta.mt W h) τ.1) * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def latR {E : Type} [Field E] [NumberField E] {m : ℕ} (hr : m = r) (L : Submodule (𝓞 E) (Fin m → E)) : Lt E r :=
  L.map (LinearMap.funLeft (𝓞 E) E (Fin.cast hr.symm))

structure IsLatOf (V W : HSp D) (hr : W.rank = r) (Λ : AddSubgroup (WO V W))
    (A : AddSubgroup (Matrix (Fin V.rank) (Fin r) D.host.E)) : Prop where
  fin : ∀ u ∈ Λ, u.map (infPart D) = 0
  opn : ∃ U : Set (WO V W), IsOpen U ∧ ∀ u : WO V W, u.map (infPart D) = 0 → (u ∈ Λ ↔ u ∈ U)
  rat : ∀ γ u, IsFinOf V W γ u → (u ∈ Λ ↔ colsR hr γ ∈ A)

def IsVarOf (V W : HSp D) (X : Data D.host.E r) (q0 : ℕ)
    (vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank) : Prop :=
  ∀ l, l.1.1 = tauE D (vr l).1 ∧ (vr l).2.2 = l.2.2 ∧
    ((vr l).2.1 : ℕ) = Sum.elim (fun i : Fin q0 => (i : ℕ)) (fun i : Fin X.p0 => q0 + (i : ℕ)) l.2.1

def IsBasOf (W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) {q0 : ℕ} (hq : X.p0 + q0 = r) (x : Frame X.Ψ r)
    (B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) : Prop :=
  ∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → ∀ (k : Fin q0 ⊕ Fin X.p0) (i a : Fin W.rank),
    (i : ℕ) = Sum.elim (fun i : Fin q0 => (i : ℕ)) (fun i : Fin X.p0 => q0 + (i : ℕ)) k →
      B ρ a i = x τ (Fin.cast hr a) (rowIdx hq k)

theorem perC_emb {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) :
    perC X x (fun τ => Data.emb τ.1 v) = per X x v := rfl

end

end GlobalTheory.AdTh
end

