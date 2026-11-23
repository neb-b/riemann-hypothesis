module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

structure IsQuasiFam (ψ : AddChar (AF D.host.F) ℂ) (S L : HSp D) (Y : GA D S → WO S L → ℂ) : Prop where
  quasi : ∀ h γ w, Y h (ratW L S γ + w) = ψ (-(symplOH S L (ratW L S γ) w)) * Y h w
  cont : Continuous fun p : GA D S × WO S L => Y p.1 p.2
  left : ∀ γ ∈ GQ S, ∀ h w, Y (γ * h) w = Y h (w * mt S γ)

def JointCont (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    ∀ f, IsThetaFunO ψ S T f → Continuous fun p : (GA D S × GA D T) × WO S T => om p.1 f p.2

def Descent (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    (∀ (S₀ : HSp D) (ρ : ℕ), HypDec S S₀ ρ → ∃ om₀ : Om S₀ T, IsWeilDatumO ψ S₀ T χS χT om₀) ∧
    ∀ (T₀ : HSp D) (ρ : ℕ), HypDec T T₀ ρ → ∃ om₀ : Om S T₀, IsWeilDatumO ψ S T₀ χS χT om₀

def FlatLaw (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ)
    (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ)
    (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ (y : Mx D V₀.rank σ)
    (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ →
      (∀ w, Integrable (flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y Ψ w) vU.ν) ∧
      IsThetaFunO ψ V₀ W₀ (flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) y Ψ)

def UnfBF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (φ : GA D B.A → ℂ)
    (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ →
      IsQuotIntL1 J.μR s.vW.μ (fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (flatBF s (s.om (1, h) Φ)))
        (B.per ψ φ (s.lift G Φ))

def EvalBF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (φ : GA D B.A → ℂ)
    (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ →
    ∀ (ν₀ : Measure (radX J.d)) (𝓝₀ : Set (radX J.d)), ν₀.IsHaarMeasure →
      IsFundamentalDomain ((GQ J.W).subgroupOf (radX J.d)) 𝓝₀ ν₀ → ν₀ 𝓝₀ = 1 →
      IsQuotIntL1 (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) s.vW.μ
        (fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (evalBF s (s.om (1, h) Φ))) (B.per ψ φ (s.lift G Φ))

def UnfFB (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ),
    IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ →
      IsQuotIntL1 B.μR s.vW.μ (fun h => B.per ψ (handFB s vL Y (flatFB s (s.om (1, h) Φ))) (rTrans h G))
        (J.per ψ B.ζ Y (s.lift G Φ))

def HandFBLaw (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ),
    IsQuasiFam ψ J.W₀ B.L Y → IsThetaFunO ψ J.W₀ B.V₀ Ξ → IsContAut B.A (handFB s vL Y Ξ)

def LinkLaw (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (L' : HSp D)
    (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Link B L' ζ') (φ : GA D B.A → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ),
    IsContAut B.A φ → IsThetaFunO ψ B.V₀ J.W₀ Ξ →
      IsQuasiFam ψ J.W₀ L' (handBF s l φ Ξ) ∧
      ∀ G' : GA D J.W → ℂ, J.perAll ψ B s.om₀ φ G' Ξ = J.per ψ ζ' (handBF s l φ Ξ) G'

def LastLaw (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D) (B : BesLev D 0) (t : Last ψ T B) (φ : GA D B.A → ℂ)
    (Φ₁ : WO B.V t.J.W → ℂ) (Φ₂ : WO t.J.W T → ℂ) (F : GA D T → ℂ), IsContAut B.A φ → IsContAut T F →
    IsThetaFunO ψ B.V t.J.W Φ₁ → IsThetaFunO ψ t.J.W T Φ₂ →
      B.per ψ φ (t.s.lift (liftS t.om t.vT.μ t.vT.𝓕 F Φ₂) Φ₁) = t.Q φ Φ₁ Φ₂ F

def DoubleStep (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (G : GA D B'.V → ℂ) (g : GA D B.V),
    IsThetaFunO ψ B.V J.W Φ₁ → IsThetaFunO ψ J.W B'.V Φ₂ → IsContAut B.A φ → RapidDec B'.V G →
    RapidDec J.W (s₂.lift G Φ₂) →
      (∀ h₁ h₂, IsContAut B'.A (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂)) ∧
      ∃ f₁ : GA D J.W → ℂ, IsQuotIntL1 J.μR s₁.vW.μ f₁ (B.per ψ φ (rTrans g (s₁.lift (s₂.lift G Φ₂) Φ₁))) ∧
        ∀ h₁, IsQuotIntL1 B'.μR s₂.vW.μ
          (fun h₂ => B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) (rTrans h₂ G)) (f₁ h₁)

def IT (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D) (ρ : ℕ) (B : BesLev D ρ) (c : Chain ψ T ρ B) (Φ : c.Data) (F : GA D T → ℂ)
    (φ : GA D B.A → ℂ) (g : GA D B.V), c.IsTheta Φ → IsContAut T F → IsContAut B.A φ → c.Rapid Φ F →
      c.Iter (c.Q Φ F φ g) (B.per ψ φ (rTrans g (c.down Φ F)))

def contr {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank)
    (Ξ₁ : WO B.V₀ S → ℂ) (Ξ₂ : WO S B'.V₀ → ℂ) (u : WO B.A S) (v : WO S B'.A) : ℂ :=
  ∫ w in vL.𝓕, Ξ₂ ((B'.o.resT S).symm (v, w)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) ∂vL.μ

def ContrLaw (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (χA χA' χz : (AE D)ˣ →* Circle) (oma : Om B.A J.W₀) (omz : Om B.L J.W₀) (omb : Om J.W₀ B'.A) (omz' : Om J.W₀ B'.L),
    s₁.χV = χA * χz → s₂.χW = χA' * χz → IsWeilDatumO ψ B.A J.W₀ χA s₁.χW oma → IsWeilDatumO ψ B.L J.W₀ χz s₁.χW omz →
    IsWeilDatumO ψ J.W₀ B'.A s₂.χV χA' omb → IsWeilDatumO ψ J.W₀ B'.L s₂.χV χz omz' →
    ∀ (φ : GA D B.A → ℂ) (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ), IsContAut B.A φ →
      IsThetaFunO ψ B.V₀ J.W₀ Ξ₁ → IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂ →
      (∀ v, IsThetaFunO ψ B.A J.W₀ fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) ∧
      (∀ p, IsThetaFunO ψ J.W₀ B'.A fun v => oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) ∧
      ∀ h₂, handFB s₂ vL (handBF s₁ l φ Ξ₁) Ξ₂ h₂ = ∫ h₁ in J.v0.𝓕, (∫ h₀ in B.vA.𝓕, φ h₀ *
        omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) 0 ∂B.vA.μ) ∂J.v0.μ

def SeeLast (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), L.rank = 1 → L''.rank = 1 →
    τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram →
    ∀ (χA χz χS χS' χT : (AE D)ˣ →* Circle) (om₁ : Om V₀ S) (oma : Om A S) (omz : Om L S) (omX : Om S X) (omT : Om S T)
      (omz'' : Om S L''), IsWeilDatumO ψ V₀ S (χA * χz) χS om₁ → IsWeilDatumO ψ A S χA χS oma →
      IsWeilDatumO ψ L S χz χS omz → IsWeilDatumO ψ S X χS' (χT * χz⁻¹) omX → IsWeilDatumO ψ S T χS' χT omT →
      IsWeilDatumO ψ S L'' χS' χz⁻¹ omz'' →
      ∀ (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), IsThetaFunO ψ V₀ S Ξ → IsThetaFunO ψ S T Φ₂ →
        (∀ u, IsThetaFunO ψ S L'' fun w => Ξ ((o.resS S).symm
          (u, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w)))) ∧
        ∀ h₀ h h', omT (h, h') Φ₂ 0 * om₁ (o.emb (h₀, 1), h) Ξ 0 =
          oma (h₀, h) (fun u => omX (h, o''.emb (h', 1)) (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm
            (u, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w)))) 0) 0

def hypZero (V : HSp D) : HypDec V V 0 where
  e := 0
  e' := 0
  i₀ := 1
  ee := Subsingleton.elim _ _
  e'e' := Subsingleton.elim _ _
  e'e := Subsingleton.elim _ _
  iso := by simp
  i₀e := Subsingleton.elim _ _
  i₀e' := Subsingleton.elim _ _
  rank_add := by simp

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

abbrev Pl (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.F)

abbrev Lat (S : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)

def compAt (D : D7) (w : Pl D) : AE D →+* Fv D.host.F w ⊗[D.host.F] D.host.E := (compFin D w).comp (finPart D)

def idAt (D : D7) (P : Pl D → Prop) : Ideal (AE D) :=
  RingHom.ker (infPart D) ⊓ ⨅ w : {w : Pl D // ¬ P w}, RingHom.ker (compAt D w.1)

def idOff (D : D7) (P : Pl D → Prop) : Ideal (AE D) := ⨅ w : {w : Pl D // P w}, RingHom.ker (compAt D w.1)

def intAt (D : D7) (P : Pl D → Prop) : Set (AE D) := {a | a ∈ idAt D P ∧ finPart D a ∈ intAE D}

def congGrp (V : HSp D) (I : Ideal (AE D)) : Subgroup (GA D V) :=
  ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp (matHom V)).ker

def grpAt (V : HSp D) (P : Pl D → Prop) : Subgroup (GA D V) := congGrp V (idAt D P)

def grpOff (V : HSp D) (P : Pl D → Prop) : Subgroup (GA D V) := congGrp V (idOff D P)

def MxAt (P : Pl D → Prop) {m n : ℕ} (x : Mx D m n) : Prop := ∀ i j, x i j ∈ idAt D P

def latMul (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) (P : Pl D → Prop) : AddSubgroup (Fin S.rank → AE D) :=
  AddSubgroup.closure {y | ∃ α ∈ intAf D.host.F, (∀ v, ¬ P v → evalV D.host.F v α = 0) ∧ ∃ a ∈ 𝔞, ∃ x ∈ L,
    y = fun i => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * x i)}

def latV (S : HSp D) (L : Lat S) (P : Pl D → Prop) : AddSubgroup (Fin S.rank → AE D) := latMul S {1} L P

def latA (S : HSp D) (L : Lat S) (P : Pl D → Prop) : AddSubgroup (Fin S.rank → AE D) :=
  latMul S {a | a ∈ D.host.AA} L P

def Moves (S : HSp D) (g : GA D S) (L M : Lat S) (P : Pl D → Prop) : Prop :=
  ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D P) → (y ∈ latV S L P ↔ mt S g *ᵥ y ∈ latV S M P)

def InK (S : HSp D) (L : Lat S) (P : Pl D → Prop) (κ : GA D S) : Prop := κ ∈ grpAt S P ∧ Moves S κ L L P

def Vac (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) P) f

def Tame (D : D7) (v : Pl D) : Prop :=
  ExtUnramAt D v ∧ ((2 : 𝓞 D.host.F) ∉ v.asIdeal ∨
    ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε)

def colMul {m n : ℕ} (x : Mx D m n) (i : Fin n) (a : AE D) : Fin m → AE D := fun k => a * x k i

def MonoAt {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D) : Prop :=
  ∀ y : Fin S.rank → AE D, y ∈ latV S L (· = v) ↔
    (∀ i, colMul d.jX i ((d.pX *ᵥ y) i) ∈ latV S L (· = v)) ∧ (∀ i, colMul d.jY i ((d.pY *ᵥ y) i) ∈ latV S L (· = v)) ∧
      d.p0 *ᵥ y ∈ latV S₀ L₀ (· = v)

def OrthAt {S A B : HSp D} (o : OrthDec S A B) (L : Lat S) (LA : Lat A) (LB : Lat B) (v : Pl D) : Prop :=
  ∀ y : Fin S.rank → AE D, y ∈ latV S L (· = v) ↔ o.pA *ᵥ y ∈ latV A LA (· = v) ∧ o.pB *ᵥ y ∈ latV B LB (· = v)

def PrimAt (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (v : Pl D) : Prop :=
  ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ s ∈ idAt D (· = v),
    (∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v)) ↔
      ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1

def ColsAt {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (x : Mx D W.rank ρ) (LV : Lat V) (LW : Lat W) (v : Pl D) : Prop :=
  ∀ i, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV V LV (· = v) ↔ colMul x i a ∈ latA W LW (· = v)

structure GoodBF (ψ : AddChar (AF D.host.F) ℂ) {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (LV : Lat B.V) (LV₀ : Lat B.V₀)
    (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D) : Prop where
  tame : Tame D v
  sdV : IsSelfDualC B.V LV
  sdV₀ : IsSelfDualC B.V₀ LV₀
  sdW : IsSelfDualC J.W LW
  sdW₀ : IsSelfDualC J.W₀ LW₀
  monoV : MonoAt B.d LV LV₀ v
  monoW : MonoAt J.d LW LW₀ v
  prim : PrimAt ψ B.d LV v
  cols : ColsAt B.d (xZero J.d) LV LW v
  last : 0 < ρ → ∀ a ∈ idAt D (· = v),
    J.d.incAdj B.V₀ (a • yZero B.V₀ ρ (vecB B.o B.ζ)) ∈ latO B.V₀ J.W (LV₀ : Set _) (LW : Set _) (· = v) ↔
      a ∈ intAt D (· = v)

structure AdaptFB (ψ : AddChar (AF D.host.F) ℂ) {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) (LV : Lat J.W)
    (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (v : Pl D) : Prop where
  tame : Tame D v
  sdV : IsSelfDualC J.W LV
  sdV₀ : IsSelfDualC J.W₀ LV₀
  sdW : IsSelfDualC B.V LW
  sdW₀ : IsSelfDualC B.V₀ LW₀
  monoV : MonoAt J.d LV LV₀ v
  monoW : MonoAt B.d LW LW₀ v
  prim : PrimAt ψ J.d LV v
  cols : ColsAt J.d (xLast B.d (vecB B.o B.ζ)) LV LW v

def SplitCore {ρ : ℕ} (B : BesLev D ρ) (L₀ : Lat B.V₀) (v : Pl D) : Prop :=
  ∃ (LA : Lat B.A) (LL : Lat B.L), IsSelfDualC B.A LA ∧ IsSelfDualC B.L LL ∧ OrthAt B.o L₀ LA LL v

def UInv (W : HSp D) {ρ : ℕ} (x y : Mx D W.rank ρ) : Prop := ∀ u : UX D ρ, pairS W (x * u.1.1) y = pairS W x y

structure HeisLaws (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (P : Pl D → Prop) (𝔉 : (WO V W → ℂ) → (WO V₀ W₀ → ℂ)) : Prop where
  theta : ∀ f, IsThetaFunO ψ V W f → IsThetaFunO ψ V₀ W₀ (𝔉 f)
  dual : ∀ f, IsThetaFunO ψ V W f → ∀ a : Mx D W.rank ρ, MxAt P a → UInv W x a →
    𝔉 (heisO ψ V W (dV.extY W a) f) = ψ (symplO V W (dV.extX W x) (dV.extY W a)) • 𝔉 f
  iso : ∀ f, IsThetaFunO ψ V W f → ∀ ξ : Mx D σ V₀.rank, MxAt P ξ →
    𝔉 (heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) f) = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • 𝔉 f
  core : ∀ f, IsThetaFunO ψ V W f → ∀ w : WO V₀ W₀, MxAt P w →
    𝔉 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) f) = heisO ψ V₀ W₀ w (𝔉 f)

variable {ψ : AddChar (AF D.host.F) ℂ}

structure IsFlatBF {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) (P : Pl D → Prop)
    (𝔉 : (WO B.V J.W → ℂ) → (WO B.V₀ J.W₀ → ℂ)) : Prop where
  Heisenberg₂ : HeisLaws ψ B.d J.d (xZero J.d) (yZero B.V₀ ρ (vecB B.o B.ζ)) P 𝔉
  equiv : ∀ f, IsThetaFunO ψ B.V J.W f → ∀ n ∈ flagN J.d, n ∈ grpAt J.W P → ∀ h ∈ grpAt J.W₀ P,
    𝔉 (s.om (1, n * J.d.emb0 h) f) = star (psiFlag ψ J.d n) • opA ψ J.d B.o B.ζ s.om₀ n h (𝔉 f)

structure IsFlatFB {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) (P : Pl D → Prop)
    (𝔉 : (WO J.W B.V → ℂ) → (WO J.W₀ B.V₀ → ℂ)) : Prop where
  Heisenberg₂ : HeisLaws ψ J.d B.d (xLast B.d (vecB B.o B.ζ)) 0 P 𝔉
  equiv : ∀ f, IsThetaFunO ψ J.W B.V f → ∀ n ∈ flagN B.d, n ∈ grpAt B.V P → ∀ h ∈ grpAt B.A P,
    𝔉 (s.om (1, n * embA B.d B.o h) f) =
      star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • s.om₀ (1, B.o.emb (h, 1)) (𝔉 f)

structure SplitPt (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] where
  v : Pl D
  e : AE D
  split : IsSplitIdem D e
  above : ∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε
  pr : AE D →+* k
  sec : k →+ AE D
  pr_sec : ∀ a, pr (sec a) = a
  sec_pr : ∀ x, sec (pr x) = e * x
  cont_pr : Continuous pr
  cont_sec : Continuous sec
  int_iff : ∀ a, a ∈ 𝒪[k] ↔ finPart D (sec a) ∈ intAE D

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

def SplitPt.IsChar (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) : Prop := ∀ a, (χ a : ℂ) = psiE ψ (p.sec a)

def SplitPt.UnitAA : Prop :=
  (∀ a ∈ intAt D (· = p.v), incA D D.host.xi0 * a ∈ intAt D (· = p.v) ∧ incA D D.host.xi0⁻¹ * a ∈ intAt D (· = p.v)) ∧
    ∀ (S : HSp D) (L : Lat S), latA S L (· = p.v) = latV S L (· = p.v)

structure Frame (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] where
  b : Matrix (Fin S.rank) n k
  b' : Matrix n (Fin S.rank) k
  bb' : b * b' = 1
  b'b : b' * b = 1
  gl : GL n k →* GA D S
  gl_supp : ∀ g, SuppAt p.e S (gl g)
  gl_mat : ∀ g, (mt S (gl g)).map p.pr = b * g.val * b'

variable {p} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def Frame.rep (β : Frame p S n) : Representation ℂ (GL n k) (GA D S → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ fun x => x * β.gl g
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [LinearMap.funLeft, mul_assoc]

def Frame.IsLat (β : Frame p S n) (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)) : Prop :=
  ∀ x : n → k, x ∈ Λ ↔ (fun i => p.sec ((β.b *ᵥ x) i)) ∈ latV S L (· = p.v)

def rd (α : Frame p S n') (β : Frame p T n) (t : WO S T) : Matrix n n' k :=
  β.b' * Matrix.map t p.pr * α.b


open Classical in
def extFun (α : Frame p S n') (β : Frame p T n) (Ψ : Matrix n n' k → ℂ) (t : WO S T) : ℂ :=
  if IsHalf p.e t then Ψ (rd α β t) else 0

def Over (ψ : AddChar (AF D.host.F) ℂ) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ)
    (Ψ : Matrix n n' k → ℂ) (f : WO S T → ℂ) : Prop :=
  IsSelfDualC S LS ∧ IsSelfDualC T LT ∧ Vac ψ S T LS LT (· = p.v) f₀ ∧ Ψ ∈ SB (Matrix n n' k) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) 1 f₀ (extFun α β Ψ) f

def IsSumFrame {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (β : Frame p A n)
    (β₀ : Frame p S₀ (n ⊕ Fin 1)) : Prop :=
  β₀.b = fromCols (o.jA.map p.pr * β.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i))

def IsRam (β : Frame p S n) (φ : Form k n (GA D S → ℂ)) : Prop :=
  φ ∈ EqForm β.rep ∧ φ ∈ Mram k n (GA D S → ℂ) ∧ ∀ P, IsContAut S (φ P)

def RamAt (β : Frame p S n) (P : Pair k n) (φ₀ : GA D S → ℂ) : Prop := ∃ φ, IsRam β φ ∧ φ P = φ₀

structure GluedCore {ρ : ℕ} (B : BesLev D ρ) (L₀ : Lat B.V₀) (q : Unif k) (β : Frame p B.A n)
    (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n) : Prop where
  unit : p.UnitAA
  sum : IsSumFrame B.o B.ζ β β₀
  norm : valuation k (p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))) = valuation k ((q.1 : 𝒪[k]) : k)
  lat : β₀.IsLat L₀ (gluedS q 1 P.ker P.vec)

def tensCol (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (x : Matrix n (n' ⊕ Fin 1) k) : ℂ :=
  Ψ (x.submatrix id Sum.inl) * a fun i => x i (Sum.inr 0)

def tensRow (Ψ : Matrix n n' k → ℂ) (b : (n' → k) → ℂ) (x : Matrix (n ⊕ Fin 1) n' k) : ℂ :=
  Ψ (x.submatrix Sum.inl id) * b (x (Sum.inr 0))


open Classical in
def vecInd (Λ : Submodule 𝒪[k] (n → k)) (y : n → k) : ℂ := if y ∈ Λ then 1 else 0


open Classical in
def dualInd (Λ : Submodule 𝒪[k] (n → k)) (η : n → k) : ℂ := if GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.InDual Λ η then 1 else 0

def charInd (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n) (y : n → k) : ℂ := χ (-Q.ev y) * vecInd Q.lat y

end Frames

def liftA {S A L T : HSp D} (o : OrthDec S A L) (om : Om S T) (vA : Vol A) (φ : GA D A → ℂ) (Ξ : WO S T → ℂ)
    (h : GA D T) (w : WO L T) : ℂ :=
  ∫ a in vA.𝓕, φ a * om (o.emb (a, 1), h) Ξ ((o.resS T).symm (0, w)) ∂vA.μ

theorem handBF_eq {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') (φ : GA D B.A → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) (h : GA D J.W₀) (w : WO J.W₀ L') :
    handBF s l φ Ξ h w = star (liftA B.o s.om₀ B.vA φ Ξ h (l.κ J.W₀ w)) := rfl

def hand0 {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
    (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ) (Ξ₁ : WO B.V₀ J.W₀ → ℂ)
    (Ξ₂ : WO J.W₀ B'.V₀ → ℂ) : GA D B'.A → ℂ :=
  handFB s₂ vL (handBF s₁ l φ Ξ₁) Ξ₂

end GlobalTheory.FinPl

end
end

