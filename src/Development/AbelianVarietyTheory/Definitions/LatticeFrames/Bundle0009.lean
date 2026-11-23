module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
section
namespace I195MixedCoordinates_f1b992d3c44b213cc9f27f15

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_f1b992d3c44b213cc9f27f15

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf

variable {D : D7}

def gramQ (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) : Matrix (Fin ρ) (Fin ρ) D.host.E :=
  xᴴ ⬝ (W.gram ⬝ x)

def Orb (W : HSp D) {ρ : ℕ} (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
  {x | LinearIndependent D.host.E x.transpose ∧ gramQ W x = gramQ W x₀}

def Rgrp (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) : Subgroup (GA D W) where
  carrier := {r | ∃ u ∈ UX D ρ, mt W r ⬝ x = x ⬝ u.1}
  one_mem' := ⟨1, one_mem _, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  mul_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨v, hv, hb⟩
    exact ⟨u * v, mul_mem hu hv, by
      rw [mt_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Units.val_mul, Matrix.mul_assoc]⟩
  inv_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h : mt W a⁻¹ ⬝ (x ⬝ u.1) = x := by rw [← ha, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    calc mt W a⁻¹ ⬝ x = mt W a⁻¹ ⬝ (x ⬝ u.1) ⬝ (u⁻¹).1 := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = x ⬝ (u⁻¹).1 := by rw [h]

section Source

variable (ψ : AddChar (AF D.host.F) ℂ) {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (W : HSp D)

def Nfix (j : Fin ρ) : Subgroup (GA D V) :=
  flagN d ⊓ ⨅ i : {i : Fin ρ // i ≤ j}, fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)

def term (v : VolM D W.rank ρ) (Ψ : WO V W → ℂ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) : ℂ :=
  (_root_.I195MixedCoordinates_f1b992d3c44b213cc9f27f15.source d) W ψ v.μ v.𝓕 Ψ (rat x) 0

structure IsTh (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ) : Prop where
  cont : Continuous fun n : flagN d => Th n.1
  left : ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ n ∈ flagN d, Th (γ * n) = Th n
  cen : ∀ c, ∀ n ∈ flagN d, Th (d.nC c * n) = star (ψ (d.qS W c (rat x₀))) * Th n
  dep : ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → gramQ W x₀ *ᵥ a = 0 →
    ∃ (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V) (u : GA D V) (c : ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u ∧ u ∈ Nfix d j ∧ c ≠ 1 ∧
      ∀ n ∈ flagN d, ∀ n' ∈ flagN d, Th (n * u * n') = c * Th (n * n')

def IsBase (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) : Prop :=
  LinearIndependent D.host.E x₀.transpose ∧
    ∀ u ∈ UX D ρ, adj u.1 ⬝ ((rat (gramQ W x₀) : Mx D ρ ρ) ⬝ u.1) = rat (gramQ W x₀)

def flFun (v : VolM D W.rank ρ) (Th : GA D V → ℂ) (x : Mx D W.rank ρ) (Ψ : WO V W → ℂ) (u : UX D ρ)
    (b : Mx D ρ V₀.rank) : ℂ :=
  Th (d.nB b * d.levi u.1) * (_root_.I195MixedCoordinates_f1b992d3c44b213cc9f27f15.source d) W ψ v.μ v.𝓕 Ψ (x ⬝ u.1.1) (x ⬝ b)

def fl (v : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (Th : GA D V → ℂ) (x : Mx D W.rank ρ)
    (Ψ : WO V W → ℂ) : ℂ :=
  ∫ u, (∫ b in vb.𝓕, flFun ψ d W v Th x Ψ u b ∂vb.μ) ∂vU.ν

end Source

def kerBF {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) (φ : GA D B.A → ℂ)
    (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ) (h : GA D J.W) : ℂ :=
  G h * ∫ h₀ in B.vA.𝓕, φ h₀ * flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0 ∂B.vA.μ

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.LinkSimil
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.StCheck

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


theorem link_simil {σ : ℕ} {B : BesLev D σ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (h : IsLineVec L' ζ')
    (l : Link B L' ζ') : l.τᴴ * (B.L.gram * l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have e : star ζ' ⬝ᵥ (l.τᴴ * (B.L.gram * l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L'.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  have c' := mul_right_cancel₀ b c
  exact c'

end GlobalTheory.Unf.StCheck

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

namespace GlobalTheory.FinPl

variable {D : D7}

section Ops

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def formAt (β : Frame p S n) (P : Pair k n) (φ₀ : GA D S → ℂ) : Form k n (GA D S → ℂ) :=
  fun P₁ => β.rep (Classical.epsilon fun g : GL n k => g • P = P₁) φ₀

def sOp (β : Frame p S n) (P : Pair k n) (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (φ₀ : GA D S → ℂ) : GA D S → ℂ :=
  dia ε (FFStar q χ (formAt β P φ₀)) P

def Frame.IsLatMoved (β : Frame p S n) (g : GA D S) (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)) : Prop :=
  ∀ x : n → k, x ∈ Λ ↔ mt S g⁻¹ *ᵥ (fun i => p.sec ((β.b *ᵥ x) i)) ∈ latV S L (· = p.v)

end Ops

def UnrAt {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (s : Step ψ V V₀ W W₀ ρ σ) (v : Pl D) : Prop :=
  CharUnramAt D s.χV v ∧ CharUnramAt D s.χW v

def FlatLaws (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop),
    (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J), IsFlatBF s P (flatBF s)) ∧
    ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), IsFlatFB s P (flatFB s)

def OneCosetBF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V)
    (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v →
    ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f →
      Vac ψ B.V₀ J.W₀ LV₀ LW₀ (· = v) (𝔉 f) ∧
      ∀ h ∈ grpAt J.W (· = v), 𝔉 (s.om (1, h) f) ≠ 0 →
        ∃ r ∈ jacGrp J.d, r ∈ grpAt J.W (· = v) ∧ ∃ κ, InK J.W LW (· = v) κ ∧ h = r * κ

def OrbitSplit (D : D7) : Prop :=
  ∀ (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (v : Pl D), Tame D v → IsSelfDualC B.V₀ L₀ → SplitCore B L₀ v →
    ∀ γ ∈ grpAt B.V₀ (· = v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = v) →
        mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = v)) →
      ∃ a ∈ grpAt B.A (· = v), ∃ κ, InK B.V₀ L₀ (· = v) κ ∧ γ = B.o.emb (a, 1) * κ

def OrbitGlued (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n)
    (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P →
    ∀ γ ∈ grpAt B.V₀ (· = p.v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) →
        mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) →
      (∃ a ∈ grpAt B.A (· = p.v), ∃ κ, InK B.V₀ L₀ (· = p.v) κ ∧ γ = B.o.emb (a, 1) * κ) ∨
      ∃ (Λ : Submodule 𝒪[k] (n → k)) (hΛ : Λ.IsFullLattice k),
        letI := hΛ
        β₀.IsLatMoved γ L₀ (lastKer Λ) ∨ β₀.IsLatMoved γ L₀ (lastPair q Λ).lat

def SourceGlued (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ₀ : AddChar k Circle)
    (hχ : HasConductor χ₀ 1) (χ : AddChar 𝓀[k] ℂ), χ = resChar χ₀ hχ q →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ →
    CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    CharUnramAt D χS p.v → CharUnramAt D χT p.v →
    ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ →
    ∀ (P P₁ : Pair k n') (Λ : Submodule 𝒪[k] (n → k)) [Λ.IsFullLattice k],
      (∃ c : ℂ, ∀ (LS : Lat S) (LT : Lat T) (f₀ Ξ : WO S T → ℂ) (Ξ' : Pair k n → WO S T → ℂ),
        Over ψ α₀ β LS LT f₀ (latInd (gluedS q 1 P.ker P.vec) Λ) Ξ →
        (∀ Q ∈ withLat Λ, Over ψ α₀ β LS LT f₀ (tensCol (phiOne P₁ Q) (charInd χ Q)) (Ξ' Q)) →
        ∀ φ, IsRam α φ → liftA o om vA (φ P) Ξ = c • ∑ Q ∈ withLat Λ, liftA o om vA (FFStar q χ φ P₁) (Ξ' Q)) ∧
      ∀ (LS : Lat S) (LT : Lat T) (f₀ Ξ : WO S T → ℂ) (a : (n → k) → ℂ),
        (Over ψ α₀ β LS LT f₀ (tensCol (latInd P.lat Λ) a) Ξ ∨ Over ψ α₀ β LS LT f₀ (tensCol (latInd P.ker Λ) a) Ξ) →
        ∀ φ, IsRam α φ → liftA o om vA (φ P) Ξ = 0

def Contraction (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ →
    ∃ ε : k, (ε = 1 ∨ ε = -1) ∧
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
      (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
      (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
      (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'')
      (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ →
      ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀)
        (f₁ Ξ₁ Ξ₁' : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ Ξ₂' : WO J.W₀ B'.V₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (Ψ₂ : Matrix n'' n k → ℂ)
        (a a' b b' : (n → k) → ℂ), a ∈ SB (n → k) → a' ∈ SB (n → k) → b ∈ SB (n → k) → b' ∈ SB (n → k) →
        Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ₁ → Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a') Ξ₁' →
        Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ₂ → Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b') Ξ₂' →
        ∀ φ, IsContAut B.A φ →
          (∫ η, (∫ y, a' y * (χ (ε * (η ⬝ᵥ y)) : ℂ) ∂μ) * b' η ∂μ) • hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ =
            (∫ η, (∫ y, a y * (χ (ε * (η ⬝ᵥ y)) : ℂ) ∂μ) * b η ∂μ) • hand0 s₁ s₂ l vL φ Ξ₁' Ξ₂'

def VertexGlued (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ →
    ∃ ε : 𝓀[k]ˣ, (ε = 1 ∨ ε = -1) ∧
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
      (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
      (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), UnrAt s₁ p.v → UnrAt s₂ p.v →
      ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'')
        (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ →
      ∀ (P P₁ : Pair k n') (Q : Pair k n),
        (∀ R : Pair k n'', ∃ c : ℂ, ∀ (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀)
          (f₁ Ξ₁ Ξ₁' : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ Ξ₂' : WO J.W₀ B'.V₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (latInd (gluedS q 1 P.ker P.vec) Q.lat) Ξ₁ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P₁ Q) (vecInd Q.lat)) Ξ₁' →
          Over ψ β γ₀ L₂' L₃ f₂ (latInd Q.lat (gluedS q 1 R.ker R.vec)) Ξ₂ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow (phiOne Q R) (dualInd Q.lat)) Ξ₂' →
          ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ =
            c • hand0 s₁ s₂ l vL (dia ε (FFStar q (resChar χ hχ q) φ) P₁) Ξ₁' Ξ₂') ∧
        ∀ (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k] (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀)
          (f₁ Ξ₁ : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ : WO J.W₀ B'.V₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (latInd (gluedS q 1 P.ker P.vec) Q.lat) Ξ₁ →
          (Over ψ β γ₀ L₂' L₃ f₂ (latInd Q.lat (lastKer Λ)) Ξ₂ ∨
            Over ψ β γ₀ L₂' L₃ f₂ (latInd Q.lat (lastPair q Λ).lat) Ξ₂) →
          ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ = 0

def RamBijective (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ₀ : AddChar k Circle)
    (hχ : HasConductor χ₀ 1) (χ : AddChar 𝓀[k] ℂ), χ = resChar χ₀ hχ q → ∀ (ε : 𝓀[k]ˣ) (S : HSp D)
    (β : Frame p S n) (P : Pair k n),
      Set.BijOn (sOp β P q χ ε) {φ₀ | RamAt β P φ₀} {φ₀ | RamAt β P φ₀} ∧
      (∀ φ, IsRam β φ → IsRam β (dia ε (FFStar q χ φ)) ∧ sOp β P q χ ε (φ P) = dia ε (FFStar q χ φ) P) ∧
      ∃ c c' : GL n k →₀ ℂ, (∀ φ₀, sOp β P q χ ε φ₀ = c.sum fun g a => a • β.rep g φ₀) ∧
        ∀ φ₀, RamAt β P φ₀ → sOp β P q χ ε (c'.sum fun g a => a • β.rep g φ₀) = φ₀ ∧
          RamAt β P (c'.sum fun g a => a • β.rep g φ₀)

def OverBasic (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ),
    IsStdChar D ψ (-1) → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T),
    IsSelfDualC S LS → IsSelfDualC T LT → ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ →
      (∀ Ψ ∈ SB (Matrix n n' k), ∃! f, Over ψ α β LS LT f₀ Ψ f) ∧
      (∀ Ψ f, Over ψ α β LS LT f₀ Ψ f → IsThetaFunO ψ S T f ∧
        ∀ (MS : Lat S) (MT : Lat T) (P : Pl D → Prop), ¬ P p.v → Vac ψ S T MS MT P f₀ → Vac ψ S T MS MT P f) ∧
      (p.UnitAA → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT →
        Over ψ α β LS LT f₀ (latInd ΛS ΛT) f₀)

def PlacesToAdeles (D : D7) : Prop :=
  ∀ (S : HSp D) (L : Lat S) (P : Pl D → Prop), IsSelfDualC S L →
    ∀ R : Subgroup (GA D S), ∀ h : GA D S,
      (∀ v, P v → ∃ hv ∈ grpAt S (· = v), ∃ h' ∈ grpOff S (· = v), h = hv * h' ∧
        ∃ r ∈ R, r ∈ grpAt S (· = v) ∧ ∃ κ, InK S L (· = v) κ ∧ hv = r * κ) →
      ∃ r ∈ R, r ∈ grpAt S P ∧ ∃ g ∈ grpOff S P, ∃ κ, InK S L P κ ∧ h = r * g * κ

end GlobalTheory.FinPl

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.FB

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ}

def x0 (B : BesLev D σ) : Mx D B.V.rank (σ + 1) := xLast B.d (vecB B.o B.ζ)

def zl (B : BesLev D σ) : Mx D B.L.rank (σ + 1) := zEll B.L (σ + 1) B.ζ

def orb (B : BesLev D σ) : Set (Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E) :=
  {x | LinearIndependent D.host.E x.transpose ∧
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat x : Mx D B.V.rank (σ + 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zl B)}

def Quasi (ψ : AddChar (AF D.host.F) ℂ) (S L : HSp D) (y : WO S L → ℂ) : Prop :=
  (∀ γ w, y (ratW L S γ + w) = ψ (-(symplOH S L (ratW L S γ) w)) * y w) ∧ Continuous y

def th (J : JacLev D (σ + 1)) (ψ : AddChar (AF D.host.F) ℂ) (B : BesLev D σ) (y : WO J.W₀ B.L → ℂ) (n : GA D J.W) : ℂ :=
  star (jacS ψ J.d B.L (zl B) n y 0) * star (psiFlag ψ J.d n)

variable {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B)

def tFlat (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) : ℂ :=
  contractT B.o J.W₀ vL.μ vL.𝓕 (flatFB s Ψ) y 0

def unfF (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ)
    (h : GA D B.V) : ℂ :=
  G h * handFB s vL Y (flatFB s (s.om (1, h) Φ)) 1

theorem quasi_of_fam {S L : HSp D} {Y : GA D S → WO S L → ℂ} (hY : IsQuasiFam ψ S L Y) (h : GA D S) : Quasi ψ S L (Y h) :=
  ⟨hY.quasi h, hY.cont.comp (Continuous.prodMk_right h)⟩

end GlobalTheory.Unf.FB

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ENNReal

namespace GlobalTheory.Unf

variable {D : D7}

def realSize (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : ℝ := ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖

def InBox {m n : ℕ} (K : Set (Mx D m n)) (x : Mx D m n) : Prop := ∃ k ∈ K, (x - k).map (finPart D) = 0


open Classical in
def maj (θ : InfFam D) {m n : ℕ} (K : Set (Mx D m n)) (N : ℕ) (x : Mx D m n) : ℝ :=
  if InBox K x then ((1 + realSize θ x) ^ N)⁻¹ else 0

def supSob (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (d : ℕ) (f : WO S T → ℂ) : ℝ≥0∞ :=
  GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) d f

structure IsSobForm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ) : Prop where
  add : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g
  smul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f
  bound : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (d : ℕ) (C : NNReal),
    ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ‖ℓ f‖ₑ ≤ C * supSob ψ θ d f

theorem realSize_nonneg (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : 0 ≤ realSize θ x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem maj_nonneg (θ : InfFam D) {m n : ℕ} (K : Set (Mx D m n)) (N : ℕ) (x : Mx D m n) : 0 ≤ maj θ K N x := by
  unfold maj
  split_ifs
  · have := realSize_nonneg θ x; positivity
  · exact le_rfl

end GlobalTheory.Unf

end
end

