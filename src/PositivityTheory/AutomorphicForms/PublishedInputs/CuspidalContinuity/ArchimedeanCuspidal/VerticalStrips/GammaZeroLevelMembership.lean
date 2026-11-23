module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.WhittakerModelGL2
public import Mathlib
public import GroundTheory.AutomorphicForms.GL2Classical.Bundle0002
public import GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
public import GroundTheory.AutomorphicForms.ReductionMeasure

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace Ad3.R

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def dt (r r' : Fin 2 → F) : F := r 0 * r' 1 - r 1 * r' 0

def m2 (ψ : AddChar F Circle) : Measure (Fin 2 → F) := Measure.pi fun _ => selfDualMeasure ψ

def upm (ϖ : Fˣ) (b : F) : GL (Fin 2) F := uni2 b * dg2 ϖ 1

def Reps (ϖ : Fˣ) (B : Finset F) : Prop :=
  ord (ϖ : F) = 1 ∧ (∀ b ∈ B, b ∈ 𝒪[F]) ∧ ∀ x ∈ 𝒪[F], ∃! b, b ∈ B ∧ ((ϖ⁻¹ : Fˣ) : F) * (x - b) ∈ 𝒪[F]

def GammaZeroLevelMembership (n : ℕ) (x : GL (Fin 2) F) (d : Fˣ) : Prop :=
  x ∈ integralGL F 2 ∧ (((unifUnit F)⁻¹ ^ n : Fˣ) : F) * x 1 0 ∈ 𝒪[F] ∧ (d : F) = x 1 1

def TypeU (ω : Fˣ →* ℂˣ) (n : ℕ) (lam : ℂ) (W : GL (Fin 2) F → ℂ) : Prop :=
  (∀ x d, GammaZeroLevelMembership n x d → ∀ g, W (g * x) = ((ω d : ℂˣ) : ℂ) * W g) ∧
    ∀ ϖ B, Reps ϖ B → ∀ g, ∑ b ∈ B, W (g * upm ϖ b) = lam * W g

def TypeT (lam : ℂ) (W : GL (Fin 2) F → ℂ) : Prop :=
  (∀ x ∈ integralGL F 2, ∀ g, W (g * x) = W g) ∧
    ∀ ϖ B, Reps ϖ B → ∀ g, ∑ b ∈ B, W (g * upm ϖ b) + W (g * dg2 1 ϖ) = lam * W g

end Loc

abbrev G2 : Type := AdelicGLn.AdelicGL ℚ 2
abbrev Jd : Type := IdeleGroup ℚ
abbrev Af : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

instance (v : Pl) : MeasurableSpace (GL (Fin 2) (Qv v)) := borel _
instance (v : Pl) : BorelSpace (GL (Fin 2) (Qv v)) := ⟨rfl⟩

abbrev dia2 (γ : GL (Fin 2) ℚ) : G2 := AdelicGLn.diagonal ℚ 2 γ

def md (a : Jd) : ℝ := (IdeleGroup.ideleModule ℚ a : ℝ)
def Dt (g : G2) : ℝ := md (GeneralLinearGroup.det g)
def cdet (c : HeckeCharacter ℚ) (g : G2) : ℂ := (c.toIdele (GeneralLinearGroup.det g) : ℂ)
def pri (α : ℚˣ) : Jd := Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom α

def lf (v : Pl) (a : Afˣ) : (Qv v)ˣ := Units.map (adeleAt v).toMonoidHom a

def band : Set G2 := {g | 1 ≤ Dt g ∧ Dt g < 2}

def inv2 (g : G2) : G2 := dg2 (GeneralLinearGroup.det g)⁻¹ (GeneralLinearGroup.det g)⁻¹ * g
abbrev KA : Type := (maxCompact : Subgroup G2)
def LInv {X : Type} (H : G2 → X) : Prop := ∀ γ g, H (dia2 γ * g) = H g
def CInv {X : Type} (H : G2 → X) : Prop := ∀ (z : Jd) g, H (dg2 z z * g) = H g

structure Set0 (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) : Prop where
  haar : μ.IsHaarMeasure
  right : μ.IsMulRightInvariant
  fd : IsFundamentalDomain (AdelicGLn.diagonal ℚ 2).range 𝓕 μ
  meas : MeasurableSet 𝓕
  vol : μ (𝓕 ∩ band) < ∞
  haarK : mK.IsHaarMeasure
  probK : IsProbabilityMeasure mK
  measD : MeasurableSet 𝓓
  uniqD : ∀ a : Jd, ∃! α : ℚˣ, pri α * a ∈ 𝓓
  finD : ∀ (τ : ℝ) (M : ℕ), 0 < τ → τ < M → ∫⁻ a in 𝓓, ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ) ∂ideleMeasure ℚ < ∞

def Dec (H : G2 → ℂ) : Prop := ∀ M : ℕ, ∃ C : ℝ, ∀ x (a : Jd) (κ : KA), ‖H (uni2 x * dg2 a 1 * κ.1)‖ ≤ C * min 1 (md a)⁻¹ ^ M

def Wh (φ : G2 → ℂ) (g : G2) : ℂ :=
  ∫ x in fundamentalSet ℚ, φ (uni2 x * g) * (adelicChar ℚ (-x) : ℂ) ∂adeleMeasure ℚ

def IsLoc2 (v : Pl) (x : GL (Fin 2) (Qv v)) (h : G2) : Prop := finAt v h = x ∧ (∀ v' ≠ v, finAt v' h = 1) ∧ ∀ w, infAt w h = 1

structure Om (N : ℕ) (χ : DirichletCharacter ℂ N) (ω : HeckeCharacter ℚ) : Prop where
  fin : IsOfFinOrder ω
  val : ∀ (d : Afˣ) (n : ℤ), (∀ v, ord (lf v d : Qv v) = 0) →
    (∀ v, pOf v ∣ N → ((N : Qv v))⁻¹ * ((lf v d : Qv v) - n) ∈ 𝒪[Qv v]) →
    (ω.toIdele (IdeleGroup.ofFinite d) : ℂ) * χ (n : ZMod N) = 1


open UpperHalfPlane in
structure Lift (k N : ℕ) [NeZero N] (f : ℍ → ℂ) (ω : HeckeCharacter ℚ) (φ : G2 → ℂ) : Prop where
  cont : Continuous φ
  left : LInv φ
  cen : ∀ (z : Jd) g, φ (dg2 z z * g) = (ω.toIdele z : ℂ) * φ g
  real : ∀ x : GL (Fin 2) ℝ, 0 < x.det.val → φ (realEmb x) = archLift (k : ℤ) f x
  rot : ∀ r : GL (Fin 2) ℝ, r.val * r.valᵀ = 1 → r.det.val = 1 → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ g, φ (g * realEmb r) = u * φ g
  level : ∀ u ∈ Gamma0Level N, ∀ d : Afˣ, (∀ v, ord (lf v d : Qv v) = 0) →
    (∀ v, pOf v ∣ N → (lf v d : Qv v) = glAt v u 1 1) → ∀ g, φ (g * finEmb ℚ 2 u) = (ω.toIdele (IdeleGroup.ofFinite d) : ℂ) * φ g

def LocFn (v : Pl) (φ : G2 → ℂ) (g : G2) (W : GL (Fin 2) (Qv v) → ℂ) : Prop := ∀ x h, IsLoc2 v x h → W x = φ (g * h)

def lamOf (k : ℕ) (a : ℕ → ℂ) (v : Pl) : ℂ := a (pOf v) * ((pOf v : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ)

structure Hk (k N : ℕ) (a : ℕ → ℂ) (ω : HeckeCharacter ℚ) (φ : G2 → ℂ) : Prop where
  good : ∀ v, ¬ pOf v ∣ N → ∀ g W, LocFn v φ g W → TypeT (lamOf k a v) W
  bad : ∀ v, pOf v ∣ N → ∀ g W, LocFn v φ g W → TypeU (localChar ω v) (N.factorization (pOf v)) (lamOf k a v) W
  glob : ∀ κ : KA, (∀ w, infAt w κ.1 = 1) → (∀ v, pOf v ∣ N → finAt v κ.1 = 1) → ∀ g, φ (g * κ.1) = φ g

structure OmL (k N : ℕ) (χ : DirichletCharacter ℂ N) (ω : HeckeCharacter ℚ) : Prop where
  good : ∀ v, ¬ pOf v ∣ N → IsUnramifiedChar (localChar ω v) ∧ (localChar ω v (unifUnit (Qv v)) : ℂ) = χ (pOf v)
  bad : ∀ v, pOf v ∣ N → quasiCharConductor (localChar ω v) = N.factorization (pOf v)
  sign : ∀ S : Finset Pl, (∀ v, pOf v ∣ N → v ∈ S) → ∏ v ∈ S, ((localChar ω v (-1) : ℂˣ) : ℂ) = (-1) ^ k

def WR (k : ℕ) (t : ℝˣ) : ℂ := if (t : ℝ) < 0 then ((Real.sqrt |(t : ℝ)| ^ k * Real.exp (-2 * Real.pi * |(t : ℝ)|) : ℝ) : ℂ) else 0

def IsUn (S : Finset Pl) (x : ∀ v : S, Qv v.1) (h : G2) : Prop :=
  (∀ v : S, finAt v.1 h = uni2 (x v)) ∧ (∀ v ∉ S, finAt v h = 1) ∧ ∀ w, infAt w h = 1

def IsK (m : ∀ v : Pl, Measure (integralGL (Qv v) 2)) : Prop := ∀ v, (m v).IsHaarMeasure ∧ IsProbabilityMeasure (m v)

end Ad3.R

end
