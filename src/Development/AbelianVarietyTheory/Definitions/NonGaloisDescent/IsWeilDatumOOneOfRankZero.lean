module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0005
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7}

def Lag (W : HSp D) : Type :=
  {Y : Submodule D.host.E ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) //
    Module.finrank D.host.E Y = W.rank ∧
      ∀ y ∈ Y, ∀ y' ∈ Y, star y.1 ⬝ᵥ W.gram.mulVec y'.1 = star y.2 ⬝ᵥ W.gram.mulVec y'.2}

def IsLagFrame (W : HSp D) (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Prop :=
  Submodule.span D.host.E (Set.range fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) = Y.1

def ratMul {a b c : ℕ} (C : Matrix (Fin a) (Fin b) D.host.E) (u : Mx D b c) : Mx D a c :=
  HMul.hMul (C.map (incA D)) (u : Matrix (Fin b) (Fin c) (AE D))

def lagTerm {V W : HSp D} (μ : Measure (WO V W)) (𝓕 : Set (WO V W))
    (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) (f₁ f₂ : WO V W → ℂ) : ℂ :=
  ∫ u in 𝓕, f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) ∂μ

structure SWSetup (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V))
    (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W))
    (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) : Prop where
  weil : IsWeilDatumO ψ V W χV χW om
  pos : V.IsPosDef
  big : 2 * W.rank < V.rank
  haarV : νV.IsHaarMeasure
  fdV : IsFundamentalDomain (GQ V) 𝓗 νV
  haarW : νW.IsHaarMeasure
  fdW : IsFundamentalDomain (GQ W) 𝓖 νW
  covol : IsCovolOne (ratL W V) μ 𝓕
  frame : ∀ Y, IsLagFrame W Y (fr Y)
  sigOK : V.SigOK

def SWPair (D : D7) : Prop :=
  ∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr →
    ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
      HasSum (fun Y : Lag W => ((νV 𝓗).toReal : ℂ) * lagTerm μ 𝓕 (fr Y) f₁ f₂)
        (∫ h in 𝓗, thetaKO om h 1 f₁ * star (thetaKO om h 1 f₂) ∂νV)

def EisAbs (D : D7) : Prop :=
  ∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr →
    ∀ θ : InfFam D, IsInfFam θ → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
      ∀ φ₁ φ₂, IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ →
        ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' Y : Lag W,
          ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ ∂νW ∂νW ≠ ⊤

def KerAbs (D : D7) : Prop :=
  ∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr →
    ∀ θ : InfFam D, IsInfFam θ → νV 𝓗 ≠ ⊤ ∧ ∀ f, IsThetaFunO ψ V W f → ∀ φ, IsAutFunSm θ W φ → IsCuspFun W φ →
      ∃ B : ℝ, ∀ h, IntegrableOn (fun g => star (thetaKO om h g f) * φ g) 𝓖 νW ∧
        ∫ g in 𝓖, ‖thetaKO om h g f‖ * ‖φ g‖ ∂νW ≤ B

def TermMove (D : D7) : Prop :=
  ∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr →
    ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
      (∀ Y C, IsLagFrame W Y C → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 (fr Y) f₁ f₂) ∧
      ∀ γ ∈ GQ W, ∀ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, mt W γ = c.map (incA D) →
        (∀ C, lagTerm μ 𝓕 (c * C.1, C.2) (om (1, γ) f₁) f₂ = lagTerm μ 𝓕 C f₁ f₂) ∧
        lagTerm μ 𝓕 (1, c) f₁ f₂ = thetaIP μ 𝓕 (om (1, γ⁻¹) f₂) f₁

def TermInv (D : D7) : Prop :=
  ∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr →
    ∀ (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I →
      Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) →
      ∀ n ∈ NI W I, ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
        lagTerm μ 𝓕 (fr Y) (om (1, n) f₁) f₂ = lagTerm μ 𝓕 (fr Y) f₁ f₂

def CuspKill (D : D7) : Prop :=
  ∀ (W : HSp D) (ν : Measure (GA D W)), ν.IsHaarMeasure → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E),
    IsIsoFrame W I → ∀ Γ : Subgroup (GA D W), Γ ≤ GQ W → NI W I ⊓ GQ W ≤ Γ → (∀ γ ∈ Γ, ∀ n ∈ NI W I, γ * n * γ⁻¹ ∈ NI W I) →
    ∀ 𝓓 : Set (GA D W), IsFundamentalDomain Γ 𝓓 ν → ∀ Φ φ : GA D W → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) →
      (∀ n ∈ NI W I, ∀ g, Φ (n * g) = Φ g) → IsAutFun W φ → IsCuspFun W φ →
      IntegrableOn (fun g => Φ g * φ g) 𝓓 ν → ∫ g in 𝓓, Φ g * φ g ∂ν = 0

section Inhabitants

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
  {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}


open scoped ComplexOrder in
theorem SWSetup.posDef {νV 𝓗 νW 𝓖 μ 𝓕 fr} (h : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) (τ : D.host.E →+* ℂ) :
    (V.gram.map τ).PosDef := by
  have h1 := h.sigOK τ
  rw [h.pos τ] at h1
  exact Formalism.IndefR.Fin.Lifts.posDef_of_sig _ h1

theorem exists_lagFrame (W : HSp D) (Y : Lag W) : ∃ C, IsLagFrame W Y C := by
  let b := Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1
  refine ⟨(fun a j => (b j).1.1 a, fun a j => (b j).1.2 a), ?_⟩
  have h := congrArg (Submodule.map Y.1.subtype) b.span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
  exact h

def Lag.diag (W : HSp D) : Lag W :=
  ⟨LinearMap.range (LinearMap.prod LinearMap.id LinearMap.id), by
    rw [LinearMap.finrank_range_of_inj (fun x y h => congrArg Prod.fst h)]
    simp, by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rfl⟩

instance (W : HSp D) : Inhabited (Lag W) := ⟨Lag.diag W⟩

theorem ratMul_one {a c : ℕ} (u : Mx D a c) : ratMul 1 u = u := by
  unfold ratMul
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem lagTerm_one_one (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (f₁ f₂ : WO V W → ℂ) :
    lagTerm μ 𝓕 (1, 1) f₁ f₂ = thetaIP μ 𝓕 f₂ f₁ := by
  simp only [lagTerm, thetaIP, ratMul_one, mul_comm]

theorem exists_haar_fundDomain (V : HSp D) :
    ∃ (ν : Measure (GA D V)) (𝓖 : Set (GA D V)), ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓖 ν := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨𝓖, h⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V Measure.haar inferInstance
  exact ⟨Measure.haar, 𝓖, inferInstance, h⟩

theorem exists_hecke_resEta (D : D7) (n : ℕ) : ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ n := by
  obtain ⟨η, h1, -, h3, -⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  refine ⟨η ^ n, ⟨?_, fun x => ?_⟩, h3.1, fun e he a => ?_⟩
  · have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by
      funext x; simp
    rw [this]
    exact h1.1.pow n
  · rw [MonoidHom.pow_apply, h1.2 x, one_pow]
  · rw [MonoidHom.pow_apply, h3.2 e he a, pow_one]

end Inhabitants

end GlobalTheory.RawLift

end
