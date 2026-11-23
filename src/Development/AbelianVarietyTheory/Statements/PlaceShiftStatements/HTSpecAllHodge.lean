module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.LocalToGlobal.CyclotomicLocalNorms.NormSubToZModPowVal
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions.Loc

namespace GlobalTheory.HTLink

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

abbrev EtV {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) : Type 1 :=
  GlobalTheory.EtC.HQ l (GlobalTheory.EtC.sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) q)) n 0

def etAct {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) (σ : ↥(GK K)) : EtV q n →ₗ[ℚ_[l]] EtV q n :=
  GlobalTheory.EtC.galHQ l (PadicAlgCl l) q n 0 (IntermediateField.fixingSubgroupEquiv K.1 σ)

def etPull {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {f : X' ⟶ X} (hf : f ≫ q = q') (n : ℕ) :
    EtV q n →ₗ[ℚ_[l]] EtV q' n :=
  GlobalTheory.EtC.pullHQ l (GlobalTheory.EtC.sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) q' f hf)) n 0

abbrev HodgeV {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) (a : Fin (n + 1)) : Type :=
  GlobalTheory.HodgeCoh.hodgeH q a (n - a)

def toC (K : FinExt l) : ↥K.1 →+* ℂ_[l] := (algebraMap (PadicAlgCl l) ℂ_[l]).comp (algebraMap ↥K.1 (PadicAlgCl l))

def chiPow (σ : GQ l) (i : ℤ) : ℂ_[l] := (algebraMap ℚ_[l] ℂ_[l] (Formalism.L2.LocGap.Gal.χQ l σ : ℚ_[l])) ^ i

structure Frame {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) : Type 1 where

  d : ℕ

  b : Module.Basis (Fin d) ℚ_[l] (EtV q n)

  e : Fin (n + 1) → ℕ

  c : ∀ a, Module.Basis (Fin (e a)) ↥K.1 (HodgeV q n a)

namespace Frame

variable {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {n : ℕ}

abbrev Col (F : Frame q n) : Type := Σ a : Fin (n + 1), Fin (F.e a)

def rho (F : Frame q n) (σ : ↥(GK K)) : Matrix (Fin F.d) (Fin F.d) ℂ_[l] :=
  (LinearMap.toMatrix F.b F.b (etAct q n σ)).map (algebraMap ℚ_[l] ℂ_[l])

def etMat (F : Frame q n) (F' : Frame q' n) {f : X' ⟶ X} (hf : f ≫ q = q') : Matrix (Fin F'.d) (Fin F.d) ℂ_[l] :=
  (LinearMap.toMatrix F.b F'.b (etPull hf n)).map (algebraMap ℚ_[l] ℂ_[l])

def hodgeMat (F : Frame q n) (F' : Frame q' n) {f : X' ⟶ X} (hf : f ≫ q = q') : Matrix F'.Col F.Col ℂ_[l] :=
  (Matrix.blockDiagonal' fun a : Fin (n + 1) =>
    LinearMap.toMatrix (F.c a) (F'.c a) (GlobalTheory.HodgeCoh.hodgePull hf a (n - a))).map (toC K)

def IsHT (F : Frame q n) (Φ : Matrix (Fin F.d) F.Col ℂ_[l]) : Prop :=
  (∃ Ψ : Matrix F.Col (Fin F.d) ℂ_[l], Φ * Ψ = 1 ∧ Ψ * Φ = 1) ∧
    ∀ σ : ↥(GK K), F.rho σ * Φ.map (Formalism.Per.σC (σ : GQ l)) =
      Φ * Matrix.diagonal fun j : F.Col => chiPow (σ : GQ l) (-((j.1 : ℕ) : ℤ))

end Frame

universe u

structure HodgeFam (K : FinExt l) : Type (max 1 (u + 1)) where

  H : ∀ {X : Scheme.{0}}, (X ⟶ Sp ↥K.1) → ∀ n : ℕ, Fin (n + 1) → Type u

  [add : ∀ {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) (a : Fin (n + 1)), AddCommGroup (H q n a)]

  [mod : ∀ {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) (a : Fin (n + 1)), Module ↥K.1 (H q n a)]

  pull : ∀ {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {f : X' ⟶ X}, f ≫ q = q' →
    ∀ (n : ℕ) (a : Fin (n + 1)), H q n a →ₗ[↥K.1] H q' n a

attribute [instance] HodgeFam.add HodgeFam.mod

end GlobalTheory.HTLink

end
