module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

variable {D : D7}

def RelLab (V : HSp D) (P : Pl D.host.E) (d : List ℤ) : Prop :=
  (Formalism.DivisionValues.conjPl P ≠ P ∧ ∃ k, k ≤ V.rank ∧ d = splitLab V.rank k) ∨ (Formalism.DivisionValues.conjPl P = P ∧ GlobalTheory.Hk3.IsLab V P d)

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Eig

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def EigF {W : Type} [AddCommGroup W] [Module ℂ W] (a : Pl D.host.E → List ℤ → ℂ) (Φ : Bridge.Gf (Vc D i) → W) : Prop :=
  ∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → RelLab (Vc D i) P d → GlobalTheory.Hk3.hkF (Vc D i) P (Finsupp.single d 1) Φ = a P d • Φ

def EigK (a : Pl D.host.E → List ℤ → D.what₂.LL) (x : A.fam.amb.FL i A.μ0) : Prop :=
  EigF R i (fun P d => D.what₂.embLL (a P d)) ((R.HV i A.μ0).e (R.jV i A.μ0 x))

end Eig

end GlobalTheory.ConjScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
section
open NumberField GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TrEll

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r n : ℕ} (P : PPol σ r)

def HasCls (k : Type) [CommRing k] [Algebra F k] (J : Matrix (Fin n) (Fin n) E) (γ : HA k σ J) (q : Cls P k) : Prop :=
  ∃ (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ),
    QuotientGroup.mk x = q ∧ gam h = γ

def MapsCls {k k' : Type} [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k'] (ψ : k →ₐ[F] k') (q : Cls P k)
    (q' : Cls P k') : Prop :=
  ∃ (x : plusUnits P k) (x' : plusUnits P k'), QuotientGroup.mk x = q ∧ QuotientGroup.mk x' = q' ∧
    x'.1.1 = Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P)) x.1.1

theorem HasCls.mem {k : Type} [CommRing k] [Algebra F k] {J : Matrix (Fin n) (Fin n) E} {γ : HA k σ J} {q : Cls P k}
    (h : HasCls P k J γ q) : q ∈ XSet P k J := by
  obtain ⟨x, φ, hφ, hq, -⟩ := h
  exact ⟨x, φ, hq, hφ⟩

theorem exists_hasCls {k : Type} [CommRing k] [Algebra F k] {J : Matrix (Fin n) (Fin n) E} {q : Cls P k}
    (h : q ∈ XSet P k J) : ∃ γ, HasCls P k J γ q := by
  obtain ⟨x, φ, hq, hφ⟩ := h
  exact ⟨gam hφ, x, φ, hφ, hq, rfl⟩

variable [NumberField F] [NumberField E]

def polKernel (J : Matrix (Fin n) (Fin n) E) (f : GAd σ J → ℂ) (x : GAd σ J) : ℂ :=
  ∑ᶠ δ : {δ : GRat σ J // δ.1.1.charpoly = P.1}, f (x⁻¹ * ratEmb σ J δ.1 * x)

end GlobalTheory.TrEll
end
end

