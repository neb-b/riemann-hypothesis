module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EventuallyDifferentiableAtOfContDiffAtTwo
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUnitOfNorm
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Formalism.FrobeniusOrbits.HostCorollaries

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix MeasureTheory Set Complex
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory.CxPts GlobalTheory.ShFam
open scoped ContDiff

namespace GlobalTheory.ChernReg

section Flat

variable {d : ℕ}

def polMat (q : (Fin d → ℂ) → ℝ) : Matrix (Fin d) (Fin d) ℂ := fun k l =>
  (q (Pi.single k 1 + Pi.single l 1) - q (Pi.single k 1 - Pi.single l 1) +
    I * q (Pi.single k 1 + I • Pi.single l 1) - I * q (Pi.single k 1 - I • Pi.single l 1)) / 4

def christoffel (b : V d → Matrix (Fin d) (Fin d) ℂ) (z ξ : V d) : V d :=
  WithLp.toLp 2 ((ξ.ofLp ᵥ* Matrix.of fun k l => del (fun v => b v k l) z ξ) ᵥ* (b z)⁻¹)

def jet (b : V d → Matrix (Fin d) (Fin d) ℂ) (n : ℕ) : V d × V d → V d :=
  n.rec Prod.fst fun _ f q => del f q (q.2, -christoffel b q.1 q.2)

variable (b : V d → Matrix (Fin d) (Fin d) ℂ)

def cutoff (t : ℝ) : ℝ := if t < 1 then ((1 - t) ^ 2)⁻¹ * Real.exp (t - 1)⁻¹ else 0

def mean (q f : (Fin d → ℂ) → ℝ) : ℝ := (∫ ξ, f ξ * cutoff (q ξ)) / ∫ ξ, cutoff (q ξ)

section Mass

variable {q : (Fin d → ℂ) → ℝ} (hc : Continuous q) (hh : ∀ (t : ℝ) ξ, q (t • ξ) = t ^ 2 * q ξ)
  (hp : ∀ ξ, ξ ≠ 0 → 0 < q ξ)
include hc hh hp

end Mass

end Flat

section Manifold

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {d : ℕ}

abbrev ChartMap (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) : Type := AlgChart p σ d → CxPts p σ → (Fin d → ℂ) → CxPts p σ

def matIn (a : ChartForm p σ d) (c : AlgChart p σ d) (v : V d) : Matrix (Fin d) (Fin d) ℂ := polMat (a c (c.e.symm v))

structure IsExph (a : ChartForm p σ d) (E : ChartMap p σ d) : Prop where

  trans : ∀ (c c' : AlgChart p σ d), ∀ y ∈ c.e.source, y ∈ c'.e.source → ∀ ξ, E c y ξ = E c' y (c.dtrans c' y ξ)

  cont : ∀ c : AlgChart p σ d, ContinuousOn (fun q : V d × V d => E c (c.e.symm q.1) q.2.ofLp) (c.e.target ×ˢ univ)

  smooth : ∀ c c' : AlgChart p σ d, ContDiffOn ℝ ∞ (fun q : V d × V d => c'.e (E c (c.e.symm q.1) q.2.ofLp))
    {q | q.1 ∈ c.e.target ∧ E c (c.e.symm q.1) q.2.ofLp ∈ c'.e.source}

  zero : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, E c y 0 = y

  jets : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ (ξ : V d) (n : ℕ),
    iteratedDeriv n (fun t : ℝ => c.e (E c y (t • ξ.ofLp))) 0 = jet (matIn a c) n (c.e y, ξ)

def ConjComm (j : CxPts p σ' → CxPts p σ) (E : ChartMap p σ d) (E' : ChartMap p σ' d) : Prop :=
  ∀ (c : AlgChart p σ d) (c' : AlgChart p σ' d),
    (∀ w ∈ c'.e.source, j w ∈ c.e.source → ∀ i, c'.e w i = starRingEnd ℂ (c.e (j w) i)) →
    ∀ z ∈ c'.e.source, j z ∈ c.e.source → ∀ ξ, j (E' c' z ξ) = E c (j z) (star ξ)

def rhoIn (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → ℝ) (c : AlgChart p σ d) (y : CxPts p σ) (t : ℝ) : ℝ :=
  mean (a c y) fun ξ => ψ (E c y (t • ξ))

structure IsRegConst (a θ : ChartForm p σ d) (Ψ : CxPts p σ → ℝ → ℝ) (A K δ : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  K_nonneg : 0 ≤ K
  δ_pos : 0 < δ
  smooth : ∀ c : AlgChart p σ d, ContDiffOn ℝ ∞ (fun q : V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖)
    (c.e.target ×ˢ {w | 0 < ‖w‖ ∧ ‖w‖ < δ})
  mono : ∀ y, MonotoneOn (fun t => Ψ y t + K * t ^ 2) (Ioo 0 δ)
  hess : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < δ → ∀ (ξ : V d) (η : ℂ),
    -(A * (‖w‖ * deriv (fun t => Ψ y t + K * t ^ 2) ‖w‖) * a c y ξ.ofLp) -
        K * (‖w‖ ^ 2 * a c y ξ.ofLp + √(a c y ξ.ofLp) * ‖η‖ + ‖η‖ ^ 2) ≤
      θ c y ξ.ofLp + (leviForm (fun q : V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖) (c.e y, w) (ξ, η) (ξ, η)).re / Real.pi

variable {a : ChartForm p σ d} {E : ChartMap p σ d} {R : AnRead p σ d}

variable [SmoothOfRelativeDimension d p]

def rho (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → ℝ) (y : CxPts p σ) (t : ℝ) : ℝ :=
  rhoIn a E ψ (AlgChart.exists_mem_source (D := d) y).choose y t



end Manifold

end GlobalTheory.ChernReg
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordAtConstMulIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier
open GlobalTheory.ShFam.Descent GlobalTheory.FlatLine

namespace GlobalTheory.ShFam.Pad

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Frame

variable (Z : Model Xo c β) {R : Type} [CommRing R] [Algebra c.F R] (P : FrPt Xo c R)

def frameOf : EigFrame Z (algebraMap c.F R) (GlobalTheory.AllWt.ptF P ≫ Z.j) := (exists_tie_frame P rfl).choose

variable {Z P}

end Frame

variable {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

def CoordAt {k : Type} [Field k] [Algebra c.F k] (P : FrPt Xo c k) (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : k) : Prop :=
  ∃ p : Sp k ⟶ Y.Y.X, p ≫ Y.π = GlobalTheory.AllWt.ptF P ≫ Z.jQ ∧ IsCoord Y p (frameOf Z P) n σ a

def CoordAtC {ι : c.F →+* ℂ} (P : FrPt Xo c (CAt ι)) (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : ℂ) : Prop :=
  letI := ι.toAlgebra; CoordAt (k := ℂ) Y P n σ a

variable {Y}

variable {r : ℕ}

end Free

end GlobalTheory.ShFam.Pad
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ImaginaryRootNeZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.Pad.LineTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)


variable {Dw} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

variable {D : D7} {A : Amb D}

end GlobalTheory.ShFam.Pad.LineTest
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM

namespace GlobalTheory.ShFam.Pad

structure FinLB (X : Scheme.{0}) : Type where
  n : ℕ
  U : Fin n → X.Opens
  g : ∀ i k, Γ(X, U i ⊓ U k)ˣ
  isLB : LB.IsLB ⟨Fin n, U, g⟩

abbrev FinLB.lb {X : Scheme.{0}} (L : FinLB X) : LB X := ⟨Fin L.n, L.U, L.g⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure LineModel (Z : Mdl Y i₀) (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Letter Dw) : Type where
  L : FinLB Z.X
  r : ∀ (a : Fin Z.m) (i : Fin L.n), Γ(Z.X, (Z.U a).1 ⊓ L.U i)ˣ
  trans : ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a i i', ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ (L.U i ⊓ L.U i')) →
    valF w _ (r a i').val = valF w _ (L.g i i').val * valF w _ (r a i).val
  chart : ∀ (k : Type) [Field k] a a' i (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k)
    (cf : Fin (Dw.mult x.1) → k), spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a' →
    ⊤ ≤ (spMap φ ≫ Z.chart a) ⁻¹ᵁ L.U i → (∀ m, x.2 < m → cf m = 0) →
    IsCombAtG (Y Z.i).t (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ x.1) cf ((Z.fr a').bc φ' x.1 x.2) →
    valF (spMap φ ≫ Z.chart a) _ (r a i).val = valF (spMap φ ≫ Z.chart a) _ (r a' i).val * cf x.2
  norm : ∀ (y : Z.Pt) a i (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S), spMap φ ≫ Z.chart a = y.gen → ⊤ ≤ y.z ⁻¹ᵁ L.U i →
    Real.log ‖valF y.gen _ (r a i).val‖ + lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p b st = 0

structure admitted (Y : LocalSystem Xo p W) (i₀ : Idx H p) : Type where
  Z : Mdl Y i₀
  full : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ
  n : ℕ
  lvl : Z.i.l.M = i₀.l.M ∧ Z.i.l.Mb = i₀.l.Mb ∧ Z.i.l.A = i₀.l.A * p ^ n
  line : ∀ (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Letter Dw), letterOf Dw st = some x → LineModel Z b st x

variable {D : D7}


open Classical in
def placeW (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p) (jc : DV.KW p →+* ℂ) : ValuationSubring ℂ :=
  Classical.epsilon fun W => (∀ x : D.what₂.LL, D.what₂.embLL x ∈ W ↔ la.1.valuation D.what₂.LL x ≤ 1) ∧
    ∀ a : DV.KW p, jc a ∈ W ↔ a ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range

abbrev AdmAt {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A) {p : ℕ} (hp : p.Prime) {W : ValuationSubring ℂ}
    (hW : (p : ℂ) ∈ W.nonunits) : Type :=
  admitted (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩

def AdmEx {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A) : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (n : ℕ),
    1 + 1 / ((p : ℝ) - 1) < n → ∃ z : AdmAt S κ hp hW, z.n = n

end GlobalTheory.ShFam.Pad
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemMaximalIdealBall
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Cht

section Ball

variable {C : Type} [NormedField C] [IsUltrametricDist C]

end Ball

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure PtAt (Z : Mdl Y i₀) (C : SCF p) : Type where
  P : PointsOfFlagModel.PtC (Y Z.i) C
  z : Sp ↥(intO ↥C.S) ⟶ Z.X
  z_π : z ≫ Z.π = P.yt

namespace PtAt

variable {Z : Mdl Y i₀} {C : SCF p} (y : PtAt Z C)

def gen : Sp ↥C.S ⟶ Z.X := spMap (intO ↥C.S).subtype ≫ y.z

end PtAt

structure Fam (Y : LocalSystem Xo p W) (i₀ : Idx H p) (C : SCF p) : Type where
  pt : ∀ Z : Mdl Y i₀, PtAt Z C
  compat : ∀ Z₁ Z₂ : Mdl Y i₀, Corr Z₁ Z₂ → NatImg Z₁ Z₂ (pt Z₁).gen (pt Z₂).gen

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

abbrev idx0 (ct : At S κ p) : Idx A.H p := ⟨κ.l, κ.c, κ.good p ct.hp⟩

structure DVP (ct : At S κ p) : Type where
  C : SCF p
  K : Subfield ↥C.S
  closed : IsClosed (K : Set ↥C.S)
  dvr : IsDiscreteValuationRing ↥(intO ↥K)
  dense : Dense {x : ↥C.S | IsAlgebraic ↥K x}
  fam : Fam ct.Y (idx0 ct) C
  rat : ∃ w : Sp ↥K ⟶ ct.YY.X, spMap K.subtype ≫ w = (fam.pt ct.YY).gen

variable {ct : At S κ p}

structure Ext (y : DVP ct) : Type where
  L : Subfield ↥y.C.S
  le : y.K ≤ L
  fin : (Subfield.inclusion le).Finite
  π : ↥(intO ↥L)
  irr : Irreducible π

variable {y : DVP ct}

variable {Z : ct.Mdl} {e : Ext y}

end GlobalTheory.LocM.Cht
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RankOneBaseWeightEqCmTheta
section
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

section Dim

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

theorem generic_dim (A : DatAt Y P) : A.U.A.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
  have := A.t.semi.smooth
  have := A.t.semi.geomConnected
  have d₀ : SmoothOfRelativeDimension (0 + A.U.A.g) (pullback.snd A.t.G.hom (Out.jK A.R)) := by
    have := A.U.A.smoothDim
    have : IsIso A.U.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map A.U.U.gen.hom))
    rw [show pullback.snd A.t.G.hom (Out.jK A.R) = A.U.U.gen.hom.left ≫ A.U.A.A.hom from (Over.w A.U.U.gen.hom).symm]
    infer_instance
  have d₁ := GenericDim.smoothOfRelativeDimension_of_generic A.R A.t.G _ d₀
  have e : spMap (DatAtCheck.fC A) ≫ A.ι = P.y ≫ Y.jQ ≫ pullback.fst _ _ := by
    refine Eq.trans ?_ P.ext
    rw [← A.fac, ← Category.assoc]
    exact congrArg (· ≫ A.ι) (Spec.map_comp (CommRingCat.ofHom A.f) (CommRingCat.ofHom (intO ↥C.S).subtype))
  have p₁ := (IsPullback.of_hasPullback A.t.G.hom (spMap (DatAtCheck.fC A))).paste_horiz A.m.cart.1
  have p₂ := (IsPullback.of_hasPullback Y.oF.t.G.hom P.y).paste_horiz Y.m.cart.1
  rw [e] at p₁
  have d₂ : SmoothOfRelativeDimension (0 + A.U.A.g) (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) d₁
  have d₃ : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (pullback.snd Y.oF.t.G.hom P.y) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      (ObjDim.smoothOfRelativeDimension Y.oF)
  have d₄ : SmoothOfRelativeDimension (0 + Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))) := by
    rw [← p₁.isoIsPullback_hom_snd _ _ p₂]
    infer_instance
  have : Surjective A.t.G.hom := inferInstance
  obtain ⟨x, -⟩ := (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))).surjective (Per.gen ↥C.S)
  simpa using H1.dim_unique _ d₂ d₄ x

theorem dim_add_rank (A : DatAt Y P) :
    A.U.D.toPre.P.g + Module.finrank ℤ A.Ylat = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
  have h := UT.dim_eq_rank_add_dim firstFiveLaws A.R _ ⟨A.noeth, inferInstance, A.normal, A.complete⟩ A.U.D A.U.A A.t.G
    A.t.semi A.U.U
  rw [← generic_dim A, add_comm]
  exact h.symm

end Dim

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem finrank_host_eq (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

theorem complexConj_eq_conj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

namespace At

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z)

def beLin : ct.Ylat y →ₗ[ℤ] ct.Ylat y →ₗ[ℤ] ℝ := (ct.dat y).beLin (PointLawsEdge.betaAdd _ p)

def evidence : Per.Reading (ct.dat y) := (Per.nonempty_reading ct.hp.one_lt (ct.dat y)).some

def tauVal (a : ct.Ylat y) (χ : ct.chX y) : ((ct.fld y).C)ˣ := (ct.evidence y).t a ((ct.phi y).symm χ)

def lineShift (a : ct.Ylat y) : ct.chX y := ct.phi y a

def mulFst (a b : ct.Ylat y) : ct.chX y := ct.lineShift y (a + b) - ct.lineShift y a

def mulSnd (a b : ct.Ylat y) : ct.chX y := ct.lineShift y (a + b) - ct.lineShift y b

def mulConst (a b : ct.Ylat y) : ((ct.fld y).C)ˣ :=
  Exists.choose (p := fun t : (↥y.C.S)ˣ => Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) (t : ↥y.C.S))
    ⟨(ct.evidence y).t a b, (ct.evidence y).isVal a b⟩

def abDim : ℕ := (ct.dat y).U.D.toPre.P.g

theorem isTauVal_mulConst (a b : ct.Ylat y) :
    Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) ((ct.mulConst y a b : ((ct.fld y).C)ˣ) : (ct.fld y).C) :=
  Exists.choose_spec (p := fun t : (↥y.C.S)ˣ => Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) (t : ↥y.C.S)) _

theorem mulFst_eq (a b : ct.Ylat y) : ct.mulFst y a b = ct.phi y b := by
  rw [mulFst, lineShift, lineShift, map_add (f := _), add_sub_cancel_left]

theorem mulSnd_eq (a b : ct.Ylat y) : ct.mulSnd y a b = ct.phi y a := by
  rw [mulSnd, lineShift, lineShift, map_add (f := _), add_sub_cancel_right]

theorem mulConst_eq (a b : ct.Ylat y) : ct.mulConst y a b = ct.tauVal y a (ct.phi y b) :=
  Units.ext ((ct.evidence y).eq_of_isTauVal (ct.isTauVal_mulConst y a b))

theorem abDim_add : ct.abDim y + Module.finrank ℤ (ct.Ylat y) = D.R.f * N := by
  have h := dim_add_rank (ct.dat y)
  rw [finrank_host_eq, S.rank_eq, Nat.mul_div_cancel_left _ two_pos] at h
  exact h

end At

def motTrue (ct : At S κ p) : MotSt ct where
  be y := ct.beLin y
  be_symm y a b := (ct.dat y).beta_symm a b
  be_bal y c c' h a b := PointLawsEdge.betaBal _ p _ _ (ct.dat y) c c' (h.trans (complexConj_eq_conj D _).symm) a b
  be_posDef y := PointLawsEdge.betaPosDef _ ct.hp.one_lt _ _ (ct.dat y)
  yl_rank y := by
    obtain ⟨ρ, h₁, h₂, h₃⟩ := PointLawsEdge.rank_le (ct.dat y)
    rw [finrank_host_eq, Nat.mul_div_cancel_left _ two_pos] at h₁
    have := S.p_eq
    have := S.rank_eq
    exact ⟨ρ, h₁, fun _ _ => by omega⟩
  psiV y a := vU p (ct.mulConst y a (w0 D • a))
  tau y := ct.tauVal y
  tau_add_left y a a' χ := (ct.evidence y).add_left a a' _
  tau_add_right y a χ χ' := (ct.evidence y).add_right a χ χ'
  tau_symm y a b := (ct.evidence y).symm a b
  tau_smul y c a χ := (ct.evidence y).bal c a χ
  be_tau y a b := (ct.evidence y).beta_eq a b
  multiplicationLatticeFirst y := ct.mulFst y
  multiplicationLatticeSecond y := ct.mulSnd y
  mulC y := ct.mulConst y
  psiV_def _ _ := rfl
  dimB y := ct.abDim y
  dimB_add y := ct.abDim_add y
  be_eq _ _ _ := rfl

section Api

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z)

theorem motTrue_mul (a b : ct.Ylat y) : (motTrue ct).multiplicationLatticeFirst y a b = ct.phi y b ∧ (motTrue ct).multiplicationLatticeSecond y a b = ct.phi y a ∧
    (motTrue ct).mulC y a b = (motTrue ct).tau y a (ct.phi y b) :=
  ⟨ct.mulFst_eq y a b, ct.mulSnd_eq y a b, ct.mulConst_eq y a b⟩

theorem motTrue_psiV_eq_be (a : ct.Ylat y) : (motTrue ct).psiV y a = (motTrue ct).be y a (w0 D • a) := by
  rw [(motTrue ct).psiV_def, (motTrue_mul ct y _ _).2.2, (motTrue ct).be_tau]

theorem motTrue_psiV_half (a : ct.Ylat y) : (motTrue ct).psiV y a = (motTrue ct).be y a a / 2 := by
  have h := (motTrue ct).be_bal y (w0 D) (1 - w0 D) (one_sub_halfSqrt_eq_conj D) a a
  rw [sub_smul, one_smul, map_sub, (motTrue ct).be_symm y (w0 D • a)] at h
  rw [motTrue_psiV_eq_be]
  linarith

end Api

end GlobalTheory.LocM
end
end

