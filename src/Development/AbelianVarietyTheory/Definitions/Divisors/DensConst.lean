module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.CechPic

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

structure MLine (p : X ⟶ Sp k) (σ : k →+* ℂ) where

  B : LB X

  φ : Weight p σ B

  cInf : φ.IsCInf

namespace MLine

def ofHerm (L : HermLB p) (σ : k →+* ℂ) : MLine p σ := ⟨L.B, L.φ σ, L.cInf σ⟩

def tens (A B : MLine p σ) : MLine p σ := ⟨CechPic.tens A.B B.B, A.φ.tens B.φ, A.cInf.tens B.cInf⟩

def pull (A : MLine p σ) {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) : MLine q σ :=
  ⟨A.B.pull π, A.φ.pull π hπ, A.cInf.pull π hπ⟩

def ofFun (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) : MLine p σ :=
  ⟨LB.triv X, Weight.ofFun u, Weight.isCInf_ofFun hu⟩

def addFn (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) : MLine p σ :=
  ⟨A.B, A.φ.addFn u, A.cInf.addFn hu⟩

def Isom (L M : MLine p σ) : Prop :=
  ∃ w : LB.Iso L.B M.B, w.IsGen ∧ ∀ (a : M.B.ι) (b : L.B.ι) (y : CxPts p σ),
    y ∈ ptsIn p σ (M.B.U a) → y ∈ ptsIn p σ (L.B.U b) →
      M.φ.φ a y = L.φ.φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2)

def logSec (M : MLine p σ) (s : M.B.Sec) (y : CxPts p σ) : ℝ := Real.log (M.φ.nsq (secVal p σ s) y) / 2

end MLine

abbrev ptMap {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (σ : k →+* ℂ) : CxPts q σ → CxPts p σ :=
  PtsOver.map π hπ (spMap σ)

def dens (L : Fin D → MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) : ℝ :=
  (Real.pi ^ D)⁻¹ * (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l =>
    c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB y) y j l).det).re

def part (L : Fin D → MLine p σ) (ε : ℤˣ) : Measure (CxPts p σ) :=
  glueMeas (fun c : AlgChart p σ D => c.e) fun c y => ENNReal.ofReal ((ε : ℤ) * dens L c y)

def Intg (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : Prop := Integrable f (part L 1) ∧ Integrable f (part L (-1))

def int (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : ℝ := ∫ y, f y ∂part L 1 - ∫ y, f y ∂part L (-1)

def clos (z : X) : Scheme.{0} := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subscheme

def closι (z : X) : clos z ⟶ X := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι

instance (z : X) : IsClosedImmersion (closι z) :=
  inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι)

def CycIntg (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) (z : X) : Prop :=
  Intg (fun i => (L i).pull (closι z) rfl) fun y => f (ptMap (closι z) rfl σ y)

def cycInt (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) (z : X) : ℝ :=
  int (fun i => (L i).pull (closι z) rfl) fun y => f (ptMap (closι z) rfl σ y)

def side [IsIntegral X] [IsLocallyNoetherian X] (N : MLine p σ) (L : Fin D → MLine p σ) (f g : CxPts p σ → ℝ)
    (Δ : CartierDiv X) : ℝ :=
  int (Fin.cons N L : Fin (D + 1) → MLine p σ) f + ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L g z

theorem dens_const (N : MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) :
    dens (fun _ => N) c y = c.chernDens N.φ y := by
  have e : (Matrix.of fun j l => c.hess N.φ (pick N.φ.isLB y) y j l) = c.hess N.φ (pick N.φ.isLB y) y := rfl
  simp only [dens, AlgChart.chernDens, e, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
  ring

theorem part_const (N : MLine p σ) (ε : ℤˣ) : part (fun _ : Fin D => N) ε = N.φ.chernPart D ε := by
  simp only [part, Weight.chernPart, dens_const]

section Generic

variable (t : X ⟶ Sp ℤ)

variable {t}

end Generic

end GlobalTheory.Mix
