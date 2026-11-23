module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0016
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PrimUniqPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameTwistCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (CZ)
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix

attribute [local instance] Over.cartesianMonoidalCategory

section Series

open MvPowerSeries

variable {S : Type} [CommRing S]

variable {n d : ℕ}

variable {c : Fin d → Fin d → S} {P Q : Pt S n d}

variable [Algebra ℚ S]



omit [Algebra ℚ S] in
theorem cc_pt (j : Fin n) (i : Fin d) : constantCoeff (pt S d j i) = 0 := by
  simp [pt]


end Series

section Jets

open MvPolynomial

variable {S : Type} [CommRing S] {d : ℕ}

theorem jetSubstP_psJet {n n' : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    {a : Fin n → Pt S n' d} (ha : CZ a) (hφ : ∀ p, constantCoeff (φ p) = 0)
    (hmk : ∀ p : Fin n × Fin d,
      Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (φ p) = psJet m (a p.1 p.2))
    (f : PS S n d) : jetSubstP m φ (psJet m f) = psJet m (ev a f) := by
  rw [ev, FBIdJet.psJet_subst m _ (fun p => ha p.1 p.2) f]
  apply DFunLike.congr_fun
  refine GermD.jet_hom_ext fun p => ?_
  rw [GermD.jetMap_mk, aeval_X]
  simp only [jetSubstP, GermD.jetMap_mk, aeval_X, hφ p, map_zero, sub_zero]
  rw [hmk p]
  rfl

theorem mk_psIn_psJet {n' : ℕ} (m : ℕ) (k : Fin n') (f : PS S 1 d) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (psIn d m ![k] f) =
      psJet m (ev ![pt S d k] f) := by
  have e : (![pt S d k] : Fin 1 → Pt S n' d) = fun i => pt S d ((![k] : Fin 1 → Fin n') i) := by
    funext i; fin_cases i; rfl
  rw [e, FBIdPh.psJet_ev_rel, psIn, FBIdPh.mk_rename]
  apply DFunLike.congr_fun
  refine GermD.jet_hom_ext fun p => ?_
  rw [GermD.jetMap_mk, aeval_X]
  simp only [jetSubstP, GermD.jetMap_mk, aeval_X, FBIdPh.rel, constantCoeff_X, map_zero, sub_zero]

theorem cz_left {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    CZ (![comp1 φ (pt S d 0), pt S d 1] : Fin 2 → Pt S 2 d) := by
  intro j i
  fin_cases j
  · exact (TB.LogPf.cc_ev TB.LogPf.czX _).trans (hφ i)
  · exact cc_pt _ i

theorem cz_right {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    CZ (![pt S d 0, comp1 φ (pt S d 1)] : Fin 2 → Pt S 2 d) := by
  intro j i
  fin_cases j
  · exact cc_pt _ i
  · exact (TB.LogPf.cc_ev TB.LogPf.czY _).trans (hφ i)

theorem jetSubstP_left (m : ℕ) {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (f : PS S 2 d) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0] (φ j), fun j => X ((1 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m f) =
      psJet m (ev (n := 2) ![comp1 φ (pt S d 0), pt S d 1] f) := by
  refine jetSubstP_psJet m _ (cz_left hφ) ?_ ?_ f
  · rintro ⟨i, j⟩
    fin_cases i
    · exact (FBIdPh.cc_psIn d m _ _).trans (hφ j)
    · simp
  · rintro ⟨i, j⟩
    fin_cases i
    · exact mk_psIn_psJet m 0 (φ j)
    · exact (FBIdSy.mk_psTrunc_X m _).symm

theorem jetSubstP_right (m : ℕ) {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (f : PS S 2 d) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (φ j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m f) =
      psJet m (ev (n := 2) ![pt S d 0, comp1 φ (pt S d 1)] f) := by
  refine jetSubstP_psJet m _ (cz_right hφ) ?_ ?_ f
  · rintro ⟨i, j⟩
    fin_cases i
    · simp
    · exact (FBIdPh.cc_psIn d m _ _).trans (hφ j)
  · rintro ⟨i, j⟩
    fin_cases i
    · exact (FBIdSy.mk_psTrunc_X m _).symm
    · exact mk_psIn_psJet m 1 (φ j)

variable [Algebra ℚ S]

end Jets

section Frames

open MvPolynomial (X)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} {d : ℕ}
variable {x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G}

variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S} {sy : MvPowerSeries (Fin 2 × Fin d) S}
  {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S} {e e' : ∀ m, FrTy y d x m}

end Frames

section Clauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)]
variable (y : FrPt Xo c S) (C : ChartAt Xo c y)

end Clauses

end GlobalTheory.FrameTwistCompare
