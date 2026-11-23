module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldBC

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l}

@[reducible] def resAlg (hle : c.F ≤ c'.F) (S : Type) [CommRing S] [Algebra c'.F S] : Algebra c.F S :=
  ((algebraMap c'.F S).comp (incF c c' hle)).toAlgebra

def nabBC (hle : c.F ≤ c'.F) (nab : NabV Xo c) : NabV Xo c' :=
  fun {S} _ _ y k F α => letI := resAlg hle S; nab (y.res hle (fun _ => rfl)) k F α

def rulBC (hle : c.F ≤ c'.F) (f : Rul Xo c) : Rul Xo c' :=
  fun p y => letI := resAlg hle p.R; evR Xo c f (y.res hle (fun _ => rfl))

def covCoeff (hle : c.F ≤ c'.F) {n : ℕ} (d : DeltaDat Xo c n) : Coeff d.l₂ where
  F := c'.F
  fin := c'.fin
  conj := c'.conj
  zeta_mem := (d.hF.le.trans hle) d.c₂.zeta_mem
  le := d.c₂.le.trans (d.hF.le.trans hle)

theorem le_covCoeff (hle : c.F ≤ c'.F) {n : ℕ} (d : DeltaDat Xo c n) : d.c₂.F ≤ (covCoeff hle d).F :=
  d.hF.le.trans hle

def ddBC (hle : c.F ≤ c'.F) {n : ℕ} (d : DeltaDat Xo c n) : DeltaDat Xo c' n where
  pd := d.pd
  I := d.I
  l₂ := d.l₂
  Xo₂ := d.Xo₂
  c₂ := covCoeff hle d
  hF := rfl
  r := d.r
  m := d.m
  nab₂ := nabBC (le_covCoeff hle d) d.nab₂
  cδ := rulBC (le_covCoeff hle d) d.cδ
  φδ := fun q => incF c c' hle (d.φδ q)

def IoOver (hle : c.F ≤ c'.F) {n : ℕ} {Ix : Type} [Fintype Ix] (lam : Ix → Formalism.BasicNotions.DomWeight n)
    (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (io' : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F) : Prop :=
  ∀ (v : VVc c lam) (v' : VVc c' lam),
    (v' : Formalism.L2.DIV.Pol c'.F Ix n) = MvPolynomial.map (incF c c' hle) (v : Formalism.L2.DIV.Pol c.F Ix n) →
      io' v' = MvPolynomial.map (incF c c' hle) (io v)

end GlobalTheory.FieldBC
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
section
noncomputable section

namespace GlobalTheory.RunIn

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

variable {D : D7}

def sOf (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {j : ℕ} (w : WeightFamilies.Wt D j) : 𝓞 B.KO :=
  nnW B hinj EX w * (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : 𝓞 B.KO)

theorem sW_eq_sOf (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) {j : ℕ}
    (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) : (scalOfP B hinj EX p ka wL wF T).sW = sOf B hinj EX wL := rfl

def ThInt {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (hinj : Function.Injective D.what₂.OtoLL)
    (EX : ErrX D) (w : WeightFamilies.Wt D j) : Prop :=
  X.WWc (sOf B hinj EX w) w ≤ B.Mlat j w

structure SecNorm (B : WeightFamilies.Prov D) where
  N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ
  h0 : ∀ j ka σ F, 0 ≤ N j ka σ F
  h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0
  h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F
  h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G
  h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F

def SecNorm.sup (B : WeightFamilies.Prov D) : SecNorm B :=
  ⟨B.supN, B.supN_nonneg, B.supN_eq_zero, B.supN_smul, B.supN_add, fun _ _ _ _ => le_rfl⟩

abbrev SecNorm.base {B : WeightFamilies.Prov D} (n : SecNorm B) : WeightFamilies.Prov D := withNorm B n.N n.h0 n.h1 n.h2 n.h3 n.h4

def recPlusN {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) :
    PJ D n.base T.G.P j :=
  PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (recPlus h j hj)

end GlobalTheory.RunIn
end
end

