module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridge
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CoeffMemOfLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
section
noncomputable section

namespace GlobalTheory.ArcCM

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM

variable {D : D7}

def nAt (D : D7) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : ℕ :=
  nQ D.host.E D.R.r (D.host.g 0 * D.host.g 1) (discr D.host.E).natAbs (Ideal.absNorm D.host.ccK)
    (WeightFamilies.c1 D CR Tt cc j) (ka.size + D.R.r)

def LaAt (D : D7) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : ℝ :=
  LaQ D.host.E D.R.r (D.R.sigW j).2 (D.host.g 0 * D.host.g 1) (discr D.host.E).natAbs (Ideal.absNorm D.host.ccK)
    (WeightFamilies.c1 D CR Tt cc j) (ka.size + D.R.r)

def FamQ (T : Core D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (K₁ : Type) [Field K₁] [NumberField K₁]
    [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) : Prop :=
  Fam (nAt D j ka CR Tt cc) (LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j) d

def KillQ {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : Prop :=
  ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁),
    FamQ T j ka CR Tt cc K₁ d →
      ∀ F : (recB h).Cusp j ka, F ∈ WeightFamilies.MggK (recB h) CR Tt cc j ka → cfOf d.yF d.μ d.jj F.1 = 0

def DetectQ {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : Prop :=
  ∀ F : (recB h).Cusp j ka,
    (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁),
      FamQ T j ka CR Tt cc K₁ d → cfOf d.yF d.μ d.jj F.1 = 0) → F ∈ WeightFamilies.MggK (recB h) CR Tt cc j ka

def CarchAt (D : D7) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : ℝ :=
  4 * Real.pi + archP D.host.E D.R.r (LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j) * ka.size

def BdegAt (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : ℝ :=
  (pDeg large₂.logOm + (1 / 2) * Real.log (LaAt D j ka CR Tt cc)) * ka.size

def RoomAt (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc C A : ℝ) : Prop :=
  CarchAt D j ka CR Tt cc ≤ WeightFamilies.PPv D large₂ C A * ka.size ∧ BdegAt large₂ j ka CR Tt cc ≤ WeightFamilies.PPv D large₂ C A * ka.size ∧
    Real.log |((discr D.host.E : ℤ) : ℝ)| + Real.log (nAt D j ka CR Tt cc) ≤ WeightFamilies.PPv D large₂ C A

end GlobalTheory.ArcCM
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PrimAn
section
noncomputable section

namespace GlobalTheory.ArcCM

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) [StarRing (𝓞 E)]

def AbDat (A : AnArc (𝓞 E)) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) : Prop :=
  (∀ a z i, A.F a z i = tyB i (a : E) * z i) ∧ IsTypeFn H DB.p DB.q tyB ∧
    (∀ (a : 𝓞 E) x, eB (a • x) = A.FLam a (eB x)) ∧ (∀ x x', DB.EF x x' = A.Ef (eB x) (eB x')) ∧
    IsPeriod DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom)

def PrimAn (A : AnArc (𝓞 E)) : Prop :=
  (∀ l, A.chi l = (-1) ^ A.Ef (A.FLam H.w0 l) l) ∧ ∀ x, (A.psi x : ℂ) = eTwoPi (A.T x (H.w0 • x))


omit [IsCMField E] [NumberField E] in
def NormAn (A : AnArc (𝓞 E)) (n : ℕ) : Prop :=
  (∀ y, n • A.ct y ∈ A.abelian₂) ∧
    ∀ y y', eTwoPi (A.T (n • y) (n • y')) * Complex.exp (Real.pi * A.H (n • A.ct y) (n • A.ct y')) = 1

end GlobalTheory.ArcCM
end
end

