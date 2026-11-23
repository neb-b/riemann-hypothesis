module

public import Formalism.PeriodIntegrals.OrbJetBase
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbAddOne
section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G

variable {D : D7}

def OrbitsAddAtConjugate (E : Ent D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p), nP D p = 1 → ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m →
    ∀ β : Pl D → ℝ, (∀ z, OneGe E p h5 u i z (β z)) →
    ∀ Th, ThetaExpansionRealPlaces D p Th → OJ.KvalGe (D.R.N i) (D.R.N (i + 1)) p (E.nu u i) Th (∑ z, β z)

end PI.OrbJet

end
end

-- bundled from Formalism.PeriodIntegrals.OrbAddUp
section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G

variable {D : D7}

def OrbitsAddLowerBound (E : Ent D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ R : Finset (Pl D), IsReps D p R →
    ∀ (ep : ℂ_[p]) (sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]), BeOK D p R ep sg be →
    ∀ β : Pl D → ℝ, (∀ r ∈ R, OrbGe E p h u i r ep (sg r) (be r) (β r)) →
    ∀ Th, ThetaExpansionAllPlaces D p R ep sg be Th → OJ.KvalGe (D.R.N i) (D.R.N (i + 1)) p (E.nu u i) Th (∑ r ∈ R, β r)

end PI.OrbJet

end
end

-- bundled from Formalism.PeriodIntegrals.OrbRestr
section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G

variable {D : D7}

def OrbitRestriction (E : Ent D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (R : Finset (Pl D)), IsReps D p R →
    ∀ (ep : ℂ_[p]) (sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]), BeOK D p R ep sg be →
    ∀ Th, ThetaExpansionAllPlaces D p R ep sg be Th → ∀ r ∈ R, OrbitThetaExpansion (orbLoc E p h u i r (restr D p r Th)) ep (sg r) (be r)

end PI.OrbJet

end
end

-- bundled from Formalism.PeriodIntegrals.OrbRestrOne
section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G

variable {D : D7}

def OrbitRestrictionAtConjugate (E : Ent D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p), nP D p = 1 → ∀ (u : D.what₂.Word) (i : ℕ),
    ∀ Th, ThetaExpansionRealPlaces D p Th → ∀ z, (oneLoc E p h5 u i z (restr1 D p z Th)).AdmB

end PI.OrbJet

end
end

-- bundled from Formalism.PeriodIntegrals.SzCt
section
noncomputable section

namespace PI.SzCt

open Formalism.BasicNotions Formalism.MainNotions.G

def Uni (eps Ct CGam Cc CT2 : ℝ) (PK : List ℝ) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) : Prop :=
  L.sc.eps = eps ∧ L.Ct = Ct ∧ L.CGam = CGam ∧ L.Cc = Cc ∧ D.host.CT2 = CT2 ∧
    [P.CkLow, P.Ck6, P.CfL, P.cLL, P.CnW, P.Crho, P.CDelG, P.CLw,
      P.Cj0, P.Cw, P.cw, P.CDel, P.CCount, P.Ch0r, P.Ch0k, P.Ch0N,
      P.Cgap, P.CetaF, P.CY, P.CYL, P.Cpde, P.CccK, P.CF] = PK

def SzCt : Prop :=
  ∀ (eps Ct CGam Cc CT2 : ℝ) (PK : List ℝ), ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L),
    Uni eps Ct CGam Cc CT2 PK D L P → x0 ≤ L.sc.x → Formalism.MainNotions.SizesAt L →
    ∀ j ∈ SizeData₂.lifts D, ∀ u : D.what₂.Word,
      ∑ t : HH D, ctD D u j t ≤ 2 * (D.host.TT.card : ℝ) * L.sc.b + 2 * (D.R.f : ℝ) * D.R.k * L.sc.b'

end PI.SzCt
end
end

-- bundled from Formalism.PeriodIntegrals.SzEatI
section
noncomputable section

namespace PI.SzEatI

open Formalism.BasicNotions Formalism.MainNotions.G

def Uni (eps Ct CGam Cc CT2 : ℝ) (PK : List ℝ) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) : Prop :=
  L.sc.eps = eps ∧ L.Ct = Ct ∧ L.CGam = CGam ∧ L.Cc = Cc ∧ D.host.CT2 = CT2 ∧
    [P.CkLow, P.Ck6, P.CfL, P.cLL, P.CnW, P.Crho, P.CDelG, P.CLw,
      P.Cj0, P.Cw, P.cw, P.CDel, P.CCount, P.Ch0r, P.Ch0k, P.Ch0N,
      P.Cgap, P.CetaF, P.CY, P.CYL, P.Cpde, P.CccK, P.CF] = PK

def SzEatI : Prop :=
  ∀ (K : Consts) (ce : ErrC) (eps Ct CGam Cc CT2 : ℝ) (PK : List ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∃ x0 : ℝ,
    ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L),
    Uni eps Ct CGam Cc CT2 PK D L P → x0 ≤ L.sc.x → Formalism.MainNotions.SizesAt L →
    ∀ j ∈ SizeData₂.lifts D, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ (IsResidueClassZero D p ∨ IsSg D p) ∧ ¬ (IsResidueClassZero D p ∧ hP D p = 0) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) →
      ∑ p ∈ S, Real.log p * (EatI L K ce j p - max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ))) ≤
        C * (D.R.f : ℝ) * L.sc.b * Real.log (L.sc.X'' D.R.n)

end PI.SzEatI
end
end

