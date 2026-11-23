module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0061
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableIndicatorOfContOn
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightContDiffOn
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.CountAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormQuotientThetaFlatAttainsSupOffCommonZeros
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.QuotientNoPositiveMaxOffCommonZeros
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.Divisibility.Bundle0003
public import Formalism.PieriBlockIdeals.StatementE
public import Formalism.PieriBlockIdeals.Bundle0007
public import Formalism.SharpRestriction.Divisibility.JumpSets

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.RefSum

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {c : Coeff l} {p : ℕ} [Fact p.Prime]

def FacBetween (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) (A B : ℝ) : Prop :=
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io,
    (A : EReal) ≤ nuFac p y f k ∧ (y.IsAlg → nuFac p y f k ≤ (B : EReal))

def NuBetween (la : PointsOfFlagModel.abelian₂ p c) (cx : Lt1 Dw → ℕ) (A B : ℝ) : Prop :=
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io,
    (A : EReal) ≤ nuP p y cx ∧ (y.IsAlg → nuP p y cx ≤ (B : EReal))


variable (c p) in
def OscLe (cx : Lt1 Dw → ℕ) (b : ℝ) : Prop :=
  ∀ la : PointsOfFlagModel.abelian₂ p c, ∃ A : ℕ, NuBetween Xo la cx A (A + b)


variable (Dw) in
def nCol : ℕ := 8 * ((∑ f : Lt1 Dw, 2 * rk f) / 8 + Fintype.card (Lt1 Dw) + 1)


variable (Dw) in
def shift (u : Weight Dw) (n : ℕ) (τ : Psi H) : ℤ :=
  ((n / 2 : ℕ) : ℤ) + 1 - if h : 0 < Dw.p then u τ ⟨Dw.p - 1, by omega⟩ else 0


variable (Dw) in
def thA (u : Weight Dw) (n : ℕ) : (E →+* ℂ) × ℕ → ℕ :=
  fun x => ((wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ)).1 x).toNat

theorem eight_dvd_nCol : 8 ∣ nCol Dw := Dvd.intro _ rfl

theorem sum_le_nCol : ∑ f : Lt1 Dw, 2 * rk f ≤ nCol Dw := by
  unfold nCol; omega

theorem OscLe.mono {cx : Lt1 Dw → ℕ} {b b' : ℝ} (h : OscLe Xo c p cx b) (hb : b ≤ b') : OscLe Xo c p cx b' := fun la => by
  obtain ⟨A, hA⟩ := h la
  exact ⟨A, fun T io e ho y => ⟨(hA T io e ho y).1, fun ha => ((hA T io e ho y).2 ha).trans
    (EReal.coe_le_coe_iff.2 (by linarith))⟩⟩

def PrimeSum (S : Finset ℕ) (e : ℕ → ℝ) (s : ℝ) : Prop :=
  (∀ q ∈ S, q.Prime) ∧ (∀ q, 0 ≤ e q) ∧ (∀ q ∉ S, e q = 0) ∧ ∑ q ∈ S, e q * Real.log q ≤ s

end Free

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

abbrev aOf (u1 : Weight (dat p i)) : (D.host.E →+* ℂ) × ℕ → ℕ := thA (dat p i) u1 (nCol (dat p i))

abbrev GOf (u1 : Weight (dat p i)) : WTZ D.host.E := wtZ (aOf p i u1) (nCol (dat p i))

def SumAt (PP C : ℝ) (u1 : Weight (dat p i)) : Prop :=
  ∃ (S : Finset ℕ) (e : ℕ → ℝ) (s : ℝ), PrimeSum S e s ∧ lenT p i PP * s ≤ C * unitE p ∧
    ∀ (q : ℕ) [Fact q.Prime], (∀ k, q ≠ D.host.g k) →
      OscLe (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c q (gap (dat p i) (aOf p i u1)) (e q)

def RefAt {l : Level p.T.Q.H} {Xo : Moduli (dat p i) l} {c : Coeff l} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
    (G : WTZ D.host.E) (PP C : ℝ) : Prop :=
  ∃ (S : Finset ℕ) (e : ℕ → ℝ) (s : ℝ), PrimeSum S e s ∧ lenT p i PP * s ≤ C * unitE p ∧
    ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) G q ≤ (e q : EReal)

end Point

end GlobalTheory.RefSum

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

namespace GlobalTheory.ShareOn

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

def sub (M : TwoLevels E r U C) (H : Subgroup U) : TwoLevels E r H C :=
  { M with
    tr := fun u c => M.tr u c
    tr_herm := fun u => M.tr_herm u
    tr_Λ := fun u => M.tr_Λ u
    tr_L' := fun u => M.tr_L' u
    tr_conj := fun u => M.tr_conj u
    tr_mul := fun u v => M.tr_mul u v
    tr_faithful := fun u c h1 h2 => Subtype.ext (M.tr_faithful u c h1 h2) }

def IsPullRep (M : TwoLevels E r U C) (la : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp la)) : Prop :=
  ∃ a : U → C → ℂˣ, ∀ (h : U) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS la) (c : C) (x : M.dom),
    ((ρ h⁻¹ ⟨M.res F, Submodule.subset_span ⟨F, hF, rfl⟩⟩ : M.cusp la) : C → M.dom → ℂ) c x = (a h c : ℂ) * M.pull h F c x.1

def Ranks (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (s : ℕ) (ep c : ℝ) : Prop :=
  Module.Finite ℂ (M.cusp ka) ∧ Module.Finite ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 s)) ∧
    (1 - ep) * finrank ℂ (M.cusp ka) ≤ finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 s)) ∧
    (finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 s)) : ℝ) ≤ c * finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 s)) ∧
    Module.Finite ℂ (M.cusp (ka - deMul M.Ψ r M.p0 s))

def ArchOne (X : Data E r) (L Fp : Wt X.Ψ r) (T : ℕ) : Prop :=
  ∃ Xa : ArchInM X, Xa.L = L ∧ Xa.Fp = Fp ∧ Xa.T = T ∧ GlobalTheory.Shares.Margins X Xa ∧ Nonempty (FlatM X Xa)

def ArchOn (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (T : ℕ) : Prop :=
  ∃ L Fp : Wt M.Ψ r, ka = Fp + T • L ∧ GapsGe M.p0 L 1 ∧ PairGe L (1.9 * T) ∧
    GapsGe M.p0 (Fp - kLog M.Ψ r - (M.dimY + 2) • L) 0 ∧ PairGe (Fp - kLog M.Ψ r - (M.dimY + 2) • L) 1 ∧
    ∀ c, ArchOne (M.comp c).toData (castWt (M.comp_Ψ c) L) (castWt (M.comp_Ψ c) Fp) T

def sOf (M : TwoLevels E r U C) : ℕ := 2 * r + 50 * r ^ 2 * M.dimX + 2

theorem even_sOf (M : TwoLevels E r U C) : Even (sOf M) := ⟨r + 25 * (r ^ 2 * M.dimX) + 1, by unfold sOf; ring⟩

theorem le_sOf (M : TwoLevels E r U C) : 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ sOf M := Nat.le_succ _

end Model

section Point

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

def HalfUnip (H : Subgroup p.P.Gp) : Prop :=
  ∃ k : Fin 2, ∀ g ∈ H, ∀ v : D.nd.PlG k,
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp (((p.R.eG.trans p.cG) g ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))

def ModelAt (T : ℕ) : Prop :=
  ∃ (C : Type) (_ : Finite C) (_ : MulAction p.P.Gp C) (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r)
    (ρ : Representation ℂ p.P.Gp (M.cusp ka)) (σ : D.what₂.LL →+* ℂ)
    (f : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[σ] M.cusp ka),
    IsPullRep M ka ρ ∧ (∀ g v, ρ g (f v) = f ((p.R.toRealDat.FW i).ρ g v)) ∧
    (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ ∧
    (∀ H, HalfUnip p H → LevelHyp (sub M H)) ∧ M.Ψ.card = D.R.f ∧
    ((M.p0 = 0 ∨ M.p0 = D.R.r) ∨ (0 < M.p0 ∧ M.p0 < D.R.r ∧ ArchOn M ka T))

def ShareW (y : ℝ) : Prop :=
  (1 - y) * (p.R.toRealDat.nW i : ℝ) ≤ (Nat.card p.P.P0 : ℝ) * finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i)

def BadW (del : ℝ) : Prop :=
  (finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i ⊓ LinearMap.ker (eGood p.R.toRealDat i) : Submodule D.what₂.LL _) : ℝ) ≤
    del * finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i)

end Point

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

namespace GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

structure HostNum (D : D7) (L : SizeData₂ D) (PP A M : ℝ) : Prop where
  big : M ≤ L.sc.L ∧ 10 ≤ L.sc.L ∧ L.sc.L ≤ L.sc.x ∧ 1 ≤ Real.log (Real.log L.sc.x)
  f8 : 8 ≤ D.R.f
  deg : Module.finrank ℚ D.host.E = 2 * D.R.f
  logfr : Real.log ((D.R.f : ℝ) * D.R.r) ≤ L.sc.L ∧ Real.log (D.R.nV : ℝ) ≤ L.sc.L
  logg : ∀ k, Real.log (D.host.g k : ℝ) ≤ 9 * L.sc.L + 1
  disc : Real.log |(discr D.host.E : ℝ)| ≤ 4 * D.R.f * L.sc.L
  logd : Real.log (D.host.d : ℝ) ≤ L.sc.L
  split : 5 ≤ D.host.splitBound
  cop : Nat.Coprime 15 (D.host.g 0 * D.host.g 1)
  ppLow : zBase L ^ 12 ≤ PP
  poly : 1 ≤ A ∧ PP ≤ L.sc.x ^ A ∧ (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L ≤ L.sc.x ^ A
  room : (L.sc.x ^ A) ^ M ≤ L.sc.b
  low : Real.sqrt L.sc.b ≤ L.sc.w'' D.R.n

def wtsAt (PP : ℝ) (h0 : ℤ) (S eta : ℝ) (u1 : Weight (dat p i)) :
    GlobalTheory.MeanTop.Wts (Psi p.T.Q.H) ((dat p i).p + (dat p i).q) :=
  { kc := D.R.k - 1, p := (dat p i).p, T := lenT p i PP, Dd := dimFlag (dat p i), c0 := cZero D ((i : ℕ) + 1), h0 := h0, S := S,
    eta := eta, b := 4 * L.sc.b, w := fun τ => (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ), u := uW p i, u1 := u1 }

theorem quo_iff (PP : ℝ) (h0 : ℤ) (S eta : ℝ) (u1 : Weight (dat p i)) : Quo p i PP u1 ↔ (wtsAt p i PP h0 S eta u1).IsDiv :=
  Iff.rfl

structure WtNum (PP : ℝ) : Prop where
  sig : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1 ∧ (dat p i).q = (D.R.sigW ((i : ℕ) + 1)).2 ∧ (dat p i).p + (dat p i).q = D.R.r
  card : Nat.card (Psi p.T.Q.H) = D.R.f
  dim : dimFlag (dat p i) = D.R.f * D.R.r.choose 2
  cols : (p.κ i).n = D.R.nV
  dom : Dom (wtA (p.κ i)) (p.κ i).n
  unit : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x)
  om : |(ofRecord D L p.Del p.h0).logOm| ≤ 3 * L.sc.L
  up : ∀ τ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| ≤ 4 * L.sc.b
  low : ∀ τ, L.sc.w'' D.R.n ≤ 2 * (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)
  what₂ : PP ^ 2 * D.R.r * D.R.m * D.R.k * (dimFlag (dat p i) : ℝ) ^ 3 ≤ L.sc.b ∧
    PP * lenT p i PP * (dimFlag (dat p i) : ℝ) ^ 2 * L.sc.L ≤ L.sc.b
  hyp : (i : ℕ) + 1 < D.R.m → ∃ (h0 : ℤ) (S eta : ℝ), 0 ≤ S ∧ 0 ≤ eta ∧ PP * (S + eta) ≤ 100 * L.sc.w'' D.R.n ∧
    4 * (lenT p i PP : ℤ) ^ 2 ≤ h0 ∧
    PP * lenT p i PP * D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * dimFlag (dat p i) ≤ h0 ∧
    ∀ u1, (wtsAt p i PP h0 S eta u1).Hyp

def HostN (M : ℝ) : Prop := Lifts fun Fm x _ ι _ _ PP A => HostNum (Fm.D x ι) (Fm.L x ι) PP A M

def WtN : Prop := Lifts fun _ _ _ _ p i PP _ => WtNum p i PP

end GlobalTheory.CovTop

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts HidaSetting WInputsLink h0)

namespace GlobalTheory.ExpTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LIncl {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0)
    (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ) : Prop :=
  ∀ z ∈ B.cutZ ℓ Z, (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (B.delZ ℓ Z)

def Covers {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0)
    (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) {ι : Type} {N : ℕ} {lam : ι → ℕ → ℕ} {I : Type}
    (X : I → HidaSetting ι N lam) : Prop :=
  ∀ J : ℕ, (∀ i, (X i).Incl (Formalism.EigenvalueLevelCeiling.plc w) J) → LIncl B ℓ Z w J

def reFr {ι : Type} (W : Wts ι) (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) : Wts ι := { W with fr := fr, cj := cj }

variable {D : D7}

structure Dict (L : SizeData₂ D) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) : Prop where
  k : P.k = D.R.k
  m : P.m = D.R.m
  t : P.t = D.R.t
  f : P.f = D.R.f
  card : Nat.card D.what₂.Tau = P.f
  Nr : P.Nr = (Vc D j).rank
  x : P.x = L.sc.x
  log : P.L = L.sc.x ^ L.sc.eps
  b : P.b = L.sc.b
  lam : ∀ τ, ∃ c : ℤ, ∀ a : Fin (Vc D j).rank,
    (W.lam τ a : ℤ) = (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ).w a + c
  forced : ∀ τ, Formalism.IndefR.Bridge.IsLamPrime (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ
  box : ∀ τ a, a < P.Nr → 0 ≤ W.U P τ a ∧ W.U P τ a ≤ (h0 P : ℤ)
  thick : W.T2.card ≤ D.host.T2.card
  special : W.Sp = Formalism.MainNotions.JumpSetsAlt.excSet D
  big : ∀ i, P.h < (D.host.g i : ℝ)

def NumOk {ι : Type} (P : Par) (W : Wts ι) : Prop :=
  P.Hyp ∧ P.Large ∧ W.Ok P ∧ ∃ X' A : ℝ, Formalism.CohomologicalDescent.LargeParameterEstimates.Rows P X' A ∧ Formalism.CohomologicalDescent.LargeParameterEstimates.Big P.L P.x X' A

section Point

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

abbrev blk (j : Fin D.R.m) (t : p.P.T) := p.P.A3.A.fam.L j t

abbrev lvlL := p.P.A3.A.fam.lvlA p.P.P0 p.P.ψ0

abbrev subZ (j : Fin D.R.m) (t : p.P.T) : Submodule D.what₂.LL (blk p j t).S.Forms :=
  (p.P.A3.fam3.toSub2 (p.R.toCx3 p.F).zs).Zl j t


open Classical in
def ModelAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∃ (fr : ℕ → D.what₂.Tau → D.what₂.Tau) (cj : ℕ → D.what₂.Tau → Bool) (I : Type) (X : I → HidaSetting D.what₂.Tau P.Nr W.lam),
    Covers (blk p j (p.R.mu w)) (lvlL p) (subZ p j (p.R.mu w)) w X ∧
      ∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)

end Point


end GlobalTheory.ExpTie

end
end

