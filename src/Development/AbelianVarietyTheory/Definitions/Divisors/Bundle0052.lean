module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
public import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
public import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
public import Formalism.SharpRestriction.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB

namespace GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar

protected abbrev zsc {D : D7} {O : Obj D} (P : RowSideFamily O.ex) (Del h0 : ℕ) (c : ℝ) :
    DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3 :=
  GlobalTheory.Fc.zsc P Del h0 c


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Part (D : D7) (O : Obj D) (c : ℝ) : Type 1 where
  R : Formalism.L2.RecT O.ex
  S : Formalism.L2.SG.SpectralTiesReal.STiesR R
  P : RowSideFamily O.ex
  pin : RowSideDetermined R.T P
  DH : {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}
  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)
  ok1 : P.A3.fam3.Ok3 1
  B : RealTB R P Dcf Spf (GlobalTheory.Fc.zsc P DH.1.1 DH.1.2 c) S
  Rr : RealRec B.Q
  psi : PsiPPTie D P.P0 P.ψ0 P.Ps P.ψs P.I.eG
  pins : RealPins B.Q
  muDef : ∀ C CH : ℝ, (B.Q.Rl.toCx3 B.Q.F).MuDef B.Q.F.cr (B.Q.Rl.num B.Q.F C CH) B.Q.Rl.mu
  recPins : RealRecPins pins Rr

def PFire : BdP Part := fun _ _ _ b =>
  b.B.Q.Rl.toRealDat.ExAt ∧ JEvBar b.B.T b.B.Q.Rl.toRealDat b.B.κ ∧ GeoAct b.B.T b.B.Q.Rl.toRealDat b.B.κ b.B.v₀ ∧
    EvInj b.B.T b.B.Q.Rl.toRealDat b.B.v₀

def PRB : BdP Part := fun _ _ _ b => RowsB b.B

def PNmj : BdP Part := fun _ O _ b => NX.NMjT b.B.Q b.B.Q.cG b.B.Q.Sx b.B.Q.nexp O.ex.nch

def L3 (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).L3 (b.B.Q.Rl.num b.B.Q.F C CH)

def ON (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).ON (b.B.Q.Rl.num b.B.Q.F C CH)

def L6 (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr true).L6 (b.B.Q.Rl.num b.B.Q.F C CH)

def FUN (C CH : ℝ) : BdP Part := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).FUN (b.B.Q.Rl.num b.B.Q.F C CH)

variable {Bd : BdT}

def Ev {𝒜 : FamClass} (σ : RawSel Bd 𝒜) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (q : BdP Bd) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, q _ _ _ (σ Fm hc x hx i)

def EvW (q : BdP Bd) (𝒜 : FamClass) (σ : RawSel Bd 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∀ hc : W3 𝒜 Fm, Ev σ Fm (w3_a hc) q

def EvWC (prem : ∀ {eps : ℝ}, FamP eps → Prop) (q : ℝ → ℝ → BdP Bd) (𝒜 : FamClass) (σ : RawSel Bd 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm CH => ∀ hc : W3 𝒜 Fm, prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ev σ Fm (w3_a hc) (q C CH)

theorem ev_of_atAll {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {q : BdP Bd} (h : AtAll q 𝒜 σ) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) :
    Ev σ Fm hc q := ⟨0, fun x hx _ i => h Fm hc x hx i⟩

end GlobalTheory.Fc.Ind


end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.OfDat
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimIn

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {Tw : Top.TwDat X.B}
  {Wt : Set X.B.places.Pl}

theorem TiesG.of_dat (z : Dat X I hX Tw Wt) (hU : z.R.toRealDat.LUnif) (hI : IoExt z.R.toRealDat)
    (hM : ∀ i, OneMapRowR z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O (fun _ => 1) i)
    (hC : GlobalTheory.TwistField.CoverField z.core z.R.toRealDat) : TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O := by
  have e : (fun i => cj (twAt X.toD7.what₂.embLL (famR X I hX (usedOf I Tw Wt) z.Xg z.tr).A.v0) (z.R.phs i)) = fun _ => (1 : ℂ) := by
    funext i
    rw [z.pins.phs i]
    exact map_one _
  refine ⟨⟨z.geo.fw, z.geo.bar⟩, z.geo.pins, ?_, hU, hI, ?_, hC⟩
  · rw [e]; exact z.geo.phase
  · rw [e]; exact hM

end GlobalTheory.PrimIn

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
section
noncomputable section

namespace GlobalTheory.ThK.Inhab

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {X : Chars F E}

theorem pairV {a a' : ℕ} {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  (Check.isPair_of_isTriple h).1

theorem pairV' {a a' : ℕ} {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  (Check.isPair_of_isTriple h).2

theorem two_le_rank {a a' : ℕ} {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    2 ≤ a' ∧ a' < a := by
  have h1 := h.geo.aBig
  exact ⟨by omega, h.geo.lt⟩

theorem conj_conj (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

end General

section Grid

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil
  GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

end Grid

end GlobalTheory.ThK.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.Params
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimIn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}

structure TiesB {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  ok : A3.fam3.Ok3 1
  char : R.WeakCharacterisation F
  ex : R.toRealDat.ExAt
  host : Formalism.IndefR.Links.HostHyp D
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  ccK : D.host.ccK = ⊤
  guard : QGuard R.toRealDat
  types : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat
  ser : SerClause D
  junk : GlobalTheory.Hk3.InertJunk A3
  trSem : (∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep
  std : IsStdChar D R.ψ (-1)
  phs : ∀ i, R.phs i = 1
  nV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

end GlobalTheory.PrimIn

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SqTower

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc}

abbrev TriG (G : GridData Lc sc) (i j : Fin D.R.m) :=
  Tri T (G.V (.grid (i + 1) (j + 1))) (G.V (.grid i j)) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j)))

def TopGrid (W : G.Weil) (i j : Fin D.R.m) (X : TriG G i j) : Prop :=
  X.rA.Λ = G.Λ (.grid (i + 1) (j + 1)) ∧ X.rA'.Λ = G.Λ (.grid i j) ∧
    X.rW.Λ = GlobalTheory.Doubling.sumLat finSumFinEquiv (G.Λ (.grid i (j + 1))) (G.Λ (.grid (i + 1) j)) ∧
    X.rA.s = W.cart (.grid (i + 1) (j + 1)) ∧ X.rA'.s = W.cart (.grid i j) ∧
    ∀ (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ AV → IsGridFr W _ AV₁ →
      X.rW.s = (frSum AV AV₁).cart

def RegConst (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (c : ℂ) : Prop :=
  ∀ M : Vol G, M.Is t → ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁, ∃ z, zdeg z ≠ 0 ∧ SquareConv W M Θ Θ' z g g₁ ∧
    zdeg z * ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _

end GlobalTheory.SqTower

end
end

