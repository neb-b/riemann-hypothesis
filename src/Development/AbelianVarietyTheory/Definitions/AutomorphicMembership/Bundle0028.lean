module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReplacementValuesBaseLevelTypePartsEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
public import Formalism.LocalToGlobal.HermitianForms.Bundle0007
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.Joint0

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InGeoGeoScalIff
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Res

section Geo

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {ph : Fin D.R.m → ℂ}


set_option maxHeartbeats 2000000 in
def geoScal (g : GlobalTheory.RealGeo.GeoHalf C R ph) (kap lam err) :
    GlobalTheory.RealGeo.GeoHalf C ({ R.upd6 kap lam with err0 := err } : RealDat D A C.Q.c.F) ph :=
  ⟨g.κ, g.v₀, GlobalTheory.RealGeo.Upd.updFWT C R kap lam err g.fw, g.bar, fun i => GlobalTheory.RealGeo.Upd.updO C R kap lam err (g.O i),
    fun i => GlobalTheory.RealGeo.Upd.omPins_upE kap lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩


end Geo

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]




def KapFixed (S : RealDat3 D A3 Ks) (κ : ℝ) : Prop :=
  Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ ∧
    ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0


open Classical in
def kapNew (S : RealDat3 D A3 Ks) : ℝ := if h : ∃ κ, KapFixed S κ then h.choose else S.kap

theorem kapNew_eq (S : RealDat3 D A3 Ks) {κ : ℝ} (h : KapFixed S κ) : kapNew S = κ := by
  have h' : ∃ κ, KapFixed S κ := ⟨κ, h⟩
  unfold kapNew
  rw [dite_eq_left h']
  obtain ⟨t, p, hp, hl⟩ := h.2
  exact Lift.IsKap.unique h'.choose_spec.1 h.1 t p hp hl

theorem kapNew_of_not (S : RealDat3 D A3 Ks) (h : ¬ ∃ κ, KapFixed S κ) : kapNew S = S.kap := dif_neg h

theorem kapNew_of_scal (S : RealDat3 D A3 Ks) (h : S.scal_kap) : kapNew S = S.kap := by
  by_cases h' : ∃ κ, KapFixed S κ
  · obtain ⟨κ, hκ⟩ := h'
    exact (kapNew_eq S hκ).trans (h κ hκ.1 hκ.2).symm
  · exact kapNew_of_not S h'


variable {f : T' → T} {μ : T'} {R : RealDat3 D (A3.comap id (f μ)) Ks} {mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T'}
  {tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}



end Generic

end Res

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat








end Dat

end Record

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroIndexPlacesTransferAlongSameFiniteGroup
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open GlobalTheory.RealGeo GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Tr

variable {B : Base} {C : Cols B} {a b : Late B C} {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : Top.TwDat B}
  {Wt : Set B.places.Pl}

theorem LevOf.transfer (b : Late B C) {U : Set I.ι} {L : Links.LevCh a.D (TupU I U)} (h : LevOf a.st I U L) :
    LevOf b.st I U (levCh b L) :=
  ⟨levIs_tr b h.is, (by with_unfolding_all exact ((congrArg (chFr b) h.C) :)), (by with_unfolding_all exact (h.xiH :)), (by with_unfolding_all exact (h.Pg :)), (by with_unfolding_all exact (h.Q :)), (by with_unfolding_all exact (h.beta :))⟩

theorem GoodSet.transfer (s : SameGrp a b) {eR : Gc B px ≃* G0g a.D.nd} {Xg : Finset (Gc B px → B.LL)}
    (h : GoodSet a.st (px := px) eR Xg) : GoodSet b.st (px := px) (eR.trans s.iso) Xg := by
  have e : ∀ g, b.D.ntypes.e0.coeff ((eR.trans s.iso) g) = a.D.ntypes.e0.coeff (eR g) := fun g => s.e0 (eR g)
  obtain ⟨h1, h2⟩ := (goodSet_iff a.st (px := px) eR Xg).1 h
  refine (goodSet_iff b.st (px := px) _ Xg).2 ⟨fun χ => (h1 χ).trans (and_congr_right fun _ => ?_), fun g => (h2 g).trans (e g).symm⟩
  exact Eq.congr_left (Finset.sum_congr rfl fun g _ => congrArg (· * B.embLL (χ g)) (e g).symm)

def Dat.transfer (s : SameGrp a b) (z : Dat a.st I hX T Wt) : Dat b.st I hX T Wt :=
  @Dat.mk b.st px I hX T Wt
    (Xg := z.Xg)
    (tr := z.tr)
    (core := coreJ b z.core)
    (alg := (by with_unfolding_all exact ((Tr.alg (a := a) b z.alg) :)))
    (alg_eq := (by with_unfolding_all exact (z.alg_eq :)))
    (R := (by with_unfolding_all exact ((real3 (a := a) b z.R) :)))
    (cG := (by with_unfolding_all exact ((z.cG.trans s.iso) :)))
    (geo := (by with_unfolding_all exact ((Tr.geoHalf (a := a) b z.geo) :)))
    (pins := (by with_unfolding_all exact ((pins_tr (a := a) b s z.pins) :)))
    (lev := (by with_unfolding_all exact ((z.lev.transfer b) :)))
    (idG := (by with_unfolding_all exact (z.idG :)))
    (good := (by with_unfolding_all exact ((GoodSet.transfer s z.good) :)))
    (mu := (by with_unfolding_all exact (z.mu :)))
    (fieldValues_mem_fixedField := (by with_unfolding_all exact (z.fieldValues_mem_fixedField :)))
    (Ks_le := (by with_unfolding_all exact (z.Ks_le :)))

namespace Dat

variable (s : SameGrp a b) (z : Dat a.st I hX T Wt)

theorem nonzeroIndexPlaces_transferAlongSameFiniteGroup (F0 : HeightOneSpectrum (𝓞 B.LL) → Fin B.R.m → ℝ) : z.W1 F0 = (z.transfer s).W1 F0 :=
  (by with_unfolding_all exact ((congrArg (fun X : type_of% (z.R.toCx3 z.F) => {w : B.places.Pl | ∃ j,
    ∃ w' ∈ ({a.D.plEq w, Formalism.DivisionValues.conjPl (a.D.plEq w)} : Set (HeightOneSpectrum (𝓞 a.D.what₂.LL))),
      IndefData.Iw (Df := (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs) (((X.data z.F.cr false))) j
          (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0 ∨
        Formalism.DivisionValues.jw (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).HT j
                  (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) w'
          (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).Tl j
            (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ∨ F0 w' j ≠ 0}) (toCx3_eq (a := a) b z.R z.F)) : _))

variable {z}

theorem holds_transfer (h : Holds z.R z.F) : Holds (z.transfer s).R (z.transfer s).F := (by with_unfolding_all exact ((holds_tr (a := a) b h) :))

theorem exAt_transfer (h : z.R.toRealDat.ExAt) : (z.transfer s).R.toRealDat.ExAt := (by with_unfolding_all exact ((exAt_tr (a := a) b h) :))

theorem inGeo_transfer (h : InGeo z.geo) : InGeo (z.transfer s).geo := (by with_unfolding_all exact ((inGeo_tr (a := a) b h) :))

end Dat

section Rows

variable {ix : C.Tup ≃ I.ι} {p0 : BaseLevelRowSide a.D}

def RowsAre.tr (c : Refill a) (r : RowsAre a.st I hX T Wt ix p0) : RowsAre c.to.st I hX T Wt ix (baseLevelRowSideTransport c p0) :=
  @RowsAre.mk c.to.st px I hX T Wt ix (baseLevelRowSideTransport c p0)
    (z := r.z.transfer c.same)
    (intersectionNumber_baseChange := Dat.holds_transfer c.same r.intersectionNumber_baseChange)
    (Y := (by with_unfolding_all exact ((read c r.Y) :)))
    (Z := (by with_unfolding_all exact ((readL c r.Z) :)))
    (tup_ix := (by with_unfolding_all exact (r.tup_ix :)))

namespace RowsAre

variable (c : Refill a) (r : RowsAre a.st I hX T Wt ix p0)

end RowsAre

end Rows

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

def PrePin (P : Pre) : Prop :=
  letI := P.host.cmStar; ∀ (a : Fin P.sp.X'.rank) (b : Fin (P.sp.X P.R.m).rank), (a : ℕ) = b →
    P.sp.iX' (P.sp.X'.frame a) = (P.sp.X P.R.m).frame b

def KPx : BaseP := fun B f => (∃ δ : Fld.FieldDat B.toPre, B.KsExact δ f) ∧ PrePin B.toPre

structure ColW (B : Base) (f : Fr B.toPre) (T : TwDat B) : Type 1 where
  px : PreX B.toPre
  I : ColIn B px
  ok : I.Ok
  C_eq : I.C = f
  S_eq : I.S = {p | p ∈ offSet B.toPre ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'}
  xi_range : Set.range I.xi = T.set f
  pins : TC.Pins B px
  l : TC.Laws I
  l0 : TC.Law0 I l
  δ : Fld.FieldDat B.toPre
  exact : B.KsExact δ f
  fld : GlobalTheory.Mem.Per.FieldOK B.host B.embLL B.embE
  val : ∀ C W V S N G, ValLL0 (assemble B C W V S N G) (Fr.at ⟨B, C, W, V, S, N, G⟩ f)

namespace ColW

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)

abbrev C : Cols B := TC.cols w.I w.l

abbrev Lt : Type _ := TC.Later B w.C

abbrev st (Z : w.Lt) : Stages := ⟨B, w.C, Z.W, Z.V, Z.S, Z.N, Z.G⟩

abbrev D (Z : w.Lt) : D7 := TC.rec7 w.I w.l Z

abbrev tw (Z : w.Lt) : TwForms (w.D Z) := TC.tw w.I w.l w.l0 Z

end ColW

abbrev WP : Type 1 := ∀ (_ : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B), ColW B f T → Prop

abbrev ZP : Type 1 := ∀ (_ : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), w.Lt → Prop

abbrev CP : Type 1 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), V4.Core K (w.st Z) f T → Prop

def positionOf (P : CP) : V4.Slot := fun K X f T c =>
  ∃ (w : ColW X.B f T) (Z : w.Lt) (c' : V4.Core K (w.st Z) f T), P K X.B f T w Z c' ∧
    (⟨X.C, ⟨X.W, X.V, X.S, X.N, X.G⟩, c⟩ : Σ (C : Cols X.B) (Y : TC.Later X.B C), V4.Core K ⟨X.B, C, Y.W, Y.V, Y.S, Y.N, Y.G⟩ f T) =
      ⟨w.C, Z, c'⟩

def HasZ (P : ZP) : WP := fun K B f T w => ∃ Z : w.Lt, P K B f T w Z

def HasC (P : CP) : WP := fun K B f T w => ∃ (Z : w.Lt) (c : V4.Core K (w.st Z) f T), P K B f T w Z c

def StepW (p q : WP) : Prop :=
  Step KPx (fun _ _ _ _ => True) fun K B f T => ∀ w : ColW B f T, p K B f T w → q K B f T w

structure ColT {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) : Type 1 where
  C : Formalism.L2.Forms.ColsTiedSym (w.D Z)
  std : TC.StdC w.I w.l Z C
  stdLv : ∀ u, TC.StdLvC w.I w.l Z u (C.forms u)
  full : Formalism.L2.Forms.ColsFullS C
  stdDt : TC.StdDt w.I w.l Z full.1.base.dt
  Gt : GatTies (w.D Z)
  cmp : LatCmp (w.D Z)
  g : Formalism.L2.G.GroupCompatibilityAll (w.D Z) Gt cmp
  herm_eq : g.herm = full.1.to0
  forms_eq : g.forms = fun u => (C.forms u).to0
  gpl : Formalism.L2.Herm.SymmetricGroupCompatibleAtPlaces (w.D Z) full.1.base.toHermColsCh full.1.g Gt

theorem positionOf_intro {P : CP} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {c : V4.Core K (w.st Z) f T} (h : P K B f T w Z c) : positionOf P K (w.st Z) f T c := ⟨w, Z, c, h, rfl⟩

theorem positionOf_ind {P : CP} {R : V4.Slot}
    (h : ∀ K B f T (w : ColW B f T) (Z : w.Lt) (c : V4.Core K (w.st Z) f T), P K B f T w Z c → R K (w.st Z) f T c)
    {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {c : V4.Core K X f T} (hc : positionOf P K X f T c) : R K X f T c := by
  obtain ⟨B, C, W, V, S, N, G⟩ := X
  dsimp only at f T
  obtain ⟨w, Z, c', hp, e⟩ := hc
  exact Eq.mpr (congrArg (fun y : Σ (C : Cols B) (Y : TC.Later B C), V4.Core K ⟨B, C, Y.W, Y.V, Y.S, Y.N, Y.G⟩ f T =>
    R K ⟨B, y.1, y.2.1.W, y.2.1.V, y.2.1.S, y.2.1.N, y.2.1.G⟩ f T y.2.2) e) (h K B f T w Z c' hp)

theorem positionOf_mono {P P' : CP} (h : ∀ K B f T w Z c, P K B f T w Z c → P' K B f T w Z c) (K : Ctx) (X : Stages) (f : Fr X.B.toPre)
    (T : TwDat X.B) (c : V4.Core K X f T) (hc : positionOf P K X f T c) : positionOf P' K X f T c :=
  let ⟨w, Z, c', hp, e⟩ := hc; ⟨w, Z, c', h _ _ _ _ _ _ _ hp, e⟩

theorem StepW.of_all {p q : WP} (h : ∀ K B f T w, K.Over B.toPre → Forced K B T → p K B f T w → q K B f T w) : StepW p q :=
  Step.of_all fun K B f T a _ b _ w => h K B f T w a b

theorem StepW.trans {p q r : WP} (h : StepW p q) (h' : StepW q r) : StepW p r :=
  (Step.and h h').trans (Step.of_all fun _ _ _ _ _ _ _ H w a => H.2 w (H.1 w a))

theorem StepW.and {p q r : WP} (h : StepW p q) (h' : StepW p r) : StepW p fun K B f T w => q K B f T w ∧ r K B f T w :=
  (Step.and h h').trans (Step.of_all fun _ _ _ _ _ _ _ H w a => ⟨H.1 w a, H.2 w a⟩)

theorem step_hasCore {admitted : AtP} {p : WP} {P : CP} (h0 : Step KPx admitted fun K B f T => ∃ w : ColW B f T, p K B f T w)
    (h1 : StepW p (HasC P)) : Step KPx admitted (HasCore (positionOf P)) :=
  (h0.and ((Step.of_all fun _ _ _ _ _ _ _ _ => trivial).trans h1)).trans (Step.of_all fun _ _ _ _ _ _ _ H =>
    let ⟨w, a⟩ := H.1
    let ⟨Z, c, hc⟩ := H.2 w a
    ⟨w.C, Z.W, Z.V, Z.S, Z.N, Z.G, c, positionOf_intro hc⟩)

end GlobalTheory.Mem.Top.Bl

end
end

