module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Formalism.LocalToGlobal.ClassRec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
public import Formalism.LocalToGlobal.GroupLattices.TiedRec
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0008
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0002
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecThm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

def coreS {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (J : Formalism.L2.Pj.Core D) :
    Formalism.L2.Pj.Core (setDiv D N h) where
  Q := ⟨J.Q.H, J.Q.l, J.Q.c, J.Q.Dw, J.Q.Xo, J.Q.eO⟩
  U := J.U
  V := J.V
  dict := J.dict
  mu := J.mu
  Kf := J.Kf
  pb := J.pb

inductive GeoCl (Γ : GeoP) : ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop
  | base {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} : Γ D J X → GeoCl Γ D J X
  | step {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
      {J : Formalism.L2.Pj.Core D} {X : DivX D} : GeoCl Γ D J X → GeoCl Γ (setDiv D N h) (coreS N h J) (divTr N h X)

def geoCl (Γ : GeoP) : GeoP := GeoCl Γ

theorem geoCl_of {Γ : GeoP} {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} (h : Γ D J X) : geoCl Γ D J X := GeoCl.base h

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev SExt : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
  (p0 : BaseLevelRowSide (w.D Z)) (r : RowsT K w Z Wt p0) (col : ColT w Z), SX K B f T w Z Wt p0 r col → Type 1

def SExt.none : SExt := fun _ _ _ _ _ _ _ _ _ _ _ => PUnit

def SXE (E : SExt) : SPosition := fun K B f T w Z Wt p0 r col => Σ a : SX K B f T w Z Wt p0 r col, E K B f T w Z Wt p0 r col a

structure Prm (hL : GlobalTheory.Published.LocalLanglandsGL) : Type 2 where
  R : RPosition
  N : NExt hL
  S : SExt
  Γ : GeoP

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

structure KPin {𝒮 : Slots} {K : Ctx} (q : WPt 𝒮 K) (t : Formalism.L2.Ker.KerEntTied q.O.ex) : Prop where
  std : TC.StdKer q.w.I q.w.l q.Z t
  O : t.O = q.x.ker.O
  ent : HEq t.ent q.x.ker.E
  adapted : t.Adapted
  top : t.TopPinned

def ZeU (𝒮 : Slots) : Prop := ∀ (K : Ctx) (q : WPt 𝒮 K), Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z)

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

def EntC {w : ColW B f T} {Z : w.Lt} {t : ColT w Z} {Y : DivX (w.D Z)} {Gy : G.LatInst (w.D Z)}
    {ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy} (k : KerT t Y Gy ker) : Prop :=
  ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl k.O Bs Y (w.tw Z)),
    k.E = Formalism.L2.Ker.kerEntC Pl k.O Bs h

def BuiltE (𝒮 : Slots) : CP := fun K _ _ _ w Z c => ∃ b : Built 𝒮 K w Z c, EntC b.ker

def GoodE (𝒮 : Slots) : CP := fun K B f T w Z c => BuiltE 𝒮 K B f T w Z c ∧ GoodO (w.D Z) c.O.nch c.O.xd

def IsBuiltE (𝒮 : Slots) : V4.Slot := positionOf (BuiltE 𝒮)

def IsGoodE (𝒮 : Slots) : V4.Slot := positionOf (GoodE 𝒮)

theorem IsBuiltE.isBuilt {𝒮 : Slots} (K X f T c) (h : IsBuiltE 𝒮 K X f T c) : IsBuilt 𝒮 K X f T c :=
  positionOf_mono (fun _ _ _ _ _ _ _ ⟨b, _⟩ => ⟨b⟩) K X f T c h

theorem IsGoodE.isBuiltE {𝒮 : Slots} (K X f T c) (h : IsGoodE 𝒮 K X f T c) : IsBuiltE 𝒮 K X f T c :=
  positionOf_mono (fun _ _ _ _ _ _ _ h => h.1) K X f T c h

def MemberE (𝒮 : Slots) : Prop :=
  BaseCond KPx ∧ FirstG KPx (IsBuiltE 𝒮) ∧ ExportF KPx (IsBuiltE 𝒮) ∧ SecondG KPx (IsBuiltE 𝒮) (IsGoodE 𝒮)

def WitExE (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (β : GlobalTheory.Fc.BPt K), β.Is (IsGoodE 𝒮) → ∃ q : WPt 𝒮 K, q.Is β.D β.O ∧ EntC q.x.ker

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TieEmbeddingCastLevelTie
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.Mem.LocalPack

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

section Ext

variable {Os Ks O Kf O' Kf' : Type} [CommRing Os] [Field Ks] [Algebra Os Ks] [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field Kf']
  [Algebra O' Kf']

end Ext

section Ties

abbrev RingTie := @Formalism.L2.G.RingCompatibleAt

abbrev LocalIs := @Formalism.L2.G.GatIs

alias standardSub_of_ringTie := Formalism.L2.G.stdSubAt_of_ring

alias localIs_of_hyperspecial := Formalism.L2.G.gatIs_recG

alias ringTie_record := Formalism.L2.G.ringTied_recC

end Ties

section Bridge

theorem pack_eq (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
    (h5 : 5 ≤ D.what₂.places.resChar w) (h2 : 2 ≤ nFr D (D.what₂.places.resChar w))
    (he : Even (nFr D (D.what₂.places.resChar w)))
    (I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : Formalism.L2.Herm.awayFrom₂ Lc (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ) :
    pack D u Lc w h5 h2 he I ψ = locPackC D u Lc w h5 h2 he I ψ := by
  first
    | with_reducible rfl
    | (delta pack locPackC frobOrder nFr; with_reducible rfl)

end Bridge

section Record

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

end Record

abbrev IsConcrete := @Formalism.L2.G.IsRecC

end GlobalTheory.Mem.LocalPack
end
end

