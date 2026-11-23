module

public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.HermitianColumns.TiedCh
public import Formalism.LocalToGlobal.HermitianColumns.TiedQC

@[expose] public section

-- bundled from Formalism.LocalToGlobal.HermitianColumns.BaseModelLevelEq
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Herm0 (D : D7) where

  lev0 : LevelData D

  g : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), GLevTie (lev0 u) (D.gat u w hg)

end Formalism.L2.Herm
end
end

-- bundled from Formalism.LocalToGlobal.HermitianColumns.StarConj
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_conj {D : D7} (x : D.host.E) : star x = D.host.conj x := bridge_star_holds D.R D.host x

def toErrX {D : D7} (X : FullTied D) : ErrX D where
  piG := (X.levelZeroCompatibility D.u₀).piG
  piG_K := (X.levelZeroCompatibility D.u₀).piG_K
  piG_norm := fun i => by rw [← star_conj]; exact (X.levelZeroCompatibility D.u₀).piG_norm i
  piT := fun u => (X.atT u).piU
  piT_K := fun u => (X.atT u).piU_K
  piT_norm := fun u => (X.atT u).piU_norm
  piT_cong := fun u => (X.atT u).piU_cong
  vPl := fun u v => (X.base.vT u v).1
  vPl_inj := fun u a b h => (X.base.vT u).injective (Subtype.ext h)
  norm_mem_place_ideal := fun u v => (X.base.vT u v).2

def GroupCompatibleAtPlaces (D : D7) (H : HermTied D) (G : GTied D H) (Gt : GatTies D) : Prop :=
  ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (x : 𝓞 D.host.F),
    x ∈ ((G u w hg).pl v).1.asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w
        (tauLL D (Gt.gat_pos u w hg ⟨v, s⟩) (algebraMap D.host.F D.host.E (x : D.host.F)))

def GIwTied {D : D7} (H : HermTied D) (G : GTied D H) {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D}
    (u : D.what₂.Word) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Formalism.MainNotions.G.Fills (D.gat u w hg)}
    {Lv : Formalism.MainNotions.G.Levels Fl} {Ch : Formalism.MainNotions.G.Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w hg Ch) : Prop :=
  ∀ (v : Fin (D.gat u w hg).P.nV) (x : D.host.E),
    (G u w hg).eQ v _ rfl (Kp.iw 0 v x) =
      ((G u w hg).spl _ ((G u w hg).pl v).2
        (inclE (F := D.host.F) (((G u w hg).pl v).1.adicCompletion D.host.F) x)).1

def GIwPos {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D}
    (u : D.what₂.Word) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Formalism.MainNotions.G.Fills (D.gat u w hg)}
    {Lv : Formalism.MainNotions.G.Levels Fl} {Ch : Formalism.MainNotions.G.Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w hg Ch) : Prop :=
  ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
    (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) (Kp.iw 0 v x)) =
      c.embW u w hg (tauLL D (Gt.gat_pos u w hg ⟨v, s⟩) (if s.val % 2 = 1 then D.host.conj x else x))

structure JoinTied {D : D7} (X : FullTied D) (lev : LevelData D) (eX : ErrX D) (Gt : GatTies D) : Prop where
  lev_eq : lev = X.base.lev0
  errX_eq : eX = toErrX X
  gpl : GroupCompatibleAtPlaces D X.base X.g Gt

structure ExtraTied {D : D7} (X : FullTied D) {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    (ex : Extra D L hT Gi Gl K Y cX) : Prop where
  join : JoinTied X ex.lev ex.errX hT
  iw : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    GIwTied X.base X.g u w h (ex.ker u w h)
  iw_pos : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    GIwPos u w h (ex.ker u w h)

end Formalism.L2.Herm

end
end

-- bundled from Formalism.LocalToGlobal.HermitianColumns.SymAll
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SymmetricLevelZeroData (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Type :=
  ∀ u, ColLevelX (H.lev0 u) (fun x => x ∈ D.host.K) (aT u).piU (H.vT u)
    (fun v c z => (D.fm u).fv 0 v c ((aT u).pr 0 v c z))

def Ad0S (D : D7) (H : HermColsCh D) (u : D.what₂.Word) (c c' : (D.mem u).C.cls 0) (γ : GX D 0)
    (v : (D.mem u).A.vT) : Prop :=
  AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c) ((H.lev0 u).y c')
    (toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) γ.1) (H.vT u v).1

def AdIS (D : D7) (H : HermColsCh D) (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m)
    (c c' : (D.mem u).C.cls i) (γ : GX D i) (v : (D.mem u).A.vT) : Prop :=
  ∃ h : H.chOf u i c' = H.chOf u i c,
    AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm (H.chOf u i c)).U
      ((H.cls u i h1 hm (H.chOf u i c)).y ⟨c, rfl⟩) ((H.cls u i h1 hm (H.chOf u i c)).y ⟨c', h⟩)
      (toGLb (D.sp.X i).frame γ.1) (H.vT u v).1

structure SymmetricAdelicCompatibility (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop where
  up0 : ∀ u v c (y : Ld D u 0 c), (D.fm u).fv 0 v c ((aT u).pr 0 v c y) = 1 →
    Ad0S D H u c ((D.fm u).up 0 v c ((aT u).pr 0 v c y)) ((aT u).upG 0 v c y) v
  upI : ∀ u i h1 hm v c (y : Ld D u i c), (D.fm u).fv i v c ((aT u).pr i v c y) = 1 →
    AdIS D H u i h1 hm c ((D.fm u).up i v c ((aT u).pr i v c y)) ((aT u).upG i v c y) v
  dn0 : ∀ u v c g, g ≠ 0 → Ad0S D H u c ((D.fm u).dn 0 v c g) ((aT u).dnG 0 v c g) v
  dnI : ∀ u i h1 hm v c g, g ≠ 0 → AdIS D H u i h1 hm c ((D.fm u).dn i v c g) ((aT u).dnG i v c g) v
  dil0 : ∀ u v a c, Ad0S D H u c ((D.fm u).dil 0 v a c) ((aT u).dilG 0 v a c) v
  dilI : ∀ u i h1 hm v a c, AdIS D H u i h1 hm c ((D.fm u).dil i v a c) ((aT u).dilG i v a c) v

def SymmetricCofactorCompatibility (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ u, D.cOf u * ((aT u).piU : D.host.E) = ((aT D.u₀).piU : D.host.E)

def PiGConstS (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (X : SymmetricLevelZeroData D H aT) : Prop :=
  ∀ u u', (X u).piG = (X u').piG

def stabPLinS (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (u : D.what₂.Word)
    (c : (D.fm u).clsP) (s : (D.fm u).stabilizer₂ c) : D.sp.X'.V ≃ₗ[D.host.E] D.sp.X'.V :=
  (toGLb D.sp.X'.frame).symm ((aT u).clsP.stabI c s : GL (Fin D.sp.X'.rank) D.host.E)

def stabMLinS (D : D7) (H : HermColsCh D) (u : D.what₂.Word) (h1 : 1 ≤ D.R.m)
    (c : (D.mem u).C.cls D.R.m) (s : (D.mem u).C.stab D.R.m c) :
    (D.sp.X D.R.m).V ≃ₗ[D.host.E] (D.sp.X D.R.m).V :=
  (toGLb (D.sp.X D.R.m).frame).symm
    ((H.cls u D.R.m h1 le_rfl (H.chOf u D.R.m c)).stabI ⟨c, rfl⟩ s : GL (Fin (D.sp.X D.R.m).rank) D.host.E)

def SymmetricStabilizerMapCompatibility (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ (u : D.what₂.Word) (h1 : 1 ≤ D.R.m) (c : (D.fm u).clsP) (s : (D.fm u).stabilizer₂ c),
    (∀ x : D.sp.X'.V,
      ((aT u).tilG c).1 (stabMLinS D H u h1 _ ((D.fm u).stabMap c s) (((aT u).tilG c).1.symm (D.sp.iX' x))) =
        D.sp.iX' (stabPLinS D H aT u c s x)) ∧
    ((aT u).tilG c).1 (stabMLinS D H u h1 _ ((D.fm u).stabMap c s) (((aT u).tilG c).1.symm (aT u).z0)) = (aT u).z0

def SymmetricResidueFieldLevels (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Type :=
  ∀ (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT) (β : H.Ch u i),
    FvTie D.sp.cm (D.sp.X i) (H.lev u i h1 hm β).Lb (H.cls u i h1 hm β).y (fun c => D.clsLat u i c.1) (H.vT u v).1
      ((D.mem u).A.Fv v) (fun c z => (D.fm u).fv i v c.1 ((aT u).pr i v c.1 z))

def SymmetricBaseCompatibility (D : D7) (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ (u : D.what₂.Word) (pb : 𝓞 D.host.E), (pb : D.host.E) = D.host.conj ((aT u).piU : D.host.E) →
    ((H.lev0 u).Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 D.host.E)
        (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (H.lev0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0) ∧
    ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : H.Ch u i),
      (H.lev u i h1 hm β).Lb ⊔ Ideal.span {pb} • dualL D.sp.cm (D.sp.X i) (H.lev u i h1 hm β).Lb =
        crdLat (D.sp.X i) (D.sp.X i).L0

structure ColsHermS (D : D7) where
  base : HermColsCh D
  atT : ∀ u, AtT D u (base.vT u) (base.Fv u)
  levelZeroCompatibility : SymmetricLevelZeroData D base atT
  ad : SymmetricAdelicCompatibility D base atT
  cof : SymmetricCofactorCompatibility D base atT
  piG : PiGConstS D base atT levelZeroCompatibility
  stabMap : SymmetricStabilizerMapCompatibility D base atT
  fvI : SymmetricResidueFieldLevels D base atT
  std : StdTied D
  baseL : SymmetricBaseCompatibility D base atT

end Formalism.L2.Herm

end
end

-- bundled from Formalism.LocalToGlobal.HermitianColumns.TiedQCJoint
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure TwChJoint {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : TwChTied D inQ)
    (H : HermCols D) : Prop where
  Uloc_off : ∀ u μ i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ →
    (T.lev u μ i h1 hm β).Uloc v = (H.lev u i h1 hm).Uloc v
  Lb_off : ∀ u μ i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ →
    locL v (T.lev u μ i h1 hm β).Lb = locL v (H.lev u i h1 hm).Lb
  Q_off : ∀ u μ, ∀ v ∈ T.Q μ, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal ∧ ∀ a, (D.host.g a : 𝓞 D.host.F) ∉ v.asIdeal

def clsCast (D : D7) (u : D.what₂.Word) (i : ℕ) : (D.mem u).C.cls i ≃ (D.chTw u D.what₂.mu0).cls i :=
  Equiv.cast (congrArg (fun C => C.cls i) (D.memberColumns_twistedChain_base u).symm)

def yCast (D : D7) (u : D.what₂.Word) (i : ℕ) : (D.mem u).C.Y i ≃ (D.chTw u D.what₂.mu0).Y i :=
  Equiv.cast (congrArg (fun C => C.Y i) (D.memberColumns_twistedChain_base u).symm)

structure TwChMu0 {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : TwChTied D inQ) : Prop where
  eY : ∀ u i hi, T.eY u D.what₂.mu0 i hi = yCast D u i
  eCls0 : ∀ u, T.eCls0 u D.what₂.mu0 = clsCast D u 0

end Formalism.L2.Herm

end
end

