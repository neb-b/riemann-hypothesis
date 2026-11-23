module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PointPropertyEqSizeFree
section
noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

structure Obj2 (D : D7) : Type 1 where

  gatT : GatTies D

  th : ThetaX D

  cmp : LatCmp D

  tw : TwForms D

  Gy : G.LatInst D

  errX : ErrX D

  nch : NChoice D

  xd : ThData D

  lev : LevelData D

  X : DivX D

  p0 : BaseLevelRowSide D

  ker : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    LocalToGlobal₂ D gatT cmp tw u w h (Gy.Ch u w h)

  amb : AmbForm D (RowSide.sharp D)

  amb0 : AmbForm D p0.s

  gauge : letI := D.host.cmStar; GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig

def layObj {D : D7} (Y : Lay D) : Obj2 D := { Y with }

def Obj2.tr {D : D7} (O : Obj2 D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : Obj2 (setDiv D N h) where
  gatT := gatTr N h O.gatT
  th := thTr N h O.th
  cmp := cmpTr N h O.cmp
  tw := twTr N h O.tw
  Gy := latTr N h O.Gy
  errX := errTr N h O.errX
  nch := nchTr N h O.nch
  xd := xdTr N h O.xd
  lev := O.lev
  X := divTr N h O.X
  p0 := ⟨sideTr N h O.p0.s⟩
  ker := fun u w g => { O.ker u w g with }
  amb := { O.amb with }
  amb0 := { O.amb0 with }
  gauge := O.gauge

def pointPropertyOfObjects (QO : ∀ D : D7, Obj2 D → Prop) : PtProp := fun D _ gatT _ Gy _ X _ ex =>
  QO D { gatT := gatT, th := ex.th, cmp := ex.cmp, tw := ex.tw, Gy := Gy, errX := ex.errX, nch := ex.nch, xd := ex.xd,
         lev := ex.lev, X := X, p0 := ex.p0, ker := ex.ker, amb := ex.amb, amb0 := ex.amb0, gauge := ex.gauge }

def allDiv (QO : ∀ D : D7, Obj2 D → Prop) (D : D7) (Y : Lay D) : Prop := ∀ N h, QO (setDiv D N h) ((layObj Y).tr N h)

def extraObj {D : D7} {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D}
    {cX : ExtraC} (ex : Extra D L gatT Gx Gy K X cX) : Obj2 D :=
  { gatT := gatT, th := ex.th, cmp := ex.cmp, tw := ex.tw, Gy := Gy, errX := ex.errX, nch := ex.nch, xd := ex.xd,
    lev := ex.lev, X := X, p0 := ex.p0, ker := ex.ker, amb := ex.amb, amb0 := ex.amb0, gauge := ex.gauge }

def ofObj {D : D7} (O : Obj D) : Obj2 D := extraObj O.ex

def pointObj {C : FC} (p : Pt C) : Obj2 p.D := extraObj p.xa.ex

theorem ofObj_obj {C : FC} {D : D7} (Y : Lay D) (p : LedPart C Y) : ofObj (Y.obj p) = layObj Y := rfl

theorem pointObj_pt {C : FC} {D : D7} {Y : Lay D} (p : LedPart C Y) : pointObj p.pt = (layObj Y).tr (nPrime p.L) p.ht := rfl

end GlobalTheory.Mem.Top

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle
open scoped Matrix

namespace GlobalTheory.GoodMetric

variable {ι : Type} {m : ι → ℕ}

abbrev EntIx (m : ι → ℕ) : Type := Σ τ, Fin (m τ) × Fin (m τ)

def evEnt {M : ℕ} (P : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ)) {R : Type} [CommRing R] (A : Mat m R) :
    Matrix (Fin M) (Fin M) R :=
  P.map (aeval fun v : EntIx m => A v.1 v.2.1 v.2.2)

structure PolyRep (m : ι → ℕ) : Type where

  M : ℕ

  ent : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ)
  one : ∀ (R : Type) [CommRing R], evEnt ent (1 : Mat m R) = 1
  mul : ∀ (R : Type) [CommRing R] (A B : Mat m R), evEnt ent (A * B) = evEnt ent A * evEnt ent B
  transp : ∀ (R : Type) [CommRing R] (A : Mat m R), evEnt ent (fun τ => (A τ)ᵀ) = (evEnt ent A)ᵀ

namespace PolyRep

def ev (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R) : Matrix (Fin ρ.M) (Fin ρ.M) R := evEnt ρ.ent A

def lie [Fintype ι] (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R) : Matrix (Fin ρ.M) (Fin ρ.M) R :=
  Matrix.of fun i j => ∑ v : EntIx m,
    aeval (fun w : EntIx m => (1 : Mat m R) w.1 w.2.1 w.2.2) (pderiv v (ρ.ent i j)) * A v.1 v.2.1 v.2.2

def proj (m : ι → ℕ) (τ : ι) : PolyRep m where
  M := m τ
  ent := Matrix.of fun i j => X ⟨τ, (i, j)⟩
  one R _ := by ext i j; simp [evEnt]
  mul R _ A B := by ext i j; simp [evEnt, Matrix.mul_apply]
  transp R _ A := by ext i j; simp [evEnt]

end PolyRep

end GlobalTheory.GoodMetric

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RedivisionStructureEq
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure New (D : D7) : Type 1 where
  Z : SNew D
  N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V
  h : D.what₂.Word → ℝ

def reD (D : D7) (Z : New D) : D7 := GlobalTheory.EX.OB.setDiv (reS D Z.Z) Z.N Z.h


set_option maxHeartbeats 4000000 in
def SameForms0LevelsAndValues {D : D7} (Z : New D) (F : ∀ u, Forms0 D u) (F' : ∀ u, Forms0 (reD D Z) u) : Prop :=
  ∀ u : D.what₂.Word, (F' u).cls0.lev = (F u).cls0.lev ∧ (F' u).cls0.y = (F u).cls0.y ∧ (F' u).val0.eY = (F u).val0.eY

variable {D : D7} (Z : New D)

def wd (u : D.what₂.Word) : (reD D Z).what₂.Word := u

def New.self (D : D7) : New D := ⟨SNew.self D, fun u => (D.div.Nu u).L, D.div.h⟩

def New.ofDiv (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : New D := ⟨SNew.self D, N, h⟩


set_option maxHeartbeats 4000000 in
def reX (X : HidaSetting D) : HidaSetting (reD D Z) := { X with }

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SPack (D : D7) (F : ∀ u, Forms0 D u) where
  X : HidaSetting D
  hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I
  Y : Formalism.L2.SG.Full.Full X
  fin : FinX Y
  ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ
  measTie : X.MeasTie hb
  ψ_char : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ
  ψ_std : Formalism.L2.SG.LocVol.IsStdChar ψ
  measCompat : Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ
  locCompat : ∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w
  tr : ∀ u, Transport X u (F u)
  into : ∀ u, ColDictInto X (tr u) Y.hK
  bij : ∀ u, ColDictBij X (tr u) Y.hK
  lev : ∀ u, LevelMatch X (tr u) Y.hK
  isom : ∀ u, ColDictIsom X (tr u) Y.hK (Y.cs u) (fin.shInj u)
  inst : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D
  G : GoodOp X

  pin : ∀ x : X.B.I.E, HEq (X.ιE x) x

structure SRest {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) where
  hI : SIso D.s (sOf P.fin)
  autTie : Formalism.MainNotions.S.AutTie D P.X.B P.X.pl
  colPin : ∀ (u : D.what₂.Word) (x : D.s.Cu u),
    colDict P.X (P.tr u) P.Y.hK (P.into u) (P.bij u) (hI.eCu u x) = D.s_Cu u x
  j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G
  rowPin : ∀ x : D.what₂.EE, hI.eHH (D.sEE x) = conjHH P.X P.G (j x)
  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D

def SRest.toSTies {D : D7} {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P) : Formalism.L2.SG.SpectralTiesReal.STies D where
  X := P.X
  hb := P.hb
  Y := P.Y
  hI := fun _ => S.hI
  ψ := P.ψ
  autTie := S.autTie
  measTie := P.measTie
  ψ_char := P.ψ_char
  ψ_std := P.ψ_std
  measCompat := P.measCompat
  locCompat := P.locCompat

theorem SRest.rowTie {D : D7} {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P) : RowDictTie P.X P.G S.hI.eHH :=
  ⟨S.j, S.rowPin⟩

def SPack.toNew {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall)
    (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) : SNew D where
  s := sOf P.fin
  s_HH := hD
  s_Cu := fun u => colDictT P.X (P.tr u) P.Y.hK (P.fin.shInj u) (P.into u) (P.bij u)
  s_PlF := Equiv.refl _
  s_Cu_isom := fun u x y => P.isom u x y
  sEE := (conjHH P.X P.G).comp j.toLinearIsometry

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdPstCycRepNeTrivWD
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst.Test

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) (LL : FinExt l)

section Generic

variable {LL} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (x : ↥(Dpst P ρ))

theorem apply_eq_of_nilpotent {W : Type} [AddCommGroup W] [Module ℂ W] (hd : finrank ℂ W = 1) {v : W}
    (hv : v ≠ 0) (u : End ℂ W) (hu : IsNilpotent (u - 1)) : u v = v := by
  obtain ⟨k, hk⟩ := hu
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp hd ((u - 1) v)
  have hp : ∀ n : ℕ, ((u - 1) ^ n) v = c ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]
  have hc0 : c = 0 := by
    have := hp k
    rw [hk, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
    exact pow_eq_zero_iff'.mp (this.resolve_right hv) |>.1
  rw [hc0, zero_smul, LinearMap.sub_apply, eq_comm, sub_eq_zero] at hc
  exact hc

end Generic

theorem lpDim_wdAt {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) :
    (wdAt P ι Bw h hj r).lpDim = a := by
  by_cases hr : IsPstAt P Bw r
  · obtain ⟨LL', r', -, h2, h3⟩ := wdAt_of_isPstAt ι Bw h hj hr
    rw [h3, lpDim_wdPst ι Bw h hj h2, LetterDim.finrank_wdSpace l P ι _ LL' _ _ h2]
    simp
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, lpDim_trivWD]


omit P ι in
theorem exists_induces (hw : w ∈ placesOver E l) (h : IsPlaceOver A w) :
    ∃ (LL : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), Induces Bw := by
  obtain ⟨j, L0, hj, hL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l E Ω w A hw h
  obtain ⟨Bw, hB, -⟩ := hL L0 le_rfl
  exact ⟨L0, Bw, fun x => by rw [hB]; exact hj x⟩


end GlobalTheory.Pst.Test
end
end

