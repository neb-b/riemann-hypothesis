module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LinearAdelicActionFixedIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockEndMinorsOfCell
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut

namespace Formalism.L2.SG.NGCut.PtPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frame_mem {D : D7} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (hz : F.fl.z ∈ Λ) (hX : XLam Λ F = XS D F.fl) (b : Fin (D.R.rS + 1)) : frame F b ∈ Λ := by
  induction b using Fin.lastCases with
  | last => rw [Formalism.MainNotions.LatticeGluingRadicals.a_frame_last]; exact hz
  | cast b =>
    rw [Formalism.MainNotions.LatticeGluingRadicals.a_frame_castSucc]
    have h : F.fl.e b ∈ XLam Λ F := by rw [hX]; exact Formalism.MainNotions.BridgeLemma₂.basis_vector_mem_span D F.fl b
    exact h.1

theorem zhatOM_isIntegral {D : D7} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (hF : ∀ b, frame F b ∈ Λ) (hF' : ∀ b, frame F' b ∈ Λ) (i j : Fin (D.R.rS + 1)) :
    IsIntegral ℤ (ZhatOM (ZhatL F F') i j) := by
  obtain ⟨c, hc⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun (hF i) (hF' j)
  have hZ : ZhatL F F' i j = (VS D).hT (frame F i) (frame F' j) := rfl
  have h1 : IsIntegral ℤ ((-1 : D.host.E) ^ (D.R.rS - j.val)) := (isIntegral_one.neg).pow _
  show IsIntegral ℤ ((-1 : D.host.E) ^ (D.R.rS - j.val) * ZhatL F F' i j)
  rw [hZ, ← hc]
  exact h1.mul (RingOfIntegers.isIntegral_coe c)


open Formalism.MainNotions.BesselShellMomentBounds Formalism.HermitianLatticeCounting.ExpansionTerms in
theorem blockEndMinors_of_cell {D : D7} (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hZ : ∀ i j, IsIntegral ℤ (Z i j)) (γ : Point D.host.E (D.R.rS + 1)) (hc : IsInCell Z γ) :
    BlockEndMinorsIntegral (toSig γ) := by
  obtain ⟨L, U, hL, hU, rfl⟩ := hc
  intro (a : Fin (toComp γ).length)
  have key := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.integral_evaluation_fourth D.host.E (integralClosure ℤ D.host.E).toSubring (D.R.rS + 1)
    (toComp γ) (toT γ) (toT_ne γ) L U
    ⟨fun i => (hL i i).2 rfl, fun i j hij => (hL i j).1 hij⟩
    ⟨fun i => (hU i i).2 rfl, fun i j hij => (hU i j).1 hij⟩
    (by intro i j; rw [← ptMat_eq]; exact hZ i j)
  have := key.1 ((a : ℕ) + 1)
  show IsIntegral ℤ (IndexedMinorEntry (toComp γ).blocksFun (toT γ) a) ∧ IndexedMinorEntry (toComp γ).blocksFun (toT γ) a ≠ 0
  rw [E5minor_eq]
  exact this

theorem stepPoints_of_ctx
    (hOV : ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPoints := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hc νL νB ng γ hγ => ?_⟩
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := hγ
  have hG : t.toTerm.G ≠ 0 := by
    intro h
    apply ht.1
    show Gt t = 0
    have h' : t.G = 0 := h
    simp [Gt, h']
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := hOV Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc t hr
    show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := hAt Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc t.toTerm hG hrel
  have hat := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  obtain ⟨F', ⟨hP, -⟩, -, hcell⟩ := hat
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam := frame_mem _ hrow.2.1.2.2.1.1 hrow.2.2
  have hF' : ∀ b, frame F' b ∈ t.toTerm.lam := frame_mem _ hP.1.1 hP.2.2.2
  have hE := blockEndMinors_of_cell _ (zhatOM_isIntegral _ _ hrow.2.1.2.1 hF hF') _ hcell
  rw [← hpt]
  exact hE

theorem stepPoints_of
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPoints :=
  stepPoints_of_ctx (fun _ _ _ _ _ _ _ _ D _ X Y u u' _ => hOV D X Y u u')
    (fun _ _ _ _ _ _ _ _ D _ X Y u u' _ => hAt D X Y u u')


end Formalism.L2.SG.NGCut.PtPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarFwd
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : Formalism.BasicNotions.D7}

def OmCls {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F'₂ F' : LFlag (D.sp.Y 0) D.R.rS T') : Prop :=
  ∀ c : Fin (D.R.rS + 1) → D.host.E, (∀ a, (VS D).hT (F0.e a) (∑ b, c b • frame F'₂ b) = 0) →
    ∑ b, c b • (frame F' b - frame F'₂ b) ∈ Xsp (lf D F0)

variable (D)

def NMove : Prop :=
  ∀ {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F'₂ F' : LFlag (D.sp.Y 0) D.R.rS T'),
    ZhatL (lf D F0) F'₂ = ZhatL (lf D F0) F' → Gval (lf D F0) F' ≠ 0 → OmCls F0 F'₂ F' →
      ∃ n ∈ unipotentFrameFixers F0, Moves n F'₂ F'

end Defs

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def OmPart : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → ∀ F', IsPartner γ Z F' → OmCls F0 F'₂ F'

def LocIn : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → ∀ F', IsPartner γ Z F' → ∀ n ∈ unipotentFrameFixers F0, Moves n F'₂ F' →
        ∀ p, lattice₂ D Zd.M p (Formalism.HermitianLatticesTheory.gmap n.symm γ.lam) ∈
          locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p)

variable {u u' F0 what₂}

theorem fwdCut_image_gmap_symm (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (n : (VS D).V → (VS D).V) '' (Formalism.HermitianLatticesTheory.gmap n.symm Λ : Set (VS D).V) = (Λ : Set (VS D).V) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe, Set.mem_image, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    SetLike.mem_coe]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨n.symm x, ⟨x, hx, rfl⟩, by simp⟩

theorem fwdCut_gval_congr {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T')
    (h : ZhatL F F₁ = ZhatL F F₂) : Gval F F₁ = Gval F F₂ := by
  simp only [Gval, Formalism.MainNotions.S.Gflag, Formalism.MainNotions.S.Dl] at h ⊢
  rw [show Formalism.MainNotions.S.Zhat F.fl F₁.fl = Formalism.MainNotions.S.Zhat F.fl F₂.fl from h]

theorem fwdC_of (hrows : IsRowReps D F0 what₂) (h1 : NMove D) (h2 : OmPart Zd u u' F0 what₂)
    (h3 : LocIn Zd u u' F0 what₂) : FwdC Zd u u' F0 what₂ := by
  intro γ Z hC F'₂ φ φ' hS F' hP
  have hEZ := hP.1
  have hZ' : ZhatL (lf D F0) F' = Z := hEZ.2.2.2.2
  have hG : Gval (lf D F0) F' ≠ 0 := hEZ.1.2.2
  obtain ⟨n, hn, hm⟩ := h1 F0 F'₂ F' (hS.1.trans hZ'.symm) hG (h2 hrows γ Z hC F'₂ φ φ' hS F' hP)
  refine ⟨Formalism.HermitianLatticesTheory.gmap n.symm γ.lam, ⟨?_, h3 hrows γ Z hC F'₂ φ φ' hS F' hP n hn hm⟩, n, hn, hm,
    fwdCut_image_gmap_symm n γ.lam⟩
  have hlat : Submodule.IsFullLattice D.host.E γ.lam := (hrows.1 γ.lam γ.mem).1.1
  letI := Formalism.HermitianLatticesTheory.isomAct_lattice n.symm γ.lam hlat.toIsLattice
  refine ⟨?_⟩
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe]
  change Submodule.span D.host.E ((n.symm : (VS D).V →ₗ[D.host.E] (VS D).V) '' (γ.lam : Set _)) = ⊤
  rw [← Submodule.map_span, hlat.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 n.symm.surjective]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FmatMulInv
section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Kset

variable (I : Formalism.MainNotions.S.AutInst)

theorem kset_inv' {x : I.Gf} (hx : x ∈ I.Kset) : x⁻¹ ∈ I.Kset :=
  (Formalism.UG.stabGL I.Lf).inv_mem hx

theorem kset_mul' {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) : x * y ∈ I.Kset :=
  (Formalism.UG.stabGL I.Lf).mul_mem hx hy

theorem kset_act {k : I.Gf} (hk : k ∈ I.Kset) (w : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    I.fmat k *ᵥ w ∈ I.Lf ↔ w ∈ I.Lf := (hk w).symm

theorem fmat_mul' (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := rfl

theorem fmat_inv_mul' (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp [Formalism.MainNotions.S.AutInst.fmat]

end Kset

section Lat

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def lat (h : Hfin X u) : Submodule (𝓞 D.host.E) (VS D).V := Classical.choose (latSub X u h)

theorem lat_coe (h : Hfin X u) : (lat X u h : Set (VS D).V) = latOf X u h :=
  Classical.choose_spec (latSub X u h)

theorem mem_lat (h : Hfin X u) (y : (VS D).V) :
    y ∈ lat X u h ↔ X.B.I.fmat ((h : X.B.I.Gf))⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf := by
  rw [← SetLike.mem_coe, lat_coe]
  show X.B.I.fmat (((h : X.B.I.Gf)) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf ↔ _
  rw [_root_.mul_inv_rev, fmat_mul', ← Matrix.mulVec_mulVec, kset_act X.B.I (kset_inv' X.B.I (X.xu_K u))]

theorem matE_fix (M : GL (Fin X.B.I.n) X.B.I.E)
    (hfix : ∀ y ∈ fixSet X u, (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) *ᵥ
      incl X.B.I y = incl X.B.I y) (y : (VS D).V) (hy : X.crd y ∈ fixSet X u) : matE X M y = y := by
  have h1 : incl X.B.I (X.crd (matE X M y)) = incl X.B.I (X.crd y) := by
    rw [matE_incl]
    exact hfix _ hy
  apply X.bas.equivFun.injective
  funext i
  exact X.ιE.symm.injective (inclInj_holds X (congrFun h1 i))

theorem matE_stab (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J)
    (hfix : ∀ y ∈ fixSet X u, (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) *ᵥ
      incl X.B.I y = incl X.B.I y) : matE X M ∈ stabF D (X.Fu u) := by
  refine ⟨matE_isom X M hM, fun j => ?_, ?_⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro a _
    rw [X.Fu_e u]
    exact matE_fix X u M hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))
  · show matE X M (X.Fu u).z = (X.Fu u).z
    rw [X.flagZVector u]
    exact matE_fix X u M hfix _ (Or.inr rfl)

theorem hfin_fix (g : Hfin X u) (y : Fin X.B.I.n → X.B.I.E) (hy : y ∈ fixSet X u) :
    X.B.I.fmat (g : X.B.I.Gf) *ᵥ incl X.B.I y = incl X.B.I y := g.2 y hy

theorem mem_gmap (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (y : (VS D).V) :
    y ∈ Formalism.HermitianLatticesTheory.gmap γ Λ ↔ γ.symm y ∈ Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨γ.symm y, hy, by simp⟩

theorem lat_act (g h k : Hfin X u) (M : GL (Fin X.B.I.n) X.B.I.E)
    (hM : X.B.I.fmat (g : X.B.I.Gf) = (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)))
    (hk : (k : X.B.I.Gf) ∈ X.B.I.Kset) :
    lat X u (g * h * k) = Formalism.HermitianLatticesTheory.gmap (matE X M) (lat X u h) := by
  ext y
  rw [mem_gmap, mem_lat, mem_lat]
  have hinc : incl X.B.I (X.crd ((matE X M).symm y)) = X.B.I.fmat ((g : X.B.I.Gf))⁻¹ *ᵥ incl X.B.I (X.crd y) := by
    have h1 := matE_incl X M ((matE X M).symm y)
    rw [LinearEquiv.apply_symm_apply, ← hM] at h1
    rw [h1, Matrix.mulVec_mulVec, fmat_inv_mul', Matrix.one_mulVec]
  rw [hinc, Matrix.mulVec_mulVec]
  show X.B.I.fmat (((g : X.B.I.Gf) * (h : X.B.I.Gf) * (k : X.B.I.Gf)))⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf ↔ _
  rw [_root_.mul_inv_rev, fmat_mul', ← Matrix.mulVec_mulVec, kset_act X.B.I (kset_inv' X.B.I hk), _root_.mul_inv_rev, fmat_mul']

end Lat

section Cls

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def cls (h : Hfin X u) : Submodule (𝓞 D.host.E) (VS D).V :=
  if hh : ∃ Λ', Λ' ∈ what₂ ∧ Eqv X u Λ' (lat X u h) then Classical.choose hh else ⊥

variable {X u what₂}

theorem cls_spec (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (h : Hfin X u) :
    cls X u what₂ h ∈ what₂ ∧ Eqv X u (cls X u what₂ h) (lat X u h) := by
  have hex : ∃ Λ', Λ' ∈ what₂ ∧ Eqv X u Λ' (lat X u h) :=
    (hR.2 (lat X u h) (hL h (lat X u h) (lat_coe X u h))).exists
  unfold cls
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

theorem cls_eq (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) {h : Hfin X u}
    {Λ' : Submodule (𝓞 D.host.E) (VS D).V} (h1 : Λ' ∈ what₂) (h2 : Eqv X u Λ' (lat X u h)) :
    cls X u what₂ h = Λ' :=
  (hR.2 (lat X u h) (hL h (lat X u h) (lat_coe X u h))).unique (cls_spec hR hL h) ⟨h1, h2⟩

theorem gamR_mat {g : Hfin X u} (hg : g ∈ gamR X u) :
    ∃ M : GL (Fin X.B.I.n) X.B.I.E, M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧
      X.B.I.fmat (g : X.B.I.Gf) = (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) :=
  (mem_gamR_iff X u g).1 hg

theorem cls_rel (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (hI : LatInj X u) (h h' : Hfin X u) :
    cls X u what₂ h = cls X u what₂ h' ↔ ∃ g ∈ gamR X u, ∃ k ∈ kR X u, h' = g * h * k := by
  constructor
  · intro hc
    have e1 := (cls_spec hR hL h).2
    have e2 := (cls_spec hR hL h').2
    rw [hc] at e1
    have e3 : Eqv X u (lat X u h) (lat X u h') := (eqvEquiv X u).trans ((eqvEquiv X u).symm e1) e2
    obtain ⟨g, k, hh', hkl⟩ := hI h h' (lat X u h) (lat X u h') (lat_coe X u h) (lat_coe X u h') e3
    refine ⟨iotaF X u g, ?_, k, ?_, hh'⟩
    · rw [mem_gamR_iff]
      obtain ⟨hGF, -⟩ := Subgroup.mem_inf.1 g.2
      have hGF' : (g : X.B.I.GA) ∈ X.B.I.GFset := hGF
      obtain ⟨M, hM, -, hf⟩ := hGF'
      exact ⟨M, hM, hf⟩
    · rw [mem_kR_iff]
      have hK := Formalism.L2.SG.Pf.LatDictK.dict_K X ((h : X.B.I.Gf) * X.xu u) ((h : X.B.I.Gf) * (k : X.B.I.Gf) * X.xu u)
        (latOf X u h) (fun y => Iff.rfl) (fun y => by rw [← hkl]; exact Iff.rfl)
      have e4 : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * (k : X.B.I.Gf) * X.xu u) =
          (X.xu u)⁻¹ * (k : X.B.I.Gf) * X.xu u := by group
      rw [e4] at hK
      have e5 : (k : X.B.I.Gf) = X.xu u * ((X.xu u)⁻¹ * (k : X.B.I.Gf) * X.xu u) * (X.xu u)⁻¹ := by group
      rw [e5]
      exact kset_mul' X.B.I (kset_mul' X.B.I (X.xu_K u) hK) (kset_inv' X.B.I (X.xu_K u))
  · rintro ⟨g, hg, k, hk, rfl⟩
    obtain ⟨M, hM, hMf⟩ := gamR_mat hg
    have hst : matE X M ∈ stabF D (X.Fu u) := matE_stab X u M hM (fun y hy => by
      rw [← hMf]; exact hfin_fix X u g y hy)
    have e1 := (cls_spec hR hL h).2
    have e2 : Eqv X u (lat X u h) (lat X u (g * h * k)) :=
      ⟨matE X M, hst, (lat_act X u g h k M hMf ((mem_kR_iff X u k).1 hk)).symm⟩
    exact (cls_eq hR hL (cls_spec hR hL h).1 ((eqvEquiv X u).trans e1 e2)).symm

theorem cls_surj (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (hS : LatSurj X u)
    (s : Submodule (𝓞 D.host.E) (VS D).V) (hs : s ∈ what₂) : ∃ h, cls X u what₂ h = s := by
  obtain ⟨h, Λ', hΛ', he⟩ := hS s (hR.1 s hs)
  have e1 : Λ' = lat X u h := SetLike.coe_injective (hΛ'.trans (lat_coe X u h).symm)
  rw [e1] at he
  exact ⟨h, cls_eq hR hL hs ((eqvEquiv X u).symm he)⟩

end Cls

end Formalism.L2.SG.RhoPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumATools
section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Tools

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

private theorem hermSp_h_sum_smul_left {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {ι : Type} [Fintype ι] (c : ι → E) (x : ι → V) (y : V) : H.h (∑ i, c i • x i) y = ∑ i, c i * H.h (x i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)
  have h1 := map_sum φ (fun i => c i • x i) Finset.univ
  simp only [φ, AddMonoidHom.mk'_apply, H.h_smul_left] at h1
  exact h1

private theorem hermSp_h_sum_smul_right {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {ι : Type} [Fintype ι] (y : V) (c : ι → E) (x : ι → V) :
    H.h y (∑ i, c i • x i) = ∑ i, M.L.cj (c i) * H.h y (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [H.h_herm (∑ i, c i • x i) y, hermSp_h_sum_smul_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← H.h_herm]

theorem gram_recomb {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {ι : Type}
    [Fintype ι] (v : ι → V) (A : Matrix ι ι E) :
    H.gram (fun j => ∑ i, A i j • v i) = (A.map M.L.cj)ᵀ * H.gram v * A := by
  ext a b
  simp only [HermSp.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hermSp_h_sum_smul_left]
  simp only [hermSp_h_sum_smul_right, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem thSpan_at (M : Model F E) (r : ℕ) (hM : M.OK) : ThSpan M r := by
  intro V _ _ H t hg
  apply le_antisymm
  · exact (Submodule.span_le (R := E)).2 fun v hv => hv.2
  · intro w hw
    have hwΛ : w ∈ Submodule.span E (t.abelian₂ : Set V) := by
      rw [hg.1.1.2.1]
      exact Submodule.mem_top
    obtain ⟨c, hc0, hc⟩ := PI.LocHerm.Glue.existsIntegralMultiple M hM V t.abelian₂ w hwΛ
    have hcW : algebraMap F E (c : F) • w ∈ ThL H t := ⟨hc, Submodule.smul_mem _ _ hw⟩
    have hunit : IsUnit (algebraMap F E (c : F)) := (Units.mk0 (c : F) hc0).isUnit.map _
    have e : w = (hunit.unit⁻¹ : Eˣ) • (algebraMap F E (c : F) • w) := by
      rw [Units.smul_def, smul_smul, IsUnit.val_inv_mul, one_smul]
    rw [e, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hcW)

theorem gramMM_holds (M : Model F E) (r n : ℕ) : GramMM M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂
  obtain ⟨hg₁, hF₂, hF₂', hI, -, -⟩ := hyp
  have hT1 := hg₁.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT1.2.2.2.1
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have e := Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hI.2.2.2.2.2
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
    have h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁
    exact isUnit_of_mul_isUnit_left h3
  obtain ⟨s, hs, hdet⟩ := gram_det H f₂ f₂' t₁.T t₁.T' hF₂ hF₂' hD₂
  have hgu : IsUnit (H.gram (Sum.elim f₂ f₂')).det := by
    have hsu : IsUnit s := ⟨⟨s, s, hs, hs⟩, rfl⟩
    have : (H.gram (Sum.elim f₂ f₂')).det = H.Gdet f₂ f₂' t₁.T t₁.T' * s := by
      rw [← hdet, mul_assoc, hs, mul_one]
    rw [this]
    exact hG₂.mul hsu
  rcases hsplit : M.split with _ | g
  · have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) = Sum.elim f₂ f₂' := by
      unfold HermSp.MMfam
      rw [hsplit]
    rw [hMM]
    exact hgu
  · set qi : E := algebraMap F E ((g.q : F)⁻¹)
    have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
    have hqi : IsUnit qi := ((Units.mk0 (g.q : F) hq0)⁻¹.isUnit).map (algebraMap F E)
    have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) =
        Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) := by
      unfold HermSp.MMfam
      rw [hsplit]
    let A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      fromBlocks 1 (-(qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))) 0 (qi • 1)
    have hw : Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) = fun j => ∑ i, A i j • Sum.elim f₂ f₂' i := by
      funext j
      rcases j with a | a
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply]
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply, smul_sub, sub_eq_add_neg, add_comm]
    rw [hMM, hw, gram_recomb, det_mul, det_mul, det_transpose]
    have hA : A.det = qi ^ (r + 1) := by
      simp [A, det_fromBlocks_zero₂₁, det_smul]
    have hAm : (A.map M.L.cj).det = M.L.cj A.det := by
      rw [show A.map M.L.cj = (M.L.cj.toRingEquiv.toRingHom).mapMatrix A from rfl, ← RingHom.map_det]
      rfl
    rw [hAm, hA]
    exact ((hqi.pow _).map M.L.cj).mul hgu |>.mul (hqi.pow _)

end Tools

end Formalism.L2.SG.LsDatumA
end
end

