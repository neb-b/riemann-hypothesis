module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.StabilizerSymmMapsOrthogonal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0384
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0361
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SimilitudeConjPreservesUnitaryHaarAtFinitePlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardGluedMiddleLatticesEqPowPrimeSubOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRowAutomorphismsEqLatticeStabilizer
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrbCard

open GlobalTheory.RowsOrb

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem frF_Xa' (F : FlagG S r T) (hT : T ≠ 0) (k : ℕ) : (GlobalTheory.TypeAsm.frF F hT).Xa k = F.Xa k := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa FlagG.Xa
  have h : (fun b : Fin r => (GlobalTheory.TypeAsm.frF F hT).e b.castSucc) = F.e := funext fun b => GlobalTheory.TypeAsm.fv_cast F b
  rw [h]

theorem frF_X' (F : FlagG S r T) (hT : T ≠ 0) : (GlobalTheory.TypeAsm.frF F hT).X = F.X := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X
  rw [frF_Xa']
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x; simp

end Gen

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem fixedFrameOfWord_X : (GlobalTheory.TypeAsm.F0 X u).X = (X.Fu u).X := frF_X' _ _

theorem FuX_eq : (X.Fu u).X = Submodule.span D.host.E (Set.range X.eX) := by
  rw [FlagG.X, X.Fu_e]

theorem Wb_le (w : Wb X) : (w : (VS D).V) ∈ perpS (VS D) (X.Fu u).X := by
  intro y hy
  rw [FuX_eq] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact (w.2 a).1
  | zero => simp
  | add y v _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

def iotaL : Wb X →ₗ[D.host.E] WbQ D (X.Fu u) :=
  (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.nX D (X.Fu u)).mkQ ∘ₗ
    Submodule.inclusion (fun v hv => Wb_le X u ⟨v, hv⟩)

theorem iotaL_apply (w : Wb X) :
    iotaL X u w = Submodule.Quotient.mk ⟨(w : (VS D).V), Wb_le X u w⟩ := rfl

theorem iotaL_bij : Function.Bijective (iotaL X u) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker, iotaL_apply, Submodule.Quotient.mk_eq_zero] at hw
    have hwX : (w : (VS D).V) ∈ Submodule.span D.host.E (Set.range X.eX) := by
      rw [← FuX_eq]; exact hw
    have h1 := Formalism.L2.SG.Pf.pj_X (f := X.fY) X.ee X.ef _ hwX
    rw [Formalism.L2.SG.Pf.pj_perp _ (fun a => w.2 a)] at h1
    exact Subtype.ext h1
  · intro q
    induction q using Submodule.Quotient.induction_on with | H a => ?_
    refine ⟨⟨Formalism.L2.SG.Pf.pj X.eX X.fY (a : (VS D).V), fun b =>
      ⟨Formalism.L2.SG.Pf.hT_e_pj X.ee X.ef _ b, Formalism.L2.SG.Pf.hT_f_pj X.ff X.ef _ b⟩⟩, ?_⟩
    rw [iotaL_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mk_eq_mk]
    show Formalism.L2.SG.Pf.pj X.eX X.fY (a : (VS D).V) - (a : (VS D).V) ∈ (X.Fu u).X
    have h := Formalism.L2.SG.Pf.pj_sub_mem (e := X.eX) (f := X.fY) (a : (VS D).V)
      (fun b => a.2 _ (by rw [FuX_eq]; exact Submodule.subset_span ⟨b, rfl⟩))
    rw [← FuX_eq] at h
    exact h

def iota : Wb X ≃ₗ[D.host.E] WbQ D (X.Fu u) := LinearEquiv.ofBijective (iotaL X u) (iotaL_bij X u)

theorem iota_apply (w : Wb X) : iota X u w = Submodule.Quotient.mk ⟨(w : (VS D).V), Wb_le X u w⟩ := rfl

theorem iota_h (x y : Wb X) : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u) (iota X u x) (iota X u y) = hb X x y := rfl

theorem definiteInclusion_orthogonal_negativeVector : iota X u (zb X u) = PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u) := by
  rw [iota_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar]
  congr 1
  apply Subtype.ext
  exact (X.flagZVector u).symm

theorem iota_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V) (w : Wb X) :
    iota X u w ∈ PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ ↔ w ∈ Lmap X u Λ := by
  rw [PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mem_Mof, mem_Lmap, fixedFrameOfWord_X]
  constructor
  · rintro ⟨a, haΛ, hmk⟩
    rw [iota_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mk_eq_mk] at hmk
    refine Submodule.mem_sup.2 ⟨a, haΛ, (w : (VS D).V) - a, ?_, by abel⟩
    have := Submodule.neg_mem _ hmk
    rw [neg_sub] at this
    exact this
  · intro hw
    obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.1 hw
    have hxX : x ∈ (X.Fu u).X := hx
    have hlp : l ∈ perpS (VS D) (X.Fu u).X := by
      have : l = (w : (VS D).V) - x := by rw [← hlx]; abel
      rw [this]
      exact Submodule.sub_mem _ (Wb_le X u w) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.X_le_perp D (X.Fu u) hxX)
    refine ⟨⟨l, hlp⟩, hl, ?_⟩
    rw [iota_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mk_eq_mk]
    have : l - (w : (VS D).V) = -x := by rw [← hlx]; abel
    show l - (w : (VS D).V) ∈ _
    rw [this]
    exact Submodule.neg_mem _ hxX

end GlobalTheory.RowsOrbCard

namespace GlobalTheory.RowsOrbCard

open GlobalTheory.RowsOrb

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def conj (g : Wb X ≃ₗ[D.host.E] Wb X) : WbQ D (X.Fu u) ≃ₗ[D.host.E] WbQ D (X.Fu u) :=
  (iota X u).symm.trans (g.trans (iota X u))

def unconj (σ : WbQ D (X.Fu u) ≃ₗ[D.host.E] WbQ D (X.Fu u)) : Wb X ≃ₗ[D.host.E] Wb X :=
  (iota X u).trans (σ.trans (iota X u).symm)

theorem conj_iota (g : Wb X ≃ₗ[D.host.E] Wb X) (w : Wb X) : conj X u g (iota X u w) = iota X u (g w) := by
  simp [conj]

theorem conj_unconj (σ : WbQ D (X.Fu u) ≃ₗ[D.host.E] WbQ D (X.Fu u)) : conj X u (unconj X u σ) = σ := by
  ext q; simp [conj, unconj]

theorem unconj_conj (g : Wb X ≃ₗ[D.host.E] Wb X) : unconj X u (conj X u g) = g := by
  ext w; simp [conj, unconj]

theorem conj_isom (g : Wb X ≃ₗ[D.host.E] Wb X) (hg : ∀ x y, hb X (g x) (g y) = hb X x y)
    (x y : WbQ D (X.Fu u)) :
    PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u) (conj X u g x) (conj X u g y) =
      PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u) x y := by
  have e : ∀ q, conj X u g q = iota X u (g ((iota X u).symm q)) := fun q => rfl
  have e2 : ∀ q, iota X u ((iota X u).symm q) = q := fun q => (iota X u).apply_symm_apply q
  rw [e, e, iota_h, hg, ← iota_h, e2, e2]

theorem gmap_conj (Λ : Submodule (𝓞 D.host.E) (VS D).V) (g : Wb X ≃ₗ[D.host.E] Wb X) :
    Formalism.HermitianLatticesTheory.gmap (conj X u g) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ) =
              PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ ↔
      Formalism.HermitianLatticesTheory.gmap g (Lmap X u Λ) = Lmap X u Λ := by
  have key : ∀ w, iota X u w ∈ Formalism.HermitianLatticesTheory.gmap (conj X u g) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ) ↔
      w ∈ Formalism.HermitianLatticesTheory.gmap g (Lmap X u Λ) := by
    intro w
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨(iota X u).symm y, (iota_mem X u Λ _).1 (by simpa using hy), ?_⟩
      apply (iota X u).injective
      rw [← h, ← conj_iota]
      simp
    · rintro ⟨y, hy, h⟩
      refine ⟨iota X u y, (iota_mem X u Λ y).2 hy, ?_⟩
      rw [conj_iota, h]
  constructor
  · intro h
    ext w
    rw [← key, h, iota_mem]
  · intro h
    ext q
    rw [← (iota X u).apply_symm_apply q, key, h, iota_mem]

theorem conj_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V) (g : MulAction.stabilizer (Gz X u) (Lmap X u Λ)) :
    conj X u (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) ∈
      PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.stabZ (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u))
        (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u)) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ) := by
  have hz : (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) (zb X u) = zb X u :=
    MulAction.mem_stabilizer_iff.1 (g : Gz X u).2
  have hL : Formalism.HermitianLatticesTheory.gmap (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) (Lmap X u Λ) =
      Lmap X u Λ := MulAction.mem_stabilizer_iff.1 g.2
  have hg : ∀ x y, hb X ((((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) x)
      ((((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) y) = hb X x y :=
    ((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)).2
  refine ⟨⟨conj_isom X u _ hg, ?_⟩, (gmap_conj X u Λ _).2 hL⟩
  have e := conj_iota X u (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) (zb X u)
  rw [hz, definiteInclusion_orthogonal_negativeVector] at e
  exact e

theorem unconj_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (σ : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.stabZ (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u))
        (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u)) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ)) :
    ∃ (h1 : unconj X u σ.1 ∈ Formalism.HermitianLatticesTheory.isom (hb X)) (h2 : (⟨unconj X u σ.1, h1⟩ : Formalism.HermitianLatticesTheory.isom (hb X)) ∈ Gz X u),
      (⟨⟨unconj X u σ.1, h1⟩, h2⟩ : Gz X u) ∈ MulAction.stabilizer (Gz X u) (Lmap X u Λ) := by
  obtain ⟨⟨hi, hz⟩, hM⟩ := σ.2
  have h1 : unconj X u σ.1 ∈ Formalism.HermitianLatticesTheory.isom (hb X) := by
    intro x y
    rw [← iota_h, ← iota_h]
    have e : ∀ w, iota X u (unconj X u σ.1 w) = σ.1 (iota X u w) := fun w => by simp [unconj]
    rw [e, e]
    exact hi _ _
  refine ⟨h1, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    show unconj X u σ.1 (zb X u) = zb X u
    apply (iota X u).injective
    simp only [unconj, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, definiteInclusion_orthogonal_negativeVector]
    exact hz
  · rw [MulAction.mem_stabilizer_iff]
    show Formalism.HermitianLatticesTheory.gmap (unconj X u σ.1) (Lmap X u Λ) = Lmap X u Λ
    rw [← gmap_conj, conj_unconj]
    exact hM

theorem card_stab (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Nat.card (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.stabZ (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u))
        (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u)) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ)) =
      Nat.card (MulAction.stabilizer (Gz X u) (Lmap X u Λ)) := by
  refine (Nat.card_congr
    { toFun := fun g => ⟨conj X u (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X), conj_mem X u Λ g⟩
      invFun := fun σ => ⟨⟨⟨unconj X u σ.1, (unconj_mem X u Λ σ).1⟩, (unconj_mem X u Λ σ).2.1⟩,
        (unconj_mem X u Λ σ).2.2⟩
      left_inv := fun g => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        exact unconj_conj X u _
      right_inv := fun σ => by
        apply Subtype.ext
        exact conj_unconj X u _ }).symm

end GlobalTheory.RowsOrbCard

namespace GlobalTheory.RowsOrb

theorem card_autLz : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ →
    ∀ Λ ∈ Y.what₂ u, Nat.card (autLz D (X.Fu u) Λ) =
      Nat.card (MulAction.stabilizer (GlobalTheory.RowsOrb.Gz X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  intro D large₂ X Y u _ Λ hΛ
  rw [PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_weight_formula D u (X.Fu u) Λ ((Y.rowsOK u).1 Λ hΛ)]
  exact GlobalTheory.RowsOrbCard.card_stab X u Λ

end GlobalTheory.RowsOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DepthZeroIdentityFiniteTypeOfTypePrimeComponent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

noncomputable section

open GlobalTheory.LabPin

namespace GlobalTheory.DepthZeroSer

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem rt_rt' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (h h' : GAf L n) (f : GAf L n → ℂ) :
    NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
  funext x; simp [NG.rt, mul_assoc]

theorem rt_one' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (f : GAf L n → ℂ) :
    NG.rt L n 1 f = f := by
  funext x; simp [NG.rt]

theorem nontrivial_of_irr {G : Type} [Group G] [TopologicalSpace G] (τ : GlobalTheory.SmGL.IrrRep G) : Nontrivial τ.V := by
  haveI := τ.irr
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
  ext x
  simp [Subsingleton.elim x 0]

theorem serFix_of_locS {L : Type} [Field L] [NumberField L] [IsCMField L] {n g : ℕ} [Fact g.Prime]
    (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (j : ℚ_[g] ≃+* s.w.adicCompletion L) (hj : Continuous j) (a : MonoidAlgebra ℂ (GL (Fin n) (ZMod g)))
    (hloc : GlobalTheory.HeightCounting.IsLocS π.S s τ)
    (ha : ∀ y ∈ GlobalTheory.GLp.fixK1 (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)),
      GlobalTheory.GLp.actK (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)) a y = y) :
    SerFix π s a := by
  classical
  obtain ⟨i, T, hi, -, hT, hTS, hTeq⟩ := hloc
  set ρ' := τ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) j.toRingHom) with hρ'
  set θ : s.v.adicCompletion (maximalRealSubfield L) ≃+* ℚ_[g] := i.trans j.symm with hθdef
  have hθ : ∀ z, Valued.v z < 1 ↔ ‖θ z‖ < 1 := fun z => _root_.GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous L s g i j hi hj z
  have hτθ : ∀ A : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom A) = ρ' (Matrix.GeneralLinearGroup.map θ.toRingHom A) := by
    intro A
    simp only [hρ', MonoidHom.coe_comp, Function.comp_apply]
    congr 1
    ext a b
    simp [θ]
  have hI := _root_.GlobalTheory.SplitAdelic.main L n s
  haveI := nontrivial_of_irr τ
  intro ℓ hℓ φ hφS hφfix
  let N : {y : GAf L n // TrivOutside {s.v}ᶜ y} → Submodule ℂ (GAf L n → ℂ) :=
    fun y => LinearMap.range ((NG.rt L n y.1).comp T)
  have hspan := _root_.GlobalTheory.SerSys.finTyp_eq_iSup_rt_local L n π s τ.V T hT hTS (fun x hx a => ⟨_, (hTeq x hx a).symm⟩)
  have hNst : ∀ y x, TrivOutside {s.v} x → ∀ f ∈ N y, NG.rt L n x f ∈ N y := by
    rintro y x hx f ⟨b, rfl⟩
    refine ⟨τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) b, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hTeq x hx b, rt_rt', rt_rt', (hI.2.1 x y.1 hx y.2).eq]
  have hsupst : ∀ (J : Finset _) x, TrivOutside {s.v} x → ∀ f ∈ ⨆ j ∈ J, N j, NG.rt L n x f ∈ ⨆ j ∈ J, N j := by
    intro J x hx f hf
    have : (⨆ j ∈ J, N j) ≤ (⨆ j ∈ J, N j).comap (NG.rt L n x) := by
      refine iSup₂_le fun j hj => ?_
      intro f hf
      exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hNst j x hx f hf))
    exact this hf
  have hdich : ∀ y (J : Finset _), Disjoint (N y) (⨆ j ∈ J, N j) ∨ N y ≤ ⨆ j ∈ J, N j :=
    fun y J => _root_.GlobalTheory.SlocDich.translate_dichotomy L n s τ i T hT hTeq y.1 y.2 _ (hsupst J)
  have hφ : φ ∈ ⨆ y, N y := hspan ▸ hφS
  obtain ⟨F, hF⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  obtain ⟨J, -, hJsup, hJuniq⟩ := _root_.GlobalTheory.indep_subfamily_of_disjoint_or_le _ _ N hdich F
  rw [← hJsup] at hF
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum N φ).1 hF
  choose c hc using fun y => (μ y).2
  have hφsum : φ = ∑ y ∈ J, NG.rt L n y.1 (T (c y)) := by
    rw [← hμ]; exact Finset.sum_congr rfl fun y _ => (hc y).symm
  have hinj : ∀ (y : {y : GAf L n // TrivOutside {s.v}ᶜ y}), Function.Injective (fun b => NG.rt L n y.1 (T b)) := by
    intro y b b' h
    apply hT
    have := congrArg (NG.rt L n y.1⁻¹) h
    simpa [rt_rt', rt_one'] using this
  have hfix : ∀ y ∈ J, c y ∈ GlobalTheory.GLp.fixK1 ρ' := by
    intro y hy
    simp only [GlobalTheory.GLp.fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro kk
    obtain ⟨x, ⟨hx1, hx2⟩, -⟩ := hI.2.2 (Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n kk))
    have hlift : IsLift s x (1 : GL (Fin n) (ZMod g)) :=
      ⟨hx1, fun p q => by
        have H := _root_.GlobalTheory.GLp.inc_map_sub_one_valued_lt_one _ s.v g n θ (fun z => (hθ z).2) (kk : GL (Fin n) ℤ_[g]) kk.2 p q
        rw [hx2]
        exact H⟩
    have hx := hφfix x hlift
    have hθx : Matrix.GeneralLinearGroup.map θ.toRingHom (s.loc n x) = GlobalTheory.GLp.inc g n kk := by
      rw [hx2]; ext; simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφsum, map_sum] at hx
    have hx' : ∑ y ∈ J, NG.rt L n y.1 (T (ρ' (GlobalTheory.GLp.inc g n kk) (c y))) = ∑ y ∈ J, NG.rt L n y.1 (T (c y)) := by
      rw [← hx]; refine Finset.sum_congr rfl fun y _ => ?_
      rw [← hθx, ← hτθ, hTeq x hx1, rt_rt', rt_rt', (hI.2.1 x y.1 hx1 y.2).eq]
    exact hinj y (hJuniq _ _ (fun y _ => ⟨_, rfl⟩) (fun y _ => ⟨_, rfl⟩) hx' y hy)
  have hfix' : ∀ y ∈ J, ∀ kk ∈ (GlobalTheory.GLp.red g n).ker, ρ' (GlobalTheory.GLp.inc g n kk) (c y) = c y := by
    intro y hy kk hkk
    have := hfix y hy
    simp only [GlobalTheory.GLp.fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at this
    exact this ⟨kk, hkk⟩
  have hℓ' : ∀ γ, ∃ kk ∈ (GlobalTheory.GLp.red g n).ker,
      Matrix.GeneralLinearGroup.map θ.toRingHom (s.loc n (ℓ γ)) = GlobalTheory.GLp.lift g n γ * GlobalTheory.GLp.inc g n kk :=
    fun γ => _root_.GlobalTheory.LiftRed.liftred_exists _ s.v g n θ (fun z => (hθ z).1) _ γ (hℓ γ).2
  choose kk hkk hkkeq using hℓ'
  have hterm : ∀ γ, NG.rt L n (ℓ γ) φ = ∑ y ∈ J, NG.rt L n y.1 (T (ρ' (GlobalTheory.GLp.lift g n γ) (c y))) := by
    intro γ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφsum, map_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [rt_rt', (hI.2.1 (ℓ γ) y.1 (hℓ γ).1 y.2).eq, ← rt_rt', ← hTeq _ (hℓ γ).1, hτθ, hkkeq, map_mul,
      Module.End.mul_apply, hfix' y hy _ (hkk γ)]
  rw [finsum_eq_sum_of_fintype]
  calc ∑ γ, a.coeff γ • NG.rt L n (ℓ γ) φ = ∑ y ∈ J, NG.rt L n y.1 (T (GlobalTheory.GLp.actK ρ' a (c y))) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hterm, Finset.smul_sum, GlobalTheory.GLp.actK, LinearMap.sum_apply,
          LinearMap.smul_apply, map_sum, map_smul]
        exact Finset.sum_comm
    _ = φ := by
        rw [hφsum]
        exact Finset.sum_congr rfl fun y hy => by rw [ha _ (hfix y hy)]

theorem serFix_of_locS' {L : Type} [Field L] [NumberField L] [IsCMField L] {n g : ℕ} [Fact g.Prime]
    (π : NG.FinTyp L n) (s : SplitPlace L) {w : HeightOneSpectrum (𝓞 L)} (h : s.w = w)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion L)))
    (j : ℚ_[g] ≃+* w.adicCompletion L) (hj : Continuous j) (a : MonoidAlgebra ℂ (GL (Fin n) (ZMod g)))
    (hloc : GlobalTheory.HeightCounting.IsLocS π.S s (h ▸ τ))
    (ha : ∀ y ∈ GlobalTheory.GLp.fixK1 (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)),
      GlobalTheory.GLp.actK (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)) a y = y) :
    SerFix π s a := by
  subst h
  exact serFix_of_locS π s τ j hj a hloc ha

theorem serFix_of_comp : ∀ (D : D7) (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (cp : GlobalTheory.GoodTypes.Comp D), IsComp I rep cp → ∀ σ k v (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))), (∀ y ∈ fixK1 (cp σ k v).ρ, actK (cp σ k v).ρ a y = y) → ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → GlobalTheory.LabPin.SerFix (rep σ) s a := by
  intro D I rep cp hc σ k v a ha s hs
  obtain ⟨s₀, h₀, τ, hloc, hcp⟩ := hc σ k v
  obtain rfl : s = s₀ := _root_.GlobalTheory.SplitUniqSer.splitPlace_unique _ s s₀ (hs.trans h₀.symm)
  rw [hcp] at ha
  exact serFix_of_locS' (rep σ) s h₀ τ (I.i k v) (I.cont k v) a hloc ha

end GlobalTheory.DepthZeroSer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameStabilizerHaarNormalisedFibreMeasure
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalStabiliserTie

theorem exists_tied_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → Formalism.L2.SG.LocVol.IsStdChar ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → 2 * (r + 1) < n → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ Formalism.L2.SG.LocVol.LocTieW σ J ψ v P μG μS := by
  intro F E _ _ _ _ _ σ hcm n J hJ hW hC ψ hψ hstd v r P T hP hn μG hG
  obtain ⟨-, -, hT, -, -⟩ := GlobalTheory.FrameGram.std_frame_gram F E σ hcm n J hJ r P T hP
  obtain ⟨hdX, hdT, hOm⟩ := _root_.GlobalTheory.LocalFibre.dX_dT_omFam F E σ hcm n J hJ hW hC ψ hψ v (r + 1) (by omega) hn
  have hfib : IsFibreFamily (Formalism.L2.SG.LocVol.dX σ J ψ v (r + 1)) (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} (Formalism.L2.SG.LocVol.dT σ ψ v (r + 1)) Set.univ
      (Formalism.L2.SG.LocVol.omFam σ J ψ v (r + 1)) := hOm
  obtain ⟨μ0, hμ0, hc1, hc2⟩ := _root_.GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser F E σ hcm n J hJ v r P T hP hT _ _ hdX hdT _ hfib μG hG
  have hconj := _root_.GlobalTheory.ConjStabiliserHaar.conj_preserves_haar F E σ hcm n J hJ v r P T hP hT _ _ hdX hdT _ hfib μ0 hμ0
  have hne : ∃ x, psiV F ψ v x ≠ 1 := GlobalTheory.StdCharTotReal.exists_psiV_ne_one F hcm.1 ψ hψ hstd v
  have hsd := GlobalTheory.TraceSelfDual.exists_selfDual_trace F E σ hcm ψ hψ v hne (Formalism.L2.SG.LocVol.UIdx r)
  have hU : (Formalism.L2.SG.LocVol.sdE (E := E) ψ v (Formalism.L2.SG.LocVol.UIdx r)).IsAddHaarMeasure := by
    unfold Formalism.L2.SG.LocVol.sdE
    rw [dite_eq_left hsd]
    exact hsd.choose_spec.1
  obtain ⟨μS, hμS, hprod⟩ := GlobalTheory.T.haar_frameStabilizer_local_fixer_section_product F E σ hcm n J hJ v r P T hP μ0 hμ0 hconj _ hU
  refine ⟨μS, hμS, μ0, hμ0, ?_, ?_⟩
  · have hom : Formalism.L2.SG.LocVol.omAt σ J ψ v (Formalism.L2.SG.LocVol.TFl σ J v P)
        = Formalism.L2.SG.LocVol.omFam σ J ψ v (r + 1) (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT) := by
      unfold Formalism.L2.SG.LocVol.omAt
      have hmem : Formalism.L2.SG.LocVol.TFl σ J v P ∈ HermR (Fv F v) σ (r + 1) :=
        map_mem_HermR (Fv F v) σ _ hT
      rw [dite_eq_left hmem]
      rfl
    unfold Formalism.L2.SG.LocVol.IsCompatLoc
    rw [hom]
    exact ⟨hc1, hc2⟩
  · intro h hh t ht
    exact hprod h hh t ht

end GlobalTheory.LocalStabiliserTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardGluedMiddleLatticesEqPowPrimeSubOneStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_gluedMiddleLattices_eq_pow_prime_sub_one : ∀ (D : D7) (u : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → IsBase D u F0 → IsRowLat D F0 Λ → ∀ L' ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)), (glueSet D u L').Finite ∧ (glueSet D u L').ncard = (Tu D u - 1) ^ D.R.f := by
  first | exact @GlobalTheory.LoopC.GlueCount.main | exact GlobalTheory.LoopC.GlueCount.main | (intros; apply GlobalTheory.LoopC.GlueCount.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowBaseLatticesMemSameHermitianGenusStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowBaseLattices_mem_same_hermitianGenus : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Λ' : LatV D, IsRowLat D F0 Λ' → L0X D Λ' (lf D F0) ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)) := by
  first | exact @GlobalTheory.LoopC.RowsGenus.main | exact GlobalTheory.LoopC.RowsGenus.main | (intros; apply GlobalTheory.LoopC.RowsGenus.main <;> assumption)
end

