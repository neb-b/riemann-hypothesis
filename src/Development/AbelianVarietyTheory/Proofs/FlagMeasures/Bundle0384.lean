module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SymmMemOfMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.SpanFrameLtSucc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.LeadMinorEMulUpper
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0368
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0035
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalInnerLatticeEqOfInnerPreimageEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalGraphEqOfLocalIotaAgree
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitRowLatticeMiddleIffGluedLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Assembly
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenus
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteTypeEqISupSplitTrivialTranslatesLocal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SerSys

theorem finTyp_eq_iSup_rt_local : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V] (T : V →ₗ[ℂ] (GAf L n → ℂ)), Function.Injective T → (∀ a, T a ∈ π.S) → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, ∃ b, NG.rt L n x (T a) = T b) → π.S = ⨆ y : {y : GAf L n // TrivOutside {s.v}ᶜ y}, LinearMap.range ((NG.rt L n y.1).comp T) := by
  intro L _ _ _ n π s V _ _ _ T hT hTS hx
  obtain ⟨hdec, hcomm, -⟩ := _root_.GlobalTheory.SplitAdelic.main L n s
  have hrt : ∀ (h h' : GAf L n) (f : GAf L n → ℂ), NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
    intro h h' f; funext g; simp [NG.rt, mul_assoc]
  have hone : ∀ f : GAf L n → ℂ, NG.rt L n 1 f = f := by
    intro f; funext g; simp [NG.rt]
  have h1 : TrivOutside {s.v}ᶜ (1 : GAf L n) := by
    intro v _; simp
  set Wd := ⨆ y : {y : GAf L n // TrivOutside {s.v}ᶜ y}, LinearMap.range ((NG.rt L n y.1).comp T) with hWd
  have hle : Wd ≤ π.S := by
    refine iSup_le fun y => ?_
    rintro f ⟨a, rfl⟩
    exact π.stable _ _ (hTS a)
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro y _ ⟨a, rfl⟩
      obtain ⟨x, y', hx1, hy', he⟩ := hdec (h * y.1)
      obtain ⟨b, hb⟩ := hx x hx1 a
      have : NG.rt L n h (NG.rt L n y.1 (T a)) = NG.rt L n y' (T b) := by
        rw [hrt, he, (hcomm x y' hx1 hy').eq, ← hrt, hb]
      simp only [LinearMap.comp_apply]
      rw [this]
      exact Submodule.mem_iSup_of_mem (⟨y', hy'⟩ : {y : GAf L n // TrivOutside {s.v}ᶜ y}) ⟨b, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add (f := _)]; exact Submodule.add_mem _ h₁ h₂
  rcases π.irr Wd hle hstab with h0 | h0
  · exfalso
    obtain ⟨a, ha⟩ := exists_ne (0 : V)
    have hmem : T a ∈ Wd := by
      have := Submodule.mem_iSup_of_mem (p := fun y : {y : GAf L n // TrivOutside {s.v}ᶜ y} => LinearMap.range ((NG.rt L n y.1).comp T)) (⟨1, h1⟩ : {y : GAf L n // TrivOutside {s.v}ᶜ y}) (⟨a, rfl⟩ : ((NG.rt L n 1).comp T) a ∈ LinearMap.range ((NG.rt L n 1).comp T))
      simpa [hone] using this
    rw [h0, Submodule.mem_bot] at hmem
    exact ha (hT (by rw [hmem, map_zero]))
  · exact h0.symm

end GlobalTheory.SerSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagTermInvariantsConstOnRationalDoubleCoset
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.CosetConst

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem mem_orth_iff' {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem frame_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T)
    (a : Fin (r + 1)) : frame (mapLF γ F) a = γ (frame F a) := by
  unfold mapLF; rw [dite_eq_left hγ]
  induction a using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem zt_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    (mapLF γ F).zt = γ F.zt := by
  unfold mapLF; rw [dite_eq_left hγ]

theorem Xflag_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapLF γ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF; rw [dite_eq_left hγ]
  show Submodule.span E ((fun a => γ (F.fl.e a)) '' {i | i.1 < j}) =
    (Submodule.span E (F.fl.e '' {i | i.1 < j})).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, Set.image_image]
  rfl

theorem Xsp_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    Xsp (mapLF γ F) = (Xsp F).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF; rw [dite_eq_left hγ]
  show Submodule.span E (Set.range fun a => γ (F.fl.e a)) =
    (Submodule.span E (Set.range F.fl.e)).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem gmap_top (γ : S.V ≃ₗ[E] S.V) : Formalism.HermitianLatticesTheory.gmap γ (⊤ : Submodule (𝓞 E) S.V) = ⊤ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_top, LinearMap.range_eq_top]
  intro y
  exact ⟨γ.symm y, by simp⟩

end Gen

section D

variable {D : D7}

theorem nlam_top_of_nrat {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat F) : n ∈ NLam (⊤ : Submodule (𝓞 D.host.E) (VS D).V) F :=
  ⟨⟨hn.1, gmap_top n⟩, hn.2.1, hn.2.2⟩

theorem conj_nlam_top {T : D.host.E} {G : LFlag (D.sp.Y 0) D.R.rS T} {γ m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hm : m ∈ NRat G) :
    γ * m * γ⁻¹ ∈ NLam (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (mapLF γ G) := by
  obtain ⟨hi, hf, hp⟩ := hm
  have happ : ∀ y, (γ * m * γ⁻¹) (γ y) = γ (m y) := fun y => by
    show γ (m (γ.symm (γ y))) = γ (m y)
    rw [γ.symm_apply_apply]
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hγ hi) ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ),
    gmap_top _⟩, ?_, ?_⟩
  · intro j x hx
    rw [Xflag_mapLF hγ] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    have e : (γ * m * γ⁻¹) ((γ : (VS D).V →ₗ[D.host.E] (VS D).V) y) - (γ : (VS D).V →ₗ[D.host.E] (VS D).V) y =
        (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (m y - y) := by
      rw [map_sub]
      exact congrArg (· - _) (happ y)
    rw [e]
    exact Submodule.mem_map_of_mem (hf j y hy)
  · intro x hx
    have hXs := Xsp_mapLF hγ G
    have hy : γ.symm x ∈ orth (VS D) (Xsp G) := by
      rw [mem_orth_iff'] at hx ⊢
      intro w hw
      have h1 := hx (γ w) (by rw [hXs]; exact Submodule.mem_map_of_mem hw)
      have h2 := hγ w (γ.symm x)
      rw [γ.apply_symm_apply] at h2
      rw [← h2]
      exact h1
    have h3 := hp _ hy
    have e : (γ * m * γ⁻¹) x - x = (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (m (γ.symm x) - γ.symm x) := by
      show γ (m (γ.symm x)) - x = γ (m (γ.symm x) - γ.symm x)
      rw [map_sub, γ.apply_symm_apply]
    rw [e, hXs]
    exact Submodule.mem_map_of_mem h3

end D

end GlobalTheory.HL.CosetConst

namespace GlobalTheory.HL.CosetConst

section Terms

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem dcrel_of_coset (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m) :
    Formalism.L2.SG.TermDef.DCRel (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D (X.Fu u)) t₀.frame t.frame := by
  have h0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have h1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hn' : n⁻¹ ∈ NRat (lf D (X.Fu u)) := Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv _ hn
  refine ⟨n⁻¹, nlam_top_of_nrat hn', t₀.lin * m * t₀.lin⁻¹, conj_nlam_top h0 hm, fun a => ?_, ?_⟩
  · show frame (mapLF t.lin (lf D (X.Fu u'))) a =
      n⁻¹ ((t₀.lin * m * t₀.lin⁻¹) (frame (mapLF t₀.lin (lf D (X.Fu u'))) a))
    rw [frame_mapLF h1, frame_mapLF h0, h]
    show n.symm (t₀.lin (m _)) = n.symm (t₀.lin (m (t₀.lin.symm (t₀.lin _))))
    rw [LinearEquiv.symm_apply_apply]
  · show (mapLF t.lin (lf D (X.Fu u'))).zt =
      n⁻¹ ((t₀.lin * m * t₀.lin⁻¹) (mapLF t₀.lin (lf D (X.Fu u'))).zt)
    rw [zt_mapLF h1, zt_mapLF h0, h]
    show n.symm (t₀.lin (m _)) = n.symm (t₀.lin (m (t₀.lin.symm (t₀.lin _))))
    rw [LinearEquiv.symm_apply_apply]

theorem relevant_iff (s : TauC Y u u') :
    s.relevant ↔ Relevant D.host.F (lf D (X.Fu u)).fl s.frame.fl :=
  Formalism.L2.SG.TermDef.isRel_mk D.host.F
    (PI.TermAttrConst.UnitaryGroupMassFormula.relFun_all D.host.F s.lam (lf D (X.Fu u))
      (Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u')) ⟨s.frame, s.rep.2.2.2.2⟩

theorem atPt_iff (s : TauC Y u u') (w : Point D.host.E (D.R.rS + 1)) :
    s.toTerm.atPt w ↔ Gval (lf D (X.Fu u)) s.frame ≠ 0 ∧
      IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) s.frame)) w :=
  Formalism.L2.SG.TermDef.atPt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) (PI.TermAttrConst.UnitaryGroupMassFormula.cellFun_all _ _ _)
    ⟨s.frame, s.rep.2.2.2.2⟩ w

end Terms

end GlobalTheory.HL.CosetConst

namespace GlobalTheory.HL.CosetConst

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem nml_eq (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m) :
    nmlOf Y u u' t = nmlOf Y u u' t₀ := by
  have hni : n⁻¹ ∈ NRat (lf D (X.Fu u)) := Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv _ hn
  have hmi : m⁻¹ ∈ NRat (lf D (X.Fu u')) := Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv _ hm
  ext δ
  simp only [nmlOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a * n⁻¹, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul _ ha hni, m * b,
      Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul _ hm hb, ?_⟩
    rw [h]; simp only [mul_assoc, inv_mul_cancel_left]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a * n, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul _ ha hn, m⁻¹ * b,
      Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul _ hmi hb, ?_⟩
    rw [h]; simp only [mul_assoc, mul_inv_cancel_left]

theorem G_eq_frames (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m) :
    Gval (lf D (X.Fu u)) t₀.frame = Gval (lf D (X.Fu u)) t.frame :=
  PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D (X.Fu u))
    (fun _ => True) ⟨t₀.frame, trivial⟩ ⟨t.frame, trivial⟩ (dcrel_of_coset t₀ t hn hm h)

theorem cell_iff_frames (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m)
    (w : Point D.host.E (D.R.rS + 1)) :
    IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t₀.frame)) w ↔ IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w :=
  PI.TermAttrConst.UnitaryGroupMassFormula.cellFun_all (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D (X.Fu u))
    (fun _ => True) ⟨t₀.frame, trivial⟩ ⟨t.frame, trivial⟩ (dcrel_of_coset t₀ t hn hm h) w

theorem rel_iff_frames (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m) :
    Relevant D.host.F (lf D (X.Fu u)).fl t₀.frame.fl ↔ Relevant D.host.F (lf D (X.Fu u)).fl t.frame.fl :=
  PI.TermAttrConst.UnitaryGroupMassFormula.relFun_all D.host.F (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D (X.Fu u))
    (fun _ => True) ⟨t₀.frame, trivial⟩ ⟨t.frame, trivial⟩ (dcrel_of_coset t₀ t hn hm h)

theorem pt_eq (t₀ t : TauC Y u u') (hrl : t.relevant ↔ t₀.relevant) (hat : ∀ w, t.toTerm.atPt w ↔ t₀.toTerm.atPt w) :
    Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.ptOf t₀.toTerm := by
  have hCP := Formalism.L2.SG.Pf.cell_point_unique_of_term_fun (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u)
  by_cases hx : ∃ w, t₀.toTerm.atPt w ∧ t₀.toTerm.relevant
  · have hx' : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant := by
      obtain ⟨w, hw, hr⟩ := hx
      exact ⟨w, (hat w).2 hw, hrl.2 hr⟩
    exact hCP t₀.toTerm _ _ ((hat _).1 (Formalism.L2.SG.PairVal.ptOf_spec t.toTerm hx'))
      (Formalism.L2.SG.PairVal.ptOf_spec t₀.toTerm hx)
  · have hx' : ¬ ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant := by
      rintro ⟨w, hw, hr⟩
      exact hx ⟨w, (hat w).1 hw, hrl.1 hr⟩
    unfold Formalism.L2.SG.PairVal.ptOf
    rw [dite_eq_right hx, dite_eq_right hx']

end GlobalTheory.HL.CosetConst

theorem GlobalTheory.HL.CosetConst.coset_const : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Formalism.MainNotions.S.Cnt.Stand D u u' →
    ∀ (t₀ t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), t₀.relevant → t₀.G ≠ 0 →
      n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m →
      t.relevant ∧ t.G = t₀.G ∧ Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.ptOf t₀.toTerm ∧
        nmlOf Y u u' t = nmlOf Y u u' t₀ ∧
        ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → (Y.tO u u').s0 t₀ t = 1 ∧ (Y.tO u u').scal t₀ t) := by
  intro D X Y u u' _ t₀ t n m hrel hG hnm
  obtain ⟨hn, hm, h⟩ := hnm
  have eG := GlobalTheory.HL.CosetConst.G_eq_frames t₀ t hn hm h
  have hrl : t.relevant ↔ t₀.relevant := by
    rw [GlobalTheory.HL.CosetConst.relevant_iff, GlobalTheory.HL.CosetConst.relevant_iff]
    exact (GlobalTheory.HL.CosetConst.rel_iff_frames t₀ t hn hm h).symm
  have hat : ∀ w, t.toTerm.atPt w ↔ t₀.toTerm.atPt w := fun w => by
    rw [GlobalTheory.HL.CosetConst.atPt_iff, GlobalTheory.HL.CosetConst.atPt_iff, eG,
      GlobalTheory.HL.CosetConst.cell_iff_frames t₀ t hn hm h w]
  have hnml := GlobalTheory.HL.CosetConst.nml_eq t₀ t hn hm h
  refine ⟨hrl.2 hrel, ?_, GlobalTheory.HL.CosetConst.pt_eq t₀ t hrl hat, hnml,
    fun hr => _root_.GlobalTheory.SnFamCoset.scalar_of_same_coset D X Y u u' t₀ t hG hr.symm hnml.symm⟩
  rw [Formalism.L2.SG.Pf.SatGram.gterm_G (X := X) (Y := Y) (t := t),
    Formalism.L2.SG.Pf.SatGram.gterm_G (X := X) (Y := Y) (t := t₀), eG]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalInnerDatumEqIffLocalDataEq
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.InnerDict

theorem inner_of_term : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r), LocNG.IsTermOver P d τ → (d.L : Set (H.Wb P.A.f)) = H.Lset τ.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset τ.abelian₂ P.B.f := _root_.GlobalTheory.InnerRead.datum_eq_Lset

theorem lset_eq_of_lsub_eq : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (Fr : LocNG.FrameD (locH Z p) D.R.rS), Fr.f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ G = Lsub Λ₂ G → (locH Z p).Lset (lattice₂ D Z.M p Λ₁) Fr.f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) Fr.f := _root_.GlobalTheory.Unfold.InnerLoc.lset_eq_of_lsub_eq

theorem lsub_eq_of_lset_eq : ∀ (D : D7) (Z : LocDat D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (Fr : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (Fr p).f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → (∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (Fr p).f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (Fr p).f) → Lsub Λ₁ G = Lsub Λ₂ G := _root_.GlobalTheory.Unfold.LsubG.lsub_eq_of_local

theorem iota_eq_of_graph_eq : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 → ∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ := _root_.GlobalTheory.Unfold.IotaLocal.iotaGraph_eq_of_gdat

theorem graph_eq_of_iota_eq : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩) → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 := _root_.GlobalTheory.Unfold.IotaGlob.graph_eq_of_local_iota

theorem datum_ext {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Loc.HermSp M V} {r : ℕ} {P : LocNG.FPair H r} (d d' : LocNG.Datum P) (h1 : d.L = d'.L) (h2 : d.L' = d'.L') (h3 : d.io = d'.io) : d = d' := by
  cases d; cases d'; simp only at h1 h2 h3; subst h1 h2 h3; rfl

theorem gdat_eq_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ₁ Λ₂ : LV D) (y₁ y₂ : Dat Z FP), LocOver Λ₁ y₁ → LocOver Λ₂ y₂ → (gdat F F' Λ₁ = gdat F F' Λ₂ ↔ y₁ = y₂) := by
  intro D X Y u u' F F' w _ _ Z FP hB _ Λ₁ Λ₂ y₁ y₂ h₁ h₂
  have hL : ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ p,
      ((y p).L : Set _) = (locH Z p).Lset (lattice₂ D Z.M p Λ) (FP p).A.f ∧
      ((y p).L' : Set _) = (locH Z p).Lset (lattice₂ D Z.M p Λ) (FP p).B.f ∧
      ∀ g, (Z.M p).split = some g → (y p).io = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ := by
    intro Λ y hy p
    obtain ⟨τ, hτ, hlam⟩ := hy.2 p
    have h1 := inner_of_term (locH Z p) D.R.rS (FP p) (y p) τ hτ
    refine ⟨h1.1.trans (congrArg (fun L => (locH Z p).Lset L (FP p).A.f) hlam),
      h1.2.trans (congrArg (fun L => (locH Z p).Lset L (FP p).B.f) hlam), fun g hg => ?_⟩
    have h2 := (hτ.2.2.2.2 g hg).2
    have e4 : ∀ (L : Submodule (Z.M p).L.O (Vp D p)) (a b c e : (D.s.atP p).Fp), L = lattice₂ D Z.M p Λ →
        (locH Z p).iotaGraph g ⟨L, (FP p).A.f, (FP p).B.f, a, b⟩ =
          (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ, (FP p).A.f, (FP p).B.f, c, e⟩ := by
      intro L a b c e hL; subst hL; rfl
    exact h2.symm.trans (e4 _ _ _ _ _ hlam)
  constructor
  · intro hg
    have hF : Lsub Λ₁ F = Lsub Λ₂ F := congrArg (fun t => t.1) hg
    have hF' : Lsub Λ₁ F' = Lsub Λ₂ F' := congrArg (fun t => t.2.1) hg
    have hΓ := congrArg (fun t => t.2.2) hg
    funext p
    apply datum_ext
    · apply SetLike.coe_injective
      exact (hL Λ₁ y₁ h₁ p).1.trans ((lset_eq_of_lsub_eq D Z p F (FP p).A (hB p).1 Λ₁ Λ₂ h₁.1 h₂.1 hF).trans (hL Λ₂ y₂ h₂ p).1.symm)
    · apply SetLike.coe_injective
      exact (hL Λ₁ y₁ h₁ p).2.1.trans ((lset_eq_of_lsub_eq D Z p F' (FP p).B (hB p).2.1 Λ₁ Λ₂ h₁.1 h₂.1 hF').trans (hL Λ₂ y₂ h₂ p).2.1.symm)
    · cases hs : (Z.M p).split with
      | none => exact ((y₁ p).io_L hs).trans ((y₂ p).io_L hs).symm
      | some g =>
        exact ((hL Λ₁ y₁ h₁ p).2.2 g hs).trans ((iota_eq_of_graph_eq D Z FP _ _ F F' hB Λ₁ Λ₂ h₁.1 h₂.1 hF hF' hΓ p g hs).trans
          ((hL Λ₂ y₂ h₂ p).2.2 g hs).symm)
  · intro hy
    subst hy
    have hF : Lsub Λ₁ F = Lsub Λ₂ F :=
      lsub_eq_of_lset_eq D Z F (fun p => (FP p).A) (fun p => (hB p).1) Λ₁ Λ₂ h₁.1 h₂.1
        (fun p => (hL Λ₁ y₁ h₁ p).1.symm.trans (hL Λ₂ y₁ h₂ p).1)
    have hF' : Lsub Λ₁ F' = Lsub Λ₂ F' :=
      lsub_eq_of_lset_eq D Z F' (fun p => (FP p).B) (fun p => (hB p).2.1) Λ₁ Λ₂ h₁.1 h₂.1
        (fun p => (hL Λ₁ y₁ h₁ p).2.1.symm.trans (hL Λ₂ y₁ h₂ p).2.1)
    have hΓ := graph_eq_of_iota_eq D Z FP _ _ F F' hB Λ₁ Λ₂ h₁.1 h₂.1 hF hF'
      (fun p g hs => ((hL Λ₁ y₁ h₁ p).2.2 g hs).symm.trans ((hL Λ₂ y₁ h₂ p).2.2 g hs))
    exact Prod.ext hF (Prod.ext hF' hΓ)

end GlobalTheory.Unfold.InnerDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueIsLatticeUnimodular
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.Glue

open GlobalTheory.LoopC.RowGlue

theorem glue_isLattice_unimodular : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D), GlobalTheory.TypeAsm.Std D large₂ → ∀ L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X), Submodule.IsLattice D.host.E L → Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L → Submodule.IsLattice D.host.E (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) := by
  intro D large₂ X _ L hL hU
  have H : IsHypFrame (VS D).hT X.eX X.fY := ⟨(VS D).herm, X.ee, X.ff, X.ef⟩
  have h0 : ∀ a, aaD D a ≠ 0 := fun a => zpow_ne_zero _ (ddS_ne_zero D)
  have hs : ∀ a, StarStable (aaD D a) := fun a => (ddS_stable D).zpow (ddS_ne_zero D) _
  have hmid : ∀ w ∈ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)),
      Mid (VS D).hT X.eX X.fY w := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  refine ⟨Submodule.IsLattice.of_fg D.host.E (((sumS_fg _ _).sup (hL.fg.map _)).sup (sumS_fg _ _)), (H.unimodular_iff (A := fun a => aaD D a) (B := fun a => (aaD D a)⁻¹) hmid
      (fun a => inv_ne_zero (h0 a)) (fun a => (hs a).inv (h0 a)) (fun a => (inv_inv _).symm)).2 ?_⟩
  · intro w hw
    have key : (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) ∈ Formalism.HermitianLatticesTheory.dual (GlobalTheory.RowsOrb.hb X) L ↔
        (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) ∈ L := by
      rw [show Formalism.HermitianLatticesTheory.dual (GlobalTheory.RowsOrb.hb X) L = L from hU]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at key ⊢
    constructor
    · intro h
      exact ⟨⟨w, hw⟩, key.1 fun y hy => h y ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨w', hw', e⟩ _ ⟨y, hy, rfl⟩
      have e' : (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) = w' := Subtype.ext e.symm
      exact key.2 (e' ▸ hw') y hy

end GlobalTheory.RowsOrb.Glue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalSelfDualMeasuresFibreFamilyExist
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibre

theorem dX_dT_omFam :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, 1 ≤ a → 2 * a < n → (Formalism.L2.SG.LocVol.dX σ J ψ v a).IsAddHaarMeasure ∧ (Formalism.L2.SG.LocVol.dT σ ψ v a).IsAddHaarMeasure ∧ Formalism.L2.SG.LocVol.IsOm σ J ψ v a (Formalism.L2.SG.LocVol.omFam σ J ψ v a) := by
  intro F E _ _ _ _ _ σ hE n J hJ ha hc ψ hψ v a ha1 ha2
  obtain ⟨X0, hdet, hT⟩ := GlobalTheory.NondegTuple.exists_tuple_gram_det_ne_zero F E σ hE n J hJ a (by omega)
  have hI : PI.VolStabS.FibInfEx :=
    PI.VolStabS.fibInfEx_of PI.VolStabS.DiscreteGroups.fibOfDens_holds PI.VolStabS.tensAll_holds
      PI.VolStabS.densInf_holds
  have hV : PI.VolStabS.FibVEx :=
    PI.VolStabS.fibVEx_of PI.VolStabS.DiscreteGroups.fibOfDens_holds PI.VolStabS.tensAll_holds
      PI.VolStabS.densV_holds
  obtain ⟨_, _, μv, νv, _, _, _, _, hμv, hνv, _, _⟩ :=
    PI.VolStabS.locEx_of hI hV PI.VolStabS.latSB_holds F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet
      ψ hψ
  have hX : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ := ⟨_, hμv v⟩
  have hH : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν := ⟨_, hνv v⟩
  have hdX : SdW F E σ n J (Fv F v) (psiV F ψ v) a (Formalism.L2.SG.LocVol.dX σ J ψ v a) := by
    unfold Formalism.L2.SG.LocVol.dX
    rw [dite_eq_left hX]
    exact hX.choose_spec
  have hdT : SdHerm F E σ (Fv F v) (psiV F ψ v) a (Formalism.L2.SG.LocVol.dT σ ψ v a) := by
    unfold Formalism.L2.SG.LocVol.dT
    rw [dite_eq_left hH]
    exact hH.choose_spec
  have hO : ∃ fib, Formalism.L2.SG.LocVol.IsOm σ J ψ v a fib :=
    hV F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v _ hdX _ hdT
  refine ⟨hdX.1, hdT.1, ?_⟩
  unfold Formalism.L2.SG.LocVol.omFam
  rw [dite_eq_left hO]
  exact hO.choose_spec

end GlobalTheory.LocalFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowBaseLatticesMemSameHermitianGenus
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.RowsGenus

theorem main : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Λ' : LatV D, IsRowLat D F0 Λ' → L0X D Λ' (lf D F0) ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)) := by
  intro D u hp _ hs F0 he hz Λ hΛ Λ' hΛ'
  have h := (GlobalTheory.Mass.RowPerp.main D u F0 he hz).2
  exact ((GlobalTheory.Mass.CyclicGenus.main D.host.E (D.sp.X 0).V (D.sp.X 0).hT D.sp.cm.cmUnram (D.sp.X 0).herm
    (D.sp.X 0).nondeg (Tu D u) hp hs).2 _ _ (h Λ hΛ).1 (h Λ hΛ).2).2 (h Λ' hΛ')

end GlobalTheory.LoopC.RowsGenus
end

