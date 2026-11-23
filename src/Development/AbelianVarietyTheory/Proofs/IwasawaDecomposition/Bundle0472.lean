module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFactorisationScalarReferenceTupleEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0467
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.HeckeFieldSplit
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0468
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyRowLiftFamilyOverColumnChoices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.PkExist

theorem rowPk_nonempty : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), Inputs (w.D Z₀) → (w.D Z₀).host.F = maximalRealSubfield (w.D Z₀).host.E → Seed.FrmC.StdLat (Yc (w.D Z₀) 0) → (∀ i, Seed.FrmC.StdLat (Wc (w.D Z₀) i)) → Holds z₀.R z₀.F → (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → Nonempty (RowPk w z₀) := by
  intro B f T w Z₀ hX Wt z₀ hIn hF hY hW hH hWt
  classical
  letI : Algebra z₀.core.Q.c.F (w.D Z₀).what₂.LL := z₀.alg
  let tupT : w.I.ι → TupU w.I (usedOf w.I T Wt) := fun a =>
    if h : ∃ t, ixOf w.I (usedOf w.I T Wt) t = a then h.choose else mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))
  have htt : ∀ t, tupT (ixOf w.I (usedOf w.I T Wt) t) = t := fun t => by
    have h : ∃ t', ixOf w.I (usedOf w.I T Wt) t' = ixOf w.I (usedOf w.I T Wt) t := ⟨t, rfl⟩
    simp only [tupT, dif_pos h]
    exact ixOf_injective w.I _ h.choose_spec
  obtain ⟨y, hy, -⟩ := HdExist.hd_exists (w.D Z₀) (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T Wt))
    (famR (w.st Z₀) w.I hX (usedOf w.I T Wt) z₀.Xg z₀.tr) z₀.core.Q.c.F z₀.R z₀.F z₀.cG z₀.pins hF hY hW
    (ixOf w.I (usedOf w.I T Wt)) tupT htt (ixOf_mu0F w.I _)
  obtain ⟨hLA, hLL⟩ := _root_.GlobalTheory.Mem.R3.Rw.Mats.mats_laws (w.st Z₀) w.px w.I hX z₀.Xg z₀.tr w.ok z₀.good.irr
  have hU := GlobalTheory.T.formsCoordinates_indexOfFamilyTuple_eq (w.st Z₀) w.px w.I hX (usedOf w.I T Wt) z₀.Xg z₀.tr
  have hO : ∀ o : (w.D Z₀).what₂.O, ∃ k : z₀.core.Q.c.F, algebraMap z₀.core.Q.c.F (w.D Z₀).what₂.LL k = (w.D Z₀).what₂.OtoLL o :=
    fun o => z₀.Ks_le _ (SetLike.coe_mem _)
  obtain ⟨p, hpL, ⟨t⟩⟩ := _root_.GlobalTheory.Mem.R3.Rw.PkRead.exists_pkT (w.D Z₀) (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T Wt))
    (famR (w.st Z₀) w.I hX (usedOf w.I T Wt) z₀.Xg z₀.tr) z₀.core.Q.c.F z₀.R z₀.F z₀.cG hO hIn z₀.pins hH y
    (mAU (w.st Z₀) w.I hX z₀.Xg z₀.tr) (mLU (w.st Z₀) w.I hX z₀.Xg z₀.tr) hLA hLL
    (fun b t => by rw [hy]; exact (hU t).1 b) (fun i t => by rw [hy]; exact (hU t).2 i)
  obtain ⟨d, ⟨per⟩⟩ := _root_.GlobalTheory.Mem.R3.Rw.PerId.exists_perT B f T w Z₀ hX z₀.Xg z₀.tr p (fun a => t.tA true a)
  obtain ⟨W₀, hmu, hkap, hsha⟩ := _root_.GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW B f T w hX Wt hWt
  obtain ⟨n, hn⟩ := exists_nums_numOK B w.C (Gc B w.px) p d W₀
  exact ⟨{
    y := y
    tup := fun t => (by rw [hy])
    p := p
    t := t
    mL := fun a j => (by rw [hpL])
    e := d
    per := per
    W₀ := W₀
    mu := hmu
    sha := hsha
    n := n
    kap := fun η hη V S N G' => hkap (p.what₂ d W₀ n η hη) rfl rfl V S N G'
    num := hn }⟩

end GlobalTheory.Mem.R3.Rw.PkExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFormsIsometryColumnPairingAtState
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.EmtTw
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 2000000

theorem inner_per_e {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) (a : w.C.Tup)
    (y y' : Df.MtCx w.I a) : inner ℂ (P.q.per.e a y) (P.q.per.e a y') = Df.cSum w.I P.hX a y y' := by
  let jA := (P.q.t.tA true a).j
  have hF := (P.q.t.tA true a).forms
  let eS : (P.q.p.sA true a).A.T →ₗ[ℂ] Df.MtCx w.I a := (P.q.per.e a).symm.toLinearMap
  let j' := eS.comp jA
  have hspan : Submodule.span ℂ (Set.range j') = ⊤ := by
    have h0 : Submodule.span ℂ (Set.range jA) = ⊤ := by
      rw [← ColTie.span_single_eq]; exact hF.span
    have h1 : Set.range j' = eS '' Set.range jA := by
      rw [← Set.range_comp]; rfl
    rw [h1, Submodule.span_image, h0, Submodule.map_top]
    exact LinearMap.range_eq_top.2 (P.q.per.e a).symm.surjective
  obtain ⟨k, hk⟩ := Df.exists_embLL_im_ne (B := B) P.hX
  refine Df.inner_eq_of_norm_sq _ j' hspan k hk (P.q.per.e a).toLinearMap (Df.cSum w.I P.hX a) (fun m => ?_) y y'
  obtain ⟨x, hx, hjx⟩ := P.q.per.crd a m
  have hj' : j' m = Df.toCx w.I P.hX a x := by
    show (P.q.per.e a).symm (jA m) = _
    rw [show jA m = _ from hjx, LinearEquiv.symm_apply_apply]
  have he : (P.q.per.e a).toLinearMap (j' m) = jA m := by
    show (P.q.per.e a) ((P.q.per.e a).symm (jA m)) = _
    rw [LinearEquiv.apply_symm_apply]
  have hL := GlobalTheory.T.classSum_complexRowForm_columnsLevel_eq (w.st P.Z₀) w.I P.hX P.z.Xg P.z.tr a m x hx
  have hI := hF.inner m m
  rw [he, hj', hL]
  calc ((‖jA m‖ ^ 2 : ℝ) : ℂ) = inner ℂ (jA m) (jA m) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
    _ = _ := hI

theorem eMtTw_isometry_state : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u (a : (w.D x.o.Z).what₂.Tup), a ≠ (w.D x.o.Z).what₂.mu0 → ∀ F G,
      inner ℂ ((w.D x.o.Z).eMtTw u a F) ((w.D x.o.Z).eMtTw u a G) = TC.ipMt w.I w.l u a F G := by
  intro K B f T w _ _ _ P x _ u a _ F G
  change inner ℂ (P.q.e.eT u a F) (P.q.e.eT u a G) = _
  have key : ∀ F : (TC.per w.I w.l u a).Mt, Df.SameForm w.I w.l u a ((P.q.per.e a).symm (P.q.e.eT u a F)) F := fun F => by
    have h := P.q.per.tw u a ((P.q.per.e a).symm (P.q.e.eT u a F))
    rw [LinearEquiv.apply_symm_apply] at h
    exact (congrArg (Df.SameForm w.I w.l u a ((P.q.per.e a).symm (P.q.e.eT u a F))) ((P.q.e.eT u a).symm_apply_apply F)).mp h
  have h1 : ∀ F : (TC.per w.I w.l u a).Mt, P.q.e.eT u a F = P.q.per.e a ((P.q.per.e a).symm (P.q.e.eT u a F)) := fun F =>
    ((P.q.per.e a).apply_symm_apply _).symm
  rw [h1 F, h1 G, inner_per_e P a, _root_.GlobalTheory.Mem.Df.ipMt_eq_cSum w.I w.ok w.pins w.l P.hX x.o.Z u a F G _ _ (key F) (key G)]

end GlobalTheory.Mem.R3.Rw.EmtTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFormsReferenceTupleIsometryColumnPairing
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.St

attribute [local instance] GlobalTheory.Mem.Col2.starE


set_option maxHeartbeats 1000000 in
theorem eMt0_isometry : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u F G, inner ℂ ((w.D x.o.Z).eMt u F) ((w.D x.o.Z).eMt u G) = TC.ipMt w.I w.l u w.I.mu0 F G := by
  intro K B f T w hO hF hP P x hη u F G
  show inner ℂ (P.q.e.e0 u F) (P.q.e.e0 u G) = _
  have hN : ∀ m : (Df.MtHL w.I P.hX w.I.mu0).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL w.I P.hX w.I.mu0).b (Df.MtHL w.I P.hX w.I.mu0).X
      (InfinitePlace.mk B.embLL) m = ‖P.q.per.e w.I.mu0 (Df.toCx w.I P.hX w.I.mu0 m)‖ :=
    GlobalTheory.T.periodRelation_preserves_levelForm_lattice_norm (w.st P.Z₀) w.I P.hX P.z.Xg P.z.tr w.I.mu0 (P.q.t.tA true w.I.mu0) (P.q.per.e w.I.mu0) (P.q.per.crd w.I.mu0)
  have hin : ∀ y y' : Df.MtCx w.I w.I.mu0, inner ℂ (P.q.per.e w.I.mu0 y) (P.q.per.e w.I.mu0 y') = Df.cSum w.I P.hX w.I.mu0 y y' := by
    intro y y'
    obtain ⟨-, ⟨j, hj⟩, -, hsp⟩ := _root_.GlobalTheory.Mem.Df.mtHL_good_basis w.I P.hX w.I.mu0
    obtain ⟨k, hk⟩ := Df.exists_embLL_im_ne (B := B) P.hX
    have hspan : Submodule.span ℂ (Set.range j) = ⊤ := by
      rw [eq_top_iff, ← hsp]
      exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, hj _⟩)
    exact Df.inner_eq_of_norm_sq B.embLL j hspan k hk (P.q.per.e w.I.mu0).toLinearMap (Df.cSum w.I P.hX w.I.mu0) (fun m => by
      rw [hj, LinearEquiv.coe_toLinearMap, ← hN m, _root_.GlobalTheory.Mem.Df.normAt_sq_eq_cSum w.I P.hX w.I.mu0 m]) y y'
  have key : ∀ F : ((w.D x.o.Z).mem u).P.Mt,
      Df.SameForm w.I w.l u w.I.mu0 ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F)) F := fun F => by
    have h := P.q.per.ref u ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F))
    erw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h
    exact h
  have h1 : ∀ F : ((w.D x.o.Z).mem u).P.Mt, P.q.e.e0 u F = P.q.per.e w.I.mu0 ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F)) :=
    fun F => ((P.q.per.e w.I.mu0).apply_symm_apply _).symm
  rw [h1 F, h1 G]
  exact (hin _ _).trans (_root_.GlobalTheory.Mem.Df.ipMt_eq_cSum w.I w.ok w.pins w.l P.hX x.o.Z u w.I.mu0 F G _ _ (key F) (key G)).symm

end GlobalTheory.Mem.R3.Rw.St

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Tr

theorem exists_iota_comp {K₁ K₂ : Type} [Field K₁] [Field K₂] (c₁ : K₁ →+* ℂ) (c₂ : K₂ →+* ℂ)
    (h : Set.range c₁ ⊆ Set.range c₂) : ∃ ι : K₁ →+* K₂, ∀ x, c₂ (ι x) = c₁ x := by
  have hle : c₁.range ≤ c₂.range := by
    intro y hy
    obtain ⟨x, rfl⟩ := RingHom.mem_range.1 hy
    obtain ⟨z, hz⟩ := h ⟨x, rfl⟩
    exact RingHom.mem_range.2 ⟨z, hz⟩
  let e : K₂ ≃+* c₂.range := RingEquiv.ofBijective c₂.rangeRestrict
    ⟨fun a b hab => c₂.injective (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective c₂⟩
  refine ⟨e.symm.toRingHom.comp ((Subring.inclusion hle).comp c₁.rangeRestrict), fun x => ?_⟩
  have h1 : c₂ (e.symm ⟨c₁ x, hle (RingHom.mem_range_self c₁ x)⟩) = c₁ x := by
    have := congrArg Subtype.val (e.apply_symm_apply ⟨c₁ x, hle (RingHom.mem_range_self c₁ x)⟩)
    exact this
  exact h1

abbrev baseOfColW {B : Base} {f : Fr B.toPre} {T : TwDat B} (_ : ColW B f T) : Base := B

theorem levelFamily_coefficientChange_liftRound (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG)
    (hH : ∀ w, (Λ₂ w).H = (Λ₁ w).H)
    (hl : ∀ w (h₁ : ↥(Λ₁ w).H) (h₂ : ↥(Λ₂ w).H), (h₁ : GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) = h₂ →
      ι (((Λ₁ w).lam h₁ : X.Kˣ) : X.K) = (((Λ₂ w).lam h₂ : Lˣ) : L))
    (φ₁ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG) => d.1.N) Λ₁).EqFun) :
    ∃ φ₂ : (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
      (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
        fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG) => d.1.N) Λ₂).EqFun,
      ∀ d, (φ₂.1 d).1 = MvPolynomial.map ι (φ₁.1 d).1 := by
  refine ⟨⟨fun d => Formalism.L2.Col.hfsJ ι lam (φ₁.1 d), ?_⟩, fun d => rfl⟩
  intro g d
  have hg : g.2.1 ∈ Λ₁.grp := by
    intro w _
    have h' : (g.2.1 w) ∈ (Λ₂ w).H := g.2.2 w (Set.mem_univ _)
    rw [hH w] at h'
    exact h'
  have h1 : φ₁.1 (g • d) = (((Λ₁.chr ⟨g.2.1, hg⟩ : X.Kˣ)) : X.K) •
      Formalism.L2.DIV.rhoVr X.emb lam (Formalism.L2.Col.ufGL X.E n g.1) (φ₁.1 d) := φ₁.2 (g.1, ⟨g.2.1, hg⟩) d
  have he' : e = fun τ => ι.comp (X.emb τ) := funext fun τ => (he τ).symm
  subst he'
  show Formalism.L2.Col.hfsJ ι lam (φ₁.1 (g • d)) = (((Λ₂.chr g.2 : Lˣ)) : L) •
    Formalism.L2.DIV.rhoVr (fun τ => ι.comp (X.emb τ)) lam (Formalism.L2.Col.ufGL X.E n g.1) (Formalism.L2.Col.hfsJ ι lam (φ₁.1 d))
  have h2 := Formalism.L2.Col.hfs_rhoVr ι lam X.emb (Formalism.L2.Col.ufGL X.E n g.1) (φ₁.1 d)
  erw [h2, h1, Formalism.L2.Col.hfsJ_smul]
  congr 1
  rw [Formalism.L2.Col.LevFam.chr_apply, show Λ₂.chr g.2 = _ from Formalism.L2.Col.piChar_apply _ _ g.2, Units.coe_prod, Units.coe_prod, map_prod]
  exact Finset.prod_congr rfl fun w _ => hl w _ _ rfl

theorem liftRound_reidx (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG₁) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG₂)
    (hΛ : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), Λ₂ ⟨w.1, hw⟩ = (Λ₁ w).coefMap ι)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x) :
    Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₂) = Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) ∧
    ∀ φ₁ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁).EqFun,
    ∃ φ₂ : (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
      (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
        fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₂) => d.1.N) Λ₂).EqFun,
      ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ (φ₂.1 d₂).1) (MvPolynomial.map c₁ (φ₁.1 d₁).1) := by
  subst hS
  have hΛ' : Λ₂ = Λ₁.coefMap ι := funext fun w => hΛ w w.2
  subst hΛ'
  refine ⟨rfl, fun φ₁ => ?_⟩
  obtain ⟨φ₂, h⟩ := levelFamily_coefficientChange_liftRound X ι e he lam Λ₁ (Λ₁.coefMap ι) (fun w => rfl) (fun w h₁ h₂ hh => by
    have : h₁ = h₂ := Subtype.ext hh
    subst this
    rfl) φ₁
  refine ⟨φ₂, fun d₁ d₂ hd => ?_⟩
  cases hd
  rw [h, MvPolynomial.map_map]
  have hc' : c₂.comp ι = c₁ := RingHom.ext hc
  rw [hc']

theorem twistRamifiedPrimes_empty_colTuples {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (W : Set B.places.Pl) :
    Formalism.L2.Col.QE w.I.sel ((mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := by
  have e : Formalism.L2.Col.QE w.I.sel (w.I.tup w.I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty w.I
  rw [w.I.trueColumn_tuple_trivial_eq_one] at e
  exact e

theorem rowLevelPrimes_colTuples_eq_vGs {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (W : Set B.places.Pl) :
    Formalism.L2.Col.rowSG (B.primes w.px) w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 = (B.primes w.px).vGs := by
  show Formalism.L2.Col.uSG _ _ = _
  rw [twistRamifiedPrimes_empty_colTuples w W]
  ext x
  simp

theorem glue_inv_coefMap_of_empty {E K L : Type} [Field E] [NumberField E] [Field K] [Field L] (ι : K →+* L) {n : ℕ}
    {SG₁ Q₁ SG₂ Q₂ : Finset (HeightOneSpectrum (𝓞 E))} (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅)
    (A₁ : Formalism.L2.Col.LevFam E K n SG₁) (B₁ : Formalism.L2.Col.LevFam E K n Q₁)
    (A₂ : Formalism.L2.Col.LevFam E L n SG₂) (B₂ : Formalism.L2.Col.LevFam E L n Q₂)
    (hA : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), A₂ ⟨w.1, hw⟩ = (A₁ w).coefMap ι) :
    ∀ (w : ↥(Formalism.L2.Col.uSG SG₁ Q₁)) (hw : w.1 ∈ Formalism.L2.Col.uSG SG₂ Q₂),
      (A₂.glue B₂).inv ⟨w.1, hw⟩ = ((A₁.glue B₁).inv w).coefMap ι := by
  intro w hw
  have h1 : w.1 ∈ SG₁ := by
    have := w.2
    simp only [Formalism.L2.Col.uSG, hQ₁, Finset.union_empty] at this
    exact this
  have h2 : w.1 ∈ SG₂ := by
    have := hw
    simp only [Formalism.L2.Col.uSG, hQ₂, Finset.union_empty] at this
    exact this
  show ((A₂.glue B₂) ⟨w.1, hw⟩).inv = (((A₁.glue B₁) w).inv).coefMap ι
  rw [Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h2, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h1, ← Formalism.L2.Col.Lev.coefMap_inv,
    hA ⟨w.1, h1⟩ h2]

theorem levKV_coefMap_of {E K L : Type} [Field E] [NumberField E] [Field K] [Field L] (ι : K →+* L) {m : ℕ}
    (w : HeightOneSpectrum (𝓞 E)) (χ₁ : Fin m → (𝓞 E ⧸ w.asIdeal)ˣ →* Kˣ) (χ₂ : Fin m → (𝓞 E ⧸ w.asIdeal)ˣ →* Lˣ)
    (h : ∀ s c, ((χ₂ s c : Lˣ) : L) = ι ((χ₁ s c : Kˣ) : K)) (nV r t s : ℕ) :
    (⟨Formalism.L2.Col.HKV (𝓞 E ⧸ w.asIdeal) nV r t, Formalism.L2.Col.lamKV (Formalism.L2.Col.extChi χ₂ s) nV r t⟩ :
        Formalism.L2.Col.Lev (𝓞 E ⧸ w.asIdeal) L nV) =
      Formalism.L2.Col.Lev.coefMap ι ⟨Formalism.L2.Col.HKV (𝓞 E ⧸ w.asIdeal) nV r t, Formalism.L2.Col.lamKV (Formalism.L2.Col.extChi χ₁ s) nV r t⟩ := by
  have hχ : χ₂ = fun s => (Units.map ι.toMonoidHom).comp (χ₁ s) :=
    funext fun s => MonoidHom.ext fun c => Units.ext (h s c)
  subst hχ
  have h' : (fun _ : ℕ => (Formalism.L2.Col.extChi (fun s => (Units.map ι.toMonoidHom).comp (χ₁ s)) s)⁻¹) =
      fun _ : ℕ => (Units.map ι.toMonoidHom).comp (Formalism.L2.Col.extChi χ₁ s)⁻¹ :=
    funext fun _ => (congrArg (·⁻¹) (Formalism.L2.Col.extChi_coefMap ι χ₁ s)).trans (Formalism.L2.Col.coefMap_comp_inv ι _)
  exact congrArg (Formalism.L2.Col.Lev.mk (Formalism.L2.Col.HKV (𝓞 E ⧸ w.asIdeal) nV r t))
    ((congrArg (fun χ => Formalism.L2.Col.lamK χ nV r [t]) h').trans (Formalism.L2.Col.lamK_coefMap ι _ _ _))

theorem lift_refTuple_enl : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (W₁ : Set B₁.places.Pl) (W₂ : Set B₂.places.Pl), Enl B₁ B₂ → HEq (B₂.primes w₂.px).vGs (B₁.primes w₁.px).vGs → (∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K)) → ∀ j₁ j₂ : ℕ, j₁ = j₂ → (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).D = (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).D ∧ ∀ φ₁ : (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).EqFun, ∃ φ₂ : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).EqFun, ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (φ₂.1 d₂).1) (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (φ₁.1 d₁).1) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ W₁ W₂ hE hv hchi j₁ j₂ hj
  subst hj
  obtain ⟨hpre, -, -, hrange⟩ := hE
  obtain ⟨ι, hι⟩ := exists_iota_comp B₁.embLL B₂.embLL hrange
  cases B₁ with | mk P₁ =>
  cases B₂ with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  refine liftRound_reidx (baseOfColW w₁).fields ι (baseOfColW w₂).tauLL ?_ _ ?_ _ _ ?_ (baseOfColW w₁).embLL
    (baseOfColW w₂).embLL hι
  · intro τ
    ext x
    apply (baseOfColW w₂).embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₁) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₂) τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    rw [RingHom.comp_apply, hι]
    exact h1.trans h2.symm
  · exact (rowLevelPrimes_colTuples_eq_vGs w₂ W₂).trans ((eq_of_heq hv).trans (rowLevelPrimes_colTuples_eq_vGs w₁ W₁).symm)
  · refine glue_inv_coefMap_of_empty ι (twistRamifiedPrimes_empty_colTuples w₁ W₁) (twistRamifiedPrimes_empty_colTuples w₂ W₂) _ _ _ _ ?_
    intro w hw
    refine levKV_coefMap_of ι w.1 (fun s => w₁.I.Ch.chi s w) (fun s => w₂.I.Ch.chi s ⟨w.1, hw⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w₂).embLL.injective
    rw [hι]
    exact hchi s s rfl w ⟨w.1, hw⟩ HEq.rfl c c HEq.rfl

end GlobalTheory.Mem.R3.Tr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeImagePointOfLiftStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representative_image_point_of_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (kk : GL (Fin ((I.rec7 l Z).R.N i)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))), kk = k (chOf c) → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ x ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') x = 1) → ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, (∀ r s, adAt (I.rec7 l Z).host.F (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((kk⁻¹ * x * kk).1 r s) = algebraMap (I.rec7 l Z).host.E ((GlobalTheory.TwU.seamP (sm I l Z) P.1).adicCompletion (I.rec7 l Z).host.E) ((GlobalTheory.TwU.seamGL (sm I l Z) g').1 r s)) → ∀ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) → LiftsInv I κ' P g' → (∀ P', P' ≠ P → LiftsInv I κ' P' 1) → PtOf (((K (chOf c)).y ⟨c, rfl⟩).1 * x * kk) (((I.stp u a i).act c.1 κ' ((I.stp u a i).rep c)).1.1) := by
  first | exact @GlobalTheory.Mem.Col2.LevLiftPt.pt_of_lift | exact GlobalTheory.Mem.Col2.LevLiftPt.pt_of_lift | (intros; apply GlobalTheory.Mem.Col2.LevLiftPt.pt_of_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowBasisCongruenceLengthsOtherLaterStagesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m) (R : RealDat3 a.D A3 Ks) (F : Face3 a.D A3), letI := alg b iK; (∀ j v, etaOf (real3 b R) (face3 b F) j v = etaOf R F j ((by with_unfolding_all exact (v :)))) ∧ ∀ (y : Hd R.toRealDat) (y' : Hd (real3 b R).toRealDat) (bb : Bool) (E : Hs) jE jE' n c Xo, HEq jE' jE → RrT F y bb (E := E) jE n c Xo → RrT (face3 b F) y' bb (E := E) jE' n c ((by with_unfolding_all exact (Xo :))) := by
  first | exact @GlobalTheory.Mem.R3.Rw.rr_eta_tr | exact GlobalTheory.Mem.R3.Rw.rr_eta_tr | (intros; apply GlobalTheory.Mem.R3.Rw.rr_eta_tr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdCopy
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.StdTr


set_option maxHeartbeats 800000 in
theorem std_copy (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w.st Z') w.I hX T Wt) : z'.Xg = z.Xg → z'.tr = z.tr → HEq z'.R (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := z.alg) z.R) → HEq z'.core (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ z.core) → z.Std → z'.Std := by
  intro hXg htr hR hc hs
  cases z' with
  | @mk Xg' tr' core' alg' alg_eq' R' cG' geo' pins' lev' idG' good' mu' le' ks' =>
  dsimp only at hXg htr hR hc ⊢
  subst hXg htr
  obtain rfl := eq_of_heq hc
  change BrgStd (w.st Z') w.I hX (usedOf w.I T Wt) z.Xg z.tr R'.toRealDat
  change HEq R' _ at hR
  have e : alg' = alg (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.st Z').B.embLL.injective
    rw [alg_eq']
    exact (z.alg_eq y).symm
  clear cG' geo' pins' lev' idG' good' mu' le' ks' alg_eq' hc
  subst e
  obtain rfl := eq_of_heq hR
  exact (by with_unfolding_all exact (hs :))

end GlobalTheory.Mem.R3.Rw.StdTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainMiddleStageChartsJoinedMemberStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleChain_middleStage_charts_joined_member : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (g : Ch → Ch0), I.ReadsK l Z u a i hi chOf K ∧ ∀ β, (∀ v, v ∉ Q → (K β).lev.Uloc v = (K0 (g β)).lev.Uloc v) ∧ (∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1) ∧ ∀ (κ : (K β).lev.U) (κ' : (K0 (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = (K0 (g β)).lev.chi κ' := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.charts_tuple | exact GlobalTheory.Mem.Col2.TC.ChTw.charts_tuple | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.charts_tuple <;> assumption)
end

