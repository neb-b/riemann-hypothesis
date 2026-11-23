module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepLatticeVacuumMemSpanInertTranslates
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem secW_compFin (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (a : AE D)
    (ha : algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v) * a = a) :
    secW hw h (GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v a)) = a := by
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm
    (GlobalTheory.LFun.InertChart.complEquiv hw h _)) = a
  rw [RingEquiv.symm_apply_apply]
  conv_rhs => rw [← ha]
  rw [show algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v) = GlobalTheory.EmbChart.tensAt D.host.E v 1 from rfl,
    GlobalTheory.EmbChart.tensAt_mul_right, one_mul]

theorem exists_uPt_eq (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {k : w.adicCompletion D.host.E} (hk0 : k ≠ 0) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E))
    (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)) {u : WO S T}
    (hu : IsHalf (algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v)) u) :
    ∃ y, uPt hw h k aS aT y = u := by
  let U : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) :=
    u.map fun a => GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v a)
  refine ⟨k⁻¹ • ((aT⁻¹).1 * U * aS.1), ?_⟩
  have e1 : k • (aT.1 * (k⁻¹ • ((aT⁻¹).1 * U * aS.1)) * (aS⁻¹).1) = U := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hk0, one_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  ext i j
  rw [uPt, e1, Matrix.map_apply]
  exact secW_compFin hw h _ (hu i j)


open GlobalTheory.Hk3 GlobalTheory.InertLoc GlobalTheory.SplitScalar GlobalTheory.FinWeilO in
set_option maxHeartbeats 1600000 in
theorem om_mem_span_uPt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v), UnrAt χS w → UnrAt χT w → ∀ (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsUnramInv ϖ c (qV D.host.F v) → IsConjAt D.sp.cm.sig h c → GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ f, VacFin ψ S T v f → ∀ (gS : Gv S v) (gT : Gv T v), om (embV S v gS, embV T v gT) f ∈ Submodule.span ℂ (Set.range fun x => heisO ψ S T (uPt hw h k aS aT x) f) := by
  intro D ψ S T χS χT om hW v w hw h uS uT c ϖ k aS aT hU hconj hk haS haT gaS gaT f hf gS gT
  have dict := GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary D v w h
  have hP : Formalism.DivisionValues.conjPl w = w := by
    by_contra hne
    exact GlobalTheory.LFun.not_isSplit_of_isInertAt hw (dict.1.2 hne)
  have he : IsPrimeIdem w (algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v))
      (algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v)) :=
    GlobalTheory.HeckeRowsCompare.isPrimeIdem_of_inert hw (GlobalTheory.AdelicU.Supp.isPlaceIdem_placeIdem D v)
  set e := algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v) with he_def
  have unr : ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → GlobalTheory.Hk3.UnrPl w χ := fun χ hχ =>
    dict.2.1 χ fun w' hw' => by rw [(GlobalTheory.LFun.InertChart.under_eq_iff hw w').1 hw']; exact hχ
  have hfix := GlobalTheory.ConjVacFix.vacFix_of_unrPl ψ S T χS χT om w hW (unr χS uS) (unr χT uT)
  obtain ⟨ϖ0, σ, q, π, hU0, h2, hc0, hV⟩ := exists_chart hP he
  obtain ⟨βS, ιS, hS, gS'⟩ := hV S
  obtain ⟨βT, ιT, hT, gT'⟩ := hV T
  have hψ := hW.std
  obtain ⟨δ, ψ', hδ, p1, p2, p3⟩ := exists_delta_psi hU0 h2 (th ψ hc0 k) (th_conj hc0 hU0.1) (by
    obtain ⟨β, -, hβ, -⟩ := hV D.sp.X'
    refine th_cond hψ hc0 hU0.2.1 hβ ⟨0, ?_⟩ hk
    have h1 := D.R.m_add_three_le_k
    rw [D.sp.X'_rank, Ranks.rankX', Ranks.r]
    omega)
  let ρ : Matrix (Fin T.rank) (Fin S.rank) (LP D w) → Module.End ℂ (thetaSub ψ S T) := fun x =>
    (heisL ψ S T (kap hc0 βS βT k x)).restrict fun _ hf =>
      GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (hc0.half_fin (kap_half hc0 x)) hf
  have hρ : ∀ x (m : thetaSub ψ S T), (ρ x m : WO S T → ℂ) = heisO ψ S T (kap hc0 βS βT k x) m := fun _ _ => rfl
  let ω : Formalism.UG.UJ σ (1 : Matrix (Fin S.rank) (Fin S.rank) (LP D w)) ×
      Formalism.UG.UJ σ (1 : Matrix (Fin T.rank) (Fin T.rank) (LP D w)) →* Module.End ℂ (thetaSub ψ S T) :=
    { toFun := fun p => (om (ιS p.1, ιT p.2)).restrict fun _ hf => hW.om_pres _ _ hf
      map_one' := LinearMap.ext fun m => Subtype.ext (by
        show om (ιS 1, ιT 1) m = m
        rw [map_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply])
      map_mul' := fun p p' => LinearMap.ext fun m => Subtype.ext (by
        show om (ιS (p.1 * p'.1), ιT (p.2 * p'.2)) m = om (ιS p.1, ιT p.2) (om (ιS p'.1, ιT p'.2) m)
        rw [map_mul, map_mul, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]) }
  have hω : ∀ g g' (m : thetaSub ψ S T), (ω (g, g') m : WO S T → ℂ) = om (ιS g, ιT g') m := fun _ _ _ => rfl
  have hlat := kap_mem_iff hc0 hU0.2.1 hS hT hk
  have hvac0 : ∀ m : thetaSub ψ S T, LocVac ρ m ↔
      ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u → heisO ψ S T u m = m := fun m => by
    refine ⟨fun hm u hu hh => ?_, fun hm x hx => Subtype.ext (hm _ ((hlat x).2 hx) (kap_half hc0 x))⟩
    obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) hc0 hk.1 hh
    exact congrArg Subtype.val (hm x ((hlat x).1 hu))
  have hvac : ∀ m : thetaSub ψ S T, LocVac ρ m ↔ IsVacAt ψ S T w m := fun m => by
    rw [hvac0]
    refine ⟨fun hm => ⟨m.2, fun e' f' he' u hu hh => hm u hu ?_⟩, fun hm u hu hh => hm.2 e e he u hu (Or.inl hh)⟩
    obtain ⟨rfl, -⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S).2.2.1 w e e he).2.2.2.1 e' f' he'
    rwa [hc0.1.2.1, or_self] at hh
  have hhyp : ∀ {V : HSp D} {β ι}, GrpChart V e σ π β ι → ∀ g, ι g ∈ hyp V w ↔
      g.1 ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.intL (LP D w)) := fun hι g =>
    ⟨fun hg => (hι.2.2.2 g).1 hg.1, fun hg => ⟨(hι.2.2.2 g).2 hg, e, e, he, hι.1 g⟩⟩
  have hone : ∀ (n : ℕ) (i j : Fin n), σ ((1 : Matrix (Fin n) (Fin n) (LP D w)) i j) = (1 : Matrix (Fin n) (Fin n) (LP D w)) j i :=
    fun n i j => by
      rw [Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij.symm, σ.map_one]
      · rw [if_neg hij, if_neg (Ne.symm hij), σ.map_zero]
  have hLP : LocPair ϖ0 σ q δ (1 : GL (Fin S.rank) (LP D w)) (1 : GL (Fin T.rank) (LP D w)) ψ' ρ ω := by
    refine ⟨hU0, odd_of_v_two hU0 h2, one_mem _, one_mem _, hone _, hone _, hδ, p1, p2, ?_, fun x y => ?_, ?_,
      fun g g' x => ?_, fun g g' hg hg' s hs => ?_⟩
    · refine LinearMap.ext fun m => Subtype.ext ?_
      rw [hρ, kap_zero, heisO_zero, Module.End.one_apply]
    · refine LinearMap.ext fun m => Subtype.ext ?_
      rw [Module.End.mul_apply, hρ, hρ, heisO_heisO, symplOH_kap hc0 hS hT, LinearMap.smul_apply, Submodule.coe_smul, hρ,
        kap_add, locH, p3, inv_one, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
      rfl
    · refine span_vacua hψ hc0.1.1 hc0.1.2.1 (fun u hu hh => ?_) _ fun u hh s m hs hm => ?_
      · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) hc0 hk.1 hh
        refine ⟨kap hc0 βS βT k ((2⁻¹ : LP D w) • x), (hlat _).2 fun i j => mul_mem (mem_intL.2 ?_) ((hlat x).1 hu i j), ?_⟩
        · rw [map_inv₀, h2, inv_one]
        · rw [← kap_add, half_add_half]
      · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) hc0 hk.1 hh
        exact Submodule.subset_span ⟨x, s, (hvac0 s).2 hs, Subtype.ext hm⟩
    · refine LinearMap.ext fun m => Subtype.ext ?_
      show om (ιS g, ιT g') (heisO ψ S T (kap hc0 βS βT k x) m) = heisO ψ S T (kap hc0 βS βT k _) (om (ιS g, ιT g') m)
      rw [hW.om_heis _ _ _ _ m.2, actO_kap hc0 gS' gT']
    · exact Subtype.ext (hfix _ ((hvac s).1 hs) _ ((hhyp gS' g).2 hg) _ ((hhyp gT' g').2 hg'))
  obtain ⟨r1, hr1⟩ := gS'.2.2.1 (embV S v gS) ((GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem S he h _).2 ⟨gS, rfl⟩)
  obtain ⟨r2, hr2⟩ := gT'.2.2.1 (embV T v gT) ((GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem T he h _).2 ⟨gT, rfl⟩)
  let fM : thetaSub ψ S T := ⟨f, hf.1⟩
  have hvf : LocVac ρ fM := (hvac fM).2 (dict.2.2.2.1 ψ S T f hf)
  haveI : CharZero (LP D w) := algebraRat.charZero _
  obtain ⟨cc, hcc⟩ := locPair_act_vac_comb (LP D w) ϖ0 σ q δ S.rank T.rank 1 1 ψ' (thetaSub ψ S T) ρ ω hLP (r1, r2)
  have e1 : om (embV S v gS, embV T v gT) f = ((ω (r1, r2) fM : thetaSub ψ S T) : WO S T → ℂ) := by
    rw [hω, hr1, hr2]
  rw [e1, hcc fM hvf, Finsupp.sum, Submodule.coe_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [Submodule.coe_smul, hρ]
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨y, hy⟩ := exists_uPt_eq hw h hk.1 aS aT (kap_half hc0 x)
  rw [← hy]
  exact Submodule.subset_span ⟨y, rfl⟩

end GlobalTheory.InertFrameLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepRankZeroWittEmbeddingValueAtZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing MeasureTheory

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.VLast.Transport

section RankZero

variable {D : D7} {S S₀ : HSp D} (d : HypDec S S₀ 0)

theorem rz_gA : gA S = adj d.p0 ⬝ (gA S₀ ⬝ d.p0) := by
  rw [d.gA_eq, Subsingleton.elim d.pX 0, Subsingleton.elim d.pY 0]
  simp

theorem rz_j0p0 : d.j0 ⬝ d.p0 = 1 := by
  have := d.sum_eq_one
  rwa [Subsingleton.elim d.jX 0, Subsingleton.elim d.jY 0, Matrix.zero_mul, Matrix.zero_mul, zero_add, add_zero] at this

theorem unitaryMatrix_rankZeroWittEmbedding_eq (g : GA D S₀) : mt S (d.emb0 g) = d.j0 ⬝ mt S₀ g ⬝ d.p0 := by
  rw [d.unitaryMatrix_wittCoreEmbedding, Subsingleton.elim d.jX 0, Subsingleton.elim d.jY 0]
  simp

theorem rz_unit (g : GA D S) : adj (d.p0 ⬝ mt S g ⬝ d.j0) ⬝ (gA S₀ ⬝ (d.p0 ⬝ mt S g ⬝ d.j0)) = gA S₀ := by
  have key : ∀ X : Mx D S.rank S₀.rank, adj d.p0 ⬝ (gA S₀ ⬝ (d.p0 ⬝ X)) = gA S ⬝ X := fun X => by
    rw [rz_gA d, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [adj_mul, adj_mul]
  simp only [Matrix.mul_assoc]
  rw [key, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)), mt_unitary]
  exact d.gram_00

def rzInv (g : GA D S) : GA D S₀ := ofMat S₀ (d.p0 ⬝ mt S g ⬝ d.j0) (rz_unit d g)

theorem mt_rzInv (g : GA D S) : mt S₀ (rzInv d g) = d.p0 ⬝ mt S g ⬝ d.j0 := mt_ofMat _ _ _

def rzEquiv : GA D S₀ ≃* GA D S where
  toFun := d.emb0
  invFun := rzInv d
  left_inv g := mt_injective S₀ (by
    rw [mt_rzInv, unitaryMatrix_rankZeroWittEmbedding_eq]
    simp only [Matrix.mul_assoc, d.p0_j0, Matrix.mul_one]
    rw [← Matrix.mul_assoc, d.p0_j0, Matrix.one_mul])
  right_inv g := mt_injective S (by
    rw [unitaryMatrix_rankZeroWittEmbedding_eq, mt_rzInv]
    simp only [Matrix.mul_assoc, rz_j0p0 d, Matrix.mul_one]
    rw [← Matrix.mul_assoc, rz_j0p0 d, Matrix.one_mul])
  map_mul' := map_mul d.emb0

theorem rzInv_continuous : Continuous (rzInv d) :=
  continuous_of_mt S₀ (by
    simp only [mt_rzInv]
    exact (continuous_const.matrix_mul (continuous_mt S)).matrix_mul continuous_const)

theorem rzInv_mem_GQ {g : GA D S} (hg : g ∈ GQ S) : rzInv d g ∈ GQ S₀ := by
  rw [mem_GQ_iff, mt_rzInv]
  exact ratMx_mul (ratMx_mul (rat_mem _) ((mem_GQ_iff S g).1 hg)) (rat_mem _)

end RankZero

theorem weilRep_rankZeroWittEmbedding_valueAtZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (d : HypDec S S₀ 0) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ f, IsThetaFunO ψ S T f → ∀ (g₀ : GA D S₀) (h : GA D T), om (d.emb0 g₀, h) f 0 = om₀ (g₀, h) (fun w => f (d.ext0 T w)) 0 := by
  intro D ψ S S₀ T d χS χT om om₀ hom hom₀ f hf g₀ h
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne (D := D) (m := T.rank) (n := 0)
  have hF := _root_.GlobalTheory.MixSourceFormulas.mixed_source D ψ S S₀ T 0 d χS χT om om₀ hom hom₀ μ 𝓕 hμ
  have H1 := (hF (om (1, h) f) (hom.om_pres _ _ hf)).core g₀ 0
  have H2 := (hF f hf).target h 0
  have hS : ∀ F x, _root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d T ψ μ 𝓕 F x =
      fun w => F (d.ext0 T w) := mixS_rankZero ψ S S₀ T d μ 𝓕 hμ
  simp only [hS] at H1 H2
  rw [H2] at H1
  have e1 : ((d.emb0 g₀, h) : GA D S × GA D T) = (d.emb0 g₀, 1) * (1, h) := by simp
  have e2 : ((g₀, h) : GA D S₀ × GA D T) = (g₀, 1) * (1, h) := by simp
  have := congrFun H1 0
  simp only [map_zero] at this
  rw [e1, e2, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp]
  exact this

theorem om_flatBF_rankZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (B : BesLev D 0) (J : JacLev D 0) (s : StepBF ψ B J) (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ (h₀ : GA D B.A) (g₀ : GA D J.W₀), s.om (embA B.d B.o h₀, J.d.emb0 g₀) Ψ 0 = s.om₀ (B.o.emb (h₀, 1), g₀) (flatBF s Ψ) 0 := by
  intro D ψ B J s Ψ hΨ h₀ g₀
  have hflat : ∀ X, flatBF s X = evalBF s X := by
    intro X; funext w
    obtain ⟨-, 𝓤, -, h1⟩ := s.vU.unit
    have : Subsingleton (UX D 0) := ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
    have hU : 𝓤 = Set.univ := by
      rcases Set.eq_empty_or_nonempty 𝓤 with he | ⟨x, hx⟩
      · rw [he, measure_empty] at h1; exact absurd h1 zero_ne_one
      · exact Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    have huniv : s.vU.ν Set.univ = 1 := hU ▸ h1
    have : IsProbabilityMeasure s.vU.ν := ⟨huniv⟩
    have hc : ∀ u : UX D 0, flatFun ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xZero J.d) (yZero B.V₀ 0 (vecB B.o B.ζ)) X w u = evalBF s X w := by
      intro u
      simp only [flatFun, evalBF, evalZero]
      rw [Subsingleton.elim (xZero J.d ⬝ u.1.1) (xZero J.d)]
      simp [psiUni, upSum, psiE]
    simp only [flatBF, flat, flatAt, hc, integral_const, probReal_univ, one_smul]
  have hd := _root_.GlobalTheory.Desc.weil_data_descend D
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedModelFormulas D := ⟨_root_.GlobalTheory.MixSourceFormulas.mixed_source D, _root_.GlobalTheory.MixTargetProof.mixedTarget D⟩
  have hv := _root_.GlobalTheory.MixValues.mixed_values D
  rw [hflat, GlobalTheory.Unf.EvalCont.om_evalBF s hd hm hv hΨ h₀ g₀]
  unfold evalBF evalZero evalAt
  have hT : ∀ F y, _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target J.d B.V₀ ψ s.vT.μ s.vT.𝓕 F y =
      fun w => F (J.d.inc0 B.V₀ w) := mixT_rankZero ψ _ _ _ J.d s.vT.μ s.vT.𝓕 s.vT.covol
  have hS : ∀ F x, _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source B.d J.W ψ s.vS.μ s.vS.𝓕 F x =
      fun w => F (B.d.ext0 J.W w) := mixS_rankZero ψ _ _ _ B.d s.vS.μ s.vS.𝓕 s.vS.covol
  rw [hT, hS]
  simp only [map_zero]

end GlobalTheory.FinPl.VLast.Transport

end
end

