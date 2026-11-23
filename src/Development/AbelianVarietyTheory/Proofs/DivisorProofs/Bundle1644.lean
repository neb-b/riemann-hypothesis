module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatiblePhaseExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0985
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TildeQDetPtEqChiId
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90USurjective
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyLiftObj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRationalPointsFixerTorusClassesLe
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem card_ratPts_fixG_tor_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ B : ℝ, ∀ (μ : Fin j → ℕ) (T : Finset (GAd σ J)), (∀ t ∈ T, t ∈ ratPts σ J) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ fixG σ J C → t = t') → (∀ t ∈ T, ∃ q ∈ fixG σ J C, ∃ w ∈ W, t = q * lv (tor F E fun i => (μ i : ℤ)) * w) → (T.card : ℝ) ≤ B * ∏ i, bse F ^ ((m + j) * μ i) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv W hW
  obtain ⟨-, hQc, -, -, hNQ, hQP, -, hnorm, hpar⟩ := _root_.GlobalTheory.SphEis.frame_facts F E σ n J j m C D Z J₀ hF
  obtain ⟨V, B₁, hV, hcov⟩ := _root_.GlobalTheory.SphEis.cover_unipRad F E σ n J j m C D Z J₀ hF lv hlv
  obtain ⟨ν, π, DN, DM, hSL⟩ := _root_.GlobalTheory.SphEis.semiLat_fixG F E σ n J j m C D Z J₀ hF
  let Λ : Subgroup (GAd σ J) := ratPts σ J ⊓ fixG σ J C
  haveI : DiscreteTopology Λ := inferInstance
  haveI : Countable Λ := inferInstance
  have hDom := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Λ (Measure.haar : Measure (GAd σ J))
  obtain ⟨B, hB0, hB⟩ := _root_.GlobalTheory.SphEis.card_le_mul_of_unip_cover (GAd σ J) (unipRad σ J C) (fixG σ J C ⊓ fixG σ J D) Λ (ratPts σ J) (fixG σ J C)
    ν π DN DM Measure.haar _ V W hSL inf_le_left inf_le_right hQc
    (fun q hq => by
      obtain ⟨u, hu, x, hx, e, -⟩ := _root_.GlobalTheory.SphEis.fixG_eq_unipRad_mul F E σ n J j m C D Z J₀ hF q hq
      exact ⟨u, hu, x, hx, e⟩)
    (fun K hK => _root_.GlobalTheory.SphEis.compact_inter_ratPts_finite F E σ n J K hK) inferInstance hDom hV hW
  refine ⟨B * B₁, fun μ T hT hdist hform => ?_⟩
  set a := lv (tor F E fun i => (μ i : ℤ)) with ha
  obtain ⟨Y, hYc, hYN, hYcov⟩ := hcov μ
  have haP : a ∈ parFlag σ J C (fun _ => 0) := hpar a _ (hlv.onC _)
  have h1 := hB a Y T
    (fun x hx => (_root_.GlobalTheory.SphEis.lv_comm_of_fix_cols F E σ n J j m C D Z J₀ hF lv hlv _ x hx))
    (fun u => by
      have := hnorm a⁻¹ (inv_mem haP) u
      simpa only [inv_inv] using this)
    hYN
    (fun u hu => by
      obtain ⟨γ, hγ, hγN, y, hy, w, hw, -, e⟩ := hYcov u hu
      exact ⟨γ, ⟨hγ, hNQ hγN⟩, hγN, y, hy, w, hw, e⟩)
    hT
    (fun t ht t' ht' h => hdist t ht t' ht' h.2)
    hform
  calc (T.card : ℝ) ≤ B * Y.card := h1
    _ ≤ B * (B₁ * ∏ i, bse F ^ ((m + j) * μ i)) := mul_le_mul_of_nonneg_left hYc hB0
    _ = B * B₁ * ∏ i, bse F ^ ((m + j) * μ i) := by ring

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftPhaseConjReadingsFiveClauses
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralShift

theorem exists_isCentralShift_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), ∀ z ∈ Subgroup.center G, ∃ ζ, IsCentralShift R i σ z ζ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ z hz
  obtain ⟨e, he⟩ := exists_idemSum R.Pg (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hC.lev.Pg)
  have h := exists_central_lift (Wc D i) (R.βW i) (R.datWp i R.triv) he (g := R.eG z) (map_center R.eG hz)
  obtain ⟨ζ, hc, hs, hl⟩ := h
  have ht : ∀ y v h, (R.HW i σ).e (R.gW i σ z y) v h = (R.HW i σ).e y v (h * ζ) := fun y v h =>
    (congrArg (fun T : MMap (R.MW i σ) => T v h) (hC.models.gW i σ z y)).trans
      (GlobalTheory.GeoActCompare.actW_apply R hC.models.HW σ hl y v h)
  refine ⟨ζ, hz, hc, hl.1, ⟨e, he, hs⟩, hl, ht,
    inner_eq_of_norm (R.gW i σ z) (GlobalTheory.gW_norm_eq R hC.models.HW hC.models.gW hC.models.νW i σ z),
    comm_of_center (R.gW i σ) hz, fun _ _ S _ y y' h => ?_⟩
  refine MultilinearMap.ext fun v => funext fun g => (ht y' v g).trans ?_
  refine (congrArg (fun T : MMap (R.MW i σ) => T v (g * ζ)) h).trans ?_
  show ∑ γ ∈ S, (R.HW i σ).e y v (g * ζ * γ) = ∑ γ ∈ S, (R.HW i σ).e (R.gW i σ z y) v (g * γ)
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [ht, mul_assoc, mul_assoc, Subgroup.mem_center_iff.1 hc γ]

end GlobalTheory.CentralShift

theorem GlobalTheory.CompPhase.exists_isCompPhase_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (u : GA D (Wc D i) → ℂ), PhaseFun R i u → ∃ U, IsCompPhase R i σ u U := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ u hu
  have hc := GlobalTheory.CompPhase.compFun_of_level _ _ hu.2.1 hu.2.2.1 hu.2.2.2
  have h := GlobalTheory.CompPhase.exists_unitary _ (hR.models.HW i σ) (postOn _ (LinearMap.mulLeft ℂ u))
    (fun T hT => Submodule.subset_span (hc.multMap hu.2.2.2 ((GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T).1 hT)))
    (fun T T' => congrArg (_ * ·) (GlobalTheory.CompPhase.ipM_phase hu.1 _ _ T T'))
  obtain ⟨U, hU⟩ := h
  exact ⟨U, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2, fun y v h => congrFun (DFunLike.congr_fun (hU y) v) h⟩

namespace GlobalTheory.ConjInner


set_option maxHeartbeats 1000000 in
theorem inner_reading_conj_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), JEvExists T R κw v₀ → JEvBar T R κw → BarTie fw → ∀ (σ : D.what₂.LL →+* ℂ), ¬ GoodEmb T.Q.c (res T σ) → ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ hC fw i hE hB hT σ hσ
  have hg : GoodEmb T.Q.c (resC T σ) := good_resC T hσ
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := fw.laws.spaceW _ (inR i) _ hg
  have h1 := (hT i σ hσ hV).1 (hB i σ hσ hV)
  obtain ⟨v, hv, h1⟩ := h1
  have h2 := fw.evaluates hE i ((starRingEnd ℂ).comp σ) hg hV
  have h3 : ∀ f g, evAt R i σ v (fw.jK i σ f) g =
      starRingEnd ℂ (evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) (fw.jK i ((starRingEnd ℂ).comp σ) f) g) := fun f g =>
    (congrFun (h1 f) g).trans (congrArg (starRingEnd ℂ) (congrFun (h2 f) g).symm)
  have h4 : ∀ f f', ⟪fw.jK i σ f, fw.jK i σ f'⟫_ℂ =
      starRingEnd ℂ ⟪fw.jK i ((starRingEnd ℂ).comp σ) f, fw.jK i ((starRingEnd ℂ).comp σ) f'⟫_ℂ := fun f f' =>
    inner_conj_of_values R hC.models.HW i σ hv (fun τ => ((fw.hv₀ i _).1 τ).1) (h3 f) (h3 f')
  have h5 := fw.ks i
  obtain ⟨n, b, hb, -, -, -, h5⟩ := h5
  refine inner_conj_of_span σ _ _ _ h5 ?_
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  have e : ∀ k, ∃ f, ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = b k := fun k =>
    ⟨(fw.e i).symm ⟨b k, hb k⟩, congrArg Subtype.val ((fw.e i).apply_symm_apply _)⟩
  have e1 := e k
  have e2 := e l
  obtain ⟨f, e1⟩ := e1
  obtain ⟨f', e2⟩ := e2
  rw [← e1, ← e2]
  exact h4 f f'

end GlobalTheory.ConjInner

namespace GlobalTheory.CoreFive

theorem shift_phase_conj : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), ∀ z ∈ Subgroup.center G, ∃ ζ, IsCentralShift R i σ z ζ) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (u : GA D (Wc D i) → ℂ), PhaseFun R i u → ∃ U, IsCompPhase R i σ u U) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), JEvExists T R κw v₀ → JEvBar T R κw → BarTie fw → ∀ (σ : D.what₂.LL →+* ℂ), ¬ GoodEmb T.Q.c (res T σ) → ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ) :=
  ⟨GlobalTheory.CentralShift.exists_isCentralShift_five, GlobalTheory.CompPhase.exists_isCompPhase_five,
    GlobalTheory.ConjInner.inner_reading_conj_five⟩

end GlobalTheory.CoreFive

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterCompatibilityStandardKernelDataTrueColu
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColRows

theorem charTie_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.CharTie (ofRecord (I.rec7 l Z) L Del h0) t.seam W t.Ch t.glob t.sel := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW
  obtain ⟨hX, hseam, hPr, hCh, hsel, -, -, -, -, -, -, hglob, -, -, -⟩ := hS
  cases t
  dsimp only at *
  subst hX
  obtain rfl := eq_of_heq hPr
  obtain rfl := eq_of_heq hseam
  obtain rfl := eq_of_heq hCh
  rw [eq_of_heq hsel, eq_of_heq hglob, eq_of_heq hW]
  exact GlobalTheory.CoreHt.charTie_trueCols I hOk l Z L

end GlobalTheory.ColRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientFieldIsFieldOfDefinitionChainSteps
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColRows.FldDef

theorem sd_of_isSdLat {B : Base} {n : ℕ} {L : Submodule (𝓞 B.host.E) (Fin n → B.host.E)}
    (h : Formalism.L2.Col.IsSdLat (E := B.fields.E) L) : letI := B.host.cmStar; IsSDLat B.host.E n L := by
  letI := B.host.cmStar
  have hspan : Submodule.span B.fields.E (L : Set (Fin n → B.fields.E)) = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro f hf
    let v : Fin n → B.fields.E := fun i => star (f (Pi.single i 1))
    have hpair : hStd B.fields.E n v = f := by
      apply (Pi.basisFun B.fields.E (Fin n)).ext
      intro i
      rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [hj]
      · simp
    have hline (r : B.fields.E) : r • v ∈ L := by
      rw [← show Formalism.HermitianLatticesTheory.dual (hStd B.fields.E n) L = L from h.2,
        Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      have hy0 : hStd B.fields.E n v y = 0 := by
        rw [hpair]
        exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
      have hz : hStd B.fields.E n y v = 0 := by
        simpa [hy0] using ((hStd_isSymm (E := B.fields.E) (n := n)).eq v y).symm
      simp [hz]
    have hv : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      let coord := (LinearMap.proj i : (Fin n → B.fields.E) →ₗ[B.fields.E] B.fields.E).restrictScalars (𝓞 B.fields.E)
      have htop : L.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.finite_def.mpr (htop ▸ h.1.fg.map coord)
      exact RingOfIntegers.not_isField B.fields.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E))
    rw [Submodule.mem_bot]
    simpa [hv] using hpair.symm
  refine ⟨h.1.fg, hspan, fun y => ?_⟩
  have h2 : y ∈ Formalism.HermitianLatticesTheory.dual (hStd B.fields.E n) L ↔ y ∈ L := by rw [h.2]
  rw [← h2, Formalism.L2.Col.mem_dual]
  refine forall₂_congr fun x _ => ?_
  rw [Submodule.mem_one]
  rfl

theorem sd_stdL (D : D7) (n : ℕ) : StandardLatticesGL3.SD D (Th.stdL D.host n) := by
  exact GlobalTheory.Glob.IntegralWittCoefficients.Model.isSDLat_std _ _

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem chiRec_detId {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)}
    (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl) (n : ℕ) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E))
    (hL : StandardLatticesGL3.SD (I.rec7 l Z) L) :
    TaylorLogMetric.chiRec (I.rec7 l Z) idl (Th.detId B.host (Th.stdL B.host n) L) = I.chi (Th.detId B.host (Th.stdL B.host n) L) := by
  letI := B.host.cmStar
  let S0 : SDLat B.host.E n := ⟨Th.stdL B.host n, sd_stdL (I.rec7 l Z) n⟩
  let L1 : SDLat B.host.E n := ⟨L, hL⟩
  have h2 : idl ((I.rec7 l Z).relDet n S0 L1) = TaylorLogMetric.detId (I.rec7 l Z) S0.1 L1.1 := hidl.2.2.2.2 n S0 L1
  have e : TaylorLogMetric.detId (I.rec7 l Z) S0.1 L1.1 = Th.detId B.host (Th.stdL B.host n) L := rfl
  have hl : TaylorLogMetric.chiRec (I.rec7 l Z) idl (Th.detId B.host (Th.stdL B.host n) L) =
      ((TaylorLogMetric.chiQ (I.rec7 l Z) ((I.rec7 l Z).relDet n S0 L1) : ℂˣ) : ℂ) := by
    rw [← e, ← h2, TaylorLogMetric.chiRec_idl _ _ hidl.1]
  rw [hl]
  obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective ((I.rec7 l Z).relDet n S0 L1)
  rw [← ht]
  have hχ := I.C.isChi
  have hK := (GlobalTheory.Mem.KerDet.kernel_open_and_factor B.R B.host).2.2.2 I.C.chiPsi hχ.triv (fun v y hy _ => hχ.unr v y hy)
    fun v _ => hχ.unr v
  have hr : (QuotientGroup.mk (toDtT B.host I.SQ t) : DtT B.host ⧸ UOT B.host) = relDetT B.host n (Th.stdL B.host n) L := by
    have h1 := toDtTMod_mk B.host I.SQ (t : DtQ B.host I.SQ)
    have h3 := toDtTMod_relDetQ B.host I.SQ n (Th.stdL B.host n) L
    have h6 : (QuotientGroup.mk (t : DtQ B.host I.SQ) : DtQ B.host I.SQ ⧸ UOQ B.host I.SQ) = relDetQ B.host I.SQ n (Th.stdL B.host n) L := ht
    rw [← h1, h6, h3]
  have h5 : ((tildeQ B.host I.SQ I.C.chiPsi t : ℂˣ) : ℂ) = ((tildeD B.host I.C.chiPsi (toDtT B.host I.SQ t) : ℂˣ) : ℂ) := by
    rw [tildeQ_eq_comp B.host I.SQ hK]; rfl
  exact h5.trans (GlobalTheory.Mem.ChiDet.tildeD_eq_chiId B.R B.host I.C.chiPsi hχ n L (Submodule.IsLattice.of_fg _ hL.1) _ hr)
end GlobalTheory.ColRows.FldDef

namespace GlobalTheory.ColRows.FldDef
open GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

theorem fieldOfDefinition_congr {B : Base} (J : AmbIn B.host) (χ₁ χ₂ : Submodule (𝓞 B.host.E) B.host.E → ℂ)
    (hχ : ∀ (n : ℕ) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E)), Formalism.L2.Col.IsSdLat (E := B.fields.E) L →
      χ₁ (Th.detId B.host (Th.stdL B.host n) L) = χ₂ (Th.detId B.host (Th.stdL B.host n) L))
    {Pr : Primes B.fields} {R : Ranks} (W : Formalism.L2.Col.Wts B.fields Pr.Word R)
    (sel : HeightOneSpectrum (𝓞 B.fields.F) → HeightOneSpectrum (𝓞 B.fields.E)) {Sg : Set ℕ}
    (mu : Tup B.fields.F B.fields.E B.fields.K Sg) (cst : LocCst B.fields (rowSG Pr sel mu)) (u : Pr.Word) :
    FieldOfDefinition W sel mu cst u (J.amb B χ₁) → FieldOfDefinition W sel mu cst u (J.amb B χ₂) := by
  intro h i hi L L' c x hR e hdeg
  obtain ⟨y, hy⟩ := h i hi L L' c x hR e hdeg
  have hc : Th.chiFac B.host χ₁ (R.N i) (R.N (i + 1)) L L' = Th.chiFac B.host χ₂ (R.N i) (R.N (i + 1)) L L' := by
    unfold Th.chiFac
    rw [hχ _ L hR.1, hχ _ L' hR.2.1]
  have he : (J.amb B χ₁).e (R.N i) (R.N (i + 1)) L L' = (J.amb B χ₂).e (R.N i) (R.N (i + 1)) L L' := by
    funext z
    show Th.chiFac B.host χ₁ _ _ L L' * _ = Th.chiFac B.host χ₂ _ _ L L' * _
    rw [hc]
  have hth : (J.amb B χ₁).thInd (Sall sel mu u) L L' c x = (J.amb B χ₂).thInd (Sall sel mu u) L L' c x := by
    unfold Amb.thInd
    rw [he]
    rfl
  refine ⟨y, hy.trans ?_⟩
  rw [hth]
  show (Th.chiFac B.host χ₁ _ _ L L')⁻¹ * _ = (Th.chiFac B.host χ₂ _ _ L L')⁻¹ * _
  rw [hc]
  rfl
end GlobalTheory.ColRows.FldDef


open GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds in
theorem GlobalTheory.ColRows.fieldOfDefinition_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → ∀ u a, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.FieldOfDefinition W t.sel (t.tup a) (t.cst a) (t.word u) t.amb := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W hJ hS hW u a
  obtain ⟨-, -, -, hFD⟩ := GlobalTheory.Core.Ht2.analyticTies_trueCols I hOk (GlobalTheory.Mem.Col2.base_fields_primes_ok B X).1 l Z hJ
  have hχ : ∀ (n : ℕ) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E)), Formalism.L2.Col.IsSdLat (E := B.fields.E) L →
      I.chi (Th.detId B.host (Th.stdL B.host n) L) = t.χ (Th.detId B.host (Th.stdL B.host n) L) := fun n L hL => by
    have h1 := GlobalTheory.ColRows.FldDef.chiRec_detId I l Z t.idl_ok n L (GlobalTheory.ColRows.FldDef.sd_of_isSdLat hL)
    have h2 := congrFun t.χ_rec (Th.detId B.host (Th.stdL B.host n) L)
    exact h1.symm.trans h2.symm
  have hF : ∀ (u' : (B.primes X).Word) (a' : I.ι), FieldOfDefinition (Pr := B.primes X) B.wts I.sel (I.tup a') (I.cst a') u' (I.J.amb B t.χ) :=
    fun u' a' => by
      have h3 := GlobalTheory.ColRows.FldDef.fieldOfDefinition_congr (R := B.R) I.J I.chi t.χ hχ B.wts I.sel (I.tup a') (I.cst a') u'
      have h4 : FieldOfDefinition (Pr := B.primes X) B.wts I.sel (I.tup a') (I.cst a') u' (I.J.amb B I.chi) := hFD u' a'
      exact h3 h4
  clear hFD hχ
  obtain ⟨hX, -, hPr, -, hsel, hS', hword, htup, hcst, -, -, -, hamb, -, -⟩ := hS
  cases t
  subst hX
  obtain rfl := eq_of_heq hPr
  subst hS'
  obtain rfl := eq_of_heq hsel
  obtain rfl := eq_of_heq htup
  obtain rfl := eq_of_heq hcst
  obtain rfl := eq_of_heq hword
  obtain rfl := eq_of_heq hW
  have hamb' := eq_of_heq hamb
  rw [hamb']
  exact hF u a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedColumnLatticeIntegralFrameCoordsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedColumnLattice_integral_frameCoords : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D), y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) → ∀ i, ((Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.FrameTransport.hatL_colLat_coord_int | exact GlobalTheory.FrameTransport.hatL_colLat_coord_int | (intros; apply GlobalTheory.FrameTransport.hatL_colLat_coord_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeMapIdealMulTransportStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedLatticeMap_idealMul_transport : ∀ {D : D7} {n : ℕ} (uf : GL (Fin n) (Lev.EAf D)) (L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (y : Fin n → Lev.EAf D), y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • L) → uf.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) := by
  first | exact @GlobalTheory.HatIdealCarry.transport | exact GlobalTheory.HatIdealCarry.transport | (intros; apply GlobalTheory.HatIdealCarry.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetSumEqSumCellSum
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelCells

variable {D : D7} {n : ℕ}

def lastDiag (R : Type) [Zero R] [One R] (n j : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => if n - j ≤ i.val then 1 else 0

def wMat (R : Type) [Ring R] (n j : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  StdUnn.blk4 (1 - lastDiag R n j) (lastDiag R n j) (-lastDiag R n j) (1 - lastDiag R n j)

theorem lastDiag_mul_self (R : Type) [Ring R] (n j : ℕ) : lastDiag R n j * lastDiag R n j = lastDiag R n j := by
  simp only [lastDiag, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split_ifs <;> simp

theorem lastDiag_mul_one_sub (R : Type) [Ring R] (n j : ℕ) : lastDiag R n j * (1 - lastDiag R n j) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, lastDiag_mul_self, sub_self]

theorem one_sub_mul_lastDiag (R : Type) [Ring R] (n j : ℕ) : (1 - lastDiag R n j) * lastDiag R n j = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, lastDiag_mul_self, sub_self]

theorem adj_lastDiag {j : ℕ} : adj (lastDiag (AE D) n j) = lastDiag (AE D) n j := by
  ext i k
  simp only [adj, lastDiag, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : k = i
  · subst h; split_ifs <;> simp
  · simp [h, Ne.symm h]

theorem wMat_key {R : Type} [CommRing R] {n : ℕ} (L : Matrix (Fin n) (Fin n) R) (h : L * L = L) :
    StdUnn.blk4 (1 - L) (-L) L (1 - L) * StdUnn.blk4 0 1 (-1) 0 * StdUnn.blk4 (1 - L) L (-L) (1 - L) =
      StdUnn.blk4 0 1 (-1) 0 := by
  rw [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.submatrix_fromBlocks_mul]
  have h1 : (1 - L) * (1 - L) = 1 - L := by rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, h, sub_self, sub_zero]
  have h2 : L * (1 - L) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
  have h3 : (1 - L) * L = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
    add_zero, zero_add]
  congr 1
  · simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, h2, h3, neg_zero, add_zero]
  · simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, h, h1, h2, h3]; abel
  · rw [h1, h]; abel
  · rw [h2, h3]; simp

theorem exists_wPart (j : ℕ) : ∃ g : StdUnn.G D n, StdUnn.mat g = wMat (AE D) n j := by
  have e1 := lastDiag_mul_self (AE D) n j
  have e2 := lastDiag_mul_one_sub (AE D) n j
  have e3 := one_sub_mul_lastDiag (AE D) n j
  have e4 : (1 - lastDiag (AE D) n j) * (1 - lastDiag (AE D) n j) = 1 - lastDiag (AE D) n j := by
    rw [Matrix.sub_mul, Matrix.one_mul, e2, sub_zero]
  refine StdUnn.Model.exists_mat _ (StdUnn.blk4 (1 - lastDiag (AE D) n j) (-lastDiag (AE D) n j) (lastDiag (AE D) n j)
    (1 - lastDiag (AE D) n j)) ?_ ?_ ?_
  · simp only [wMat, StdUnn.Model.submatrix_fromBlocks_mul, e1, e2, e3, e4, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← StdUnn.Model.block_matrix_one]; congr 1 <;> abel
  · simp only [wMat, StdUnn.Model.submatrix_fromBlocks_mul, e1, e2, e3, e4, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← StdUnn.Model.block_matrix_one]; congr 1 <;> abel
  · have ha : adj (wMat (AE D) n j) = StdUnn.blk4 (1 - lastDiag (AE D) n j) (-lastDiag (AE D) n j) (lastDiag (AE D) n j)
        (1 - lastDiag (AE D) n j) := by
      rw [wMat, StdUnn.Model.adelicConjTranspose_blockMatrixTwoByTwoFin, adj_sub, adj_one, adj_neg, adj_lastDiag]
    rw [ha]
    exact wMat_key _ e1






end GlobalTheory.SiegelCells

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCutOperatorsMirabolicFinitePlacesStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cutOperators_mirabolic_finitePlaces : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (n : ℕ) (h : Fin n → GA E (m + 1)) (c : Fin n → ℂ), (∀ i, h i ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∑ i, c i * W (p * h i) = (GlobalTheory.JSW.MirPatch.cell K q).indicator W p := by
  first
  | exact @GlobalTheory.JSW.MirPatch.cut_operators
  | exact GlobalTheory.JSW.MirPatch.cut_operators
  | (intros; apply GlobalTheory.JSW.MirPatch.cut_operators <;> assumption)
end

