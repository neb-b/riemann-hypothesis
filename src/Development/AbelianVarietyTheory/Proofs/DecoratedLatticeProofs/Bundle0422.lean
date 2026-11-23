module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0325
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlacesGroupEqProductLocalGroups
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QProd

open GlobalTheory.FinPl in
theorem at_eq' {D : D7} (V : HSp D) (P : Pl D → Prop) : grpAt V P = GfC V ⊓ grpOff V (fun p => ¬ P p) := by
  rw [(GlobalTheory.FinPl.SetCut.grp_split D V ∅).2.2.2.2.2.2.2.1 (fun p => ¬ P p)]
  simp only [not_not]

open GlobalTheory.FinPl in
theorem at_le_off' {D : D7} (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → ¬ P' p) : grpAt V P ≤ grpOff V P' :=
  (GlobalTheory.FinPl.SetCut.grp_split D V ∅).2.2.2.2.2.2.1 P P' h


open GlobalTheory.FinPl in
theorem off_mono {D : D7} {V : HSp D} {R R' : Pl D → Prop} (hR : ∀ p, R' p → R p) {g : GA D V} (h : g ∈ grpOff V R) :
    g ∈ grpOff V R' := by
  unfold grpOff at h ⊢
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at h ⊢
  intro a b
  have := h a b
  unfold idOff at this ⊢
  rw [Submodule.mem_iInf] at this ⊢
  intro u
  exact this ⟨u.1, hR u.1 u.2⟩


open GlobalTheory.FinPl in
theorem off_of_each {D : D7} {V : HSp D} {R : Pl D → Prop} {g : GA D V} (h : ∀ p, R p → g ∈ grpOff V (· = p)) :
    g ∈ grpOff V R := by
  unfold grpOff
  rw [GlobalTheory.FinPlLoc.mem_congGrp]
  intro a b
  unfold idOff
  rw [Submodule.mem_iInf]
  intro u
  have hu := h u.1 u.2
  unfold grpOff at hu
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at hu
  have := hu a b
  unfold idOff at this
  rw [Submodule.mem_iInf] at this
  exact this ⟨u.1, rfl⟩

theorem prod_local : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ P : (∀ i, GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k) →* GA D (c.V (j + 1)), (∀ (H : Subgroup (GA D (c.V (j + 1)))) y, (∀ i, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i) ∈ H) → P y ∈ H) ∧ (∀ y, P y ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), ∃ y, x = P y ∧ ∀ i, x * ((F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
  intro D c v t w F hF j σ h
  have hd : ∀ i : Fin F.r, j + 1 + (2 * σ + 2) = (F.Q i).s + 1 := fun i => by have := (F.Q i).hs; omega
  have key := fun i => GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V (j + 1)) ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2))
    ((F.Q i).FY (j + 1) (2 * σ + 2) (hd i)) ((F.Q i).gl (j + 1) (2 * σ + 2) (hd i)) ((F.Q i).gl_loc (j + 1) (2 * σ + 2) (hd i))
  let gl := fun i => (F.Q i).gl (j + 1) (2 * σ + 2) (hd i)
  have hoff : ∀ i i', i ≠ i' → ∀ g, gl i' g ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
    intro i i' hne g
    have hr : gl i' g ∈ (gl i').range := ⟨g, rfl⟩
    rw [(key i').2.1] at hr
    exact at_le_off' _ (fun p hp hq => hne (hF.inj (hq.symm.trans hp))) hr
  have hcomm : Pairwise fun i i' => ∀ x y, Commute (gl i x) (gl i' y) := by
    intro i i' hne x y
    exact (key i).2.2.2.1 x _ (hoff i i' hne y)
  have hmem : ∀ (H : Subgroup (GA D (c.V (j + 1)))) y, (∀ i, gl i (y i) ∈ H) →
      MonoidHom.noncommPiCoprod gl hcomm y ∈ H := by
    intro H y hy
    exact Submonoid.noncommProd_mem H.toSubmonoid Finset.univ _ (fun _ _ _ _ h => hcomm h _ _) (fun i _ => hy i)
  have hat : ∀ i g, gl i g ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q) := by
    intro i g
    have hr : gl i g ∈ (gl i).range := ⟨g, rfl⟩
    rw [(key i).2.1] at hr
    rw [at_eq'] at hr ⊢
    refine ⟨hr.1, off_mono (fun p hp hq => hp ((hF.places p).2 ⟨i, hq.symm⟩)) hr.2⟩
  refine ⟨MonoidHom.noncommPiCoprod gl hcomm, hmem, fun y => hmem _ y fun i => hat i (y i), ?_⟩
  intro x hx
  choose y hy _ using fun i => (key i).2.2.1 x
  set P := MonoidHom.noncommPiCoprod gl hcomm
  have hsplit : ∀ i, P y = P (Function.update y i 1) * gl i (y i) := by
    intro i
    have hy' : y = Function.update y i 1 * Pi.mulSingle i (y i) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    conv_lhs => rw [hy']
    rw [map_mul, MonoidHom.noncommPiCoprod_mulSingle]
  have hrest : ∀ i, P (Function.update y i 1) ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
    intro i
    refine hmem _ _ fun k => ?_
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk]
      exact hoff i k (Ne.symm hk) _
  have hz_i : ∀ i, x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
    intro i
    rw [hsplit i, _root_.mul_inv_rev, ← mul_assoc]
    exact Subgroup.mul_mem _ (hy i) (Subgroup.inv_mem _ (hrest i))
  have hzQ : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q) :=
    Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hmem _ y fun i => hat i (y i)))
  rw [at_eq'] at hzQ
  have hall : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (fun _ => ¬ False) := by
    refine off_of_each fun p _ => ?_
    by_cases hp : p ∈ w.Q
    · obtain ⟨i, rfl⟩ := (hF.places p).1 hp
      exact hz_i i
    · exact off_mono (fun p' hp' => hp'.symm ▸ hp) hzQ.2
  have hz1 : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (fun _ => False) := by
    rw [at_eq']
    exact ⟨hzQ.1, hall⟩
  have := GlobalTheory.VacFixP.eq_one_of_grpAt (fun _ h => h) hz1
  exact ⟨y, mul_inv_eq_one.1 this, hy⟩

end GlobalTheory.QProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentMeanThetaLiftEqOrbitIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal NNReal

namespace GlobalTheory.Unf

theorem mean_lift_eq_orbit_integral : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → (∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, ‖Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1‖ₑ ∂(vN.ν.prod vW.μ) ≠ ⊤) ∧ ∫ n in vN.𝓝, Th n.1 * liftS om vW.μ vW.𝓕 G Φ n.1 ∂vN.ν = ∫ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1 ∂(vN.ν.prod vW.μ) := by
  intro D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN vW x₀ Th hB hTh G Φ hG hΦ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  haveI := vN.unit.1
  haveI := vW.haar
  have hT := _root_.GlobalTheory.Unf.TermLaw.term_laws D ψ V V₀ W ρ d χV χW om om' hw hw' vS
  have hsplit : ∀ (g : GA D V) (h : GA D W), om (g, h) Φ = om (g, 1) (om (1, h) Φ) := by
    intro g h
    rw [show ((g, h) : GA D V × GA D W) = (g, 1) * (1, h) by simp, map_mul, Module.End.mul_apply]
  have hsum : ∀ (n : flagN d) (h : GA D W), HasSum (term ψ d W vS (om (n.1, h) Φ)) (om (n.1, h) Φ 0) :=
    fun n h => (hT _ (hw.om_pres _ _ hΦ)).2.2.2.2

  obtain ⟨C, A, hC⟩ := _root_.GlobalTheory.Unf.sum_term_bound D ψ V V₀ W ρ d χV χW om om' hw hw' vS Φ hΦ
  have hbd : ∀ (n : flagN d) (h : GA D W), ∑' x, ‖term ψ d W vS (om (n.1, h) Φ) x‖ₑ ≤
      ENNReal.ofReal (max C 0 * quotHeight W h ^ A) := fun n h => by
    have := hC 1 h n.1 n.2
    rw [mul_one, height_one, one_mul] at this
    exact this.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (quotHeight_pos W h).le _)))
  obtain ⟨B, hBd⟩ := hG.2.2 A
  have hB0 : 0 ≤ B := (mul_nonneg (norm_nonneg _) (pow_nonneg (quotHeight_pos W 1).le _)).trans (hBd 1)

  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun n : flagN d => Th n.1) hTh.cont.continuousOn
  have hThb : ∀ n : flagN d, ‖Th n.1‖ ≤ M := by
    intro n
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    have hγ' : (γ : GA D V) ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have : Th ((γ * k : flagN d) : GA D V) = Th k.1 := hTh.left γ.1 hγ' γ.2 k.1 k.2
    rw [this]
    exact hM k hk
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hThb 1)

  have hGt : ∀ (n : flagN d) (h : GA D W), ‖G h‖ₑ * ∑' x, ‖term ψ d W vS (om (n.1, h) Φ) x‖ₑ ≤
      ENNReal.ofReal (max C 0 * B) := fun n h => by
    refine (mul_le_mul' le_rfl (hbd n h)).trans ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖G h‖ * (max C 0 * quotHeight W h ^ A) = max C 0 * (‖G h‖ * quotHeight W h ^ A) := by ring
      _ ≤ max C 0 * B := mul_le_mul_of_nonneg_left (hBd h) (le_max_right _ _)
  have hall : ∀ (n : flagN d) (h : GA D W) (S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E)),
      ∑' y : S, ‖Th n.1 * G h * term ψ d W vS (om (n.1, h) Φ) y.1‖ₑ ≤ ENNReal.ofReal (M * (max C 0 * B)) := by
    intro n h S
    simp_rw [enorm_mul]
    rw [ENNReal.tsum_mul_left, mul_assoc, ENNReal.ofReal_mul hM0]
    refine mul_le_mul' ?_ ?_
    · rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (hThb n)
    · exact (mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _)).trans (hGt n h)
  have hK0 : 0 ≤ M * (max C 0 * B) := mul_nonneg hM0 (mul_nonneg (le_max_right _ _) hB0)
  have hnorm : ∀ (n : flagN d) (h : GA D W), ‖om (n.1, h) Φ 0‖ * ‖G h‖ ≤ max C 0 * B := fun n h => by
    have h1 : ‖om (n.1, h) Φ 0‖ₑ * ‖G h‖ₑ ≤ ENNReal.ofReal (max C 0 * B) := by
      rw [mul_comm, ← (hsum n h).tsum_eq]
      exact (mul_le_mul' le_rfl enorm_tsum_le_tsum_enorm).trans (hGt n h)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_mul, toReal_enorm, toReal_enorm,
      ENNReal.toReal_ofReal (mul_nonneg (le_max_right _ _) hB0)] at h2
  haveI : IsFiniteMeasure (vN.ν.restrict vN.𝓝) :=
    isFiniteMeasure_restrict.2 (by rw [vN.unit.2.2]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (vW.μ.restrict vW.𝓕) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.Chain.LiftReg.vol_ne_top vW.haar vW.fund)
  have hfin : (vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕) ≠ ⊤ := by
    rw [Measure.prod_prod, vN.unit.2.2, one_mul]
    exact GlobalTheory.Chain.LiftReg.vol_ne_top vW.haar vW.fund
  refine ⟨ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := M * (max C 0 * B))) hfin) ?_, ?_⟩
  · calc _ ≤ ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ENNReal.ofReal (M * (max C 0 * B)) ∂(vN.ν.prod vW.μ) :=
          lintegral_mono fun p => hall p.1 p.2 _
      _ = _ := setLIntegral_const _ _
  have hF : Integrable (fun p : flagN d × GA D W => Th p.1.1 * (om (p.1.1, p.2) Φ 0 * G p.2))
      ((vN.ν.restrict vN.𝓝).prod (vW.μ.restrict vW.𝓕)) := by
    refine Integrable.of_bound ?_ (M * (max C 0 * B)) (Filter.Eventually.of_forall fun p => ?_)
    · exact ((hTh.cont.comp continuous_fst).mul (((hw.om_cont Φ hΦ 0).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).mul
          (hG.2.1.comp continuous_snd))).aestronglyMeasurable
    · rw [norm_mul, norm_mul]
      exact mul_le_mul (hThb p.1) (hnorm p.1 p.2) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hM0
  have hH : Integrable (fun p : flagN d × GA D W =>
      ∑' y : Orb W x₀, Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1)
      ((vN.ν.restrict vN.𝓝).prod (vW.μ.restrict vW.𝓕)) := by
    refine Integrable.of_bound ?_ (M * (max C 0 * B)) (Filter.Eventually.of_forall fun p => ?_)
    · refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset (Orb W x₀)))
        (f := fun s p => ∑ y ∈ s, Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1) (fun s => ?_)
        (Filter.Eventually.of_forall fun p => ?_)
      · exact (continuous_finsetSum _ fun y _ => ((hTh.cont.comp continuous_fst).mul (hG.2.1.comp continuous_snd)).mul
          (((hT Φ hΦ).2.2.2.1 y.1).comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))).aestronglyMeasurable
      · exact (((hsum p.1 p.2).summable.mul_left (Th p.1.1 * G p.2)).subtype _).hasSum
    · have h1 := enorm_tsum_le_tsum_enorm.trans (hall p.1 p.2 (Orb W x₀))
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [toReal_enorm, ENNReal.toReal_ofReal hK0] at h2
  rw [← Measure.prod_restrict]
  simp only [liftS_apply]
  calc ∫ n in vN.𝓝, Th n.1 * ∫ h in vW.𝓕, om (n.1, h) Φ 0 * G h ∂vW.μ ∂vN.ν
      = ∫ n in vN.𝓝, ∫ h in vW.𝓕, Th n.1 * (om (n.1, h) Φ 0 * G h) ∂vW.μ ∂vN.ν := by
        congr 1; funext n; exact (integral_const_mul _ _).symm
    _ = ∫ h in vW.𝓕, ∫ n in vN.𝓝, Th n.1 * (om (n.1, h) Φ 0 * G h) ∂vN.ν ∂vW.μ :=
        integral_integral_swap hF
    _ = ∫ h in vW.𝓕, G h * ∫ n in vN.𝓝, Th n.1 * om (n.1, 1) (om (1, h) Φ) 0 ∂vN.ν ∂vW.μ := by
        congr 1; funext h; rw [← integral_const_mul]; congr 1; funext n; rw [hsplit]; ring
    _ = ∫ h in vW.𝓕, G h * ∫ n in vN.𝓝, ∑' x : Orb W x₀,
          Th n.1 * term ψ d W vS (om (n.1, 1) (om (1, h) Φ)) x.1 ∂vN.ν ∂vW.μ := by
        congr 1; funext h
        rw [_root_.GlobalTheory.Unf.mean_theta_orbit D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh _ (hw.om_pres _ _ hΦ)]
    _ = ∫ h in vW.𝓕, ∫ n in vN.𝓝, ∑' y : Orb W x₀,
          Th n.1 * G h * term ψ d W vS (om (n.1, h) Φ) y.1 ∂vN.ν ∂vW.μ := by
        congr 1; funext h; rw [← integral_const_mul]; congr 1; funext n
        rw [← tsum_mul_left, ← hsplit]; congr 1; funext x; ring
    _ = _ := (integral_prod_symm _ hH).symm

end GlobalTheory.Unf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VolumeSeeSawTupleLevelEqSphericalDivIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevIdx

theorem core {D : D7} (S : HSp D) (N : Lat S) (hN : IsSelfDualC S N) {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)]
    [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)]
    (q : (i : Fin r) → SplitPt D (k i)) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (F : (i : Fin r) → GlobalTheory.LocMod.Frame (k i) S.rank (Y i))
    (hinj : Function.Injective fun i => (q i).v)
    (hlat : ∀ i, IntIn (q i) S (F i) N) (J : (i : Fin r) → Subgroup (GL (Y i) (k i)))
    (hJ : ∀ i, J i ≤ GlobalTheory.SplitWeil.KO (k i) (Y i)) (hJo : ∀ i, IsOpen (J i : Set (GL (Y i) (k i))))
    (μ : Measure (GfC S)) [μ.IsHaarMeasure] (U U' : Subgroup (GA D S)) (b : GA D S) (hb : b ∈ GfC S) (hU : U ≤ GfC S)
    (hUc : IsCompact (U : Set (GA D S))) (hUo : IsOpen ((U.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)))
    (hK : ∀ κ, InK S N (fun p => ∃ i, (q i).v = p) κ → κ ∈ U)
    (hM : ∀ g ∈ U, Moves S g N N (fun p => ∃ i, (q i).v = p))
    (hU' : ∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i (x : GL (Y i) (k i)), (mt S g).map (q i).pr = (F i).β * x.val * (F i).γ → x ∈ J i) :
    μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((J i).relIndex (GlobalTheory.SplitWeil.KO (k i) (Y i)) : ℝ) =
      μ.real {g | b * g.1 * b⁻¹ ∈ U} := by
  set φ : GA D S →* ((i : Fin r) → GL (Y i) (k i)) := MonoidHom.pi fun i => locHom (q i) S (F i) with hφ
  have hφi : ∀ g i, φ g i = locHom (q i) S (F i) g := fun _ _ => rfl
  have hU'' : ∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ J i := by
    intro g
    rw [hU' g]
    refine and_congr_right fun _ => forall_congr' fun i => ?_
    refine ⟨fun h => h _ ((eq_locHom_iff _ _ _ _ _).2 rfl), fun h x hx => ?_⟩
    rw [(eq_locHom_iff _ _ _ _ _).1 hx]; exact h
  have hle : U' ≤ U := fun g hg => ((hU'' g).1 hg).1

  have hidx : U'.relIndex U = ∏ i, (J i).relIndex (GlobalTheory.SplitWeil.KO (k i) (Y i)) := by
    refine _root_.GlobalTheory.relIndex_preimage_pi_eq_prod φ U U' (fun i => GlobalTheory.SplitWeil.KO (k i) (Y i)) J hJ ?_ ?_ hU''
    · intro g hg i
      exact _root_.GlobalTheory.SplitInt.mem_KO_of_moves (q i) S (F i) N _ ⟨i, rfl⟩ (hlat i) g (hM g hg) _ ((eq_locHom_iff _ _ _ _ _).2 rfl)
    · intro x hx
      obtain ⟨g, hg, hgx⟩ := _root_.GlobalTheory.SplitOnto.exists_of_local S N hN k q Y F hinj hlat x hx
      refine ⟨g, hK g hg, funext fun i => ?_⟩
      rw [hφi]; exact ((eq_locHom_iff _ _ _ _ _).1 (hgx i)).symm

  let cj : GfC S →* GfC S :=
    { toFun := fun g => ⟨b * g.1 * b⁻¹, (GfC S).mul_mem ((GfC S).mul_mem hb g.2) ((GfC S).inv_mem hb)⟩
      map_one' := by ext1; simp
      map_mul' := fun g h => by ext1; simp [mul_assoc] }
  have hcj : Continuous cj :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hcjb : Function.Bijective cj := by
    refine ⟨fun g h e => ?_, fun g => ⟨⟨b⁻¹ * g.1 * b, (GfC S).mul_mem ((GfC S).mul_mem ((GfC S).inv_mem hb) g.2) hb⟩, ?_⟩⟩
    · have := congrArg Subtype.val e
      ext1; simpa [cj] using this
    · ext1; simp [cj, mul_assoc]
  set H := (U.subgroupOf (GfC S)).comap cj
  set H' := (U'.subgroupOf (GfC S)).comap cj
  have eH : {g : GfC S | b * g.1 * b⁻¹ ∈ U} = (H : Set (GfC S)) := rfl
  have eH' : {g : GfC S | b * g.1 * b⁻¹ ∈ U'} = (H' : Set (GfC S)) := rfl
  have hHH' : H'.relIndex H = U'.relIndex U := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hcjb.2, Subgroup.relIndex_subgroupOf hU]

  have hHc : IsCompact (H : Set (GfC S)) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    have e : Subtype.val '' (H : Set (GfC S)) = (fun g => b⁻¹ * g * b) '' (U : Set (GA D S)) := by
      ext y; constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨b * g.1 * b⁻¹, hg, by simp [mul_assoc]⟩
      · rintro ⟨u, hu, rfl⟩
        refine ⟨⟨b⁻¹ * u * b, (GfC S).mul_mem ((GfC S).mul_mem ((GfC S).inv_mem hb) (hU hu)) hb⟩, ?_, rfl⟩
        change b * (b⁻¹ * u * b) * b⁻¹ ∈ U
        simpa [mul_assoc] using hu
    convert hUc.image ((continuous_const.mul continuous_id).mul continuous_const) using 1
    exact e

  have hU'o : IsOpen ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) := by
    have e : ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) =
        ((U.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) ∩
          ⋂ i, (fun g : GfC S => locHom (q i) S (F i) g.1) ⁻¹' (J i : Set (GL (Y i) (k i))) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      rw [hU'']
      rfl
    rw [e]
    exact hUo.inter (isOpen_iInter_of_finite fun i =>
      (hJo i).preimage ((continuous_locHom (q i) S (F i)).comp continuous_subtype_val))
  have hH'o : IsOpen (H' : Set (GfC S)) := hU'o.preimage hcj
  have hH'H : H' ≤ H := fun g hg => hle hg
  rw [eH, eH', ← Nat.cast_prod, ← hidx, ← hHH']
  exact vol_mul_relIndex μ H H' hH'H hHc hH'o

end GlobalTheory.LevIdx

theorem GlobalTheory.LevIdx.vol_level_eq : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : GlobalTheory.QPl.QFam v t), F.Pins w → (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) → ∀ (μ : Measure (GfC (c.V j))), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D (c.V j))) (b : GA D (c.V j)), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D (c.V j))) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (c.V j))) : Set (GfC (c.V j))) → (∀ κ, InK _ (v.N j) (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g (v.N j) (v.N j) (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i d hd x, (mt _ g).map (F.Q i).q.pr = ((F.Q i).FY j d hd).β * x.val * ((F.Q i).FY j d hd).γ → x ∈ ((F.Q i).T.lev j d hd).J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx j : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) ∧ (IsSelfDualC c.T v.NT → (∀ i, IsOpen ((F.Q i).T.levTop.J : Set (GL (F.Q i).Z (F.Q i).k))) → ∀ (μ : Measure (GfC c.T)), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D c.T)) (b : GA D c.T), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D c.T)) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC c.T)) : Set (GfC c.T)) → (∀ κ, InK _ v.NT (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g v.NT v.NT (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i (x : GL (F.Q i).Z (F.Q i).k), (mt _ g).map (F.Q i).q.pr = (F.Q i).FT.β * x.val * (F.Q i).FT.γ → x ∈ (F.Q i).T.levTop.J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx D.R.m : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) := by
  intro D c v t w F hP
  have hQ : (· ∈ w.Q) = fun p => ∃ i, (F.Q i).q.v = p := funext fun p => propext (hP.places p)
  have hs : ∀ i, (F.Q i).s + 1 + 1 = D.R.m := fun i => (F.Q i).hs
  refine ⟨fun j hj hN μ hμ U U' b hb hU hUc hUo hK hM hU' => ?_, fun hN hTo μ hμ U U' b hb hU hUc hUo hK hM hU' => ?_⟩
  · let d : Fin F.r → ℕ := fun i => (F.Q i).s + 1 - j
    have hd : ∀ i, j + d i = (F.Q i).s + 1 := fun i => by have := hs i; simp only [d]; omega
    rw [hQ] at hK hM
    have key := GlobalTheory.LevIdx.core (c.V j) (v.N j) hN (fun i => (F.Q i).k) (fun i => (F.Q i).q) (fun i => (F.Q i).X j ⊕ Fin (d i))
      (fun i => (F.Q i).FY j (d i) (hd i)) hP.inj (fun i => (F.Q i).latY j (d i) (hd i))
      (fun i => ((F.Q i).T.lev j (d i) (hd i)).J) (fun i => (F.Q i).le j (d i) (hd i))
      (fun i => ((F.Q i).reg.2.2 j (d i) (hd i)).1) μ U U' b hb hU hUc hUo hK hM ?_
    · have e : ∀ i, (F.Q i).idx j = (((F.Q i).T.lev j (d i) (hd i)).J).relIndex (GlobalTheory.SplitWeil.KO (F.Q i).k _) :=
        fun i => (F.Q i).idx_mid j (d i) (hd i)
      simp only [e]
      exact key
    · intro g
      rw [hU' g]
      refine and_congr_right fun _ => forall_congr' fun i => ⟨fun h x hx => h (d i) (hd i) x hx, fun h d' hd' x hx => ?_⟩
      obtain rfl : d' = d i := by have := hd i; omega
      exact h x hx
  · rw [hQ] at hK hM
    have key := GlobalTheory.LevIdx.core c.T v.NT hN (fun i => (F.Q i).k) (fun i => (F.Q i).q) (fun i => (F.Q i).Z)
      (fun i => (F.Q i).FT) hP.inj (fun i => (F.Q i).latT)
      (fun i => (F.Q i).T.levTop.J) (fun i => (F.Q i).leT) hTo μ U U' b hb hU hUc hUo hK hM hU'
    have e : ∀ i, (F.Q i).idx D.R.m = ((F.Q i).T.levTop.J).relIndex (GlobalTheory.SplitWeil.KO (F.Q i).k _) :=
      fun i => by rw [← hs i]; exact (F.Q i).idx_top
    simp only [e]
    exact key

end
end

