module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankFacGen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

noncomputable section
namespace GlobalTheory.TowerCT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vol : ∀ (D : D7) (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → κ 𝓝 ≠ ⊤ := by
  intro D V r C hC κ 𝓝 hκ h𝓝
  have hint : IntegrableOn (fun _ : NI V C => (1 : ℂ)) 𝓝 κ := by
    have key : ∀ N : Subgroup (GA D V),
        N = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) (GlobalTheory.AutFunCompare.colSpan V C) →
        ∀ Q : Subgroup (GA D V), Q = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ratPts D.sp.cm V →
        ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μ →
          IntegrableOn (fun _ : N => (1 : ℂ)) 𝓕 μ := by
      rintro N rfl Q rfl μ 𝓕 hμ h𝓕
      exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V _ ((GlobalTheory.AutFunCompare.isIsoFrame_iff V C).1 hC).2
        (fun _ => 1) continuous_const (fun _ _ _ => rfl) μ hμ 𝓕 h𝓕 1
    exact key _ (GlobalTheory.AutFunCompare.NI_eq V C) _ (GlobalTheory.AutFunCompare.GQ_eq V) κ 𝓝 hκ h𝓝
  rcases (integrableOn_const_iff (C := (1 : ℂ))).1 hint with h | h
  · exact absurd h (by simp)
  · exact h.ne

theorem cusp : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L →
    ∀ (ν : Measure (GA D W)), ν.IsHaarMeasure → ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → IsCuspFun W F →
    ∀ Γ : Subgroup (GA D W), Γ ≤ GQ W → (∀ γ ∈ Γ, ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) →
    (∀ n ∈ NI W L, n ∈ GQ W → n ∈ Γ) → ∀ K : GA D W → ℂ, Measurable K → (∀ n ∈ NI W L, ∀ h, K (n * h) = K h) →
    (∀ γ ∈ Γ, ∀ h, K (γ * h) = K h) → ∀ 𝓖 : Set (GA D W), IsFundamentalDomain Γ 𝓖 ν →
    IntegrableOn (fun h => K h * F h) 𝓖 ν → ∫ h in 𝓖, K h * F h ∂ν = 0 := by
  intro D W s L hL ν hν F hF hcusp Γ hle hnorm hin K hKm hKn hKγ 𝓖 h𝓖 hint
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hcl := GlobalTheory.CuspDecay.Model.isClosed_NI W hL
  have : LocallyCompactSpace (NI W L) := hcl.locallyCompactSpace
  have hQ : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig W.gram
  let i : NIQ W L → GQ W := fun x => ⟨x.1.1, x.2⟩
  have hi : Function.Injective i := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ W => z.1) h))
  have : DiscreteTopology (NIQ W L) := DiscreteTopology.of_continuous_injective (f := i)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hi
  have : Countable (NIQ W L) := hi.countable
  have : SecondCountableTopology (NI W L) := TopologicalSpace.Subtype.secondCountableTopology _
  let κ : Measure (NI W L) := Measure.haar
  obtain ⟨𝓝, h𝓝⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (NIQ W L) κ
  have hκ : κ.IsHaarMeasure := inferInstance
  have hΓ : Countable Γ := (Subgroup.inclusion_injective hle).countable
  have e : Γ.subgroupOf (NI W L) = NIQ W L := by
    ext n
    exact ⟨fun h => hle h, fun h => hin _ n.2 h⟩
  have h𝓝' : IsFundamentalDomain (Γ.subgroupOf (NI W L)) 𝓝 κ := by
    rw [e]
    exact h𝓝
  exact _root_.GlobalTheory.UnfoldNormal.unfold_zero_mean (GA D W) ν Γ (NI W L) hΓ hcl hnorm κ 𝓝 hκ h𝓝' (vol D W s L hL κ 𝓝 hκ h𝓝) K F hKm
    hF.2.1.measurable hKn hKγ (fun γ hγ h => hF.1 γ (hle hγ) h) (fun h => hcusp s L hL κ 𝓝 hκ h𝓝 h) 𝓖 h𝓖 hint

theorem rankFacGen {K : Type} [Field K] {a b : ℕ} (y : Matrix (Fin a) (Fin b) K) (hy : y ≠ 0) :
    ∃ (s : ℕ) (L : Matrix (Fin a) (Fin s) K) (m : Matrix (Fin s) (Fin b) K) (m' : Matrix (Fin b) (Fin s) K),
      0 < s ∧ LinearIndependent K L.transpose ∧ m.rank = s ∧ m * m' = 1 ∧ y = L * m := by
  classical
  let U : Submodule K (Fin a → K) := Submodule.span K (Set.range y.transpose)
  let s := Module.finrank K U
  let bs : Module.Basis (Fin s) K U := Module.finBasisOfFinrankEq K U rfl
  have hcol : ∀ j, y.transpose j ∈ U := fun j => Submodule.subset_span ⟨j, rfl⟩
  let L : Matrix (Fin a) (Fin s) K := Matrix.of fun i k => (bs k : Fin a → K) i
  let m : Matrix (Fin s) (Fin b) K := Matrix.of fun k j => bs.repr ⟨y.transpose j, hcol j⟩ k
  have hym : y = L * m := by
    ext i j
    have h := bs.sum_repr ⟨y.transpose j, hcol j⟩
    have h2 := congrArg (fun u : U => (u : Fin a → K) i) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    simp only [Matrix.mul_apply, L, m, Matrix.of_apply]
    rw [show y i j = y.transpose j i from rfl, ← h2]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hLi : LinearIndependent K L.transpose := by
    have : LinearIndependent K fun k => (bs k : Fin a → K) := bs.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    exact this
  have hrk : y.rank = s := by
    rw [Matrix.rank_eq_finrank_span_cols]
    rfl
  have hs : 0 < s := by
    refine Nat.pos_of_ne_zero fun h => hy ?_
    have hU : U = ⊥ := Submodule.finrank_eq_zero.1 h
    ext i j
    have := hcol j
    rw [hU, Submodule.mem_bot] at this
    exact congrFun this i
  have hle : s ≤ m.rank := by
    calc s = y.rank := hrk.symm
      _ = (L * m).rank := by rw [← hym]
      _ ≤ m.rank := Matrix.rank_mul_le_right _ _
  have hm : m.rank = s := le_antisymm ((Matrix.rank_le_height m)) hle
  have hsurj : Function.Surjective m.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have : Module.finrank K (LinearMap.range m.mulVecLin) = s := hm
    simpa using this
  obtain ⟨g, hg⟩ := m.mulVecLin.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  refine ⟨s, L, m, LinearMap.toMatrix' g, hs, hLi, hm, ?_, hym⟩
  have : Matrix.toLin' (m * LinearMap.toMatrix' g) = LinearMap.id := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    exact hg
  apply Matrix.toLin'.injective
  rw [this, Matrix.toLin'_one]

theorem rankFac : ∀ (D : D7) (W : HSp D) (r : ℕ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), y ≠ 0 →
    adj D y * W.gram * y = 0 → ∃ (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E) (m : Matrix (Fin s) (Fin r) D.host.E)
      (m' : Matrix (Fin r) (Fin s) D.host.E), IsIsoFrame W L ∧ m.rank = s ∧ m * m' = 1 ∧ y = L * m := by
  intro D W r y hy hiso
  obtain ⟨s, L, m, m', hs, hL, hm, hmm, e⟩ := rankFacGen y hy
  refine ⟨s, L, m, m', ⟨hs, hL, ?_⟩, hm, hmm, e⟩
  have hLy : L = y * m' := by rw [e, Matrix.mul_assoc, hmm, Matrix.mul_one]
  have hc : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) L = adj D m' * adj D y := by
    rw [hLy]
    simp only [adj, Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  rw [hc]
  calc adj D m' * adj D y * W.gram * L = adj D m' * (adj D y * W.gram * y) * m' := by
        rw [hLy]
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hiso, Matrix.mul_zero, Matrix.zero_mul]

theorem fub {N H Y : Type} [MeasurableSpace N] [MeasurableSpace H] [Countable Y]
    (κ : Measure N) (ν : Measure H) [SFinite κ] [SFinite ν] (𝓝 : Set N) (𝓕 : Set H)
    (T : Y → N → H → ℂ) (hT : ∀ y, Measurable (Function.uncurry (T y))) (Θ : N → H → ℂ)
    (F : H → ℂ) (hF : Measurable F) (hs : ∀ n h, HasSum (fun y => T y n h) (Θ n h))
    (hb : ∫⁻ n in 𝓝, ∫⁻ h in 𝓕, (∑' y, ‖T y n h‖ₑ) * ‖F h‖ₑ ∂ν ∂κ ≠ ⊤) :
    IntegrableOn (fun n => ∫ h in 𝓕, Θ n h * F h ∂ν) 𝓝 κ ∧
    (∑' y, ∫⁻ h in 𝓕, ‖(∫ n in 𝓝, T y n h ∂κ) * F h‖ₑ ∂ν) ≠ ⊤ ∧
    HasSum (fun y => ∫ h in 𝓕, (∫ n in 𝓝, T y n h ∂κ) * F h ∂ν)
      (∫ n in 𝓝, ∫ h in 𝓕, Θ n h * F h ∂ν ∂κ) := by
  set P := (κ.restrict 𝓝).prod (ν.restrict 𝓕) with hP
  let G : Y → N × H → ℂ := fun y p => T y p.1 p.2 * F p.2
  have hGm : ∀ y, Measurable (G y) := fun y => (hT y).mul (hF.comp measurable_snd)
  have hGe : ∀ y, Measurable fun p => ‖G y p‖ₑ := fun y => (hGm y).enorm
  have hlin : ∫⁻ p, ∑' y, ‖G y p‖ₑ ∂P ≠ ⊤ := by
    rw [hP, lintegral_prod _ (Measurable.tsum hGe).aemeasurable]
    convert hb using 6 with n _ h
    simp only [G, enorm_mul]
    rw [ENNReal.tsum_mul_right]
  have hsum : ∑' y, ∫⁻ p, ‖G y p‖ₑ ∂P ≠ ⊤ := by
    rwa [← lintegral_tsum fun y => (hGe y).aemeasurable]
  have hfin : ∀ y, ∫⁻ p, ‖G y p‖ₑ ∂P ≠ ⊤ := fun y => ENNReal.ne_top_of_tsum_ne_top hsum y
  have hGi : ∀ y, Integrable (G y) P := fun y =>
    ⟨(hGm y).aestronglyMeasurable, lt_top_iff_ne_top.2 (hfin y)⟩
  have hsp : ∀ p : N × H, HasSum (fun y => G y p) (Θ p.1 p.2 * F p.2) := fun p => (hs p.1 p.2).mul_right _
  have hΘm : Measurable fun p : N × H => Θ p.1 p.2 * F p.2 :=
    measurable_of_tendsto_metrizable' Filter.atTop (f := fun (s : Finset Y) p => ∑ y ∈ s, G y p)
      (fun s => Finset.measurable_sum _ fun y _ => hGm y) (tendsto_pi_nhds.2 hsp)
  have hle : ∀ p : N × H, ‖Θ p.1 p.2 * F p.2‖ₑ ≤ ∑' y, ‖G y p‖ₑ := fun p =>
    le_of_tendsto' ((continuous_enorm.tendsto _).comp (hsp p)) fun s =>
      (enorm_sum_le s _).trans (ENNReal.sum_le_tsum s)
  have hΘi : Integrable (fun p : N × H => Θ p.1 p.2 * F p.2) P :=
    ⟨hΘm.aestronglyMeasurable, ((lintegral_mono hle).trans_lt (lt_top_iff_ne_top.2 hlin))⟩
  have hnorm : Summable fun y => ∫ p, ‖G y p‖ ∂P := by
    have e : ∀ y, ∫ p, ‖G y p‖ ∂P = (∫⁻ p, ‖G y p‖ₑ ∂P).toReal := fun y => by
      rw [integral_norm_eq_lintegral_enorm (hGm y).aestronglyMeasurable]
    simp only [e]
    exact ENNReal.summable_toReal hsum
  have hS := hasSum_integral_of_summable_integral_norm hGi hnorm
  have eT : (fun p => ∑' y, G y p) = fun p : N × H => Θ p.1 p.2 * F p.2 := funext fun p => (hsp p).tsum_eq
  rw [eT, hP, integral_prod _ (by rw [← hP]; exact hΘi)] at hS
  refine ⟨hΘi.integral_prod_left, ?_, ?_⟩
  · refine ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun y => ?_)
    rw [hP, lintegral_prod_symm _ (hGe y).aemeasurable]
    refine lintegral_mono fun h => ?_
    simp only [G, enorm_mul]
    rw [lintegral_mul_const _ ((hT y).of_uncurry_right.enorm)]
    exact mul_le_mul' (enorm_integral_le_lintegral_enorm _) le_rfl
  · have e : (fun y => ∫ h in 𝓕, (∫ n in 𝓝, T y n h ∂κ) * F h ∂ν) =
        fun y => ∫ p, G y p ∂(κ.restrict 𝓝).prod (ν.restrict 𝓕) := funext fun y => by
      rw [integral_prod_symm _ (by rw [← hP]; exact hGi y)]
      refine integral_congr_ae (.of_forall fun h => ?_)
      simp only [G]
      rw [integral_mul_const]
    rw [e]
    exact hS

end GlobalTheory.TowerCT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointIdentificationLeastSizeLinearGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.IotaNorm

theorem iota_norm_of_eq {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) :
    (∀ g ∈ GinfC (D.sp.Y 0), ((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm) g).2 = 1) ∧
    (1 ≤ (D.sp.Y 0).rank → ∀ x : I.GA, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GinfC (D.sp.Y 0),
      (GlobalTheory.Count.tau1 I (x * (Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm) g))⁻¹ ≤
        C * normInf θ (D.sp.Y 0) g) := by
  subst h
  set ι := (Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm) with hιdef
  have key : ∀ k, (∀ v, Formalism.MainNotions.S.uMat ((ι k).1 v) = Formalism.L2.SG.AdBridge.ofHAInf (Formalism.L2.SG.InstExistsPf.instOf D) k v) ∧ (Formalism.L2.SG.InstExistsPf.instOf D).fmat (ι k).2 = Formalism.L2.SG.AdBridge.ofHAFin _ k := by
    intro k
    have := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D k)
    have e := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply k
    exact ⟨fun v => (this.1 v).trans (congrArg (fun z => Formalism.L2.SG.AdBridge.ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) z v) e),
      this.2.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin (Formalism.IndefR.RationalEmbedding.inst D)) e)⟩
  have hinf : ∀ k v, Formalism.MainNotions.S.uMat ((ι k).1 v) = ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ *
      Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J (θ ((Formalism.L2.Host.tauPl D).symm v)) k *
      (Formalism.L2.SG.InstExistsPf.instOf D).P v := fun k v =>
    ((key k).1 v).trans (congrArg (fun M => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M * (Formalism.L2.SG.InstExistsPf.instOf D).P v)
      (GlobalTheory.IotaReal.map_thetaV_gen (Formalism.L2.SG.InstExistsPf.instOf D) v (θ ((Formalism.L2.Host.tauPl D).symm v)) (hθ _) k))
  have hfin : ∀ g ∈ GinfC (D.sp.Y 0), (ι g).2 = 1 := by
    intro g hg
    apply Subtype.ext
    apply Units.ext
    refine (key g).2.trans (GlobalTheory.IotaReal.ofHAFin_eq_one _ _ ?_)
    have e3 : (finHom (D.sp.Y 0) g).val = 1 := by
      rw [show finHom (D.sp.Y 0) g = 1 from hg]; rfl
    ext i j
    exact congrFun (congrFun e3 i) j
  refine ⟨hfin, fun hn x => ?_⟩
  choose c hc0 hc using fun v => GlobalTheory.TauNorm.exp_dOp_le ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ ((Formalism.L2.SG.InstExistsPf.instOf D).P v)
  have hC : 0 ≤ ∑ v, c v := Finset.sum_nonneg fun v _ => hc0 v
  have hn' : 1 ≤ (Formalism.L2.SG.InstExistsPf.instOf D).n := hn
  have hp : 0 ≤ (GlobalTheory.Count.tau1 (Formalism.L2.SG.InstExistsPf.instOf D) x)⁻¹ :=
    inv_nonneg.2 ((GlobalTheory.TauLipschitz.tauLip (Formalism.L2.SG.InstExistsPf.instOf D) hn').1 _).le
  refine ⟨(GlobalTheory.Count.tau1 (Formalism.L2.SG.InstExistsPf.instOf D) x)⁻¹ * ∑ v, c v, mul_nonneg hp hC, fun g hg => ?_⟩
  have hv : ∀ v, Real.exp (GlobalTheory.Count.dOp (Formalism.MainNotions.S.uMat ((ι g).1 v))) ≤ (∑ v, c v) * normInf θ (D.sp.Y 0) g := by
    intro v
    have h0 := GlobalTheory.TauNorm.uMat_ne_zero (Formalism.L2.SG.InstExistsPf.instOf D) hn' (ι g) v
    rw [hinf g v] at h0 ⊢
    have h2 := hc v _ h0
    have h3 : c v ≤ ∑ v, c v := Finset.single_le_sum (fun v _ => hc0 v) (Finset.mem_univ _)
    exact h2.trans (mul_le_mul h3 (GlobalTheory.TauNorm.sum_le_normInf θ g ((Formalism.L2.Host.tauPl D).symm v))
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hC)
  have hh := GlobalTheory.TauNorm.inv_tau_mul_le (Formalism.L2.SG.InstExistsPf.instOf D) hn' x (ι g) (hfin g hg) _ hv
  rw [← mul_assoc] at hh
  exact hh

theorem iotaX_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ g ∈ GinfC (D.sp.Y 0), (iotaX X h g).2 = 1) ∧ (1 ≤ (D.sp.Y 0).rank → ∀ x : X.B.I.GA, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GinfC (D.sp.Y 0), (GlobalTheory.Count.tau1 X.B.I (x * iotaX X h g))⁻¹ ≤ C * normInf R.θ (D.sp.Y 0) g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ hMod _
  exact iota_norm_of_eq R.θ hMod.inf X.B.I h

end GlobalTheory.IotaNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionTrivialOfConjugatePlaceSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjPlaceRedGen


set_option maxHeartbeats 1000000 in
theorem redFn_eq_one_of_conj : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank), IsSelfDualC V L → ∀ β : GL (Fin V.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, Lev.finE V k ∈ Formalism.L2.DIV.St β → ∀ (PP PP' : Formalism.L2.DIV.Pl D.host.E), Formalism.IndefR.Lev.IsConjPl PP' PP → Formalism.L2.DIV.redFn β PP' (Lev.finE V k) = 1 → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  intro D V L hsd β hβ k hk PP PP' hc h1
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D V L hsd
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) V.gram β _ hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd
  obtain ⟨h, hh⟩ := hk
  have hU : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ ∈
      Formalism.UG.UJ (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        (V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) := by
    have e : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ = Lev.finE V k := hh
    rw [e]
    exact GlobalTheory.LevSplit.finE_mem_UA V k
  have key := GlobalTheory.FrameMove.conj_gram_sub (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (Formalism.L2.Herm.intAf D.host.F D.host.E) _ β G h hG hU
  rw [← hh, Formalism.L2.DIV.redFn_frGL] at h1 ⊢
  have h1' : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP') h⁻¹ = 1 := by rw [map_inv, h1, inv_one]
  have h2 : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (G * h * G⁻¹) = 1 := by
    apply Units.ext
    ext i j
    have hz : Formalism.L2.DIV.resS D.host.F PP' ((h⁻¹).val j i) = if j = i then 1 else 0 := by
      have e : ((Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP') h⁻¹ : GL (Fin V.rank) (Formalism.L2.DIV.kP PP')) : Matrix _ _ (Formalism.L2.DIV.kP PP')) j i =
          Formalism.L2.DIV.resS D.host.F PP' ((h⁻¹).val j i) := rfl
      rw [← e, h1', Units.val_one, Matrix.one_apply]
    have h0 := GlobalTheory.ConjPlaceRed.resS_conj_ite D.sp.cm.sig PP' PP hc _ _ (key i j) (j = i) hz
    refine h0.trans ?_
    rw [Units.val_one, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  rw [map_mul, map_mul, map_inv] at h2
  exact _root_.conj_eq_one_iff.1 h2

end GlobalTheory.ConjPlaceRedGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReframeVacuumAndLiftVector
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ReVec

theorem L_lat : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (LT : Set (Fin T.rank → D.host.E)) (u : WO (reS S b) T), u ∈ latO (reS S b) T (L0c D (reS S b)) LT (fun _ => True) ↔ reW S T b u ∈ latO S T (L0c D S) LT (fun _ => True) := _root_.GlobalTheory.AdSpan.ReVec.latO_reW_iff

theorem L_sympl : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x y : WO (reS S b) T), symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y) := _root_.GlobalTheory.AdSpan.ReVec.Sympl.symplO_reW

theorem L_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ (reS S b) T (reF S T b f) := _root_.GlobalTheory.AdSpan.ReVec.ThetaCarry.isThetaFunO_reF

theorem L_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), IsInfFam θ → (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ (τ : D.what₂.Tau) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 sT) f → IsFockVacAt (heisO ψ (reS S b) T) θ τ (cplxO 1 sT) (reF S T b f) := _root_.GlobalTheory.AdSpan.ReVec.FockVac.isFockVacAt_reF

theorem L_norm : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ), AllSome (fun p : Measure (WO S T) × Set (WO S T) => IsCovolOne (ratL T S) p.1 p.2) (fun p => nrm2 p.1 p.2 f = 1) → AllSome (fun p : Measure (WO (reS S b) T) × Set (WO (reS S b) T) => IsCovolOne (ratL T (reS S b)) p.1 p.2) (fun p => nrm2 p.1 p.2 (reF S T b f) = 1) := _root_.GlobalTheory.AdSpan.ReVec.reframeFunctionOnHoms_norm_one_covolumeOne

theorem L_thetaAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (e : AE D) (Λ : AddSubgroup (WO S T)) (Λ' : AddSubgroup (WO (reS S b) T)) (c : ℂ) (f₀ Φ f : WO S T → ℂ), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → (∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → IsThetaAt ψ (symplO (reS S b) T) (heisO ψ (reS S b) T) e Λ' c (reF S T b f₀) (fun x => Φ (reW S T b x)) (reF S T b f) := _root_.GlobalTheory.ThetaAtReframe.isThetaAt_reframe

theorem L_frMap : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO (reS S b) T), frMapAdj (reS S b) T (frPinvGL S b * βS) βT x = frMapAdj S T βS βT (reW S T b x) := _root_.GlobalTheory.AdSpan.ReVec.FrMap.frMapAdj_reS

theorem L_frame : ∀ (D : D7) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), StdFrame.OrthFrame (reS S b) → (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame (frPinvGL S b * βS) (stdL D.host.E (reS S b).rank) := _root_.GlobalTheory.AdSpan.ReVec.isFrame_frPinvGL_mul

theorem pi_eq_stdL' (E : Type) [Field E] [NumberField E] (n : ℕ) :
    (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) = stdL E n := by
  apply le_antisymm
  · intro x hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx a trivial)
    have : (Pi.single a (x a) : Fin n → E) = b • (Pi.single a 1 : Fin n → E) := by
      rw [← Pi.single_smul, ← hb, Algebra.smul_def, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩ j -
    by_cases h : j = a
    · subst h
      exact Submodule.mem_one.2 ⟨1, by simp⟩
    · simp [h]

theorem L_std : ∀ (D : D7) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), StdFrame.OrthFrame (reS S b) → L0c D (reS S b) = (stdL D.host.E (reS S b).rank : Set (Fin (reS S b).rank → D.host.E)) := by
  intro D S b hO
  ext x
  rw [SetLike.mem_coe, ← pi_eq_stdL', Submodule.mem_pi]
  exact (hO.mem_iff x).trans ⟨fun k a _ => k a, fun k a => k a trivial⟩

theorem reframe_thPVecOf : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), StdFrame.OrthFrame (reS S b) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Lt D.host.E S.rank) (ΛT : Set (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → Formalism.L2.DIV.IsFrame βS ΛS → IsThPVecOf ψ θ S T (fun _ => 1) sT (ΛS : Set (Fin S.rank → D.host.E)) ΛT βS βT Pg Q ξ f₀ f → ∃ βS' : GL (Fin (reS S b).rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame βS' (stdL D.host.E (reS S b).rank) ∧ IsThPVecOf ψ θ (reS S b) T (fun _ => 1) sT (stdL D.host.E (reS S b).rank : Set (Fin (reS S b).rank → D.host.E)) ΛT βS' βT Pg Q ξ (reF S T b f₀) (reF S T b f) := by
  intro D S T b hO ψ θ sT ΛS ΛT βS βT Pg Q ξ f₀ f hΛ hfr hv
  have hL := L_std D S b hO
  refine ⟨frPinvGL S b * βS, L_frame D S b βS ΛS hO hΛ hfr, ?_⟩
  rw [← hL]
  rw [hΛ] at hv
  obtain ⟨⟨hstd, hvac⟩, e, he, hth⟩ := hv
  have hs := L_sympl D S T b
  have hlat := L_lat D S T b ΛT
  refine ⟨⟨hstd, ?_⟩, e, he, ?_⟩
  · exact
      { inf := hvac.inf
        theta := L_theta D ψ S T b hs f₀ hvac.theta
        lat := ⟨fun u hu => by
            rw [heisO_reF S T b ψ hs, reW_nsmul, hvac.lat.1 _ ((hlat u).1 hu)],
          fun e' he' u hu hh => by
            rw [heisO_reF S T b ψ hs, hvac.lat.2 e' he' _ ((hlat u).1 hu) ((isHalf_reW_iff S T b e' u).2 hh)]⟩
        fock := fun τ => L_fock D ψ θ S T b hvac.inf hs τ (sT τ) f₀ (hvac.fock τ)
        norm := L_norm D S T b f₀ hvac.norm }
  · refine (congrArg (fun Φ => IsThetaAt ψ (symplO (reS S b) T) (heisO ψ (reS S b) T) (cA D e)
      (latO (reS S b) T (L0c D (reS S b)) ΛT fun _ => True) 1 (reF S T b f₀) Φ (reF S T b f)) ?_).mpr
      (L_thetaAt D ψ S T b (cA D e) _ _ 1 f₀ _ f hs hlat hth)
    funext x
    simp only [L_frMap D S T b βS βT x]
    rw [isHalf_reW_iff S T b (cA D e) x]
    exact if_congr Iff.rfl rfl rfl

end GlobalTheory.AdSpan.ReVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesLeftMulUnitaryKUInvarianStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_integralMatrices_leftMul_unitary_KU_invariant : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (c : L →+* L) (r n : ℕ) (t k₁ k₂ : GU c r), k₁ ∈ KU c r → k₂ ∈ KU c r → (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (k₁ * t * k₂).1.1)) = (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul t.1.1)) := by
  first | exact @GlobalTheory.InertHomIdx.relIndex_intMat_lmul_KU | exact GlobalTheory.InertHomIdx.relIndex_intMat_lmul_KU | (intros; apply GlobalTheory.InertHomIdx.relIndex_intMat_lmul_KU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexUniformizerPowMulIntegersEqSqPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_uniformizer_pow_mul_integers_eq_sq_pow : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ), IsUnramInv ϖ c q → ∀ e : ℕ, ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ e))).relIndex (Formalism.UG.intL L).toAddSubgroup = (q ^ 2) ^ e := by
  first | exact @GlobalTheory.UnramIntIndex.relIndex_mul_uniformizer_pow | exact GlobalTheory.UnramIntIndex.relIndex_mul_uniformizer_pow | (intros; apply GlobalTheory.UnramIntIndex.relIndex_mul_uniformizer_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsEqCoverDiscreteSeries
section
open Formalism.BasicNotions

namespace GlobalTheory

theorem modelsAreCoverSeries_of_hypotheses :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
      ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D :=
  _root_.GlobalTheory.CoverModel.modelsAreCoverSeries_all

end GlobalTheory
end

