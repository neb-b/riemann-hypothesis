module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0087
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeSheet
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesLiftPointStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_frames_lift_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), z₁ ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z₁ ∘ Cv.v)) → M'.IsFlagOf F' z₁ h → M.IsFlagOf F z₀ (fun τ => Cv.trans F' F (basePart M'.blk z₁) τ * h τ) → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → M.blk p = some k → ∃ (e : Φ') (s : ι k → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ m, transPt Cv ⟨k, m⟩ = e * s m ∧ IsValueAt y' (s m) z₁ (t * z₀ ⟨k, m⟩) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z₁ z₀ F' F h p k hz₁ hF' hF hG' hG hfl' hfl horb hp
  set zb := basePart M'.blk z₁ with hzbdef
  have hzb : zb ∈ mcPts (mCoordIdeal M'.x) := (_root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K' ι' Φ' y' Ψ N j M').1 z₁ hz₁
  have hzv := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.comp_v_mem_mcPts K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb hzb
  have hstep : IsProperStep N j p.2 := by
    by_contra hn
    rw [(M.blk_none p).2 hn] at hp
    exact absurd hp (by simp)
  obtain ⟨k', hk'⟩ : ∃ k', M'.blk p = some k' :=
    Option.ne_none_iff_exists'.1 fun e => (M'.blk_none p).1 e hstep
  obtain ⟨c', hc'⟩ := hz₁.1 k'
  obtain ⟨hy0, hratio⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_coord_ratio K' ι' Φ' y' z₁ k' c' hz₁ hc'
  have ch' : ∀ k, M'.x ⟨k, F'.c k⟩ ≠ 0 := fun k => coord_ne hzb (hG'.1 k)
  have ch : ∀ k, M.x ⟨k, F.c k⟩ ≠ 0 := fun k => coord_ne hzv (hG.1 k)
  obtain ⟨c, hc0, htr⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr.transPt_eq_smul_sum K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv F' F hF' hF ch' ch p k k' hp hk'
  obtain ⟨a', ha', hz1⟩ := hfl'.2.2 p k' hk'
  obtain ⟨a, ha, hz0⟩ := hfl.2.2 p k hp
  have hcoeff (q : Σ k, ι k) (r : Σ k, ι' k) :
      RegAt M'.x (mCoordIdeal zb) (coE Cv F' F p q r) ∧
        valAt M'.x (coE Cv F' F p q r) zb =
          ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
            valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' *
              valAt M'.x (F'.u' I' r) zb := by
    have hT : ∀ a b, RegAt M'.x (mCoordIdeal zb) (trMat Cv F' F p.1 a b) := fun a b =>
      (Cv.agree zb hzb F' F hF' hF hG' hG p.1 a b).1
    have hminor := CovMap.LocImg.reg_minor hzb hT
    have hxv : M'.x ∘ Cv.v = Cv.φ ∘ M.x := funext Cv.x_eq
    have hu (I : Finset (Fin N)) :
        RegAt M'.x (mCoordIdeal zb) (Cv.φ (F.u q I)) ∧
          valAt M'.x (Cv.φ (F.u q I)) zb = valAt M.x (F.u q I) (zb ∘ Cv.v) := by
      obtain ⟨d, g, h, hg, hh, hn, he⟩ := (hG.2.1 q I).1
      have hg' := RegPhi.isMultiHomog_rename_block Cv.block hg
      have hh' := RegPhi.isMultiHomog_rename_block Cv.block hh
      have hn' := RegPhi.rename_notMem Cv.block hn
      have hae (f : MRing (baseIdx ι M.blk)) :
          aeval M'.x (rename Cv.v f) = Cv.φ (aeval M.x f) := by
        rw [aeval_rename, hxv, RegPhi.aeval_comp_ringHom]
      have he' : aeval M'.x (rename Cv.v g) = Cv.φ (F.u q I) * aeval M'.x (rename Cv.v h) := by
        rw [hae, hae, he, map_mul]
      refine ⟨⟨_, _, _, hg', hh', hn', he'⟩, ?_⟩
      let value := eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) g) /
        eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h)
      have hv : IsValueAt M.x (F.u q I) (zb ∘ Cv.v) value :=
        ⟨d, g, h, hg, hh, ValRing.aeval_ne_zero_of_notMem hzv hh hn, he,
          ValRing.eval_ne_zero_of_notMem hh hn, rfl⟩
      have hv' : IsValueAt M'.x (Cv.φ (F.u q I)) zb value := by
        refine ⟨_, _, _, hg', hh', ValRing.aeval_ne_zero_of_notMem hzb hh' hn', he',
          ValRing.eval_ne_zero_of_notMem hh' hn', ?_⟩
        rw [RegPhi.eval_rename_block, RegPhi.eval_rename_block]
      exact (valAt_eq hzb hv').trans (valAt_eq hzv hv).symm
    have hterm (I I' : Finset (Fin N)) :
        RegAt M'.x (mCoordIdeal zb) (Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r) ∧
          valAt M'.x (Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r) zb =
            valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' *
              valAt M'.x (F'.u' I' r) zb := by
      obtain ⟨hreg, hval⟩ := CovMap.LocImg.reg_mul hzb (hu I).1 (hminor I I').1
      obtain ⟨hreg', hval'⟩ := CovMap.LocImg.reg_mul hzb hreg (hG'.2.1 r I').2
      refine ⟨hreg', hval'.trans ?_⟩
      rw [hval, (hu I).2, (hminor I I').2]
      rfl
    have hin (I : Finset (Fin N)) := CovMap.LocImg.reg_sum hzb
      (Finset.univ.filter (IsStepRows N j p.2)) _ (fun I' _ => (hterm I I').1)
    have hout := CovMap.LocImg.reg_sum hzb Finset.univ _ (fun I _ => (hin I).1)
    refine ⟨hout.1, hout.2.trans (Finset.sum_congr rfl fun I _ => ?_)⟩
    rw [(hin I).2]
    exact Finset.sum_congr rfl fun I' _ => (hterm I I').2
  have hE (m : ι k) (m' : ι' k') := hcoeff ⟨k, m⟩ ⟨k', m'⟩
  have hmin := _root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j p.2 M.j_le
  have hne : stepCols N j p.2 ≠ ∅ := stepCols_ne p.2 M.j_le
  obtain ⟨cc, hcc, horbE⟩ := horb
  have hval : ∀ s, valAt M.x s (basePart M.blk z₀) = valAt M.x s (zb ∘ Cv.v) := fun s => by
    rw [horbE]
    exact ((StepW.TorusAct.main _ _ _ M.x (zb ∘ Cv.v) cc hcc).2 hzv).2 s
  have hμ : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ (h p.1) I (stepCols N j p.2) = 0 := fun I hI =>
    (hmin.2.1 (h p.1) I (hfl'.2.1 p.1).1 hI).resolve_right hne
  have isValueAt_valAt (s : M'.Ω) (hs : RegAt M'.x (mCoordIdeal zb) s) :
      IsValueAt M'.x s zb (valAt M'.x s zb) := by
    obtain ⟨v, hv⟩ := ValRing.exists_isValueAt hzb hs
    rwa [valAt_eq hzb hv]
  have valAt_sum_mul {α : Type} (S : Finset α) (f g : α → M'.Ω)
      (hf : ∀ i ∈ S, RegAt M'.x (mCoordIdeal zb) (f i))
      (hg : ∀ i ∈ S, RegAt M'.x (mCoordIdeal zb) (g i)) :
      valAt M'.x (∑ i ∈ S, f i * g i) zb = ∑ i ∈ S, valAt M'.x (f i) zb * valAt M'.x (g i) zb :=
    valAt_eq hzb (isValueAt_sum S _ _ fun i hi =>
      isValueAt_mul (isValueAt_valAt (f i) (hf i hi)) (isValueAt_valAt (g i) (hg i hi)))
  have hAB : ∀ I I', IsStepRows N j p.2 I → IsStepRows N j p.2 I' →
      ∑ m, valAt M'.x (F'.u' I ⟨k', m⟩) zb * valAt M'.x (F'.u ⟨k', m⟩ I') zb =
        if I = I' then 1 else 0 := fun I I' hI hI' => by
    rw [← valAt_sum_mul Finset.univ _ _ (fun m _ => (hG'.2.1 ⟨k', m⟩ I).2)
      (fun m _ => (hG'.2.1 ⟨k', m⟩ I').1), hF'.2.2.1 p k' hk' I I' hI hI']
    have h3 := ValRing.regAt_valAt_ring _ _ _ M'.x zb hzb
    split_ifs
    · exact h3.2.2.2.1
    · exact h3.2.2.1
  have hread := read_minor (IsStepRows N j p.2) _ _ hAB _ hμ (fun m => z₁ ⟨k', m⟩) a' hz1
  have key : ∀ m, ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * z₁ ⟨k', m'⟩ =
      a' * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (zb ∘ Cv.v) *
        minorIJ (Cv.trans F' F zb p.1 * h p.1) I (stepCols N j p.2) := fun m => by
    simp only [fun m' => (hE m m').2, hmin.1]
    exact move_minor (IsStepRows N j p.2) _ (fun I => by simp) _ _ _ _ hμ _ a' hread
  have baseValue (s : M'.Ω) (hs : RegAt M'.x (mCoordIdeal zb) s) :
      IsValueAt y' (algebraMap M'.Ω Φ' s) z₁ (valAt M'.x s zb) := by
    obtain ⟨v, hv⟩ := GlobalTheory.CompanionTheory.Ar.PB.ValRing.exists_isValueAt hzb hs
    rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt_eq hzb hv]
    obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
    let f : (Σ k, baseIdx ι' M'.blk k) → (Σ k, ι' k) := fun q => ⟨q.1.1, q.2⟩
    have ha : ∀ p : MRing (baseIdx ι' M'.blk), aeval y' (rename f p) = algebraMap M'.Ω Φ' (aeval M'.x p) := fun p => by
      have e : y' ∘ f = algebraMap M'.Ω Φ' ∘ M'.x := funext M'.y_base
      rw [aeval_rename, e, aeval_algebraMap_apply]
    have hev : ∀ p : MRing (baseIdx ι' M'.blk), eval z₁ (map (Int.castRingHom ℂ) (rename f p)) =
        eval (basePart M'.blk z₁) (map (Int.castRingHom ℂ) p) := fun p => by
      rw [map_rename, eval_rename]
      rfl
    refine ⟨_, rename f g, rename f h, isMultiHomog_rename_base M'.blk hg, isMultiHomog_rename_base M'.blk hh, ?_, ?_, ?_, ?_⟩
    · rw [ha]
      exact (map_ne_zero _).2 hy
    · rw [ha, ha, heq, map_mul]
    · rw [hev]
      exact hz0
    · rw [hev, hev]
  refine ⟨c * y' ⟨k', c'⟩, fun m => ∑ m', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) *
    (y' ⟨k', m'⟩ / y' ⟨k', c'⟩), a' / (a * z₁ ⟨k', c'⟩), mul_ne_zero hc0 hy0,
    div_ne_zero ha' (mul_ne_zero ha hc'), fun m => ⟨?_, ?_⟩⟩
  · show transPt Cv ⟨k, m⟩ = c * y' ⟨k', c'⟩ * ∑ m', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) *
      (y' ⟨k', m'⟩ / y' ⟨k', c'⟩)
    rw [htr m, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    field_simp
  · have hv := isValueAt_sum Finset.univ
      (fun m' => algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * (y' ⟨k', m'⟩ / y' ⟨k', c'⟩))
      (fun m' => valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩))
      fun m' _ => isValueAt_mul (baseValue _ (hE m m').1) (hratio m')
    have e : ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩) =
        a' / (a * z₁ ⟨k', c'⟩) * z₀ ⟨k, m⟩ := by
      have e1 : ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩) =
          (z₁ ⟨k', c'⟩)⁻¹ * ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * z₁ ⟨k', m'⟩ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m' _ => by ring
      rw [e1, key m, hz0 m]
      simp only [hval]
      field_simp
    rw [← e]
    exact hv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralFibreSumChangeOfVariables
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

theorem integrable_mInt_fibreSum {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite)
    (hsm : ∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x))
    (hG : MIntegrable A Φ G) :
    Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x) ∧
      mInt A Φ G = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x := by
  classical
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hm : mInt A Φ G = integralWith A hne.some Φ G := by unfold mInt; rw [dite_eq_left hne]
  set Pt := hne.some with hPt
  set hj : Fin A.n → (Fin e → ℂ) → ℝ := fun j u =>
    Pt.χ j ((A.chart j).symm u) * G ((A.chart j).symm u) * locDens A Φ j u with hhj
  have hN : ∀ j, volume ((q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ ?_
    · intro u hu
      exact (hu.1.2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact measure_mono_null (Set.inter_subset_inter_left _ fun u (hu : u ∈ goodT A q j) => hu.1)
        (hS j)
  have hfinj : ∀ j, ∀ᵐ y, (goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN j)] with y hy
    rw [goodT_fibre_eq A q S hq j hy]
    exact ((hfin y).subset Set.inter_subset_right).image _
  have harea : ∀ j, Integrable (fibSum (goodT A q j) (q ∘ (A.chart j).symm) (hj j)) ∧
      ∫ u in goodT A q j, hj j u = ∫ y, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (hj j) y :=
    fun j => area_open (isOpen_goodT A q j) (fun u hu => hu.2)
      ((integrableOn_chart A Pt Φ G hG j).mono_set fun u hu => hu.1) (hfinj j)
  have hset : ∀ j, ∫ u in (A.chart j).target, hj j u = ∫ u in goodT A q j, hj j u := by
    intro j
    refine setIntegral_congr_set (ae_eq_set.mpr ⟨?_, ?_⟩)
    · exact measure_mono_null (target_diff_goodT_subset A q S hq j) (hS j)
    · rw [Set.sdiff_eq_empty.mpr fun u (hu : u ∈ goodT A q j) => hu.1]; exact measure_empty
  have hterm : ∀ j x, x ∈ (A.chart j).source → x ∉ S →
      hj j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) =
        Pt.χ j x * (G x * pushDens A Φ q x) := by
    intro j x hx hxS
    simp only [hhj, (A.chart j).left_inv hx]
    rw [mul_div_assoc, locDens_div_jacN A Φ q S hq hsm j hx hxS, mul_assoc]
  have hae := sum_fibSum_ae A q S hN hq hfin Pt hj (fun x => G x * pushDens A Φ q x) hterm
  refine ⟨(integrable_finsetSum Finset.univ fun j _ => (harea j).1).congr hae, ?_⟩
  rw [hm]
  unfold integralWith
  have hsum : ∑ j, ∫ u in (A.chart j).target, hj j u =
      ∫ y, ∑ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (hj j) y := by
    rw [integral_finsetSum _ fun j _ => (harea j).1]
    exact Finset.sum_congr rfl fun j _ => (hset j).trans (harea j).2
  exact hsum.trans (integral_congr_ae hae)

end GlobalTheory.CompanionTheory.Ar.Giv.Push
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberMetricChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tele

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem ptsIntegral_congr_on {e : ℕ} (P : Ideal (MRing J)) (φ : Fin e → ((Σ k, J k) → ℂ) → ℝ)
    {g g' : ((Σ k, J k) → ℂ) → ℝ} (h : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  have hs : ∀ (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w,
      sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ g' y w := by
    intro Ψ y w
    unfold sheetDensity
    by_cases hs : ∃ c, IsSheet P Ψ y w c
    · rw [dite_eq_left hs, dite_eq_left hs, h _ hs.choose_spec.2.self_of_nhds.2.1]
    · rw [dite_eq_right hs, dite_eq_right hs]
  unfold ptsIntegral ptsIntegralAt
  simp only [hs]

def logDiff (A B : HermLine J) (z : (Σ k, J k) → ℂ) : ℝ := by
  classical
  exact if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then Real.log (A.h z) - Real.log (B.h z) else 0

theorem cone_smul_iff (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    (∀ k, ∃ i, (fun p : (Σ k, J k) => c p.1 * z p) ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, hc, false_or]

theorem logDiff_smul {A B : HermLine J} (hab : B.a = A.a) (c : K → ℂ) (z : (Σ k, J k) → ℂ)
    (hc : ∀ k, c k ≠ 0) : logDiff A B (fun p => c p.1 * z p) = logDiff A B z := by
  unfold logDiff
  by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · rw [if_pos hz, if_pos ((cone_smul_iff c hc z).2 hz), A.smul c z hc, B.smul c z hc, hab]
    have hp : (∏ k, ‖c k‖ ^ A.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    rw [Real.log_mul hp (A.pos z hz).ne', Real.log_mul hp (B.pos z hz).ne']
    ring
  · rw [if_neg hz, if_neg fun h => hz ((cone_smul_iff c hc z).1 h)]

theorem logDiff_smooth {A B : HermLine J} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.SmoothFn (logDiff A B) := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.log (A.h z) - Real.log (B.h z))
      {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (ContDiffOn.log hA fun z hz => (A.pos z hz).ne').sub
      (ContDiffOn.log hB fun z hz => (B.pos z hz).ne')
  refine h1.congr fun z hz => ?_
  unfold logDiff
  exact if_pos hz

theorem step (hLoc : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement)
    (I : Ideal (MRing J) → (n : ℕ) → (Fin n → HermLine J) → ℝ) (hI : IsIntersectionFamily I)
    (P : Ideal (MRing J)) (n : ℕ) (L : Fin n → HermLine J) (A B : HermLine J)
    (hP : IsArithVar P (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hB : IsSmoothHerm B) (hab : B.a = A.a) :
    I P (n + 1) (Fin.snoc L B) = I P (n + 1) (Fin.snoc L A) -
      ptsIntegral P (pot L) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
  have hu := fun (c : K → ℂ) z (hc : ∀ k, c k ≠ 0) => logDiff_smul (A := A) (B := B) hab c z hc
  have hus := logDiff_smooth hA hB
  have hch := metricChange K J I hI P n L A (logDiff A B) hu hP hL hA hus
  set T := A.tensor (HermLine.ofWeight (logDiff A B) hu) with hT
  have hTh : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → T.h z = B.h z := by
    intro z hz
    have e : T.h z = A.h z * Real.exp (-logDiff A B z) := rfl
    rw [e]
    unfold logDiff
    rw [if_pos hz, neg_sub, Real.exp_sub, Real.exp_log (B.pos z hz), Real.exp_log (A.pos z hz)]
    have := (A.pos z hz).ne'
    field_simp
  have hTs : IsSmoothHerm T := by
    unfold IsSmoothHerm
    exact (ContDiffOn.congr hB fun z hz => hTh z hz)
  have hTa : T.a = B.a := by
    rw [hab]
    show A.a + 0 = A.a
    simp
  have hSn : ∀ X : HermLine J, IsSmoothHerm X → ∀ j, IsSmoothHerm ((Fin.snoc L X : Fin (n + 1) → HermLine J) j) := by
    intro X hX j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hX
    · simpa using hL j
  have hloc : I P (n + 1) (Fin.snoc L T) = I P (n + 1) (Fin.snoc L B) := by
    refine hLoc K J I hI P (n + 1) _ _ hP (hSn T hTs) (hSn B hB) (fun j => ?_) (fun j z hz => ?_)
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hTa
      · simp
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hTh z hz.1
      · simp
  rw [← hloc, hch]
  congr 1
  refine ptsIntegral_congr_on P _ fun z hz => ?_
  unfold logDiff
  rw [if_pos hz.1]

def toLast {n : ℕ} (p : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' p).trans finSuccEquivLast.symm

theorem toLast_self {n : ℕ} (p : Fin (n + 1)) : toLast p p = Fin.last n := by
  simp [toLast]

theorem toLast_succAbove {n : ℕ} (p : Fin (n + 1)) (j : Fin n) :
    toLast p (p.succAbove j) = j.castSucc := by
  simp [toLast]

def word (A B : HermLine J) (m i : ℕ) : Fin m → HermLine J := fun j => if (j : ℕ) < i then B else A

theorem word_snoc (A B X : HermLine J) (n : ℕ) (p : Fin (n + 1)) (q : Fin (n + 1)) :
    (Fin.snoc (word A B n p) X : Fin (n + 1) → HermLine J) (toLast p q) =
      if (q : ℕ) < p then B else if q = p then X else A := by
  rcases Fin.eq_self_or_eq_succAbove p q with rfl | ⟨j, rfl⟩
  · simp [toLast_self]
  · rw [toLast_succAbove, Fin.snoc_castSucc]
    have hne := Fin.succAbove_ne p j
    rw [if_neg hne]
    unfold word
    by_cases h : (j : ℕ) < p
    · have : p.succAbove j = j.castSucc := Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)
      simp [this, h]
    · have : p.succAbove j = j.succ := Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)
      have h' : ¬ ((j : ℕ) + 1 < p) := by omega
      simp [this, h, h']

theorem smooth_snoc {n : ℕ} {L : Fin n → HermLine J} {X : HermLine J} (hL : ∀ j, IsSmoothHerm (L j))
    (hX : IsSmoothHerm X) (j : Fin (n + 1)) :
    IsSmoothHerm ((Fin.snoc L X : Fin (n + 1) → HermLine J) j) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa using hX
  · simpa using hL j

theorem word_smooth {A B : HermLine J} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (m i : ℕ)
    (j : Fin m) : IsSmoothHerm (word A B m i j) := by
  unfold word
  split_ifs
  · exact hB
  · exact hA

theorem word_step (hLoc : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement)
    (I : Ideal (MRing J) → (n : ℕ) → (Fin n → HermLine J) → ℝ) (hI : IsIntersectionFamily I)
    (P : Ideal (MRing J)) (n : ℕ) (A B : HermLine J)
    (hP : IsArithVar P (n + 1)) (hA : IsSmoothHerm A)
    (hB : IsSmoothHerm B) (hab : B.a = A.a) (i : ℕ) (hi : i < n + 1) :
    I P (n + 1) (word A B (n + 1) (i + 1)) = I P (n + 1) (word A B (n + 1) i) -
      ptsIntegral P (pot (word A B n i)) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
  let p : Fin (n + 1) := ⟨i, hi⟩
  have hL := word_smooth (J := J) hA hB n i
  have sB : word A B (n + 1) (i + 1) = (Fin.snoc (word A B n i) B : Fin (n + 1) → HermLine J) ∘ toLast p := by
    funext q
    have h := word_snoc A B B n p q
    simp only [Function.comp_apply]
    refine Eq.trans ?_ h.symm
    unfold word
    have hq : q = p ↔ (q : ℕ) = i := by simp [p, Fin.ext_iff]
    by_cases h1 : (q : ℕ) < i
    · have h2 : (q : ℕ) < i + 1 := by omega
      simp only [p, h1, h2, if_true]
    · by_cases h3 : (q : ℕ) = i
      · have h2 : (q : ℕ) < i + 1 := by omega
        simp [p, h1, h2, hq.2 h3]
      · have h2 : ¬ (q : ℕ) < i + 1 := by omega
        have h4 : q ≠ p := fun e => h3 (hq.1 e)
        simp [p, h1, h2, h4]
  have sA : word A B (n + 1) i = (Fin.snoc (word A B n i) A : Fin (n + 1) → HermLine J) ∘ toLast p := by
    funext q
    have h := word_snoc A B A n p q
    simp only [Function.comp_apply]
    refine Eq.trans ?_ h.symm
    unfold word
    by_cases h1 : (q : ℕ) < i
    · simp [p, h1]
    · simp [p, h1]
  rw [sB, sA, hI.1 P (n + 1) _ (toLast p) hP (smooth_snoc hL hB),
    hI.1 P (n + 1) _ (toLast p) hP (smooth_snoc hL hA)]
  exact step hLoc I hI P n _ A B hP hL hA hB hab

theorem telescope : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing J)) (n : ℕ) (A B : HermLine J), IsFullIntersectionSystem II → IsArithVar P (n + 1) → IsSmoothHerm A → IsSmoothHerm B → B.a = A.a → II K J P (n + 1) (fun _ => B) = II K J P (n + 1) (fun _ => A) - ∑ i ∈ Finset.range (n + 1), ptsIntegral P (pot fun j : Fin n => if (j : ℕ) < i then B else A) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
  intro hLoc K _ J _ II P n A B hII hP hA hB hab
  have hI : IsIntersectionFamily (II K J) := hII.1 K J
  have key : ∀ i, i ≤ n + 1 → II K J P (n + 1) (word A B (n + 1) i) =
      II K J P (n + 1) (word A B (n + 1) 0) - ∑ k ∈ Finset.range i,
        ptsIntegral P (pot (word A B n k)) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      rw [word_step hLoc _ hI P n A B hP hA hB hab i (by omega), ih (by omega),
        Finset.sum_range_succ]
      ring
  have e1 : word A B (n + 1) (n + 1) = fun _ => B := by
    funext j
    simp [word, j.isLt]
  have e0 : word A B (n + 1) 0 = fun _ => A := by
    funext j
    simp [word]
  have h := key (n + 1) le_rfl
  rw [e1, e0] at h
  exact h

end GlobalTheory.CompanionTheory.Ar.Tele
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnAtlasContinuous
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.AtlasSmooth

theorem continuous_of_atlas_smooth :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e X) (f : X → ℝ),
      A.Smooth f → Continuous f :=
  fun _ _ _ A _ hf => ReciprocityTheory.AnForm.M.st_smooth_continuous A hf

end GlobalTheory.CompanionTheory.Ar.AtlasSmooth
end

