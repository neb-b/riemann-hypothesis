module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.ImportsAlt
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0048
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStB
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0032
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftSectionSeparation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine constLine isSmoothHerm_powLine isSmoothHerm_constLine
  inter_tensor inter_powLine)

noncomputable section

namespace ShiftSectionSeparation

variable {K : Type} [Fintype K] {ι : K → Type}

theorem hermLine_ext {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

theorem powLine_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m : ℕ) (z : (Σ k, ι k) → ℂ) : (powLine A m).h z = A.h z ^ m := by
  induction m with
  | zero => simp [powLine, constLine]
  | succ m ih => simp [powLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ih, pow_succ]

theorem zcomb_eq [∀ k, Fintype (ι k)] (A H : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (q : ℕ) :
    HermLine.zcomb A H (q : ℤ) 1 = (powLine A q).tensor H := by
  refine hermLine_ext ?_ ?_
  · funext k
    simp [HermLine.zcomb, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, IndefiniteRowSideFullHecke.HeightsSet.powLine_a]
  · funext z
    simp [HermLine.zcomb, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, powLine_h]

end ShiftSectionSeparation


open ShiftSectionSeparation in
theorem ShiftSectionSeparation.proof (h₁ : ArithIntersectionSystemStatement)
    (h₂ : IndefiniteRowSideFullHecke.HeightsSet.DenseBoundedHeight.Statement) (h₃ : SmallSectionPointHeight.Statement) :
    ShiftSectionSeparation.Statement := by
  intro K _ ι _ Ω _ y D A hP hy hA
  obtain ⟨II, hII⟩ := h₁
  have hIS : IsIntersectionSystem II := hII.1
  have hI : IsIntersectionFamily (II K ι) := hIS K ι
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  obtain ⟨C₀, F, hF, hFW⟩ := h₂ K ι (II K ι) (mCoordIdeal y) D (fsH ι) hI hP hH rfl
  obtain ⟨k, C₁, hk⟩ := IndefiniteRowSideFullHecke.HeightsSet.HeightComparison.proof IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full
    K ι (II K ι) A (fsH ι) hI hA hH rfl
  refine ⟨|(k : ℝ) * C₀ + C₁| + |C₀|, by positivity, fun q _ n s hs hs0 c hc hb => ?_⟩
  set C := |(k : ℝ) * C₀ + C₁| + |C₀| with hC
  rw [zcomb_eq] at hs hb
  set N := (powLine A q).tensor (fsH ι) with hNdef
  have hN : IsSmoothHerm N := isSmoothHerm_tensor (isSmoothHerm_powLine hA q) hH
  set X := C * n * ((q : ℝ) + 1) with hX
  set c₁ := max c (Real.exp (-X) / 2) with hc₁
  have hc₁pos : 0 < c₁ := lt_max_of_lt_right (by positivity)
  have hc₁lt : c₁ < Real.exp (-X) := max_lt hc (by linarith [Real.exp_pos (-X)])
  set B := (powLine N n).tensor (constLine c₁ hc₁pos) with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_tensor (isSmoothHerm_powLine hN n) (isSmoothHerm_constLine _ _)
  have hBa : ∀ k, ((1 : ℕ) : ℤ) * B.a k = (n : ℤ) * N.a k := fun k => by
    simp [hBdef, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, IndefiniteRowSideFullHecke.HeightsSet.powLine_a, constLine]
  have hsB : s ∈ chartLat y B.a 1 := by
    intro c' hc'
    have h := hs c' hc'
    simp only [hBa]
    exact h
  have hsmall : IsSmallH (mCoordIdeal y) y B 1 s := by
    intro dg dh g h z hg hh hd hgh hz
    have hd' : ∀ k, (dg k : ℤ) = dh k + n * N.a k := fun k => by rw [hd k, hBa k]
    have h1 := hb dg dh g h z hg hh hd' hgh hz
    have hBh : B.h z = N.h z ^ n * c₁ := by simp [hBdef, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, powLine_h, constLine]
    have hnn : 0 ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * N.h z ^ n :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (N.pos z hz.1).le _)
    rw [pow_one, hBh]
    calc ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ c * ‖eval z (map (Int.castRingHom ℂ) h)‖ * N.h z ^ n := h1
      _ ≤ c₁ * (‖eval z (map (Int.castRingHom ℂ) h)‖ * N.h z ^ n) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
      _ = _ := by ring
  obtain ⟨f, hfd, hfP, hfW⟩ := h₃ K ι Ω y D B 1 s II hIS hP hy hB le_rfl
    (SmallSectionPointHeight.chartLat_le_chartLatNm _ _ _ hsB) hs0 hsmall
  obtain ⟨W, hWF, hfW'⟩ := hF f hfd hfP
  obtain ⟨hW, hPW, hWH⟩ := hFW W hWF
  have h0 := hfW W hW hPW hfW'
  have : Nonempty K := hW.1
  have hdegN := LowerBoundFree.degC_pos_of_isArithVar_one hW
  have hdeg : (0 : ℝ) < degC W := Nat.cast_pos.2 hdegN
  rw [hBdef, inter_tensor _ hI hW (isSmoothHerm_powLine hN n) (isSmoothHerm_constLine _ _),
    inter_powLine _ hI hW hN n, hNdef, inter_tensor _ hI hW (isSmoothHerm_powLine hA q) hH,
    inter_powLine _ hI hW hA q,
    LowerBoundFree.inter_constLine_eq _ hI hW hW.2.1.2.1 hdegN c₁ hc₁pos] at h0
  have hcmp := hk W hW
  simp only [IndefiniteRowSideFullHecke.HeightsSet.height] at hcmp hWH
  set d : ℝ := (degC W : ℝ)
  set a := II K ι W 1 ![A] / d with ha
  set b := II K ι W 1 ![fsH ι] / d with hb'
  have hIA : II K ι W 1 ![A] = a * d := by rw [ha]; field_simp
  have hIH : II K ι W 1 ![fsH ι] = b * d := by rw [hb']; field_simp
  rw [hIA, hIH] at h0
  have hkey : 0 ≤ (n : ℝ) * ((q : ℝ) * a + b) + Real.log c₁ := by
    have e : (n : ℝ) * ((q : ℝ) * (a * d) + b * d) + Real.log c₁ * d =
        d * ((n : ℝ) * ((q : ℝ) * a + b) + Real.log c₁) := by ring
    rw [e] at h0
    exact (mul_nonneg_iff_of_pos_left hdeg).mp h0
  have hak : a ≤ (k : ℝ) * C₀ + C₁ := by
    have := mul_le_mul_of_nonneg_left hWH (Nat.cast_nonneg (α := ℝ) k)
    linarith [le_abs_self a]
  have hq1 : (q : ℝ) * a ≤ (q : ℝ) * C :=
    mul_le_mul_of_nonneg_left (hak.trans ((le_abs_self _).trans (by rw [hC]; linarith [abs_nonneg C₀])))
      (Nat.cast_nonneg q)
  have hb1 : b ≤ C := hWH.trans ((le_abs_self _).trans (by rw [hC]; linarith [abs_nonneg ((k : ℝ) * C₀ + C₁)]))
  have h2 : (n : ℝ) * ((q : ℝ) * a + b) ≤ (n : ℝ) * (C * ((q : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg n)
  have hlog : Real.log c₁ < -X := by
    have := Real.log_lt_log hc₁pos hc₁lt
    rwa [Real.log_exp] at this
  rw [hX] at hlog
  nlinarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace TwoBlockTop

variable {κ : Type}

theorem isPullHerm_blockLine [Fintype κ] (m : ConeMetric ℂ (Ix κ)) (b : Fin 2) :
    IsPullHerm (blkOf b) (blkV κ b) (HermLine.ofCone m) (blockLine m b) := by
  refine ⟨?_, fun z => rfl⟩
  funext k
  show (Pi.single b 1 : Fin 2 → ℤ) k = Function.extend (blkOf b) (fun _ : Unit => (1 : ℤ)) 0 k
  by_cases hk : k = b
  · subst hk
    rw [Pi.single_eq_same]
    exact (Function.Injective.extend_apply (f := blkOf k) (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ => (1 : ℤ)) (0 : Fin 2 → ℤ) ()).symm
  · rw [Pi.single_eq_of_ne hk, Function.extend_apply' _ _ _ (fun ⟨_, hu⟩ => hk hu.symm)]
    rfl

theorem pair_comp_blkV_zero {Ω : Type} [Field Ω] (x x' : Ix κ → Ω) : pair x x' ∘ blkV κ 0 = x := by
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  simp [pair, blkV]

theorem pair_comp_blkV_one {Ω : Type} [Field Ω] (x x' : Ix κ → Ω) : pair x x' ∘ blkV κ 1 = x' := by
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  simp [pair, blkV]

end TwoBlockTop


open TwoBlockTop in
theorem TwoBlockTop.proof (hPF : PFCoordStatement) (hIm : ImageCoordStatement) (hA : CoordArithOfFnField.Statement)
    (hF : TwoBlockFnField.Statement) (hS : MetricTransportSmooth.Statement) : TwoBlockTop.Statement := by
  classical
  intro D Ω _ _ κ _ I x B m m' hI hx _ hB hm hm'
  obtain ⟨hFp, hFB⟩ := hF Ω κ x B hB
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hx

  obtain ⟨i, hi⟩ := hx.2.1.2.2 ()
  have hx0 : x ≠ 0 := fun h => hi ((X_mem_coordIdeal_iff x _).mpr (by rw [h]; rfl))
  obtain ⟨B', -, hB'⟩ := isInvMat_mul hB
  have hBx0 : matAct B x ≠ 0 := fun h => hx0 ((matAct_eq_zero_iff hB' x).mp h)
  obtain ⟨⟨⟨⟩, i₀⟩, hi₀⟩ := Function.ne_iff.mp hx0
  obtain ⟨⟨⟨⟩, i₁⟩, hi₁⟩ := Function.ne_iff.mp hBx0

  have hpA : IsArithVar (mCoordIdeal (ι := FinTwoTypeFamily κ) (pair x (matAct B x))) (D + 1) :=
    hA Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x (matAct B x)) (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨i₀, by simpa [pair] using hi₀⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  have hBA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) (matAct B x)) (D + 1) :=
    hA Unit (GlobalTheory κ) Unit (GlobalTheory κ) Ω x (matAct B x) (D + 1) ⟨()⟩ (fun _ => ⟨i₁, hi₁⟩) hFB.symm hxA

  have key : ∀ (b : Fin 2) (z : Ix κ → Ω) (μ : ConeMetric ℂ (Ix κ)), pair x (matAct B x) ∘ blkV κ b = z →
      IsArithVar (mCoordIdeal (ι := GlobalTheory κ) z) (D + 1) →
      blockFnField (ι := GlobalTheory κ) z = blockFnField (ι := GlobalTheory κ) x → IsSmoothMetric μ →
      I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine μ b) = top I z μ D := by
    intro b z μ hz hzA hzF hμ
    have himg : imageZ (blkV κ b) (mCoordIdeal (ι := FinTwoTypeFamily κ) (pair x (matAct B x))) = coordIdeal ℤ z := by
      rw [hIm Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) (blkOf b) (blkV κ b) Ω _ (isBlockMap_blkV κ b), hz,
        coordIdeal_eq_mCoordIdeal]
    have h := hPF I hI Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) (blkOf b) (blkV κ b) Ω (pair x (matAct B x)) (D + 1)
      (fun _ => HermLine.ofCone μ) (fun _ => blockLine μ b) (isBlockMap_blkV κ b) hpA
      (by rw [himg, coordIdeal_eq_mCoordIdeal]; exact hzA)
      (fun _ => gbamix_smoothHerm_ofCone hμ) (fun _ => isPullHerm_blockLine μ b)
    rw [IntermediateField.relfinrank_eq_one_iff.mpr (by rw [hz, hzF, hFp]), Nat.cast_one, one_mul] at h
    rw [top, ← himg]
    exact h
  exact ⟨key 0 x m (pair_comp_blkV_zero _ _) hxA rfl hm,
    key 1 (matAct B x) m' (pair_comp_blkV_one _ _) hBA hFB (hS κ B m m' hB hm hm')⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionPotentials
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem resLift_continuousOn (d : HSMDatum D Ω κ) (x : d.R.X) (p : Ix κ) :
    ContinuousOn (fun z => d.R.lift x z p) (d.R.U x) := by
  intro z hz
  obtain ⟨j, hj⟩ := d.R.A.cover z
  have hzt : d.R.A.chart j z ∈ (d.R.A.chart j).target := (d.R.A.chart j).map_source hj
  have hc : ContinuousAt ((fun z => d.R.lift x z p) ∘ (d.R.A.chart j).symm) (d.R.A.chart j z) :=
    (d.R.holo x p j _ ⟨hzt, by rwa [Set.mem_preimage, (d.R.A.chart j).left_inv hj]⟩).continuousAt
  have h := ((d.R.A.chart j).symm.continuousAt_iff_continuousAt_comp_right
    (f := fun z => d.R.lift x z p) (x := z) (by simpa using hj)).mpr (by simpa using hc)
  exact h.continuousWithinAt

theorem resLift_contDiffOn (d : HSMDatum D Ω κ) (x : d.R.X) (j : Fin d.R.A.n) :
    ContDiffOn ℝ ∞ (fun y => d.R.lift x ((d.R.A.chart j).symm y))
      ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x) :=
  contDiffOn_pi.mpr fun p => ((d.R.holo x p j).contDiffOn_of_completeSpace).restrict_scalars ℝ

theorem resPot_smoothOn (d : HSMDatum D Ω κ) {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m)
    (x : d.R.X) : d.R.A.SmoothOn ((resPot d m).U x) ((resPot d m).φ x) := fun j => by
  have hne : ∀ y ∈ (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x,
      d.R.lift x ((d.R.A.chart j).symm y) ∈ {z : Ix κ → ℂ | z ≠ 0} :=
    fun y hy => gaamix_ne_zero_of_mcPts (d.R.mem x _ hy.2)
  exact (hm.comp (resLift_contDiffOn d x j) hne).log fun y hy => (m.pos _ (hne y hy)).ne'

theorem isPotential_resPot (d : HSMDatum D Ω κ) {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsPotential d.R.A (resPot d m) := by
  refine ⟨resPot_smoothOn d hm, fun x x' y hy => ?_⟩
  have hy' : y ∈ d.R.U x ∩ d.R.U x' := hy
  obtain ⟨p, hp⟩ := (d.R.mem x' y hy'.2).1 ()
  obtain ⟨c, hc, hcy⟩ := d.R.compat x x' y hy'
  have hnum : d.R.lift x y ⟨(), p⟩ ≠ 0 := by
    rw [hcy]
    exact mul_ne_zero (hc ()) hp
  set r : ℂ := d.R.lift x y ⟨(), p⟩ / d.R.lift x' y ⟨(), p⟩ with hr_def
  have hr : r ≠ 0 := div_ne_zero hnum hp
  have hO : IsOpen (d.R.U x ∩ d.R.U x') := (d.R.isOpen_U x).inter (d.R.isOpen_U x')
  let q : d.R.X → ℂ := fun z => d.R.lift x z ⟨(), p⟩ / d.R.lift x' z ⟨(), p⟩ / r
  let W : Set d.R.X :=
    {z | z ∈ d.R.U x ∩ d.R.U x' ∧ d.R.lift x' z ⟨(), p⟩ ≠ 0 ∧ q z ∈ Complex.slitPlane}
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hn : ContinuousAt (fun z => d.R.lift x z ⟨(), p⟩) z :=
      ((resLift_continuousOn d x _).mono Set.inter_subset_left).continuousAt (hO.mem_nhds hz.1)
    have hd : ContinuousAt (fun z => d.R.lift x' z ⟨(), p⟩) z :=
      ((resLift_continuousOn d x' _).mono Set.inter_subset_right).continuousAt (hO.mem_nhds hz.1)
    filter_upwards [hO.mem_nhds hz.1, hd.eventually_ne hz.2.1,
      ((hn.div hd hz.2.1).div_const r).eventually_mem (Complex.isOpen_slitPlane.mem_nhds hz.2.2)]
      with w h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hyW : y ∈ W := by
    refine ⟨hy', hp, ?_⟩
    have h1 : q y = 1 := div_self hr
    rw [h1]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
  let G : d.R.X → ℂ := fun z => Complex.log (q z) + ((Real.log ‖r‖ : ℝ) : ℂ)
  refine ⟨W, hW, hyW, G, fun j y' hy'' => ?_, fun z hz => ?_⟩
  · have hz : (d.R.A.chart j).symm y' ∈ W := hy''.2
    have hn : AnalyticAt ℂ (fun y'' => d.R.lift x ((d.R.A.chart j).symm y'') ⟨(), p⟩) y' :=
      d.R.holo x _ j y' ⟨hy''.1, hz.1.1⟩
    have hd : AnalyticAt ℂ (fun y'' => d.R.lift x' ((d.R.A.chart j).symm y'') ⟨(), p⟩) y' :=
      d.R.holo x' _ j y' ⟨hy''.1, hz.1.2⟩
    have hq : AnalyticAt ℂ (fun y'' => q ((d.R.A.chart j).symm y'')) y' :=
      (hn.div hd hz.2.1).div analyticAt_const hr
    have hl : AnalyticAt ℂ (Complex.log ∘ fun y'' => q ((d.R.A.chart j).symm y'')) y' :=
      AnalyticAt.comp (f := fun y'' => q ((d.R.A.chart j).symm y'')) (analyticAt_clog hz.2.2) hq
    exact hl.add analyticAt_const
  · have hzW : z ∈ W := hz.1.1
    obtain ⟨c', hc', hcz⟩ := d.R.compat x x' z hzW.1
    have hpos : 0 < m.ρ (d.R.lift x' z) := m.pos _ (gaamix_ne_zero_of_mcPts (d.R.mem x' z hzW.1.2))
    have hsm : d.R.lift x z = c' () • d.R.lift x' z := by
      rw [hcz]
      funext w
      rfl
    have hqz : q z = c' () / r := by
      show d.R.lift x z ⟨(), p⟩ / d.R.lift x' z ⟨(), p⟩ / r = _
      rw [hsm, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hzW.2.1, mul_one]
    show Real.log (m.ρ (d.R.lift x z)) - Real.log (m.ρ (d.R.lift x' z)) = (G z).re
    rw [hsm, m.smul, Real.log_mul (norm_ne_zero_iff.mpr (hc' ())) hpos.ne', add_sub_cancel_right]
    show Real.log ‖c' ()‖ = (Complex.log (q z) + ((Real.log ‖r‖ : ℝ) : ℂ)).re
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, hqz, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr (hc' ())) (norm_ne_zero_iff.mpr hr)]
    ring

theorem continuous_logRatio_resPt (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (h₀ : IsSmoothMetric m₀) (h₁ : IsSmoothMetric m₁) :
    Continuous fun y => logRatio m₀ m₁ (resPt d y) := by
  refine continuous_iff_continuousAt.2 fun y0 => ?_
  have hU : d.R.U y0 ∈ 𝓝 y0 := (d.R.isOpen_U y0).mem_nhds (d.R.mem_U y0)
  have hL : ContinuousOn (d.R.lift y0) (d.R.U y0) :=
    continuousOn_pi.2 fun p => resLift_continuousOn d y0 p
  have hlog : ContinuousOn (fun y => logRatio m₀ m₁ (d.R.lift y0 y)) (d.R.U y0) :=
    (gbamix_smooth_logRatio h₀ h₁).continuousOn.comp hL
      fun y hy => gaamix_ne_zero_of_mcPts (d.R.mem y0 y hy)
  have heq : (fun y => logRatio m₀ m₁ (d.R.lift y0 y)) =ᶠ[𝓝 y0]
      fun y => logRatio m₀ m₁ (resPt d y) := by
    filter_upwards [hU] with y hy
    obtain ⟨c, hc, hcy⟩ := d.R.compat y y0 y ⟨d.R.mem_U y, hy⟩
    show _ = logRatio m₀ m₁ (d.R.lift y y)
    rw [hcy, gbamix_logRatio_deg c _ hc]
  exact (hlog.continuousAt hU).congr heq

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGenPtRel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameGenPtRel.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∀ G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))),
      (∀ n : ℕ, (n : G.Φ') = 0 → n = 0) ∧
      coordIdeal ℤ (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) = coordIdeal ℤ x ∧
      (∀ k : Fin (D + 1), G.x' ⟨Sum.inr (), k⟩ * G.x' ⟨Sum.inl (e 0).1, (e 0).2⟩ =
        G.x' ⟨Sum.inr (), (0 : Fin (D + 1))⟩ * G.x' ⟨Sum.inl (e k).1, (e k).2⟩) ∧
      (algebraMap G.Φ G.Φ').fieldRange = Subfield.closure (Set.range fun k : Fin (D + 1) => G.x' ⟨Sum.inr (), k⟩)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeDegreeInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullConeDegreeInt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (N M : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ c : ∀ k, ι k, (M : MRing ι) * (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N ∈ coneNullIdealZ y L) →
    ∀ (d : K → ℕ) (g : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d → (∀ k, e k + N * Fintype.card (ι k) ≤ d k) →
      ∃ a : Fin (D + 1) → MRing ι, (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (a j) (d - e)) ∧
        (M : Ω) * aeval y g = ∑ j, aeval y (a j) * aeval y (L j)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

