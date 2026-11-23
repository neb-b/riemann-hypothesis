module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalSquareEqHilbertSchmidtNormalisedVector
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0179
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0155
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0065
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeOneEqResidue
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeSiegelStep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianOrbitUniqueLatticeIntegralFrames
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0161

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexCoordinatesMeasurePreserving
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.ReImVolume

noncomputable def reImLinear (ι : Type) (n : ℕ) :
    (ι → Fin n → ℂ) ≃ₗ[ℝ] (ι × Fin n × Bool → ℝ) where
  toFun y p := if p.2.2 then (y p.1 p.2.1).re else (y p.1 p.2.1).im
  invFun x v i := ⟨x (v, i, true), x (v, i, false)⟩
  map_add' y z := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp
  map_smul' c y := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp
  left_inv y := by
    funext v i
    simp
  right_inv x := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp

theorem volume_re_im (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    volume {z : ℂ | z.re ∈ A ∧ z.im ∈ B} = volume A * volume B := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (hA.prod hB).nullMeasurableSet
  rw [Measure.volume_eq_prod, Measure.prod_prod] at h
  rw [← h]
  rfl

theorem measurePreserving_reImLinear (ι : Type) [Fintype ι] (n : ℕ) :
    MeasurePreserving (reImLinear ι n) volume volume := by
  have hm : Measurable (reImLinear ι n) :=
    (reImLinear ι n).toLinearMap.continuous_of_finiteDimensional.measurable
  refine ⟨hm, ?_⟩
  rw [volume_pi (α := fun _ : ι × Fin n × Bool => ℝ)]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (reImLinear ι n) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun v => Set.univ.pi fun i =>
        {z : ℂ | z.re ∈ s (v, i, true) ∧ z.im ∈ s (v, i, false)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_setOf_eq]
    constructor
    · intro h v i
      exact ⟨h (v, i, true), h (v, i, false)⟩
    · rintro h ⟨v, i, _ | _⟩
      · exact (h v i).2
      · exact (h v i).1
  rw [hpre, volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool, volume_re_im _ _ (hs _) (hs _)]

theorem exists_reIm_measurePreserving :
    ∀ (ι : Type) [Fintype ι] (n : ℕ), ∃ T : (ι → Fin n → ℂ) ≃ₜ+ (ι × Fin n × Bool → ℝ),
      MeasurePreserving T volume volume ∧
        ∀ y v i, T y (v, i, true) = (y v i).re ∧ T y (v, i, false) = (y v i).im := by
  intro ι _ n
  let L := (reImLinear ι n).toContinuousLinearEquiv
  refine ⟨{ toAddEquiv := (reImLinear ι n).toAddEquiv
            continuous_toFun := L.continuous
            continuous_invFun := L.symm.continuous }, ?_, fun y v i => ⟨rfl, rfl⟩⟩
  exact measurePreserving_reImLinear ι n

end GlobalTheory.ReImVolume
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
section
noncomputable section

namespace GlobalTheory.GaugeQuot

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal

variable {P Q P' Q' : ℕ}

def hsDist (g : UpqT P Q) : ℝ := ∑ i, ∑ j, ‖(UpqT.mat g - 1) i j‖ ^ 2

def ptSq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) : ℝ :=
  ‖y (e none) - 1‖ ^ 2 + 2 * ∑ i, ‖y (e (some i))‖ ^ 2

def tanSq (t : ℝ × Sp P' Q') : ℝ := t.1 ^ 2 + 2 * ∑ i, ‖t.2 i‖ ^ 2

def gaussSp (y : Sp P Q) : ℝ := Real.exp (-∑ i, ‖y i‖ ^ 2)

def ballVol (d : ℕ) (r : ℝ) : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)

def HasEuclDensity (μ : Measure (UpqT P Q)) : Prop :=
  Tendsto (fun r : ℝ => μ {g | hsDist g < r ^ 2} / ballVol ((P + Q) ^ 2) r) (𝓝[>] 0) (𝓝 1)

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.hsDist_nonneg (g : _root_.Formalism.BasicNotions.UpqT P Q) : 0 ≤ _root_.GlobalTheory.GaugeQuot.hsDist g := by
  unfold _root_.GlobalTheory.GaugeQuot.hsDist
  positivity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_hsDist : Continuous (_root_.GlobalTheory.GaugeQuot.hsDist : _root_.Formalism.BasicNotions.UpqT P Q → ℝ) := by
  have hmat : Continuous (_root_.Formalism.BasicNotions.UpqT.mat : _root_.Formalism.BasicNotions.UpqT P Q → _) := _root_.GlobalTheory.UpqTopology.continuous_mat
  unfold _root_.GlobalTheory.GaugeQuot.hsDist
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ptSq_nonneg (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) : 0 ≤ _root_.GlobalTheory.GaugeQuot.ptSq e y := by
  unfold _root_.GlobalTheory.GaugeQuot.ptSq
  positivity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_ptSq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (_root_.GlobalTheory.GaugeQuot.ptSq e) := by
  unfold _root_.GlobalTheory.GaugeQuot.ptSq
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.tanSq_nonneg (t : ℝ × _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P' Q') :
    0 ≤ _root_.GlobalTheory.GaugeQuot.tanSq t := by
  unfold _root_.GlobalTheory.GaugeQuot.tanSq
  positivity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_tanSq :
    Continuous (_root_.GlobalTheory.GaugeQuot.tanSq : ℝ × _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P' Q' → ℝ) := by
  unfold _root_.GlobalTheory.GaugeQuot.tanSq
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_gaussSp :
    Continuous (_root_.GlobalTheory.GaugeQuot.gaussSp : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q → ℝ) := by
  unfold _root_.GlobalTheory.GaugeQuot.gaussSp
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ballVol_mul (d : ℕ) (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    _root_.GlobalTheory.GaugeQuot.ballVol d (t * r) = ENNReal.ofReal (t ^ d) * _root_.GlobalTheory.GaugeQuot.ballVol d r := by
  unfold _root_.GlobalTheory.GaugeQuot.ballVol
  rw [Measure.addHaar_ball_mul_of_pos _ _ ht, finrank_euclideanSpace_fin]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ballVol_ne_zero (d : ℕ) {r : ℝ} (hr : 0 < r) :
    _root_.GlobalTheory.GaugeQuot.ballVol d r ≠ 0 :=
  (Metric.measure_ball_pos volume _ hr).ne'

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ballVol_ne_top (d : ℕ) (r : ℝ) : _root_.GlobalTheory.GaugeQuot.ballVol d r ≠ ⊤ :=
  measure_ball_lt_top.ne

end GlobalTheory.GaugeQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRootHaar
section
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.ThA.OrbSq
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Dx2
open scoped ENNReal

namespace GlobalTheory.Amp.RootQuot

variable {k r : ℕ}

theorem exists_setting (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') : ∃ Bs : B.RealPlaceData k r ℂ ℂ, Bs.z = z ∧ Bs.z' = z' := by
  obtain ⟨μG, hG⟩ := unitary_group_haar_exists k r
  obtain ⟨μN, hN⟩ := unipotent_haar_exists k r
  obtain ⟨μW, hW⟩ := weyl_haar_exists k r z hz hT
  obtain ⟨μW', hW'⟩ := weyl_haar_exists k r z' hz' hT'
  obtain ⟨μsec, hs⟩ := SettingConstruction.sectionExists k r z z' hk hz hz' hT hT'
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := character_exists_alt
  exact ⟨⟨z, z', fun _ => 1, fun _ => 1, μG, μW, μN, μW', μsec, χ, hk, hz, hz', hT, hT',
    ⟨rfl, fun _ _ _ _ => rfl⟩, ⟨rfl, fun _ _ _ _ => rfl⟩, fun _ _ _ => rfl, fun _ _ _ => rfl,
    continuousOn_const, continuousOn_const, hG, hW, hN, hW', hs, hχ1, hχ2, hχ3⟩, rfl, rfl⟩

theorem perm_invol (p : C.LPt) (n : ℕ) (h : D.ptSize p = n) (a : Fin n) :
    (h ▸ D.ptPerm p : Equiv.Perm (Fin n)) ((h ▸ D.ptPerm p : Equiv.Perm (Fin n)) a) = a := by
  subst h
  exact Dx1.ptPerm_invol p a

theorem zhat_inv_mono {z z' : Fin (2 * r + k + 1) → ℂ} (p : Point ℂ (r + 1)) {g : Mat k r} (hg : g ∈ GG k r)
    (hZ : ZhatO k r z z' g = ptMat p) :
    ∃ d : Fin (r + 1) → ℂ, (∀ a, d a ≠ 0) ∧ Zhat k r z' z g⁻¹ = C2.monoP (permOf p) d := by
  obtain ⟨hw, hd⟩ := VV.ptMatN_monoP' (sw p.1) (r + 1) (isLocPt_sw p).2 (isLocPt_sw p).1
  rw [ptMat_sw, ← hZ] at hw
  generalize (Eq.rec (motive := fun x _ => Fin x → ℂ) (D.ptDiag (sw p.1)) (isLocPt_sw p).2) = d at hw hd
  have hi : ∀ a, permOf p (permOf p a) = a := perm_invol _ _ _
  refine ⟨fun a => star ((-1) ^ (r - (permOf p a).val) * d (permOf p a)), fun a => ?_, ?_⟩
  · exact star_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hd _))
  · rw [NfMid.zhat_inv z z' hg]
    ext i a
    have h1 : (-1 : ℂ) ^ (r - i.val) * Zhat k r z z' g a i = if a = permOf p i then d i else 0 :=
      congrFun (congrFun hw a) i
    have h2 : Zhat k r z z' g a i = (-1 : ℂ) ^ (r - i.val) * if a = permOf p i then d i else 0 := by
      rw [← h1, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [conjTranspose_apply, h2]
    show _ = if i = permOf p a then _ else 0
    by_cases h : a = permOf p i
    · subst h
      simp [hi]
    · rw [if_neg h, if_neg (fun e => h (by rw [e, hi])), mul_zero, star_zero]

theorem gf_inv (z z' : Fin (2 * r + k + 1) → ℂ) {g : Mat k r} (hg : g ∈ GG k r) :
    Gf k r z' z g⁻¹ = Gf k r z z' g := by
  unfold Gf
  simp only [Complex.normSq_eq_norm_sq, NfMid.dmin_inv z z' hg]
  ring

theorem exists_root_haar (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (p : Point ℂ (r + 1)) {g : Mat k r} (hg : g ∈ GG k r)
    (hZ : ZhatO k r z z' g = ptMat p) (hG0 : Gf k r z z' g ≠ 0) :
    ∃ μ : Measure (Mt k r), IsHaarOn (Rset k r g) μ ∧ IsUnimod (Rset k r g) μ ∧
      μ.map (rootCoords k r z' p) = volume := by
  obtain ⟨Bs, rfl, rfl⟩ := exists_setting hk hz' hz hT' hT
  obtain ⟨d, hd, hZw⟩ := zhat_inv_mono p hg hZ
  have hu := isUnit_det_of_mem_GG hg
  have hgi : g⁻¹ ∈ B.GV k r := isClosedSub_GG.2.2.2.2 _ hg
  have hpos : 0 < Gf k r Bs.z Bs.z' g⁻¹ := by
    rw [gf_inv _ _ hg]
    exact lt_of_le_of_ne (gNonneg k r _ _ hz hz' hT hT' g hg) hG0.symm
  have hG : Rad.Good Bs g⁻¹ (permOf p) d :=
    ⟨Rad.exists_rho Bs hgi hpos hd hZw, Rad.u_inj Bs hgi hpos hd hZw, fun ρ hρ => Rad.u_lstg Bs hgi hpos hd hZw hρ⟩
  have hm := Rad.rhoF_meas Bs hgi hd hG
  have hH := Rad.haar_good Bs hgi hd hG
  have hI := haar_measure_inversion k r _ _ (OrbJ.closedR (Matrix.isUnit_nonsing_inv_det g hu)) hH
  have hset : C6.Rset g⁻¹ = Rset k r g := by
    ext x
    simp only [C6.Rset, Formalism.MainNotions.S.Rset, Set.mem_setOf_eq, Matrix.nonsing_inv_nonsing_inv _ hu]
  rw [hset] at hH
  have hmu : D.muR Bs g⁻¹ (permOf p) = (volume : Measure (C2.Lstidx (permOf p) → ℂ)).map
      (fun x => (Matrix.of.symm (Rad.rhoF Bs g⁻¹ (permOf p) x) : Mt k r)) := rfl
  have hphi : ∀ x : Mt k r, Rad.phi0 Bs (permOf p) x = cjE (rootEquiv p) (rootCoords k r Bs.z p x) := by
    intro x
    funext q
    rw [cjE_apply]
    have hq : q.1.2.val < r := by have h1 := q.2.1; have h2 := q.1.1.isLt; rw [Fin.lt_def] at h1; omega
    show star (C2.uMap k r Bs.z (Matrix.of x) q.1.2 q.1.1) = star (flagMat k r Bs.z (Matrix.of x) q.1.2 q.1.1)
    unfold C2.uMap flagMat
    rw [dite_eq_left hq, dite_eq_left hq]
    exact congrArg star (DF.herm_es _ _)
  have hrc : rootCoords k r Bs.z p = (cjE (rootEquiv p)).symm ∘ Rad.phi0 Bs (permOf p) := by
    funext x; simp [hphi x]
  have hrm : Measurable (rootCoords k r Bs.z p) := by
    rw [hrc]; exact (cjE (rootEquiv p)).symm.measurable.comp (Rad.continuous_radial_phi Bs).measurable
  refine ⟨D.muR Bs g⁻¹ (permOf p), ⟨OrbJ.sigmaF hH, hH.ne_zero, hH.conc, hH.left⟩, ⟨hH.right, hI⟩, ?_⟩
  rw [hmu, Measure.map_map hrm hm]
  have : rootCoords k r Bs.z p ∘ (fun x => (Matrix.of.symm (Rad.rhoF Bs g⁻¹ (permOf p) x) : Mt k r)) =
      (cjE (rootEquiv p)).symm := by
    funext x
    rw [hrc]
    simp only [Function.comp]
    rw [Rad.coordMap_hermRep_leftInverse Bs hgi hd hG]
  rw [this, (cjE_mp _).symm.map_eq]

theorem scale_pos (D : D7) : 0 < 2 * D.host.ka / gg D / (2 * Real.pi) := by
  have h1 : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    have h : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
    have := Real.rpow_pos_of_pos h ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))
    positivity
  have h2 : 0 < gg D := by
    unfold gg
    have a := (D.host.g_prime 0).pos
    have b := (D.host.g_prime 1).pos
    positivity
  positivity

theorem exists_rMeas : ∀ (D : D7) (W : LocW D.R.k D.R.rS) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)), inWb D.R.k D.R.rS W.z → inWb D.R.k D.R.rS W.z' → 0 < Tz D.R.k D.R.rS W.z → 0 < Tz D.R.k D.R.rS W.z' → IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG → RelPt D W.z W.z' γ p → ∃ ν, RMeas D W γ 1 ν := by
  rintro D W γ p hz hz' hT hT' hG ⟨hγ, hC, hG0⟩
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨n, hn, n', hn', g, hg, rfl, hZ⟩ := GlobalTheory.CellRep.cell_rep _ _ W.z W.z' γ p hz hz' hT hT' hγ hC
  rw [gInv _ _ W.z W.z' hz hz' n ⟨1, (isClosedSub_UWset W.z).2.2.1, n, hn, (Matrix.one_mul _).symm⟩
    n' ⟨1, (isClosedSub_UWset W.z').2.2.1, n', hn', (Matrix.one_mul _).symm⟩] at hG0
  obtain ⟨μ, h1, h2, h3⟩ := exists_root_haar hk hz hz' hT hT' p hg hZ hG0
  obtain ⟨n1, -, -, -, n5⟩ := isClosedSub_Nset (k := D.R.k) (r := D.R.rS)
  obtain ⟨d1, d2⟩ := StabMeas.haar_smul h1 h2 (pow_pos (scale_pos D) (rootPat p).card)
  obtain ⟨e1, e2⟩ := StabMeas.haar_conj (isUnit_det_of_mem_GG (n1 (n5 _ hn'))) (StabMeas.conj_mem_Rset hn hn' g) d1 d2
  obtain ⟨ν, hν⟩ := GlobalTheory.SgQuot.exists_isQuotMeas _ _ _ W.μG _ (StabMeas.isClosedSub_Rset hγ) hG e1 e2
  refine ⟨ν, p, _, ⟨n, hn, n', hn', g, rfl, hZ, _, d1.2.2.1, ?_, rfl⟩, ?_⟩
  · rw [Measure.map_smul, h3]
    apply Continuous.aemeasurable
    refine continuous_pi fun q => ?_
    unfold rootCoords flagMat
    split_ifs <;> first | exact continuous_const | fun_prop
  · have e : (fun x : Mt D.R.k D.R.rS => fun i j => (n'⁻¹ * Matrix.of x * n') i j) = conjM n'⁻¹ := by
      funext x
      unfold conjM
      rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG (n1 hn'))]
    rw [ENNReal.ofReal_one, one_smul, e]
    exact hν

end GlobalTheory.Amp.RootQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodModKLocalGen
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

open ValuativeRel Formalism.MainNotions.S.Loc IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DiffModProd

theorem different_ne_zero (F : Type) [Field F] [NumberField F] : differentIdeal ℤ (𝓞 F) ≠ 0 := by
  intro h
  have := absNorm_differentIdeal F (𝓞 F)
  rw [h, map_zero] at this
  exact discr_ne_zero F (Int.natAbs_eq_zero.1 this.symm)

theorem card_infinitePlace (D : D7) : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
  rw [← D.what₂.card_Tau]
  exact (Fintype.card_of_bijective
    ((Function.bijective_iff_existsUnique _).2 (GlobalTheory.RealPlaces.existsUnique_place D))).symm

theorem rdE_pow (D : D7) :
    D.host.rdE ^ (2 * Fintype.card (InfinitePlace D.host.E)) = |(NumberField.discr D.host.F : ℝ)| ^ 2 := by
  obtain ⟨h1, -⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hpos : Module.finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  rw [card_infinitePlace, ← GlobalTheory.RealPlaces.finrank_E D]
  unfold Host.rdE
  rw [one_div, Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
  have h3 : |(discr D.host.E : ℝ)| = (discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
  rw [h3, sq_abs]

theorem finprod_modK_localGen : ∀ (D : D7) (Z : LocDat D),
    (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (Z.δ p))).Finite ∧
    ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (Z.δ p)) =
      (D.host.rdE ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹ := by
  intro D Z
  let A : GlobalTheory.HL.Places D.host.F D.host.E D.conjF :=
    { quad := D.sp.cm.deg2, loc := D.s.atP, L := fun p => (Z.M p).L, L_cj := fun p => Z.hcj p }
  have hex : ∀ p : PlF D, ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ := fun p => by
    haveI := (D.s.atP p).lf
    exact IsDiscreteValuationRing.exists_irreducible _
  choose ϖ hϖ using hex
  have hδ : ∀ p, Z.δ p ≠ 0 := fun p => (Z.agree p).2.1
  have hI := different_ne_zero D.host.F
  set g : PlF D → ℝ := fun p =>
    (GlobalTheory.HL.resQ (ϖ p) : ℝ) ^ GlobalTheory.HL.vE (Z.M p).L (ϖ p) (algebraMap _ _ (Z.δ p)) with hg
  have hmod : ∀ p, (Z.M p).modK (algebraMap _ _ (Z.δ p)) = (g p ^ 2)⁻¹ := by
    intro p
    rw [(GlobalTheory.BaseModule.modK_algebraMap (Z.M p) (Z.agree p).1 (ϖ p) (hϖ p)).2 _ (hδ p), hg]
    dsimp only
    rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]
    congr 1
    push_cast
    ring
  have hcount : ∀ p, GlobalTheory.HL.vE (Z.M p).L (ϖ p) (algebraMap _ _ (Z.δ p)) =
      ((Associates.mk p.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 D.host.F))).factors : ℕ) :=
    fun p => GlobalTheory.IdealResProd.vE_eq_count (D.s.atP p) (Z.M p).L (hϖ p) _ hI (hδ p) (_root_.GlobalTheory.LocDiffGen.span_different_eq D Z p)
  have hfin : (Function.mulSupport g).Finite := by
    refine (Ideal.finite_factors hI).subset fun p hp => ?_
    simp only [Set.mem_setOf_eq]
    by_contra h
    apply hp
    have h0 : (Associates.mk p.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 D.host.F))).factors = 0 := by
      by_contra hne
      exact h ((Associates.count_ne_zero_iff_dvd hI p.irreducible).1 hne)
    simp [g, hcount p, h0]
  have hprod : ∏ᶠ p, g p = |(NumberField.discr D.host.F : ℝ)| :=
    (GlobalTheory.IdealResProd.discr_and_level A ϖ hϖ).1 (fun p => Units.mk0 (Z.δ p) (hδ p))
      (fun p => _root_.GlobalTheory.LocDiffGen.span_different_eq D Z p)
  have hsupp : (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (Z.δ p))) ⊆
      Function.mulSupport g := fun p hp h => hp (by show (Z.M p).modK _ = 1; rw [hmod, h]; simp)
  refine ⟨hfin.subset hsupp, ?_⟩
  rw [finprod_congr hmod, finprod_inv_distrib, ← finprod_pow hfin, hprod, rdE_pow]

end GlobalTheory.DiffModProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenLinTamagawaVolume
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem genLinVolume : GenLinVolume := by
  intro E _ _ hE j hj
  induction j, hj using Nat.le_induction with
  | base => simpa using _root_.GlobalTheory.NormOneVol.glVol_one E hE
  | succ j hj ih =>
    have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv E := by
      unfold Formalism.HermitianLatticesTheory.vInv
      positivity
    have hz : 0 ≤ zetaE E (j + 1) := zero_le_one.trans (_root_.GlobalTheory.DedekindZetaBound.one_le_zetaE_and_le E (j + 1) (by omega)).1
    have h := _root_.GlobalTheory.FlagBase.SiegelStep.glVol_step E hE (j + 1) (by omega)
      (by rw [Nat.add_sub_cancel, ih]; exact ENNReal.ofReal_lt_top)
    rw [h, Nat.add_sub_cancel, ih, ← ENNReal.ofReal_mul' (mul_nonneg (pow_nonneg hv _) hz),
      Finset.prod_Icc_succ_top (by omega)]
    congr 1
    have e : Formalism.HermitianLatticesTheory.fDeg E * (j + 1) ^ 2 =
        Formalism.HermitianLatticesTheory.fDeg E * j ^ 2 + Formalism.HermitianLatticesTheory.fDeg E * (2 * (j + 1) - 1) := by
      have : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [this]; ring
    rw [e, pow_add]
    ring

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianOrbitUniqueLatticeIntegralFramesStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_orbit_unique_lattice_integral_frames : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → P.PrimeTo → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → A a b = 0 ∧ A' a b = 0) → (∀ a, A a a = 1 ∧ A' a a = 1) → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O) → ∀ (f f' : Fin (r + 1) → V), (∀ j, f j = ∑ i, A i j • P.A.f i) → (∀ j, f' j = ∑ i, A' i j • P.B.f i) → ∀ d0 : LocNG.Datum P, (∃ t, LocNG.IsTermOver P d0 t) → ∀ d : LocNG.Datum P, (LocNG.Datum.Rel d0 d → ∃! Λ : Submodule M.L.O V, LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ∧ ((∃ t, LocNG.IsTermOver P d t) → LocNG.Datum.Rel d0 d) := by
  first | exact @GlobalTheory.HL.GoodFrames.main | exact GlobalTheory.HL.GoodFrames.main | (intros; apply GlobalTheory.HL.GoodFrames.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothFunctionalOrbitSmoothVectorStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_functional_orbit_smoothVector : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (σ : Mat k r → (H →L[ℂ] H)) (Λ : H →L[ℂ] B), IsURepOn (GG k r) σ → ∀ v : H, IsSmoothVec (k := k) (r := r) σ v → SmoothOnH (Hpk k r) (fun g : Mat k r => Λ (σ g v)) ∧ ∀ ws : List (Mat k r), (∀ X ∈ ws, InLieHpk k r X) → ∀ x ∈ GG k r, rdWord ws (fun g : Mat k r => Λ (σ g v)) x = Λ (σ x (dsigW σ ws v)) := by
  first | exact @GlobalTheory.SgInfOrb.smooth_rdWord_functional | exact GlobalTheory.SgInfOrb.smooth_rdWord_functional | (intros; apply GlobalTheory.SgInfOrb.smooth_rdWord_functional <;> assumption)
end

