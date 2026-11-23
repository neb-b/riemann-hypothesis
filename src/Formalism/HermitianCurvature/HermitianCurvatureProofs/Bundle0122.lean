module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjugateBlockSingleLastColumn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubMulRight
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0099
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0117
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0017
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairingTriangular
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AverageOne

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerCoordinateProd
section
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section cut

variable {j : ℕ}

def blkU (M : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ) : Matrix (Fin j) (Fin j) ℂ := M.submatrix Fin.castSucc Fin.castSucc

def x0c (w0 : Equiv.Perm (Fin j)) (W : Matrix (Fin j) (Fin j) ℂ) : C2.Lstidx w0 → ℂ :=
  ((StabilizerDisintegration.UC.eSp w0).symm (StabilizerDisintegration.utc W)).1

def boxC : Set ℂ := Complex.equivRealProd ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)

def chiL (w0 : Equiv.Perm (Fin j)) (x : C2.Lstidx w0 → ℂ) : ℝ :=
  (Set.univ.pi fun _ : C2.Lstidx w0 => boxC).indicator (fun _ => (1 : ℝ)) x

theorem boxR_meas : MeasurableSet (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc

theorem boxC_meas : MeasurableSet boxC := (Complex.measurable_re.prodMk Complex.measurable_im) boxR_meas

theorem boxC_vol : volume boxC = 1 := by
  have h := (Complex.volume_preserving_equiv_real_prod.measure_preimage boxR_meas.nullMeasurableSet)
  change volume (Complex.measurableEquivRealProd ⁻¹' _) = 1
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  simp

theorem chiL_meas (w0 : Equiv.Perm (Fin j)) : Measurable (chiL w0) := measurable_const.indicator (MeasurableSet.univ_pi fun _ => boxC_meas)

theorem chiL_nonneg (w0 : Equiv.Perm (Fin j)) (x : C2.Lstidx w0 → ℂ) : 0 ≤ chiL w0 x := by
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

theorem chiL_int (w0 : Equiv.Perm (Fin j)) : ∫ x, chiL w0 x = 1 := by
  unfold chiL
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => boxC_meas), Measure.real,
    volume_pi_pi]
  simp [boxC_vol]

end cut

section low

variable {r : ℕ} (w : Equiv.Perm (Fin (r + 1))) (w0 : Equiv.Perm (Fin r))

theorem w_last (hw : ∀ a : Fin r, w.symm a.castSucc = (w0.symm a).castSucc) :
    w.symm (Fin.last r) = Fin.last r := by
  by_contra h
  obtain ⟨b, hb⟩ := Fin.exists_castSucc_eq.2 h
  have h2 : w.symm (w0 b).castSucc = b.castSucc := by rw [hw, Equiv.symm_apply_apply]
  rw [hb] at h2
  exact (Fin.castSucc_lt_last (w0 b)).ne (w.symm.injective h2)

theorem w_last' (hw : ∀ a : Fin r, w.symm a.castSucc = (w0.symm a).castSucc) : w (Fin.last r) = Fin.last r := by
  exact ((Equiv.symm_apply_eq w).1 (w_last w w0 hw)).symm

variable (hw : ∀ a : Fin r, w.symm a.castSucc = (w0.symm a).castSucc)
include hw

theorem lst_ne_last (q : C2.Lstidx w) : q.1.1 ≠ Fin.last r ∧ q.1.2 ≠ Fin.last r := by
  refine ⟨fun h => ?_, ne_of_lt (lt_of_lt_of_le q.2.1 (Fin.le_last _))⟩
  have h2 := q.2.2
  rw [h, w_last w w0 hw] at h2
  exact absurd h2 (not_lt.2 (Fin.le_last _))

def eL : C2.Lstidx w0 ≃ C2.Lstidx w where
  toFun q := ⟨(q.1.1.castSucc, q.1.2.castSucc), Fin.castSucc_lt_castSucc_iff.2 q.2.1, by
    rw [hw, hw]; exact Fin.castSucc_lt_castSucc_iff.2 q.2.2⟩
  invFun q := ⟨((q.1.1).castPred (lst_ne_last w w0 hw q).1, (q.1.2).castPred (lst_ne_last w w0 hw q).2), by
    refine ⟨?_, ?_⟩
    · rw [← Fin.castSucc_lt_castSucc_iff]; simpa using q.2.1
    · have ha : ((q.1.1).castPred (lst_ne_last w w0 hw q).1).castSucc = q.1.1 := Fin.castSucc_castPred _ _
      have hb : ((q.1.2).castPred (lst_ne_last w w0 hw q).2).castSucc = q.1.2 := Fin.castSucc_castPred _ _
      have h2 : w.symm ((q.1.1).castPred (lst_ne_last w w0 hw q).1).castSucc <
          w.symm ((q.1.2).castPred (lst_ne_last w w0 hw q).2).castSucc := by rw [ha, hb]; exact q.2.2
      rw [hw, hw] at h2
      exact Fin.castSucc_lt_castSucc_iff.1 h2⟩
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp

theorem low_blk (x : C2.Lstidx w → ℂ) : blkU (Dx2.Rad.low w x) = Dx2.Rad.low w0 (x ∘ eL w w0 hw) := by
  ext i j
  rw [← StabilizerDisintegration.UC.lowS_eq_low, ← StabilizerDisintegration.UC.lowS_eq_low]
  simp only [blkU, Matrix.submatrix_apply, StabilizerDisintegration.lowS, C2.lowOf, Matrix.add_apply, Matrix.of_apply,
    Function.comp_apply]
  rw [← (eL w w0 hw).sum_comp (fun q => if q.1 = (i.castSucc, j.castSucc) then x q else 0)]
  congr 1
  · simp [Matrix.one_apply]
  · refine Finset.sum_congr rfl fun q _ => ?_
    have he : ((eL w w0 hw) q).1 = (q.1.1.castSucc, q.1.2.castSucc) := rfl
    simp only [he, Prod.ext_iff, Fin.castSucc_inj]

theorem low_last_row (x : C2.Lstidx w → ℂ) (a : Fin r) : Dx2.Rad.low w x (Fin.last r) a.castSucc = 0 := by
  rw [← StabilizerDisintegration.UC.lowS_eq_low]
  simp only [StabilizerDisintegration.lowS, C2.lowOf, Matrix.add_apply, Matrix.of_apply]
  rw [Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne', zero_add]
  exact Finset.sum_eq_zero fun q _ => if_neg fun h => (lst_ne_last w w0 hw q).1 (congrArg Prod.fst h)

omit hw in
theorem blkU_mul (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hA : ∀ a : Fin r, A a.castSucc (Fin.last r) = 0) :
    blkU (A * B) = blkU A * blkU B := by
  ext i j
  simp only [blkU, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hA, zero_mul, add_zero]

omit hw in
theorem blkU_ct (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : blkU Aᴴ = (blkU A)ᴴ := by
  ext i j
  rfl

omit hw in
theorem blkU_UT {A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hA : A ∈ C2.UTset (r + 1)) : blkU A ∈ C2.UTset r := ⟨fun i j h => hA.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 h), fun i => hA.2 _⟩

end low

section normcut

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def theta0 (z : Fin (2 * r + k + 1) → ℂ) (w0 : Equiv.Perm (Fin r)) (p : B.SS k r) : ℝ :=
  chiL w0 (x0c w0 (blkU (C2.uMap k r z (Matrix.of p.1.2))))

theorem theta0_meas (z : Fin (2 * r + k + 1) → ℂ) (w0 : Equiv.Perm (Fin r)) : Measurable (theta0 (k := k) z w0) := by
  have hU : Measurable fun p : B.SS k r => StabilizerDisintegration.utc (blkU (C2.uMap k r z (Matrix.of p.1.2))) := by
    refine Measurable.of_eval fun q => ?_
    have hc : Continuous fun p : B.SS k r =>
        C2.uMap k r z (Matrix.of p.1.2) q.1.1.castSucc q.1.2.castSucc := by
      simp only [C2.uMap, Formalism.QuantumDeterminants.herm, Fin.coe_castSucc, Fin.is_lt, dif_pos, dotProduct,
        Matrix.mulVec, Matrix.of_apply]
      fun_prop
    exact hc.measurable
  unfold theta0 x0c
  exact (chiL_meas w0).comp (measurable_fst.comp ((StabilizerDisintegration.UC.eSp w0).symm.measurable.comp hU))

theorem lower_coordinate_prod (w0 : Equiv.Perm (Fin r)) (x a : C2.Lstidx w0 → ℂ) (y : C2.LPidx w0 → ℂ) :
    x0c w0 ((StabilizerDisintegration.lowS w0 x)ᴴ * ((StabilizerDisintegration.lowS w0 a)ᴴ * (StabilizerDisintegration.lowP w0 y)ᴴ)) =
      StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 a * StabilizerDisintegration.lowS w0 x) := by
  have hL := ((StabilizerDisintegration.UC.lstLeft r w0 (fun _ => 1) (fun _ => one_ne_zero) a).2 x)
  have hM : (StabilizerDisintegration.lowS w0 x)ᴴ * ((StabilizerDisintegration.lowS w0 a)ᴴ * (StabilizerDisintegration.lowP w0 y)ᴴ) =
      (StabilizerDisintegration.lowS w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 a * StabilizerDisintegration.lowS w0 x)))ᴴ * (StabilizerDisintegration.lowP w0 y)ᴴ := by
    rw [← hL, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hE : StabilizerDisintegration.utc ((StabilizerDisintegration.lowS w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 a * StabilizerDisintegration.lowS w0 x)))ᴴ *
      (StabilizerDisintegration.lowP w0 y)ᴴ) = StabilizerDisintegration.UC.eSp w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 a * StabilizerDisintegration.lowS w0 x), y) := rfl
  unfold x0c
  rw [hM, hE, MeasurableEquiv.symm_apply_apply]

theorem theta0_normCut (S : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hZ : Zhat k r S.z S.z' γ = C2.monoP w d) (w0 : Equiv.Perm (Fin r))
    (hw : ∀ a : Fin r, w.symm a.castSucc = (w0.symm a).castSucc) :
    D.IsNormCut S γ (D.muR S γ w) (theta0 S.z w0) := by
  have hB : w (Fin.last r) = Fin.last r := w_last' w w0 hw
  have hG : Dx2.Rad.Good S γ w d :=
    ⟨Dx2.Rad.ex_degen S hγ hd hZ hB, Dx2.Rad.inj_degen S hγ hd hZ hB, fun ρ hρ => Dx2.Rad.lst_gen S hγ hd hZ hρ⟩
  refine ⟨theta0_meas S.z w0, fun p => chiL_nonneg w0 _, fun p hp => ?_⟩
  have hmuR : D.muR S γ w = (volume : Measure (C2.Lstidx w → ℂ)).map
      (fun x => (Matrix.of.symm (Dx2.Rad.rhoF S γ w x) : Mt k r)) := rfl
  have hact : Measurable fun x : Mt k r => theta0 S.z w0 (C6.actR γ (Matrix.of x) p) := by
    refine (theta0_meas S.z w0).comp ?_
    unfold C6.actR
    refine Measurable.prodMk (Measurable.prodMk measurable_const ?_) (Measurable.prodMk measurable_const ?_)
    · refine (continuous_pi fun i => continuous_pi fun l => ?_).measurable
      simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
      fun_prop
    · refine (continuous_pi fun i => continuous_pi fun l => ?_).measurable
      simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
      fun_prop
  rw [hmuR, integral_map (Dx2.Rad.rhoF_meas S hγ hd hG).aemeasurable hact.aestronglyMeasurable]

  have hn : Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r := hp.2.1
  have hUT : blkU (C2.uMap k r S.z (Matrix.of p.1.2)) ∈ C2.UTset r :=
    blkU_UT ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r S.z ⟨S.z_mem, S.T_pos⟩).1 _ (Dx2.Rad.N_sub_S S.z hn)).2.1
  set pa := (StabilizerDisintegration.UC.eSp w0).symm (StabilizerDisintegration.utc (blkU (C2.uMap k r S.z (Matrix.of p.1.2)))) with hpa
  have hsplit : blkU (C2.uMap k r S.z (Matrix.of p.1.2)) = (StabilizerDisintegration.lowS w0 pa.1)ᴴ * (StabilizerDisintegration.lowP w0 pa.2)ᴴ := by
    rw [← StabilizerDisintegration.UC.upper_fSp, ← StabilizerDisintegration.UC.upper_utc hUT]
    congr 1
    show _ = StabilizerDisintegration.UC.eSp w0 pa
    rw [hpa, (StabilizerDisintegration.UC.eSp w0).apply_symm_apply]
  have hpt : ∀ x : C2.Lstidx w → ℂ, theta0 S.z w0 (C6.actR γ (Matrix.of (Matrix.of.symm (Dx2.Rad.rhoF S γ w x))) p) =
      chiL w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 pa.1 * StabilizerDisintegration.lowS w0 (x ∘ eL w w0 hw))) := by
    intro x
    obtain ⟨hρR, hρu⟩ := Dx2.Rad.rhoF_spec S hγ hd hG x
    unfold theta0
    simp only [C6.actR, Equiv.apply_symm_apply]
    rw [Dx2.Rad.uMap_mul S hρR.1 hn, hρu,
      blkU_mul _ _ (fun a => by rw [Matrix.conjTranspose_apply, low_last_row w w0 hw, star_zero]),
      blkU_ct, low_blk w w0 hw, hsplit, ← StabilizerDisintegration.UC.lowS_eq_low, lower_coordinate_prod]
  simp_rw [hpt]
  have hmp1 := (MeasureTheory.measurePreserving_piCongrLeft (fun _ : C2.Lstidx w => (volume : Measure ℂ))
    (eL w w0 hw)).symm
  have hmp2 := (StabilizerDisintegration.lstLeft r w0 (fun _ => 1) (fun _ => one_ne_zero) pa.1).1
  have e1 : ∫ x : C2.Lstidx w → ℂ, chiL w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 pa.1 * StabilizerDisintegration.lowS w0 (x ∘ eL w w0 hw))) =
      ∫ x' : C2.Lstidx w0 → ℂ, chiL w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 pa.1 * StabilizerDisintegration.lowS w0 x')) := by
    have h := hmp1.integral_comp (MeasurableEquiv.measurableEmbedding _)
      (fun y : C2.Lstidx w0 → ℂ => chiL w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 pa.1 * StabilizerDisintegration.lowS w0 y)))
    exact h
  rw [e1, ← integral_map hmp2.measurable.aemeasurable (chiL_meas w0).aestronglyMeasurable, hmp2.map_eq,
    chiL_int]

end normcut

end Formalism.FourierDecayAlt.P.PBM
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCStep
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

theorem norm_psiG (g : ℝ) (l c : ℂ) : ‖psiG g l c‖ = 1 := by
  simp only [psiG]
  rw [Complex.norm_exp]
  simp

theorem continuous_psiG (g : ℝ) (l : ℂ) : Continuous (psiG g l) := by
  unfold psiG
  fun_prop

theorem psi_prod (g : ℝ) (hg : g ≠ 0) (σ z : crystallineComparison.V f) :
    crystallineComparison.psi (σ * z) = ∏ v, psiG g ((g • σ) v) (z v) := by
  have key : ∀ v, (2 * (((g • σ) v) * z v).re / g : ℝ) = 2 * (σ v * z v).re := by
    intro v
    rw [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]
    field_simp
  simp only [psiG, key]
  rw [← Complex.exp_sum, Formalism.FourierDecayAlt.P.PairingConjugationLemmas.psi_mul, Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair, Complex.ofReal_sum,
    Finset.mul_sum]

theorem integrable_mul_psiG {φ : ℂ → ℂ} (hφ : Integrable φ) (g : ℝ) (l : ℂ) :
    Integrable fun c => φ c * psiG g l c := by
  refine hφ.norm.mono' (hφ.aestronglyMeasurable.mul (continuous_psiG g l).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun c => by rw [norm_mul, norm_psiG, mul_one]

theorem fourier_Nz (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : g ≠ 0) (dl : Fin f → ℝ)
    (hdl : ∀ v, dl v ≠ 0) (hat : Fin f → ℂ → H → H → ℂ)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c) (σ : crystallineComparison.V f) :
    crystallineComparison.fourier (Nz Y κ D) σ = (∏ v, ((dl v : ℝ) : ℂ)) * Hh Y κ hat (g • σ) := by
  have hae : (fun z => ((Nz Y κ D z : ℝ) : ℂ) * crystallineComparison.psi (σ * z)) =ᵐ[volume]
      fun z => Fz Y κ D z * crystallineComparison.psi (σ * z) := by
    filter_upwards [ae_good] with z hz
    have h0 := Complex.nonneg_iff.mp (Fz_nonneg Y κ hκ D hD z hz)
    rw [Nz, if_pos hz]
    congr 1
    exact Complex.ext (by simp) (by simp [← h0.2])
  have hpt : ∀ z : crystallineComparison.V f, Fz Y κ D z * crystallineComparison.psi (σ * z) =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (D v h h' (z v) * psiG g ((g • σ) v) (z v)) := by
    intro z
    rw [Fz, psi_prod g hg σ z, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [Finset.prod_mul_distrib, mul_assoc]
  have hone : ∀ v h h', ∫ c, D v h h' c * psiG g ((g • σ) v) c =
      ((dl v : ℝ) : ℂ) * hat v ((g • σ) v) h h' := by
    intro v h h'
    rw [hhat, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hdl v), one_mul]
  have hint : ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (fun z : crystallineComparison.V f =>
      κ h h' * ∏ v, (D v h h' (z v) * psiG g ((g • σ) v) (z v))) := by
    intro h hh h' hh'
    exact (Integrable.fintype_prod (fun v => integrable_mul_psiG (hDi v h hh h' hh') g _)).const_mul _
  unfold crystallineComparison.fourier
  rw [integral_congr_ae hae]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun h hh => integrable_finsetSum _ (fun h' hh' => hint h hh h' hh')),
    Hh, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [integral_finsetSum _ (fun h' hh' => hint h hh h' hh'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun h' hh' => ?_
  have hp := integral_fintype_prod_volume_eq_prod (fun v (c : ℂ) => D v h h' c * psiG g ((g • σ) v) c)
  rw [integral_const_mul, hp]
  simp_rw [hone]
  rw [Finset.prod_mul_distrib]
  ring

theorem exists_good (τ : crystallineComparison.V f) : ∃ x : crystallineComparison.V f, Good x ∧ Good (x + τ) := by
  refine ⟨fun v => ((‖τ v‖ + 1 : ℝ) : ℂ), fun v => ?_, fun v => ?_⟩
  · show ((‖τ v‖ + 1 : ℝ) : ℂ) ≠ 0
    have hpos : (0 : ℝ) < ‖τ v‖ + 1 := by positivity
    exact_mod_cast hpos.ne'
  · show ((‖τ v‖ + 1 : ℝ) : ℂ) + τ v ≠ 0
    intro h
    have h2 : τ v = -(((‖τ v‖ + 1 : ℝ) : ℂ)) := by linear_combination h
    have h3 := congrArg (fun w : ℂ => ‖w‖) h2
    simp only [norm_neg] at h3
    rw [Complex.norm_of_nonneg (by positivity)] at h3
    linarith

theorem herglotz_germ (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : 0 < g) (dl : Fin f → ℝ)
    (hdl : ∀ v, 0 < dl v) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (hat : Fin f → ℂ → H → H → ℂ)
    (hG : GermData Y U P Q hat)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c)
    (La : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (Lm : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology Lm] [IsZLattice ℝ Lm]
    (hLm : ∀ σ ∈ crystallineComparison.dualSet La, g • σ ∈ Lm) (F : crystallineComparison.V f → ℝ)
    (hFs : Summable fun σ : crystallineComparison.dualSet La => F σ)
    (hF : ∀ σ ∈ crystallineComparison.dualSet La, ∀ x : crystallineComparison.V f, Good x → Good (x + g • σ) → ‖phi Y κ U x (x + g • σ)‖ ≤ F σ)
    (z₀ : crystallineComparison.V f) (S : Finset (crystallineComparison.V f)) (hS : ∀ z ∈ S, z - z₀ ∈ La) :
    ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := by
  have hgne : g ≠ 0 := hg.ne'
  have hdlne : ∀ v, dl v ≠ 0 := fun v => (hdl v).ne'
  have hc0 : 0 ≤ ∏ v, dl v := Finset.prod_nonneg fun v _ => (hdl v).le
  have hfour : ∀ σ : crystallineComparison.V f, crystallineComparison.fourier (Nz Y κ D) σ = ((∏ v, dl v : ℝ) : ℂ) * Hh Y κ hat (g • σ) := by
    intro σ
    rw [fourier_Nz Y κ hκ D hD hDi g hgne dl hdlne hat hhat σ, Complex.ofReal_prod]
  obtain ⟨LIM, hL⟩ := Formalism.FourierDecayAlt.P.invariantMeanExists f Lm
  have hbd : ∀ σ ∈ crystallineComparison.dualSet La,
      ‖Hh Y κ hat (g • σ) + A0 Lm.toAddSubgroup LIM Y κ U P Q (g • σ)‖ ≤ F σ := by
    intro σ hσ
    rw [← mean_split Lm.toAddSubgroup LIM hG κ hκ hL (g • σ)]
    refine Formalism.FourierDecayAlt.P.mean_bound_estimate _ LIM _ (F σ) hL.1 ?_
    intro x
    unfold phiG
    split_ifs with hx
    · exact hF σ hσ x hx.1 hx.2
    · obtain ⟨x0, h1, h2⟩ := exists_good (g • σ)
      simpa using (norm_nonneg _).trans (hF σ hσ x0 h1 h2)
  let A : crystallineComparison.V f → ℂ := fun σ => ((∏ v, dl v : ℝ) : ℂ) * A0 Lm.toAddSubgroup LIM Y κ U P Q (g • σ)
  have hPD : crystallineComparison.PDOn (crystallineComparison.dualSet La) A := by
    intro T w hT
    have hinj : Set.InjOn (fun σ : crystallineComparison.V f => g • σ) T :=
      fun a _ b _ hab => smul_right_injective (crystallineComparison.V f) hgne hab
    have hT' : ∀ τ ∈ T.image (fun σ : crystallineComparison.V f => g • σ), τ ∈ Lm.toAddSubgroup := by
      intro τ hτ
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
      exact hLm σ (hT σ hσ)
    have h0 := limit_average_positive_definite Lm.toAddSubgroup LIM hG κ hκ hL.1 (T.image (fun σ : crystallineComparison.V f => g • σ)) hT'
      (fun τ => w (g⁻¹ • τ))
    simp_rw [Finset.sum_image hinj] at h0
    simp only [inv_smul_smul₀ hgne, ← smul_sub] at h0
    have hsplit : (∑ σ ∈ T, ∑ σ' ∈ T, A (σ - σ') * w σ * starRingEnd ℂ (w σ')) =
        ((∏ v, dl v : ℝ) : ℂ) * ∑ σ ∈ T, ∑ σ' ∈ T,
          A0 Lm.toAddSubgroup LIM Y κ U P Q (g • (σ - σ')) * w σ * starRingEnd ℂ (w σ') := by
      simp only [A, Finset.mul_sum, mul_assoc]
    rw [hsplit, Complex.re_ofReal_mul]
    exact mul_nonneg hc0 h0
  have hb : ∀ σ : crystallineComparison.dualSet La, ‖crystallineComparison.fourier (Nz Y κ D) σ + A σ‖ ≤ (∏ v, dl v) * F σ := by
    intro σ
    rw [hfour]
    simp only [A]
    rw [← mul_add, norm_mul, Complex.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hbd σ σ.2) hc0
  have hsum : Summable fun σ : crystallineComparison.dualSet La => (∏ v, dl v) * F σ := hFs.mul_left _
  have hS2 : Summable fun σ : crystallineComparison.dualSet La => ‖crystallineComparison.fourier (Nz Y κ D) σ + A σ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
  have key := Formalism.FourierDecayAlt.P.latticeHerglotzBound_statement f La (Nz Y κ D) A (Nz_nonneg Y κ hκ D hD)
    (Nz_lsc Y κ hκ D hD hDc) (Nz_integrable Y κ D hDi) hPD hS2 z₀ S hS
  calc ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ _ := key
    _ ≤ ∑' σ : crystallineComparison.dualSet La, (∏ v, dl v) * F σ := hS2.tsum_le_tsum hb hsum
    _ = (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := tsum_mul_left

theorem herglotz_plain (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : 0 < g) (dl : Fin f → ℝ)
    (hdl : ∀ v, 0 < dl v) (hat : Fin f → ℂ → H → H → ℂ)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c)
    (La : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology La] [IsZLattice ℝ La] (F : crystallineComparison.V f → ℝ)
    (hFs : Summable fun σ : crystallineComparison.dualSet La => F σ)
    (hF : ∀ σ ∈ crystallineComparison.dualSet La, ‖Hh Y κ hat (g • σ)‖ ≤ F σ)
    (z₀ : crystallineComparison.V f) (S : Finset (crystallineComparison.V f)) (hS : ∀ z ∈ S, z - z₀ ∈ La) :
    ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := by
  have hgne : g ≠ 0 := hg.ne'
  have hdlne : ∀ v, dl v ≠ 0 := fun v => (hdl v).ne'
  have hc0 : 0 ≤ ∏ v, dl v := Finset.prod_nonneg fun v _ => (hdl v).le
  have hfour : ∀ σ : crystallineComparison.V f, crystallineComparison.fourier (Nz Y κ D) σ = ((∏ v, dl v : ℝ) : ℂ) * Hh Y κ hat (g • σ) := by
    intro σ
    rw [fourier_Nz Y κ hκ D hD hDi g hgne dl hdlne hat hhat σ, Complex.ofReal_prod]
  have hPD : crystallineComparison.PDOn (crystallineComparison.dualSet La) (0 : crystallineComparison.V f → ℂ) := by
    intro T w _
    simp
  have hb : ∀ σ : crystallineComparison.dualSet La,
      ‖crystallineComparison.fourier (Nz Y κ D) σ + (0 : crystallineComparison.V f → ℂ) σ‖ ≤ (∏ v, dl v) * F σ := by
    intro σ
    rw [Pi.zero_apply, add_zero, hfour, norm_mul, Complex.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hF σ σ.2) hc0
  have hsum : Summable fun σ : crystallineComparison.dualSet La => (∏ v, dl v) * F σ := hFs.mul_left _
  have hS2 : Summable fun σ : crystallineComparison.dualSet La => ‖crystallineComparison.fourier (Nz Y κ D) σ + (0 : crystallineComparison.V f → ℂ) σ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
  have key := Formalism.FourierDecayAlt.P.latticeHerglotzBound_statement f La (Nz Y κ D) 0 (Nz_nonneg Y κ hκ D hD)
    (Nz_lsc Y κ hκ D hD hDc) (Nz_integrable Y κ D hDi) hPD hS2 z₀ S hS
  calc ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ _ := key
    _ ≤ ∑' σ : crystallineComparison.dualSet La, (∏ v, dl v) * F σ := hS2.tsum_le_tsum hb hsum
    _ = (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := tsum_mul_left

end

end Formalism.FourierDecayAlt.P.PBC
end

