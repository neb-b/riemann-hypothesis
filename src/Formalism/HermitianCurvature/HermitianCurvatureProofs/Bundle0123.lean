module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableCoordinateMap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0116

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RearrSymm
section
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.OJ

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

private theorem herm_hpk_bvec_esI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (esI k r a)) = v (eI k r a) := by
  have ha := a.isLt
  have he : (eI k r a).val = a.val := rfl
  have hs : (esI k r a).val = 2 * r + k - a.val := rfl
  unfold herm bvec
  rw [← Pi.single_star, star_one, single_dotProduct, one_mul, Matrix.mulVec, dotProduct,
    Finset.sum_eq_single (eI k r a)]
  · have h1 : Hpk k r (esI k r a) (eI k r a) = 1 := by
      simp only [Hpk]
      rw [if_neg (fun h => absurd h.1 (by omega)), if_pos ⟨by omega, by omega⟩]
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ a.val := fun h => hj (Fin.ext (h.trans he.symm))
    have h0 : Hpk k r (esI k r a) j = 0 := by
      simp only [Hpk]
      rw [if_neg (fun h => absurd h.1 (by omega)), if_neg (fun h => hj' (by have := h.2; omega)),
        if_neg (fun h => absurd h.2.1 (by omega))]
    rw [h0, zero_mul]
  · simp

theorem ell_eq (z : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : ell k r z g = C2.simpleUp (C2.uMap k r z g) := by
  unfold ell C2.simpleUp
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, lt_self_iff_false, dite_false, add_zero, Fin.val_castSucc]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha : a.val + 1 < r + 1 := by omega
  rw [dite_eq_left ha]
  simp only [C2.uMap, Fin.val_castSucc, a.isLt, dite_true]
  rw [herm_hpk_bvec_esI]
  simp only [fvec]
  by_cases h1 : a.val + 1 < r
  · simp [h1, bvec, Matrix.mulVec_single]
  · simp [h1]

theorem psi_prod (a b : ℂ) :
    Complex.exp (Complex.I * (((1 : ℝ) * (cStd * a).re - (1 : ℝ) * (cStd * b).re : ℝ) : ℂ)) =
      C2.psiC cStd a * star (C2.psiC cStd b) := by
  simp only [C2.psiC, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem xi_at (S : B.RealPlaceData k r Wp Wq) {v u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hv : v ∈ C2.UTset (r + 1))
    (hu' : u' ∈ C2.UTset (r + 1)) {n0 n0' : Mt k r} (hn0 : Matrix.of n0 ∈ C2.N0set k r S.z)
    (hn0' : Matrix.of n0' ∈ C2.N0set k r S.z') (h h' : Mt k r) :
    B.xiTau S (1, 1) ((h, Matrix.of.symm (C2.tauM k r S.z v * Matrix.of n0)),
      (h', Matrix.of.symm (C2.tauM k r S.z' u' * Matrix.of n0'))) =
      C2.psiC cStd (C2.simpleUp v) * star (C2.psiC cStd (C2.simpleUp u')) := by
  have key : ∀ {z : Fin (2 * r + k + 1) → ℂ}, C2.StdZ k r z → ∀ {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ},
      v ∈ C2.UTset (r + 1) → ∀ {n0 : Mt k r}, Matrix.of n0 ∈ C2.N0set k r z →
      ell k r z (C2.tauM k r z v * Matrix.of n0) = C2.simpleUp v := by
    intro z hz v hv n0 hn0
    rw [ell_eq, HC.uMap_mul hz (HC.tau_N hz hv) hn0.1, HC.tau_u hz hv, hn0.2, mul_one]
  unfold B.xiTau B.lam
  simp only [Equiv.apply_symm_apply]
  rw [key ⟨S.z_mem, S.T_pos⟩ hv hn0, key ⟨S.z'_mem, S.T'_pos⟩ hu' hn0']
  exact psi_prod _ _

theorem pt_eq (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (Y : (C2.LPidx w → ℂ) × (G.UT (r + 1) → ℂ)) (p : B.SS k r)
    (hp1 : Matrix.of p.1.2 ∈ C2.N0set k r S.z) (hp2 : Matrix.of p.2.2 ∈ C2.N0set k r S.z') :
    D.orbIntegrand S γ F (Xi0 S w ((p.1.1, (Y.1, p.1.2)), (p.2.1, (Y.2, p.2.2)))) =
      (C2.psiC cStd (C2.simpleUp (lowP w Y.1)ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper Y.2)))) •
        B.rho S p F ((C2.tauM k r S.z (lowP w Y.1)ᴴ)⁻¹ * γ * C2.tauM k r S.z' (G.upper Y.2)) := by
  have hv := OD.lowPH_UT Y.1
  have hu := HC.upper_mem Y.2
  have hr : B.rho S ((p.1.1, Matrix.of.symm (C2.tauM k r S.z (lowP w Y.1)ᴴ * Matrix.of p.1.2)),
        (p.2.1, Matrix.of.symm (C2.tauM k r S.z' (G.upper Y.2) * Matrix.of p.2.2))) F γ =
      B.rho S p F ((C2.tauM k r S.z (lowP w Y.1)ᴴ)⁻¹ * γ * C2.tauM k r S.z' (G.upper Y.2)) := by
    unfold B.rho B.sgs
    simp only [Equiv.apply_symm_apply, Matrix.mul_inv_rev, Matrix.mul_assoc]
  unfold D.orbIntegrand
  rw [show Xi0 S w ((p.1.1, (Y.1, p.1.2)), (p.2.1, (Y.2, p.2.2))) =
      ((p.1.1, Matrix.of.symm (C2.tauM k r S.z (lowP w Y.1)ᴴ * Matrix.of p.1.2)),
        (p.2.1, Matrix.of.symm (C2.tauM k r S.z' (G.upper Y.2) * Matrix.of p.2.2))) from rfl,
    xi_at S hv hu hp1 hp2 p.1.1 p.2.1, hr]

theorem cell_int [CompleteSpace Wp] (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    {μ0 μ0' : Measure (Mt k r)} (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
    (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0') (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hI : Integrable (fun q => D.orbIntegrand S γ F (Xi0 S w q)) (nuR S w μ0 μ0')) :
    ∫ q, D.orbIntegrand S γ F (Xi0 S w q) ∂(nuR S w μ0 μ0') =
      ∫ Y : (C2.LPidx w → ℂ) × (G.UT (r + 1) → ℂ),
        (C2.psiC cStd (C2.simpleUp (lowP w Y.1)ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper Y.2)))) •
          PBI.fibInt S μ0 μ0' F ((C2.tauM k r S.z (lowP w Y.1)ᴴ)⁻¹ * γ * C2.tauM k r S.z' (G.upper Y.2)) := by
  have := Dx2.OrbJ.sigmaF hμ0
  have := Dx2.OrbJ.sigmaF hμ0'
  have := Dx2.OrbJ.sigmaF S.haarW
  have := Dx2.OrbJ.sigmaF S.haarW'
  have hmp := RE.mp_rearr S w hμ0 hμ0'
  let Φ : ((C2.LPidx w → ℂ) × (G.UT (r + 1) → ℂ)) × B.SS k r → (Wq →L[ℂ] Wp) := fun x =>
    (C2.psiC cStd (C2.simpleUp (lowP w x.1.1)ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper x.1.2)))) •
      B.rho S x.2 F ((C2.tauM k r S.z (lowP w x.1.1)ᴴ)⁻¹ * γ * C2.tauM k r S.z' (G.upper x.1.2))
  have hae : (fun q => D.orbIntegrand S γ F (Xi0 S w q)) =ᵐ[nuR S w μ0 μ0'] fun q => Φ (RE.rearr k r w q) := by
    filter_upwards [OG.ae_good S w hμ0 hμ0'] with q hq
    rw [RE.rearr_apply]
    exact pt_eq S γ w F (q.1.2.1, q.2.2.1) ((q.1.1, q.1.2.2), (q.2.1, q.2.2.2)) hq.2.1 hq.2.2.2
  have hIp : Integrable Φ (((volume : Measure (C2.LPidx w → ℂ)).prod (volume : Measure (G.UT (r + 1) → ℂ))).prod
      ((S.μW.prod μ0).prod (S.μW'.prod μ0'))) :=
    (hmp.integrable_comp_emb (RE.rearr k r w).measurableEmbedding).mp (hI.congr hae)
  rw [integral_congr_ae hae, hmp.integral_comp' Φ, integral_prod Φ hIp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
  simp only [Φ]
  rw [integral_smul]
  rfl

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.OJ
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TripleIntegrandMeasurable
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem meas_G (γ : Mx k r) (b : ℝ) :
    Measurable (fun pp : B.SS k r =>
      ‖B.gN (Matrix.of pp.1.1 * Matrix.of pp.1.2 * γ * (Matrix.of pp.2.2)⁻¹ * (Matrix.of pp.2.1)⁻¹) ^ (-b)‖ₑ) := by
  have hi := B2x1.invM_meas (k := k) (r := r)
  have m1 : Measurable (fun pp : B.SS k r => pp.1.1) := measurable_fst.fst
  have m2 : Measurable (fun pp : B.SS k r => pp.1.2) := measurable_fst.snd
  have m3 : Measurable (fun pp : B.SS k r => B2.invM pp.2.2) := hi.comp measurable_snd.snd
  have m4 : Measurable (fun pp : B.SS k r => B2.invM pp.2.1) := hi.comp measurable_snd.fst
  have mγ : Measurable (fun _ : B.SS k r => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) := measurable_const
  have M := meas_matmul (meas_matmul (meas_matmul (meas_matmul m1 m2) mγ) m3) m4
  have hg : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => B.gN (Matrix.of y)) := gN_cont.comp mt_cont
  exact ((hg.measurable.comp M).pow_const (-b)).enorm

def Phi3 (e1 e2 : Mx k r → ℂ) (γi : Mx k r) (x : Formalism.QuantumDeterminants.Mt k r) (p q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ * ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γi * Matrix.of x))‖ₑ

theorem triple_integrand_measurable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    {X : α → Formalism.QuantumDeterminants.Mt k r} {Pp Qq : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Continuous X) (hP : Continuous Pp) (hQ : Continuous Qq) :
    Measurable (fun t => Phi3 e1 e2 γi (X t) (Pp t) (Qq t)) := by
  unfold Phi3
  exact ((he1.comp (((mt_cont.comp hP.fst).matrix_mul (mt_cont.comp hP.snd)).matrix_mul
    (mt_cont.comp hX))).enorm.measurable).mul
    ((he2.comp (((mt_cont.comp hQ.fst).matrix_mul (mt_cont.comp hQ.snd)).matrix_mul
    (continuous_const.matrix_mul (mt_cont.comp hX)))).enorm.measurable)

theorem triple_lintegral_product {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (x : Formalism.QuantumDeterminants.Mt k r) :
    (∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂μp) *
      (∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γi * Matrix.of x))‖ₑ ∂μq) =
      ∫⁻ p, ∫⁻ q, Phi3 e1 e2 γi x p q ∂μq ∂μp := by
  simp only [Phi3]
  have ha : Measurable fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ :=
    (he1.comp (((mt_cont.comp continuous_fst).matrix_mul (mt_cont.comp continuous_snd)).matrix_mul
      continuous_const)).enorm.measurable
  rw [← lintegral_mul_const _ ha]
  refine lintegral_congr fun p => ?_
  rw [lintegral_const_mul' _ _ enorm_ne_top]

theorem triple_lintegral_swap {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    (μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    [SFinite μG] [SFinite μp] [SFinite μq] :
    ∫⁻ x, ∫⁻ p, ∫⁻ q, Phi3 e1 e2 γi x p q ∂μq ∂μp ∂μG =
      ∫⁻ p, ∫⁻ q, ∫⁻ x, Phi3 e1 e2 γi x p q ∂μG ∂μq ∂μp := by
  have h1 : Measurable (Function.uncurry fun (x : Formalism.QuantumDeterminants.Mt k r)
      (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => ∫⁻ q, Phi3 e1 e2 γi x p q ∂μq) := by
    have hm := triple_integrand_measurable he1 he2 γi
      (α := (Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
      (X := fun z => z.1.1) (Pp := fun z => z.1.2) (Qq := fun z => z.2)
      (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst) continuous_snd
    exact hm.lintegral_prod_right'
  rw [lintegral_lintegral_swap h1.aemeasurable]
  refine lintegral_congr fun p => ?_
  have h2 : Measurable (Function.uncurry fun (x : Formalism.QuantumDeterminants.Mt k r)
      (q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => Phi3 e1 e2 γi x p q) :=
    triple_integrand_measurable he1 he2 γi (X := fun z : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => z.1)
      (Pp := fun _ => p) (Qq := fun z => z.2) continuous_fst continuous_const continuous_snd
  exact lintegral_lintegral_swap h2.aemeasurable

end Formalism.FourierDecayAlt.P.S3dx4
end
end

