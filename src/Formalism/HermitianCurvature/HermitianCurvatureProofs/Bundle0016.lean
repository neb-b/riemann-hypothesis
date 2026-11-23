module

public import Formalism.HermitianCurvature.Bundle0004
public import Formalism.HermitianCurvature.StatementLE
public import Formalism.HermitianCurvature.StatementWd
public import Formalism.HermitianCurvature.StatementTB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0015
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockStartPoints
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0012
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0011
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0014
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0009

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockEstimatesSumForm
section
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.BaseGramNonnegativity

open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB

theorem sum_re_nonneg {α : Type} (Y : Finset α) (κ G : α → α → ℂ) (hκ : PSDOn Y κ) (hG : PSDOn Y G) :
    0 ≤ (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * G h h').re := by
  have H := (Matrix.PosSemidef.hadamard hκ hG).re_dotProduct_nonneg (fun _ => (1 : ℂ))
  simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply,
    star_one, one_mul, mul_one, RCLike.re_to_complex] at H
  convert H using 2
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Finset.sum_coe_sort Y]

variable {E W : Type} [Field E] (D : Data E W)

theorem baseGram_nonneg (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ :=
  div_nonneg (sum_re_nonneg Y κ _ hκ (hG ε hε k w Y)) (hW w).le

theorem Wb_mono {n m : ℕ} (h : n ≤ m) : D.Wb n ⊆ D.Wb m := by
  intro x hx
  simp only [Data.Wb, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans h⟩

theorem estBlockOfSumForm_ok : EstBlockOfSumForm := by
  intro E W _ D C₄ hG hW hSF ε hε i s hs hsi hir w hw hcnt hvol
  obtain ⟨Mv, hMv, θ, hθ, hb⟩ := hSF ε hε i s hs hsi hir w hw hcnt hvol
  have hsub : D.Wb (D.cnt w + s * D.K) ⊆ D.Wb (D.cnt w + (s + 1) * D.K) :=
    Wb_mono D (by nlinarith)
  have hext : ∀ g : W → ℝ, ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K), θ w' * g w' =
      ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * g w' := by
    intro g
    symm
    refine Finset.sum_subset hsub (fun x _ hx => ?_)
    rw [hθ.2.1 x hx, zero_mul]
  refine ⟨θ, ⟨hθ.1, fun a ha => hθ.2.1 a (fun h => ha (hsub h)), ?_⟩, ?_⟩
  · have := hext (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hθ.2.2]
  · intro Y hY κ hκ t₀ S hS
    have h := hb Y hY κ hκ t₀ S hS
    rw [hext]
    have hX : 0 ≤ ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * D.N0 ε (i - s) w' Y κ :=
      Finset.sum_nonneg (fun w' _ => mul_nonneg (hθ.1 w') (baseGram_nonneg D hG hW hε _ _ Y κ hκ))
    exact h.trans (mul_le_mul_of_nonneg_right hMv hX)

end Formalism.FourierDecayAlt.P.BaseGramNonnegativity

theorem Formalism.FourierDecayAlt.P.blockEstimateOfCosetSum : Formalism.FourierDecayAlt.crystallineComparison.EstBlockOfSumForm :=
  Formalism.FourierDecayAlt.P.BaseGramNonnegativity.estBlockOfSumForm_ok
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DegreeOfProdLinearLe
section
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset

open MvPolynomial

end Formalism.FourierDecayAlt.P.LEx2
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.KroneckerEmbedMulApply
section
namespace Formalism.FourierDecayAlt.P.Wd2

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

section Units

variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

end Units

section Entries

variable {K B : Type} [CommRing K] [Ring B] [Algebra K B]

end Entries

section Slots

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

end Slots

section Start

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem io_smul (c : K) (x : A) : (io (c • x) : SlopeTestRemainingChoices S A) = c • io x := by
  ext x y
  simp only [io, Matrix.scalar_apply, Matrix.smul_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem liftMatrix_eq_map_scalar (M : M2 A) : (lift0 M : M2 (SlopeTestRemainingChoices S A)) = M.map (Matrix.scalar (Ix S)) := rfl

theorem firstEmbed_liftMatrix (M : M2 A) :
    E1 (lift0 M : M2 (SlopeTestRemainingChoices S A)) = (E1 M).map (Matrix.scalar (Ix S)) := by
  ext p q
  simp only [E1, lift0, io, Matrix.of_apply, Matrix.map_apply, Matrix.map_apply]
  split_ifs <;> simp

theorem secondEmbed_liftMatrix (M : M2 A) :
    E2 (lift0 M : M2 (SlopeTestRemainingChoices S A)) = (E2 M).map (Matrix.scalar (Ix S)) := by
  ext p q
  simp only [E2, lift0, io, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp

theorem core_map (c : K) :
    c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A) =
      (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A).map (Matrix.scalar (Ix S)) := by
  have hsc : ∀ x : A, Matrix.scalar (Ix S) (c • x) = c • Matrix.scalar (Ix S) x := io_smul c
  ext p q : 1
  simp only [Pf, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply]
  split_ifs <;> simp [map_sub, map_neg, hsc]

theorem J_map : YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) = (YangianSpanCharacter.T.J A).map (Matrix.scalar (Ix S)) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J] <;>
    (try (ext x y; simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.smul_apply]; split_ifs <;> simp))

theorem smulJ_map (c : K) :
    algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) =
      (algebraMap K A c • YangianSpanCharacter.T.J A).map (Matrix.scalar (Ix S)) := by
  have hsc : ∀ x : A, Matrix.scalar (Ix S) (c • x) = c • Matrix.scalar (Ix S) x := io_smul c
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J, Algebra.algebraMap_eq_smul_one, hsc] <;>
    (try (ext x y; simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.smul_apply]; split_ifs <;> simp))

theorem rtt_lift0 (M N : M2 A) (c : K)
    (H : (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E1 M * E2 N =
      E2 N * E1 M * (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A)) :
    (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) *
        E1 (lift0 M) * E2 (lift0 N) =
      E2 (lift0 N) * E1 (lift0 M) *
        (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) := by
  rw [core_map, firstEmbed_liftMatrix, secondEmbed_liftMatrix, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

theorem det_lift0 (M M' : M2 A) (c : K) (H : M'ᵀ * YangianSpanCharacter.T.J A * M = algebraMap K A c • YangianSpanCharacter.T.J A) :
    (lift0 M' : M2 (SlopeTestRemainingChoices S A))ᵀ * YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * lift0 M = algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
  rw [smulJ_map, liftMatrix_eq_map_scalar, liftMatrix_eq_map_scalar, J_map, ← Matrix.transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

theorem det_lift0' (M M' : M2 A) (c : K) (H : M * YangianSpanCharacter.T.J A * M'ᵀ = algebraMap K A c • YangianSpanCharacter.T.J A) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A)) * YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * (lift0 M')ᵀ = algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
  rw [smulJ_map, liftMatrix_eq_map_scalar, liftMatrix_eq_map_scalar, J_map, ← Matrix.transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

theorem liftMatrix_conjTranspose [StarRing A] (M : M2 A) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A))ᴴ = lift0 Mᴴ := by
  ext i j x y
  simp [lift0, io, Matrix.conjTranspose_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.star_apply]
  split_ifs <;> simp_all [@eq_comm _ y x]

theorem d0_one : (d0 (1 : SlopeTestRemainingChoices S A)) = 1 := by
  unfold d0
  exact Matrix.diagonal_one

end Start

end Formalism.FourierDecayAlt.P.Wd2

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

theorem initial_module_structure : Formalism.FourierDecayAlt.Wd.StartModule := by
  intro K A S _ _ _ _ _ _ _ _ QQ q hS
  refine ⟨star_one _, fun Y _ hY => ?_, fun Y _ Y' _ => ?_, fun Y _ _ => ?_, hS.q_real⟩
  · rw [Formalism.FourierDecayAlt.P.Wd2.d0_one, one_mul, Formalism.FourierDecayAlt.P.Wd2.liftMatrix_conjTranspose, hS.herm Y hY]
  · exact Formalism.FourierDecayAlt.P.Wd2.rtt_lift0 (QQ Y') (QQ Y) (Y' - Y) (hS.rtt Y Y')
  · exact ⟨Formalism.FourierDecayAlt.P.Wd2.det_lift0 (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).1,
      Formalism.FourierDecayAlt.P.Wd2.det_lift0' (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).2⟩

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaEprimeFromSteps
section
namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem smoothLog_sc (c : Cut) (ε : ℝ) (m : ℕ) : SmoothLog (c.sc ε m) := by
  unfold SmoothLog Cut.sc
  exact (c.smooth.comp (Real.contDiff_exp.div_const ε)).pow m






theorem thetaForm : ThetaForm := by
  intro ε σ hε v
  unfold th
  have h1 : Real.exp v / (Real.exp v + ε) = (1 + ε * Real.exp (-v))⁻¹ := by
    rw [Real.exp_neg]; have := Real.exp_pos v; field_simp
  have h2 : 0 ≤ 1 + ε * Real.exp (-v) := by positivity
  rw [h1, Real.inv_rpow h2, Real.rpow_neg h2]

theorem thetaSmooth : ThetaSmooth := by
  intro ε σ hε
  unfold SmoothLog
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ) := by
    funext u; exact thetaForm ε σ hε u
  rw [this]
  refine ContDiff.rpow_const_of_ne ?_ ?_
  · exact contDiff_const.add (contDiff_const.mul (Real.contDiff_exp.comp contDiff_neg))
  · intro u; positivity

theorem thetaBound : ThetaBound := by
  intro hC σ ε hσ hε p x hx
  unfold ld
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ) := by
    funext u; exact thetaForm ε σ hε u
  rw [this]
  have h := hC σ ε hσ hε p (Real.log x)
  rwa [← thetaForm ε σ hε (Real.log x), Real.exp_log hx] at h

theorem iterDeriv_const' (p : ℕ) (k t : ℝ) : iteratedDeriv p (fun _ : ℝ => k) t = if p = 0 then k else 0 := by
  cases p with
  | zero => simp
  | succ n => simp [iteratedDeriv_succ']

theorem cutBound : CutBound := by
  intro c m p hm
  set h : ℝ → ℝ := fun t => c.χ (Real.exp t) ^ m with hh
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := (c.smooth.comp Real.contDiff_exp).pow m
  have hcont : Continuous (iteratedDeriv p h) := hsm.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  have hlow : ∀ t, t < Real.log (1/2) → iteratedDeriv p h t = 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have : Real.exp s ≤ 1/2 := by
        have := Real.exp_lt_exp.mpr hs
        rw [Real.exp_log (by norm_num)] at this; exact this.le
      simp only [hh, c.zero _ this]
      exact zero_pow (by omega)
    rw [this.iteratedDeriv_eq p, iterDeriv_const']; simp
  have hhigh : ∀ t, 0 < t → iteratedDeriv p h t = if p = 0 then 1 else 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      have : 1 ≤ Real.exp s := Real.one_le_exp (le_of_lt hs)
      simp [hh, c.one _ this]
    rw [this.iteratedDeriv_eq p, iterDeriv_const']
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := Real.log (1/2)) (b := 0)).exists_bound_of_continuousOn hcont.continuousOn
  have hbd : ∀ t, |iteratedDeriv p h t| ≤ max C0 1 := by
    intro t
    rcases lt_or_ge t (Real.log (1/2)) with h1 | h1
    · rw [hlow t h1]; simp
    · rcases lt_or_ge 0 t with h2 | h2
      · rw [hhigh t h2]; split_ifs <;> simp
      · exact (hC0 t ⟨h1, h2⟩).trans (le_max_left _ _)
  have key : ∀ ε x : ℝ, 0 < ε → ld p (c.sc ε m) x = iteratedDeriv p h (Real.log x - Real.log ε) := by
    intro ε x hε
    unfold ld
    have : (fun u : ℝ => c.sc ε m (Real.exp u)) = fun u : ℝ => h (u - Real.log ε) := by
      funext u; simp only [hh, Cut.sc]; rw [Real.exp_sub, Real.exp_log hε]
    rw [this, iteratedDeriv_comp_sub_const]
  refine ⟨max C0 1, fun ε x hε hx => ?_⟩
  rw [key ε x hε]
  refine ⟨hbd _, fun hlt => hlow _ ?_, fun hlt => hhigh _ ?_⟩
  · rw [← Real.log_div hx.ne' hε.ne']
    refine Real.log_lt_log (by positivity) ?_
    rw [div_lt_iff₀ hε]; linarith
  · have := Real.log_lt_log hε hlt; linarith

end Formalism.FourierDecayAlt.P.LEx1
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantIntegrals
section
open MeasureTheory Set

noncomputable section

namespace Formalism.FourierDecayAlt.P.MajorantIntegrals

open Formalism.FourierDecayAlt.crystallineComparison

theorem radial_eq (K : ℕ) (x : ℝ) (hx : 0 < x) (y : ℝ) (hy : 0 < y) :
    y ^ (Module.finrank ℝ ℂ - 1) • mfac K x y =
      if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K) := by
  rw [Complex.finrank_real_complex]
  simp only [mfac, hy.ne', if_false, smul_eq_mul, show 2 - 1 = 1 from rfl, pow_one]
  split_ifs with hxy
  · rw [min_eq_left (one_le_pow₀ ((one_le_div hy).mpr hxy)), mul_one]
  · push Not at hxy
    have h1 : (x / y) ^ K ≤ 1 :=
      pow_le_one₀ (div_nonneg hx.le hy.le) ((div_le_one hy).mpr hxy.le)
    rw [min_eq_right h1, Real.rpow_sub hy, Real.rpow_one, Real.rpow_natCast, div_pow]
    field_simp

theorem volC : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
  simp [Measure.real, Complex.volume_ball]

theorem majIntegral_ok : MajIntegral := by
  intro K x hK hx
  have hK' : (2 : ℝ) < K := by exact_mod_cast hK
  have hcongr : EqOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • mfac K x y)
      (fun y => if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K)) (Ioi 0) :=
    fun y hy => radial_eq K x hx y hy
  have hIoc : IntegrableOn (fun y : ℝ => y) (Ioc 0 x) :=
    (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hIoi : IntegrableOn (fun y : ℝ => x ^ K * y ^ ((1 : ℝ) - K)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hx).const_mul _
  have hA : IntegrableOn (fun y : ℝ => if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K)) (Ioc 0 x) :=
    hIoc.congr_fun (fun y hy => by simp [hy.2]) measurableSet_Ioc
  have hB : IntegrableOn (fun y : ℝ => if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K)) (Ioi x) :=
    hIoi.congr_fun (fun y hy => by simp [not_le.mpr (mem_Ioi.mp hy)]) measurableSet_Ioi
  have hint : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • mfac K x y) (Ioi 0) := by
    refine IntegrableOn.congr_fun ?_ hcongr.symm measurableSet_Ioi
    rw [← Ioc_union_Ioi_eq_Ioi hx.le]
    exact hA.union hB
  refine ⟨(integrable_fun_norm_addHaar volume (f := mfac K x)).mpr hint, ?_⟩
  rw [integral_fun_norm_addHaar volume (mfac K x), setIntegral_congr_fun measurableSet_Ioi hcongr,
    ← Ioc_union_Ioi_eq_Ioi hx.le,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hA hB,
    setIntegral_congr_fun measurableSet_Ioc (fun y hy => if_pos hy.2),
    setIntegral_congr_fun measurableSet_Ioi (fun y hy => if_neg (not_le.mpr (mem_Ioi.mp hy))),
    ← intervalIntegral.integral_of_le hx.le, integral_id, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) hx, volC, Complex.finrank_real_complex]
  have e : x ^ K * x ^ ((1 : ℝ) - K + 1) = x ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx]
    rw [show (K : ℝ) + (1 - K + 1) = ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hK2 : (K : ℝ) - 2 ≠ 0 := by linarith
  have hK3 : (1 : ℝ) - K + 1 ≠ 0 := by linarith
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  rw [neg_div, mul_neg, ← mul_div_assoc, e]
  have hK4 : (1 : ℝ) - K + 1 = -((K : ℝ) - 2) := by ring
  rw [hK4]
  field_simp
  ring

theorem majIntegralProd_ok : MajIntegralProd := by
  intro f K x hK hx
  have h1 := fun v => (majIntegral_ok K (x v) hK (hx v))
  refine ⟨Integrable.fintype_prod (f := fun v (l : ℂ) => mfac K (x v) ‖l‖)
    (μ := fun _ => volume) (fun v => (h1 v).1), ?_⟩
  have h2 := integral_fintype_prod_volume_eq_prod (ι := Fin f) (E := fun _ => ℂ)
    (fun v (l : ℂ) => mfac K (x v) ‖l‖)
  exact h2.trans (Finset.prod_congr rfl (fun v _ => (h1 v).2))

end Formalism.FourierDecayAlt.P.MajorantIntegrals
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasIterDeriv
section
namespace Formalism.FourierDecayAlt.P.LEx2.A3
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section

def DsMeas : Prop := ∀ (B : Base) (S : Step B), S.Meas → S.I4 → ∀ Y ∈ S.J, ∀ (p : ℕ) k, Measurable fun ω => S.ds Y p ω k

theorem meas_iterDeriv {Ω : Type} [MeasurableSpace Ω] (F : ℝ → Ω → ℂ)
    (hsm : ∀ ω, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => F s ω)) (hm : ∀ s, Measurable (F s)) :
    ∀ (p : ℕ) (s : ℝ), Measurable (fun ω => iteratedDeriv p (fun s => F s ω) s) := by
  intro p
  induction p with
  | zero => intro s; simpa using hm s
  | succ p ih =>
    intro s
    have hlim : ∀ ω, Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ •
        (iteratedDeriv p (fun s => F s ω) (s + 1 / ((n : ℝ) + 1)) - iteratedDeriv p (fun s => F s ω) s)) atTop
        (𝓝 (iteratedDeriv (p + 1) (fun s => F s ω) s)) := by
      intro ω
      have hd : Differentiable ℝ (iteratedDeriv p (fun s => F s ω)) :=
        (hsm ω).differentiable_iteratedDeriv p (by exact_mod_cast WithTop.coe_lt_top _)
      have h1 := (hd s).hasDerivAt.tendsto_slope_zero
      rw [iteratedDeriv_succ]
      refine h1.comp ?_
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      exact Filter.Eventually.of_forall (fun n => by
        have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact this.ne')
    refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) ω => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ •
        (iteratedDeriv p (fun s => F s ω) (s + 1 / ((n : ℝ) + 1)) - iteratedDeriv p (fun s => F s ω) s)) ?_ ?_
    · intro n
      exact ((ih _).sub (ih _)).const_smul (((1 : ℝ) / ((n : ℝ) + 1))⁻¹)
    · exact tendsto_pi_nhds.2 hlim

theorem dsMeas : DsMeas := by
  intro B S hMeas hI4 Y hY p k
  obtain ⟨c, hc⟩ := hI4 Y hY
  have := meas_iterDeriv (fun s ω => S.gs Y s ω k) (fun ω => by
      have : (fun s : ℝ => S.gs Y s ω k) = fun s : ℝ => ∑ q ∈ range (S.r + 1 + 1), (s : ℂ) ^ q * c q ω k := by
        funext s; exact hc s ω k
      rw [this]
      apply ContDiff.sum
      intro q _
      exact (Complex.ofRealCLM.contDiff.pow q).mul contDiff_const)
    (fun s => (hMeas.2.2 Y hY).2 s k) p 0
  exact this

end
end Formalism.FourierDecayAlt.P.LEx2.A3
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneLevelInequalitySplitBySize
section
namespace Formalism.FourierDecayAlt.P

theorem one_level_inequality_split_by_size : Formalism.FourierDecayAlt.TB.OneLevel :=
  levelInequalityOfSteps splitByLastSize schurRecursion_true diagStep
    singleBlockStep longBlockStep

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaAtBasePointZero
section
open Set Filter Topology Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

theorem theta_at_base_point_zero : th TT α (x0 TT) = 0 := by
  simp [th, prim_eq]

theorem exp_base_point_eq (hTT : 0 ≤ TT) : Complex.exp (x0 TT) = ((TT + 1 : ℝ) : ℂ) := by
  rw [x0, ← Complex.ofReal_exp, Real.exp_log (by linarith)]

theorem circleMap_eq (hTT : 0 ≤ TT) (θ : ℝ) : circleMap 0 (TT + 1) θ = Complex.exp (x0 TT + (θ : ℂ) * I) := by
  simp [circleMap, Complex.exp_add, exp_base_point_eq hTT]

theorem vert_mem (hTT : 0 ≤ TT) (θ : ℝ) : x0 TT + (θ : ℂ) * I ∈ Hh TT := by
  show TT < Complex.normSq (Complex.exp (x0 TT + (θ : ℂ) * I))
  rw [Complex.exp_add, exp_base_point_eq hTT, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp_ofReal_mul_I]
  nlinarith

theorem circleIntegral_eq (hTT : 0 ≤ TT) :
    circleIntegral α 0 (TT + 1) = ∫ θ in (0 : ℝ)..2 * Real.pi, I * bet α (x0 TT + (θ : ℂ) * I) := by
  unfold circleIntegral
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [deriv_circleMap, smul_eq_mul, circleMap_eq hTT θ, bet]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

