module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0149
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0120
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0148
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0078
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRCentre
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0145
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0144
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRMatFrom
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0070
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.WbPartOfInWb
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.GsFramesOfIso

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AeSS
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem ae_mem_UWset_and_mem_Nset {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] :
    ∀ᵐ p ∂(D.μW.prod D.μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ Formalism.QuantumDeterminants.UWset k r D.z := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => hx) D.haarW.conc
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Formalism.QuantumDeterminants.Nset k r := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => hx) D.haarN.conc
  exact (Measure.quasiMeasurePreserving_fst.ae hW).and (Measure.quasiMeasurePreserving_snd.ae hN)

set_option maxHeartbeats 800000 in
theorem quadB_of (hNI : NormInv) (hGS : GrowthS) (hGG : GrowthG) (hDD : DecDD) (hIn : Inputs) {k r : ℕ}
    {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    {u : Fin k → ℝ} {νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hS1 : Side k r ε lam h σ w0 D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq)
    {l : H → Wp}
    (hbe : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z Formalism.QuantumDeterminants.cStd D.π σ D.μW D.μN x y = (innerSL ℂ (l y)).smulRight (l x)) :
    ∫⁻ zz, ∫⁻ zz', ∫⁻ s,
      ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
        ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
      ∂(muSof D.μW D.μN) ∂νq ∂νq < ⊤ := by
  have hS1' := hS1
  obtain ⟨hl, hds, -, hG, hw0, hz1, hT, -, hπ, hW, hN, hGm, hq⟩ := hS1'
  have : SigmaFinite D.μW := hW.1
  have : SigmaFinite D.μN := hN.1
  have : SigmaFinite D.μG := hGm.1
  have hGc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hGm.2.2.1
  have hw0DD := cmHalfIntegralGenerator_mem_algebraicClosure hds w0
  have hf1 := DDSmoothness.muSof_facts hW hN
  have hae1 := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hf1.1 hf1.2 hq
  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  swap
  · push Not at hA
    calc _ ≤ ∫⁻ zz, (0 : ℝ≥0∞) ∂νq := by
          apply lintegral_mono_ae
          filter_upwards [hae1] with zz hzz
          simp [hA _ (dd_stable hds hzz w0 hw0DD)]
      _ < ⊤ := by simp
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨e0, he0, hee0⟩ := coef_ext hds w0 w0
  obtain ⟨e1, he1, hee1⟩ := coef_ext hds v w0
  obtain ⟨C0, hC0⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD
    w0 hw0DD
  obtain ⟨C1, hC1⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD v hv
  have hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee0 y hy]; exact hC0 y hy
  have hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee1 y hy]; exact hC1 y hy
  have h4 := gap4 hG
  have hAG := ag_nonneg k r
  have hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  obtain ⟨ee, heedef⟩ : ∃ ee : ℝ, ee = AG k r + 1 := ⟨_, rfl⟩
  have hee0' : 0 ≤ ee := by rw [heedef]; linarith
  have heea : ee ≤ aOf r h := by rw [heedef]; linarith
  have hLs : ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-ee)‖ₑ ∂(D.μW.prod D.μN) < ⊤ :=
    (hGS k r D.z D.μW D.μN D.μG νq ee hz1 hT hW hN hGm hq (by rw [heedef]; linarith)).hasFiniteIntegral
  obtain ⟨Ls, hLsdef⟩ : ∃ Ls : ℝ≥0∞, Ls = ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-ee)‖ₑ ∂(D.μW.prod D.μN) :=
    ⟨_, rfl⟩
  rw [← hLsdef] at hLs
  have hKg : ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ ∂D.μG < ⊤ :=
    (hGG k r D.μG _ hGm (by rw [heedef]; linarith)).hasFiniteIntegral
  have hpUH : ∀ᵐ p ∂(D.μW.prod D.μN), Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    (prod_ae hW hN).mono fun p hp => DDSmoothness.uh_mul hp.1.1 hp.2.1
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ≥0∞, K1 = ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ := ⟨_, rfl⟩
  have hK : K1 * K1 ≠ ⊤ := by rw [hK1]; simp [ENNReal.mul_eq_top]
  have hA1m := Aext_meas he1
  have hI1m := Iint_meas hA1m (D.μW.prod D.μN)
  obtain ⟨LL, hLL⟩ : ∃ LL : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, LL = Lam1 e0 (D.μW.prod D.μN) := ⟨_, rfl⟩
  have hLLm : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => LL t.1 t.2) := by
    rw [hLL]; exact measurable_lambda_integral he0 (D.μW.prod D.μN)
  have step1 : ∀ᵐ zz ∂νq, ∀ᵐ zz' ∂νq, ∫⁻ s,
      ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
        ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
      ∂(muSof D.μW D.μN) ≤
      (K1 * K1) * (Iint (Aext e1) (D.μW.prod D.μN) zz * (Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz')) := by
    filter_upwards [hae1] with zz hzz
    filter_upwards [hae1] with zz' hzz'
    have bl : ‖l (σ (Matrix.of zz) w0)‖ₑ ≤ K1 * Iint (Aext e1) (D.μW.prod D.μN) zz := by
      rw [hK1]; exact l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hee1 hzz
    have bl' : ‖l (σ (Matrix.of zz') w0)‖ₑ ≤ K1 * Iint (Aext e1) (D.μW.prod D.μN) zz' := by
      rw [hK1]; exact l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hee1 hzz'
    have hc : ‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ ≠ ⊤ :=
      ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
    have hqi := quad_inner1 hds w0 he0 hee0 hf1.2 hzz hzz'
    rw [← hLL] at hqi
    simp only [← enorm_eq_nnnorm]
    calc ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ *
          ‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ ∂(muSof D.μW D.μN)
        = ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ *
          (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ) ∂(muSof D.μW D.μN) :=
          lintegral_congr fun s => mul_assoc _ _ _
      _ = (∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof D.μW D.μN)) *
          (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ) := lintegral_mul_const' _ _ hc
      _ = LL zz zz' * (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ) := by rw [hqi]
      _ ≤ LL zz zz' * ((K1 * Iint (Aext e1) (D.μW.prod D.μN) zz) * (K1 * Iint (Aext e1) (D.μW.prod D.μN) zz')) := by
          gcongr
      _ = (K1 * K1) * (Iint (Aext e1) (D.μW.prod D.μN) zz * (Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz')) := by
          ring
  have hinvR : ∀ zz, ∀ᵐ z ∂νq, ∀ᵐ q ∂(D.μW.prod D.μN),
      LL zz (fun i j => (Matrix.of q.1 * Matrix.of q.2 * Matrix.of z) i j) = LL zz z := by
    intro zz
    rw [hLL]
    exact Filter.Eventually.of_forall fun z => (ae_mem_UWset_and_mem_Nset D).mono
      fun q hq0 => lambda_right_translation he0 D.haarW D.haarN hz1 hT hq0.1 hq0.2 zz z
  have hinvL : ∀ᵐ z ∂νq, ∀ᵐ p ∂(D.μW.prod D.μN),
      (∫⁻ y, Aext e1 y * LL (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) y ∂D.μG) =
        ∫⁻ y, Aext e1 y * LL z y ∂D.μG := by
    rw [hLL]
    exact Filter.Eventually.of_forall fun z => (prod_ae hW hN).mono
      fun p hp0 => lintegral_congr fun y => by rw [lambda_left_translation he0 hW hN hz1 hp0.1 hp0.2 z y]
  have hLz : ∀ zz, Measurable (fun y => LL zz y) := fun zz => hLLm.comp (measurable_const.prodMk measurable_id)
  have hΦm : Measurable (fun x => ∫⁻ y, Aext e1 y * LL x y ∂D.μG) :=
    ((hA1m.comp measurable_snd).mul hLLm).lintegral_prod_right'
  obtain ⟨Fx, hFx⟩ : ∃ Fx : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, Fx = fun x => ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ :=
    ⟨_, rfl⟩
  have hFxm : Measurable Fx := by
    rw [hFx]; exact (((gN_cont.comp mt_cont).measurable).pow_const _).enorm
  have hKg' : ∫⁻ x, Fx x ∂D.μG < ⊤ := by rw [hFx]; exact hKg
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ≥0∞, c = ENNReal.ofReal |C1| * ENNReal.ofReal |C1| * (ENNReal.ofReal |C0| * Ls) :=
    ⟨_, rfl⟩
  have hc : c ≠ ⊤ := by
    rw [hcdef]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLs.ne)
  have hgpos : ∀ x : Mx k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → 0 < B.gN x :=
    fun x hx => lt_of_lt_of_le one_pos ((hNI k r).2 x hx).2
  have hpt : ∀ᵐ x ∂D.μG, Aext e1 x * ∫⁻ y, Aext e1 y * LL x y ∂D.μG ≤ ∫⁻ y, c * (Fx x * Fx y) ∂D.μG := by
    filter_upwards [hGc] with x hx
    rw [← lintegral_const_mul' (Aext e1 x) _ (by unfold Aext; exact enorm_ne_top)]
    apply lintegral_mono_ae
    filter_upwards [hGc] with y hy
    have hL := lambda_integral_bound hNI hb0e hee0' heea hpUH hx hy
    rw [← hLL, ← hLsdef] at hL
    have hx0 := hgpos _ hx
    have hy0 := hgpos _ hy
    have w1 := e_weight (b := ee) hb1 hx hx0
    have w2 := e_weight (b := ee) hb1 hy hy0
    have split : ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ ee) =
        ENNReal.ofReal |C0| * (ENNReal.ofReal (B.gN (Matrix.of x) ^ ee) * ENNReal.ofReal (B.gN (Matrix.of y) ^ ee)) := by
      rw [Real.mul_rpow hx0.le hy0.le, ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hx0.le _)]
    have hFxx : Fx x = ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ := by rw [hFx]
    have hFxy : Fx y = ‖B.gN (Matrix.of y) ^ (-(aOf r h - ee))‖ₑ := by rw [hFx]
    calc Aext e1 x * (Aext e1 y * LL x y)
        ≤ Aext e1 x * (Aext e1 y * (ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ ee) * Ls)) := by
          gcongr
      _ = (Aext e1 x * ENNReal.ofReal (B.gN (Matrix.of x) ^ ee)) *
            (Aext e1 y * ENNReal.ofReal (B.gN (Matrix.of y) ^ ee)) * (ENNReal.ofReal |C0| * Ls) := by
          rw [split]; ring
      _ ≤ (ENNReal.ofReal |C1| * Fx x) * (ENNReal.ofReal |C1| * Fx y) * (ENNReal.ofReal |C0| * Ls) := by
          rw [hFxx, hFxy]
          exact mul_le_mul' (mul_le_mul' w1 w2) le_rfl
      _ = c * (Fx x * Fx y) := by rw [hcdef]; ring
  calc _ ≤ ∫⁻ zz, ∫⁻ zz', (K1 * K1) * (Iint (Aext e1) (D.μW.prod D.μN) zz *
          (Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz')) ∂νq ∂νq :=
        lintegral_mono_ae (step1.mono fun zz h => lintegral_mono_ae h)
    _ = (K1 * K1) * ∫⁻ zz, Iint (Aext e1) (D.μW.prod D.μN) zz *
          ∫⁻ zz', Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz' ∂νq ∂νq :=
        pull2 _ _ _ hK (fun zz => hI1m.mul (hLz zz))
    _ = (K1 * K1) * ∫⁻ zz, Iint (Aext e1) (D.μW.prod D.μN) zz * ∫⁻ y, Aext e1 y * LL zz y ∂D.μG ∂νq := by
        congr 1; apply lintegral_congr; intro zz; congr 1
        exact unfold_Iint hq hA1m (hLz zz) (hinvR zz)
    _ = (K1 * K1) * ∫⁻ x, Aext e1 x * ∫⁻ y, Aext e1 y * LL x y ∂D.μG ∂D.μG := by
        congr 1
        exact unfold_Iint hq hA1m hΦm hinvL
    _ ≤ (K1 * K1) * ∫⁻ x, ∫⁻ y, c * (Fx x * Fx y) ∂D.μG ∂D.μG := by
        gcongr 1
        exact lintegral_mono_ae hpt
    _ = (K1 * K1) * (c * ((∫⁻ x, Fx x ∂D.μG) * ∫⁻ y, Fx y ∂D.μG)) := by rw [final2 Fx hFxm hc]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK)
          (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) (ENNReal.mul_lt_top hKg' hKg'))

end Formalism.FourierDecayAlt.P.S3dx4
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
section
namespace Formalism.FourierDecayAlt.P.BXiAsm
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem closed_of (hX : XiExists) : LemmaBClosed := Formalism.FourierDecayAlt.P.b_lemmaBClosed_of hX

theorem norm_of (hX : XiExists) : LemmaBNorm :=
  Formalism.FourierDecayAlt.Final.lemma_b_norm_of_parts (closed_of hX) Formalism.FourierDecayAlt.Final.conjugation_invariance_all Formalism.FourierDecayAlt.Final.dilation_jacobian_all
    Formalism.FourierDecayAlt.Final.integral_bound_all

theorem any_of (hX : XiExists) : LemmaBAny :=
  Formalism.FourierDecayAlt.Final.lemma_b_from_norm_bound (norm_of hX) Formalism.FourierDecayAlt.Final.integral_norm_bound_variant_b

end Formalism.FourierDecayAlt.P.BXiAsm

namespace Formalism.FourierDecayAlt.P

theorem b_any_of_xi : Formalism.FourierDecayAlt.B2.LemmaBAny := Formalism.FourierDecayAlt.P.BXiAsm.any_of exists_auxiliary_xi

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvTr
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvTr

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem dZb_sub {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w) (hg : DifferentiableAt ℝ g w) :
    NF.dZb (fun x => f x - g x) w = NF.dZb f w - NF.dZb g w := by
  simp only [NF.dZb]
  rw [show (fun x => f x - g x) = f - g from rfl, (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem dzQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have hev : (MA.DQ P).ev M.vz 1 = 0 := by
    apply Subtype.ext
    funext q
    show MA.coordE M.vz q.1 * MA.wirt M.vz (MA.ext ((1 : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = 0
    have hloc : MA.ext (1 : MA.Qp P.r P.TT → ℂ) =ᶠ[nhds q.1] fun _ => (1 : ℂ) := by
      filter_upwards [(MA.Qset_open P.r P.TT).mem_nhds q.2] with x hx
      simp [MA.ext, hx]
    simp [MA.wirt, hloc.fderiv_eq]
  simp only [dzQ, MA.DAlg.dzP, MA.DAlg.mkP]
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vz)) ((MA.DQ P).ev M.vz 1) = 0
  rw [hev, map_zero]

theorem dzbQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzbQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have hev : (MA.DQ P).ev M.vzb 1 = 0 := by
    apply Subtype.ext
    funext q
    show MA.coordE M.vzb q.1 * MA.wirt M.vzb (MA.ext ((1 : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = 0
    have hloc : MA.ext (1 : MA.Qp P.r P.TT → ℂ) =ᶠ[nhds q.1] fun _ => (1 : ℂ) := by
      filter_upwards [(MA.Qset_open P.r P.TT).mem_nhds q.2] with x hx
      simp [MA.ext, hx]
    simp [MA.wirt, hloc.fderiv_eq]
  simp only [dzbQ, MA.DAlg.dzbP, MA.DAlg.mkP]
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vzb)) ((MA.DQ P).ev M.vzb 1) = 0
  rw [hev, map_zero]

theorem actA_ggiA (P : M.Par) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.ggiA P (MA.DQ P)) g ρ = mulQ P ((MA.DQ P).ggiP P.TT) (g ρ) := by
  simp only [MA.actA, MA.ggiA, MA.sc, mulQ, Matrix.scalar_apply]
  refine (Finset.sum_eq_single ρ ?_ ?_).trans ?_
  · intro b _ hb
    simp [Matrix.diagonal, Ne.symm hb]
    rfl
  · intro h
    exact absurd (Finset.mem_univ ρ) h
  · simp [Matrix.diagonal]
    rfl

theorem curvTr_core
    (hmod : ∀ (P : M.Par) (ρ : M.Ty P) (ζ : ℂ), ζ ∈ Ann P →
      NF.dZb (modA P ρ) ζ = -(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2) :
    GTCCurvTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hK A B hAB hC hBA hcurv ρ ζ hζ
  have hTT : 0 ≤ P.TT := tt_nonneg_of_hyp hyp
  have hev : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT),
      ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q :=
    fun Φ σ q => SSTr.trR_apply P Bs hyp.1 hyp.2.1 e he Φ σ q
  have tsub : ∀ (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT),
      ((trR P Bs e (Φ - Ψ) σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q -
          ((trR P Bs e Ψ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := by
    intro Φ Ψ σ q
    rw [hev, hev, hev, Submodule.coe_sub, sub_eq_add_neg, ← neg_one_smul ℂ (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      VLem.rawR_add, VLem.rawR_smul]
    simp [sub_eq_add_neg]
  have tsmul : ∀ (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT),
      ((trR P Bs e (c • Φ) σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        c * ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := by
    intro c Φ σ q
    rw [hev, hev, Submodule.coe_smul, VLem.rawR_smul]
    rfl
  obtain ⟨Φ₀, hΦ₀, -⟩ := SSTr.exists_tr P Bs hyp.1 hyp.2.1 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  have hAs := (hAB ρ).1
  have hBs := (hAB ρ).2
  have hΨ : trR P Bs e ((d.κ (dTy P ρ)).1 Φ₀) ρ = 1 := by
    rw [hK, actA_kap, hΦ₀]
    simp [dTy]
  have hN : trR P Bs e (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀)) ρ = fnZ P (A ρ) := by
    rw [(hC _ ρ).1, hΨ, dzQ_one P hTT, zero_add, mul_one]
  have hS : trR P Bs e (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀)) ρ = fnZ P (B ρ) := by
    rw [(hC _ ρ).2, hΨ, dzbQ_one P hTT, neg_zero, zero_add, mul_one]
  have hSN : trR P Bs e (d.L.nabs.1 (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀))) ρ =
      -dzbQ P (fnZ P (A ρ)) + fnZ P (B ρ) * fnZ P (A ρ) := by
    rw [(hC _ ρ).2, hN]
  have hNS : trR P Bs e (d.L.nab.1 (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀))) ρ =
      dzQ P (fnZ P (B ρ)) + fnZ P (A ρ) * fnZ P (B ρ) := by
    rw [(hC _ ρ).1, hS]
  have hG : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      trR P Bs e (d.L.GGi.1 Φ) ρ = mulQ P ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ ρ) := by
    intro Φ
    rw [((GT.gauge_function_holds Wp Wq P Bs X d hyp e) Φ).2.2.2.2.2, actA_ggiA]
  have hc' : d.L.nabs.1 (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀)) - d.L.nab.1 (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀)) =
      ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) • d.L.GGi.1 (d.L.GGi.1 ((d.κ (dTy P ρ)).1 Φ₀)) :=
    congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 Φ₀) (hcurv ρ)
  have hζQ : (((fun _ => (1 : ℂ)), ζ) : MA.E P.r) ∈ MA.Qset P.r P.TT := ⟨fun _ => one_ne_zero, hζ⟩
  have key := congrArg (fun Φ => ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) ⟨_, hζQ⟩) hc'
  rw [tsub, tsmul, hSN, hNS, hG, hG, hΨ] at key
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_neg, Pi.add_apply, Pi.mul_apply, Pi.neg_apply,
    mulQ_ggiP, Subalgebra.coe_one, Pi.one_apply, dzbQ_apply P hTT, dzQ_apply P hTT,
    fnZ_val P hAs, fnZ_val P hBs] at key
  have hz1 := wirt_fnZ_zb P hAs ⟨_, hζQ⟩
  have hz2 := wirtinger_derivative_fibre_function P hBs ⟨_, hζQ⟩
  dsimp only at hz1 hz2
  rw [hz1, hz2] at key
  have hAd : DifferentiableAt ℝ (A ρ) ζ := (hAs.contDiffAt ((ann_open P).mem_nhds hζ)).differentiableAt (by simp)
  have hmd : DifferentiableAt ℝ (modA P ρ) ζ :=
    ((modA_smooth P ρ hTT).contDiffAt ((ann_open P).mem_nhds hζ)).differentiableAt (by simp)
  have hBeq : B ρ =ᶠ[nhds ζ] fun w => star (A ρ w) := by
    filter_upwards [(ann_open P).mem_nhds hζ] with w hw
    exact hBA ρ w hw
  have hdZB : NF.dZ (B ρ) ζ = star (NF.dZb (A ρ) ζ) := by
    rw [Formalism.FourierDecayAlt.P5.HerB.dZ_eq, hBeq.fderiv_eq, ← Formalism.FourierDecayAlt.P5.HerB.dZ_eq]
    exact Formalism.FourierDecayAlt.P5.HerB.dZ_conj hAd
  change -NF.dZb (A ρ) ζ + B ρ ζ * A ρ ζ - (NF.dZ (B ρ) ζ + A ρ ζ * B ρ ζ) =
    ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ *
      (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ * 1)) at key
  rw [hdZB] at key
  have h2 : -NF.dZb (A ρ) ζ + B ρ ζ * A ρ ζ - (star (NF.dZb (A ρ) ζ) + A ρ ζ * B ρ ζ) =
      -(NF.dZb (A ρ) ζ + star (NF.dZb (A ρ) ζ)) := by ring
  have h4 : ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ *
      (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ * 1)) =
      ((2 * M.aC P ρ * P.TT * ((Complex.normSq ζ - P.TT)⁻¹ * (Complex.normSq ζ - P.TT)⁻¹) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h2, h4] at key
  have h3 := congrArg Complex.re key
  rw [Complex.neg_re, Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re] at h3
  have hx : 0 < Complex.normSq ζ - P.TT := sub_pos.mpr hζ
  rw [dZb_sub hmd hAd, Complex.sub_re, re_dZb_modA P ρ hζ]
  have hw : (NF.dZb (A ρ) ζ).re = -(M.aC P ρ * P.TT) * ((Complex.normSq ζ - P.TT)⁻¹ * (Complex.normSq ζ - P.TT)⁻¹) := by
    linarith
  rw [hw]
  field_simp
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvTr

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem curvature_trace_holds : GTCCurvTr := CurvTr.curvTr_core (fun P ρ ζ hζ => dZb_modA P ρ hζ)

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotK
section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rotation_K_invariance_holds : GTRRotK :=
  gTRRotK_of_mat_fin_centre_sec_ode_wirt rotation_matrix_form_holds rotation_finite_from_matrix rotation_centre_condition rotation_section_holds rotation_ode_holds rotation_wirtinger_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomCut
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ComplexConjugate Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def nuG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  unitH k r (PI.UnitaryGroupMassFormula.GsFr.omW k r z z' g)

def nuG' (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  unitH k r (PI.UnitaryGroupMassFormula.GsFr.omW' k r z z' g)

def PpG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : B.Mat k r :=
  PI.UnitaryGroupMassFormula.GsFr.Pm k r z' - PI.UnitaryGroupMassFormula.GsFr.Rk k r (nuG' z z' g) (nuG' z z' g) * PI.UnitaryGroupMassFormula.GsFr.Pm k r z'

def ioG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : B.Mat k r :=
  PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g * PpG z z' g

def posG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ 0 < Gf k r z z' g}

def geG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ε : ℝ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ ε ≤ Gf k r z z' g}

def GeomSmooth : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    B.CkOn ⊤ (posG k r z z') (nuG z z') ∧ B.CkOn ⊤ (posG k r z z') (nuG' z z') ∧
      B.CkOn ⊤ (posG k r z z') (ioG z z')

def GeomEqvNu : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ h' ∈ UWset k r z', ∀ n' ∈ Nset k r, ∀ g ∈ posG k r z z',
      nuG z z' g = h *ᵥ nuG z z' (h⁻¹ * n⁻¹ * g * n' * h') ∧
        nuG' z z' g = h' *ᵥ nuG' z z' (h⁻¹ * n⁻¹ * g * n' * h')

def GeomEqvIo : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ h' ∈ UWset k r z', ∀ n' ∈ Nset k r, ∀ g ∈ posG k r z z',
      ioG z z' g = h * ioG z z' (h⁻¹ * n⁻¹ * g * n' * h') * h'⁻¹

def GeomAtGq : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 1 ≤ k →
    C2.StdZ k r z → C2.StdZ k r z' → IsSection k r z z' μsec →
    ∀ (c : Fin r → ℂ) (ζ : ℂ), (∀ l, c l ≠ 0) → Tz k r z * Tz k r z' < Complex.normSq ζ →
      nuG z z' (bigCell k r c (μsec ζ)) = phD c • nu0 k r z z' μsec ζ ∧
        nuG' z z' (bigCell k r c (μsec ζ)) = conj (phD c) • nu0' k r z z' μsec ζ ∧
          ioG z z' (bigCell k r c (μsec ζ)) = io0 k r z z' μsec ζ

def GeomBd0 : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∃ C : ℝ, ∀ g ∈ posG k r z z', ‖nuG z z' g‖ ≤ C ∧ ‖nuG' z z' g‖ ≤ C ∧ ‖ioG z z' g‖ ≤ C

def UBLInvSqrt : Prop :=
  ∀ (k r d : ℕ) (P : B.Mat k r → ℂ), U.IsPolyDeg d P → ∀ (S : Set (B.Mat k r)), S ⊆ B.GV k r →
    ∀ c : ℝ, 0 < c → (∀ g ∈ S, c ≤ (P g).re) → ∀ n : ℕ,
      UBL (fun g => (((Real.sqrt (P g).re)⁻¹ : ℝ) : ℂ)) S n 0 d

def GeomUBL : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' → ∀ ε : ℝ, 0 < ε →
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (nuG z z') (geG k r z z' ε) n e γ) ∧
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (nuG' z z') (geG k r z z' ε) n e γ) ∧
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (ioG z z') (geG k r z z' ε) n e γ)

def GeomAssemble : Prop :=
  GeomSmooth → GeomEqvNu → GeomEqvIo → GeomAtGq → GeomBd0 → GeomUBL → SSnGeom

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

