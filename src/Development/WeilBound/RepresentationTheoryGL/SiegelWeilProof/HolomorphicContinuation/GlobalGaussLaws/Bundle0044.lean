module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0042
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0032
public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawE
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem fromBlocks_of (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    mR y = Matrix.fromBlocks (mR y).toBlocks₁₁ (mR y).toBlocks₁₂ 0 (mR y).toBlocks₂₂ := by
  rw [← hy]
  exact (Matrix.fromBlocks_toBlocks _).symm

theorem blocks_ad (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    ((mR y).toBlocks₁₁)ᴴ * (mR y).toBlocks₂₂ = 1 := by
  have hG : (mR y)ᴴ * PositivityTheory.Rg.Sw.JJ n * mR y = PositivityTheory.Rg.Sw.JJ n := y.2
  have hJ : PositivityTheory.Rg.Sw.JJ n = Matrix.fromBlocks 0 1 (-1) 0 := rfl
  rw [hJ, fromBlocks_of y hy, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hG
  have h12 := hG.2.1
  simpa using h12

theorem det_rel (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    star ((mR y).toBlocks₁₁).det * ((mR y).toBlocks₂₂).det = 1 := by
  have h := congrArg Matrix.det (blocks_ad y hy)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  exact h

theorem det_ne (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) : ((mR y).toBlocks₁₁).det ≠ 0 := by
  intro h0
  have h := det_rel y hy
  rw [h0, star_zero, zero_mul] at h
  exact zero_ne_one h

def aOf (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) : GL (Fin n) ℂ :=
  ⟨(mR y).toBlocks₁₁, ((mR y).toBlocks₁₁)⁻¹, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_ne y hy)),
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (det_ne y hy))⟩

theorem aOf_val (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) : (aOf y hy).1 = (mR y).toBlocks₁₁ := rfl

theorem decomp (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    mR ((mOf (aOf y hy))⁻¹ * y) = Matrix.fromBlocks 1 (((mR y).toBlocks₁₁)⁻¹ * (mR y).toBlocks₁₂) 0 1 := by
  have hmul : mR ((mOf (aOf y hy))⁻¹ * y) = mR (mOf (aOf y hy))⁻¹ * mR y := rfl
  have hinv : (((aOf y hy)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = ((mR y).toBlocks₁₁)⁻¹ := rfl
  have hval : ((aOf y hy : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (mR y).toBlocks₁₁ := rfl
  rw [hmul, mR_mOf_inv, hinv, hval]
  conv_lhs => rw [fromBlocks_of y hy]
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (det_ne y hy)), blocks_ad y hy]

set_option maxHeartbeats 400000 in
theorem glob_law {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → NNReal}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)} {τ : D.what₂.Tau}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : PositivityTheory.Rg.Sw.GR n →* G D n}
    (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) {L : PositivityTheory.Rg.Sw.GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}
    (hL : IsLocOp ω l s τ fr ι L) {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (P : PX V.rank n)
    (y g : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    sLd L (cLoc l τ) P (y * g) =
      (χ (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy)))) ((V.rank : ℂ) / 2) *
        sLd L (cLoc l τ) P g := by
  obtain ⟨-, -, -, -, -, hω, -, -, -, -, -, -, -, hι, -⟩ := hC
  obtain ⟨hlevi, hunip, -⟩ := hω
  have hphase : ∀ b : Formalism.IndefR.Datum.Mx D n n,
      ψ (GlobalTheory.StdUnn.halfTr ((b * GlobalTheory.StdUnn.inner V (0 : Formalism.IndefR.Datum.Mx D V.rank n) 0).trace)) = 1 := by
    intro b
    have hin : GlobalTheory.StdUnn.inner V (0 : Formalism.IndefR.Datum.Mx D V.rank n) 0 = 0 := by
      show GlobalTheory.MixModel.adj 0 * (GlobalTheory.MixModel.gA V * 0) = 0
      rw [Matrix.mul_zero, Matrix.mul_zero]
    have htr : GlobalTheory.StdUnn.trA (0 : Formalism.L2.Theta.AE D) = 0 := by
      show Algebra.trace _ _ (0 : Formalism.L2.Theta.AE D) = 0
      exact map_zero _
    have hh : GlobalTheory.StdUnn.halfTr (0 : Formalism.L2.Theta.AE D) = 0 := by
      show _ * GlobalTheory.StdUnn.trA (0 : Formalism.L2.Theta.AE D) = 0
      rw [htr, mul_zero]
    rw [hin, Matrix.mul_zero, Matrix.trace_zero, hh, AddChar.map_zero_eq_one]
  have hL0 : ∀ z : PositivityTheory.Rg.Sw.GR n,
      ((ω (ι z)) (PositivityTheory.Rg.Sw.Glob.phiS θ τ fr (PositivityTheory.Rg.Sw.Glob.cLoc l τ)
        (PositivityTheory.Rg.Sw.Glob.LocLawH.psi0 θ V n l s τ) P) : Formalism.IndefR.Datum.Mx D V.rank n → ℂ) 0 =
        L z (PositivityTheory.Rg.Sw.Glob.fP (PositivityTheory.Rg.Sw.Glob.cLoc l τ) P) 0 := by
    intro z
    rw [hL z _ (PositivityTheory.Rg.Sw.Glob.LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ) P, PositivityTheory.Rg.Sw.Glob.LocLawH.tens_zero,
      PositivityTheory.Rg.Sw.Glob.LocLawH.cmTraceAdditiveCharacter_zero, mul_one]
  have hsplit : mOf (aOf y hy) * ((mOf (aOf y hy))⁻¹ * y * g) = y * g := by
    rw [← mul_assoc, mul_inv_cancel_left]
  have hm := PositivityTheory.Rg.Sw.Glob.LocLawH.mat_mOf hσ hι (aOf y hy)
  have hn := PositivityTheory.Rg.Sw.Glob.LocLawH.mat_nOf hσ hι ((mOf (aOf y hy))⁻¹ * y) _ (decomp y hy)
  have key := hL0 (y * g)
  rw [← hsplit, map_mul ι (mOf (aOf y hy)) ((mOf (aOf y hy))⁻¹ * y * g), map_mul ι ((mOf (aOf y hy))⁻¹ * y) g,
    map_mul ω, map_mul ω, Module.End.mul_apply, Module.End.mul_apply, hlevi _ _ hm, Matrix.zero_mul,
    hunip _ _ hn, hphase, one_mul, hL0 g, hsplit] at key
  show L (y * g) (PositivityTheory.Rg.Sw.Glob.fP (PositivityTheory.Rg.Sw.Glob.cLoc l τ) P) 0 =
    _ * _ * L g (PositivityTheory.Rg.Sw.Glob.fP (PositivityTheory.Rg.Sw.Glob.cLoc l τ) P) 0
  exact key.symm

end PositivityTheory.Rg.Sw.Glob.LocLawH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.NormIterFstComp
section
noncomputable section

open Filter Topology MvPolynomial Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.Glob.SchDH

section general

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iter_snd (q : ℝ × E) (l : ℕ) :
    ‖iteratedFDeriv ℝ l (fun q : ℝ × E => q.2) q‖ ≤ 1 + ‖q.2‖ := by
  have e : (fun q : ℝ × E => q.2) = ⇑(ContinuousLinearMap.snd ℝ ℝ E) := rfl
  rcases l with _ | l
  · rw [norm_iteratedFDeriv_zero]; linarith
  · rw [← norm_iteratedFDeriv_fderiv]
    have hf : fderiv ℝ (fun q : ℝ × E => q.2) = fun _ => ContinuousLinearMap.snd ℝ ℝ E := by
      funext y; rw [e]; exact (ContinuousLinearMap.snd ℝ ℝ E).fderiv
    rw [hf]
    rcases l with _ | l
    · rw [norm_iteratedFDeriv_zero]
      linarith [ContinuousLinearMap.norm_snd_le ℝ ℝ E, norm_nonneg q.2]
    · rw [iteratedFDeriv_const_of_ne (by omega)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

theorem norm_iter_fst_comp {A : ℝ → E →L[ℝ] E} (hA : ContDiff ℝ ∞ A) (q : ℝ × E) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun q : ℝ × E => A q.1) q‖ ≤ ‖iteratedFDeriv ℝ j A q.1‖ := by
  have e : (fun q : ℝ × E => A q.1) = A ∘ ⇑(ContinuousLinearMap.fst ℝ ℝ E) := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hA _ (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => ContinuousLinearMap.norm_fst_le ℝ ℝ E

theorem bound_comp (φ : SchwartzMap E ℂ) (A : ℝ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A)
    (hinv : ∀ t y, A (-t) (A t y) = y) (k N : ℕ) :
    ∃ C, ∀ p : ℝ, ‖p - 0‖ ≤ 1 → ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (fun q : ℝ × E => φ (A q.1 q.2)) (p, x)‖ ≤ C := by
  obtain ⟨KA, hKA⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun s => ∑ j ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ j A s‖)
    (continuous_finsetSum _ (fun j _ => (hA.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm)).continuousOn
  have hj : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ j ≤ N, ‖iteratedFDeriv ℝ j A s‖ ≤ KA := by
    intro s hs j hjN
    have h1 := hKA s hs
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
    exact (Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j A s‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hjN))).trans h1
  have hKA0 : 0 ≤ KA := (norm_nonneg _).trans (hj 0 (by norm_num) 0 (Nat.zero_le _))
  have hAn : ∀ s ∈ Icc (-1 : ℝ) 1, ‖A s‖ ≤ KA := fun s hs => by
    have := hj s hs 0 (Nat.zero_le _); rwa [norm_iteratedFDeriv_zero] at this
  set f : ℝ × E → E := fun q => A q.1 q.2 with hfdef
  have hf : ContDiff ℝ ∞ f := (hA.comp contDiff_fst).clm_apply contDiff_snd
  have hDf : ∀ q : ℝ × E, q.1 ∈ Icc (-1 : ℝ) 1 → ∀ i ≤ N,
      ‖iteratedFDeriv ℝ i f q‖ ≤ 2 ^ i * KA * (1 + ‖q.2‖) := by
    intro q hq i hi
    have hb := (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).norm_iteratedFDeriv_le_of_bilinear
      (f := fun q : ℝ × E => A q.1) (g := fun q : ℝ × E => q.2) (hA.comp contDiff_fst) contDiff_snd q
      (n := i) (by exact_mod_cast le_top)
    have e : (fun y : ℝ × E => (ContinuousLinearMap.id ℝ (E →L[ℝ] E)) (A y.1) y.2) = f := rfl
    rw [e] at hb
    refine hb.trans ?_
    have hterm : ∀ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun q : ℝ × E => A q.1) q‖ *
        ‖iteratedFDeriv ℝ (i - j) (fun q : ℝ × E => q.2) q‖ ≤ (i.choose j : ℝ) * (KA * (1 + ‖q.2‖)) := by
      intro j hjm
      have hjN : j ≤ N := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hjm)).trans hi
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul ((norm_iter_fst_comp hA q j).trans (hj q.1 hq j hjN))
        (norm_iter_snd q _) (norm_nonneg _) hKA0) (by positivity)
    calc ‖ContinuousLinearMap.id ℝ (E →L[ℝ] E)‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j (fun q : ℝ × E => A q.1) q‖ * ‖iteratedFDeriv ℝ (i - j) (fun q : ℝ × E => q.2) q‖
        ≤ 1 * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (KA * (1 + ‖q.2‖)) :=
          mul_le_mul ContinuousLinearMap.norm_id_le (Finset.sum_le_sum hterm)
            (Finset.sum_nonneg fun j _ => by positivity) zero_le_one
      _ = 2 ^ i * KA * (1 + ‖q.2‖) := by
          rw [one_mul, ← Finset.sum_mul]
          have := Nat.sum_range_choose i
          have h2 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) = 2 ^ i := by exact_mod_cast this
          rw [h2]; ring
  set S := 2 ^ (k + N) * ((Finset.Iic (k + N, N)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ with hSdef
  have hS : ∀ y, ∀ i ≤ N, (1 + ‖y‖) ^ (k + N) * ‖iteratedFDeriv ℝ i φ y‖ ≤ S := fun y i hi =>
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (k + N, N)) le_rfl hi φ y
  have hS0 : 0 ≤ S := le_trans (by positivity) (hS 0 0 (Nat.zero_le _))
  set KD := max 1 (2 ^ N * KA) with hKD
  set K' := max 1 KA with hK'
  have hKD1 : 1 ≤ KD := le_max_left _ _
  have hK'1 : 1 ≤ K' := le_max_left _ _
  refine ⟨N.factorial * S * KD ^ N * K' ^ (k + N), fun p hp x => ?_⟩
  have hp' : p ∈ Icc (-1 : ℝ) 1 := by
    rw [sub_zero, Real.norm_eq_abs] at hp; exact ⟨by linarith [neg_abs_le p], (le_abs_self p).trans hp⟩
  have hmp : -p ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hp'.2], by linarith [hp'.1]⟩
  set y := f (p, x) with hy
  have hxy : ‖x‖ ≤ KA * ‖y‖ := by
    have e1 : x = A (-p) y := (hinv p x).symm
    calc ‖x‖ = ‖A (-p) y‖ := by rw [← e1]
      _ ≤ ‖A (-p)‖ * ‖y‖ := (A (-p)).le_opNorm y
      _ ≤ KA * ‖y‖ := by gcongr; exact hAn _ hmp
  have h1x : 1 + ‖x‖ ≤ K' * (1 + ‖y‖) := by
    have h2 : KA * ‖y‖ ≤ K' * ‖y‖ := by gcongr; exact le_max_right _ _
    nlinarith [norm_nonneg y]
  have hyp : 0 < (1 + ‖y‖) ^ (k + N) := by positivity
  have hC : ∀ i ≤ N, ‖iteratedFDeriv ℝ i φ (f (p, x))‖ ≤ S / (1 + ‖y‖) ^ (k + N) := by
    intro i hi
    rw [le_div_iff₀ hyp, mul_comm]
    exact hS y i hi
  have hD : ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv ℝ i f (p, x)‖ ≤ (KD * (1 + ‖x‖)) ^ i := by
    intro i hi1 hiN
    have hb1 : 1 ≤ KD * (1 + ‖x‖) := by nlinarith [norm_nonneg x]
    refine (hDf (p, x) hp' i hiN).trans ?_
    have h3 : 2 ^ i * KA ≤ KD := by
      refine le_trans ?_ (le_max_right _ _)
      gcongr
      · norm_num
    calc 2 ^ i * KA * (1 + ‖(p, x).2‖) ≤ KD * (1 + ‖x‖) := by gcongr
      _ ≤ (KD * (1 + ‖x‖)) ^ i := le_self_pow₀ hb1 (by omega)
  have hcomp := norm_iteratedFDeriv_comp_le (g := ⇑φ) (f := f) (φ.smooth ⊤) hf (n := N)
    (by exact_mod_cast le_top) (p, x) hC hD
  have e2 : (fun q : ℝ × E => φ (A q.1 q.2)) = ⇑φ ∘ f := rfl
  rw [e2]
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
  have hpow : (1 + ‖x‖) ^ (k + N) ≤ K' ^ (k + N) * (1 + ‖y‖) ^ (k + N) := by
    rw [← mul_pow]; gcongr
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (⇑φ ∘ f) (p, x)‖
      ≤ (1 + ‖x‖) ^ k * (N.factorial * (S / (1 + ‖y‖) ^ (k + N)) * (KD * (1 + ‖x‖)) ^ N) := by
        gcongr
    _ = N.factorial * S * KD ^ N * ((1 + ‖x‖) ^ (k + N) / (1 + ‖y‖) ^ (k + N)) := by
        rw [mul_pow, pow_add]; field_simp; ring
    _ ≤ N.factorial * S * KD ^ N * K' ^ (k + N) := by
        gcongr
        rw [div_le_iff₀ hyp]; exact hpow

end general

end PositivityTheory.Rg.Sw.Glob.SchDH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SchDecay
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

def Pk (μ : Measure (Mx D m n)) (π : Mx D m n → (Fin m → Fin n → ℂ)) (B : Mx D m n → ℂ) (κ : ℂ) : Prop :=
  ∀ a : (Fin m → Fin n → ℂ) → ℂ, Measurable a → (∃ C, ∀ u, ‖a u‖ ≤ C * (1 + ‖u‖) ^ (-rr m n)) →
    ∫ z, a (π z) * B z ∂μ = κ * ∫ u, a u

def kap (μ : Measure (Mx D m n)) (π : Mx D m n → (Fin m → Fin n → ℂ)) (B : Mx D m n → ℂ) : ℂ :=
  Classical.epsilon (Pk μ π B)

set_option synthInstance.maxHeartbeats 800000 in
theorem kap_spec {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (μ : Measure (Mx D V.rank n)) [μ.IsAddHaarMeasure]
    {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (x : Mx D V.rank n) :
    Pk μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x) (kap μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x)) := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  apply Classical.epsilon_spec
  have hρc : Continuous fun u : Fin V.rank → Fin n → ℂ => (1 + ‖u‖) ^ (-rr V.rank n) :=
    (continuous_const.add continuous_norm).rpow_const fun u => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg u)).ne'
  exact LocCellT.tauFact μ (piF θ τ fr) (continuous_piF hθ τ fr) (sIns τ fr)
    (fun z u => by rw [map_add (piF θ τ fr), piF_sIns hθ τ hdet]) (Bw ψ V θ τ fr Ψ x)
    (continuous_Bw hθ hψ hΨ x).measurable (fun z u => Bw_add hθ hdet ψ hΨ x z u)
    (fun u => (1 + ‖u‖) ^ (-rr V.rank n)) hρc (fun u => Real.rpow_pos_of_pos (by positivity) _)
    (hint_int hθ hdet μ hΨ hψ x)

theorem sch_decay (f : (Fin m → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    ∃ C, ∀ u, ‖f u‖ ≤ C * (1 + ‖u‖) ^ (-rr m n) := by
  obtain ⟨S, rfl⟩ := hf
  set k : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hk
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (Fin m → Fin n → ℂ) ℂ) S, fun u => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl S u
  rw [norm_iteratedFDeriv_zero] at h
  have hpos : 0 < (1 + ‖u‖) ^ k := by positivity
  have e : (1 + ‖u‖) ^ (-rr m n) = ((1 + ‖u‖) ^ k)⁻¹ := by
    rw [rr, Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [e, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact h

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

