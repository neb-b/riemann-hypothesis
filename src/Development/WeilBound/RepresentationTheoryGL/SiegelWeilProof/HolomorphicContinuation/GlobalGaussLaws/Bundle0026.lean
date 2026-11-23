module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0024
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchange
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LamSing
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0022
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0004
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentMapContinuousAdditive
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0634
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0510
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussI
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

variable {n : ℕ}

theorem siegelOrb : SiegelOrb := by
  intro n Z hZ
  obtain ⟨S, hSS, hSu⟩ := exists_sqrt (show ((-(Complex.I / 2)) • (Z - Zᴴ)).PosDef from hZ)
  set X : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (Z + Zᴴ) with hXdef
  have hX : Xᴴ = X := conj_half_smul Z
  have hSu' : IsUnit Sᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hSu.star
  refine ⟨mkGR (nU X) (by rw [det_nU]; exact one_ne_zero) (inG_nU hX) * mkGR (mM S) (det_mM hSu) (inG_mM hSu), ?_, ?_⟩
  · rw [mR_mul, mR_mkGR, mR_mkGR, toBlocks₂₁_mul]
    simp [nU, mM]
  · unfold actZ
    rw [mR_mul, mR_mkGR, mR_mkGR, toBlocks₁₁_mul, toBlocks₁₂_mul, toBlocks₂₁_mul, toBlocks₂₂_mul]
    simp only [nU, mM, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
      Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero]
    rw [Matrix.nonsing_inv_nonsing_inv _ hSu', Matrix.add_mul, Matrix.mul_assoc X, Matrix.nonsing_inv_mul _ hSu',
      Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hSS, hXdef, smul_smul]
    have hc : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, ← mul_div_assoc, Complex.I_mul_I]
      norm_num
    rw [hc, ← smul_add, show Z - Zᴴ + (Z + Zᴴ) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]
    norm_num

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocC
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R : Type} [CommRing R] {n : ℕ}

theorem det_cT (σ : R →+* R) (a : Matrix (Fin n) (Fin n) R) : (Formalism.UG.cT σ a).det = σ a.det := by
  unfold Formalism.UG.cT; rw [det_transpose, det_map]

theorem cT_cT (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) {m p : Type} (a : Matrix m p R) :
    Formalism.UG.cT σ (Formalism.UG.cT σ a) = a := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cT_inv (σ : R →+* R) (a : Matrix (Fin n) (Fin n) R) (ha : IsUnit a.det) :
    Formalism.UG.cT σ a⁻¹ = (Formalism.UG.cT σ a)⁻¹ := by
  unfold Formalism.UG.cT; rw [map_nonsing_inv σ a ha, transpose_nonsing_inv]

theorem uni_levi (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (a : Matrix (Fin n) (Fin n) R) (ha : IsUnit a.det) :
    Uni σ (GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹) := by
  have hca : IsUnit (Formalism.UG.cT σ a).det := by rw [det_cT]; exact ha.map σ
  apply bf_injective
  unfold J2
  rw [bf_mul, bf_mul, bf_cT, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
  rw [cT_inv σ _ hca, cT_cT σ hσ]
  have hc0 : Formalism.UG.cT σ (0 : Matrix (Fin n) (Fin n) R) = 0 := by ext; simp [Formalism.UG.cT]
  simp only [hc0, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero,
    zero_add, mul_nonsing_inv _ hca, nonsing_inv_mul _ ha, neg_zero]

theorem eI_mul_eI (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) R) * eI I = eI I := by
  unfold eI; rw [diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> simp

theorem cT_eI (σ : R →+* R) (I : Finset (Fin n)) : Formalism.UG.cT σ (eI I : Matrix (Fin n) (Fin n) R) = eI I := by
  unfold Formalism.UG.cT; rw [eI_map, eI, diagonal_transpose]

theorem uni_wIm (σ : R →+* R) (I : Finset (Fin n)) : Uni σ (wIm I : Matrix (Fin (n + n)) (Fin (n + n)) R) := by
  apply bf_injective
  unfold J2 wIm
  rw [bf_mul, bf_mul, bf_cT, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
  have h1 : Formalism.UG.cT σ (1 - eI I : Matrix (Fin n) (Fin n) R) = 1 - eI I := by
    unfold Formalism.UG.cT; rw [Matrix.map_sub _ (map_sub σ), Matrix.map_one _ (map_zero σ) (map_one σ), eI_map, transpose_sub,
      transpose_one, eI, diagonal_transpose]
  have h2 : Formalism.UG.cT σ (-eI I : Matrix (Fin n) (Fin n) R) = -eI I := by
    unfold Formalism.UG.cT; rw [Matrix.map_neg _ (map_neg σ), eI_map, transpose_neg, eI, diagonal_transpose]
  rw [h1, h2, cT_eI]
  have hE := eI_mul_eI (R := R) I
  congr 1 <;> simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero,
    zero_add, neg_neg, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, hE] <;> abel_nf

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IteratedDerivOfReal
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilCH

variable {D : D7} {n : ℕ} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem tens_cancel (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) {F G : (Fin V.rank → Fin n → ℂ) → ℂ}
    (h : tens θ τ fr F Ψ = tens θ τ fr G Ψ) : F = G := by
  funext u
  obtain ⟨x, hxu, hxo, hxf⟩ := DilBH.pointAt θ hθ τ fr hfr x₀ u
  have hΨx : Ψ x = Ψ x₀ := hΨ.1 x x₀ hxo hxf
  have := congrFun h x
  simp only [tens, hxu, hΨx] at this
  exact mul_right_cancel₀ hx₀ this

variable {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {ι : GR n →* G D n}
  {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}

theorem L_sub (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y : GR n) {f g : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) (hg : IsSch g) : L y (f - g) = L y f - L y g := by
  have h := hL.2 y Ψ hΨ (f - g) (SchwartzDifferenceQuotient.isSch_sub hf hg)
  have e : (⟨tens θ τ fr (f - g) Ψ, hΨ.2 _ (SchwartzDifferenceQuotient.isSch_sub hf hg)⟩ : schwartzA θ V.rank n) =
      ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ - ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ :=
    Subtype.ext (by funext x; simp only [tens, Submodule.coe_sub]; show (f _ - g _) * _ = f _ * _ - g _ * _; ring)
  rw [e, map_sub, Submodule.coe_sub, hL.2 y Ψ hΨ f hf, hL.2 y Ψ hΨ g hg] at h
  refine tens_cancel hθ hfr hΨ hx₀ ?_
  rw [← h]; funext x
  show tens θ τ fr (L y f) Ψ x - tens θ τ fr (L y g) Ψ x = _
  simp only [tens]
  show _ = (L y f _ - L y g _) * _
  ring

theorem L_smul (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y : GR n) (a : ℂ) {f : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) : L y (fun u => a * f u) = fun u => a * L y f u := by
  have h := hL.2 y Ψ hΨ _ (SchwartzDifferenceQuotient.isSch_smul a hf)
  have e : (⟨tens θ τ fr (fun u => a * f u) Ψ, hΨ.2 _ (SchwartzDifferenceQuotient.isSch_smul a hf)⟩ : schwartzA θ V.rank n) =
      a • ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ :=
    Subtype.ext (by funext x; simp [tens, mul_assoc])
  rw [e, map_smul, Submodule.coe_smul, hL.2 y Ψ hΨ f hf] at h
  refine tens_cancel hθ hfr hΨ hx₀ ?_
  rw [← h]; funext x; simp [tens, mul_assoc]

theorem L_mul (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y y' : GR n) {f : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) : L (y * y') f = L y (L y' f) := by
  have h := hL.2 (y * y') Ψ hΨ f hf
  have h' : ω (ι y') ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ = ⟨tens θ τ fr (L y' f) Ψ, hΨ.2 _ (hL.1 y' f hf)⟩ :=
    Subtype.ext (hL.2 y' Ψ hΨ f hf)
  rw [map_mul, map_mul, Module.End.mul_apply, h', hL.2 y Ψ hΨ _ (hL.1 y' f hf)] at h
  exact tens_cancel hθ hfr hΨ hx₀ h.symm

theorem diffOn_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (r : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv r f) U := by
  induction r with
  | zero => simpa using hf
  | succ r ih => rw [iteratedDeriv_succ]; exact ih.deriv hU

theorem iteratedDeriv_ofReal {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hR : ∀ s : ℝ, (s : ℂ) ∈ U) (r : ℕ) : iteratedDeriv r (fun t : ℝ => f t) = fun t : ℝ => iteratedDeriv r f t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd : DifferentiableAt ℂ (iteratedDeriv r f) t :=
      (diffOn_iteratedDeriv hU hf r).differentiableAt (hU.mem_nhds (hR t))
    rw [iteratedDeriv_succ]
    exact (hd.hasDerivAt.comp_ofReal).deriv

end PositivityTheory.Rg.Sw.Glob.DilCH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LamTop
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem nbFacts : NbFacts := _root_.GlobalTheory.CompanionTheory.SiegelUnip.nb_facts

theorem charFacts : CharFacts := _root_.GlobalTheory.CompanionTheory.CoefWeight.continuous_norm_coefChar

theorem gLamBd : GLamBd := gLamBd_of nbFacts charFacts hermCocompact

theorem splitTauP : SplitTauP := fun _ _ _ _ _ hθ hι g => splitTau hθ hι g

namespace LamTopH

theorem chiPer : ChiPer := by
  intro D n ψ hψ β l hl
  have hl' : (hermA D n).subtype l ∈ ratMx D n n := AddSubgroup.mem_comap.1 hl
  obtain ⟨γ, hγ⟩ := hl'
  have e : Matrix.trace (HMul.hMul (β.1.map (incA D)) l.1 : Mx D n n) = incA D (Matrix.trace (β.1 * γ)) := by
    change Matrix.trace (β.1.map (incA D) * ((hermA D n).subtype l)) = _
    rw [← hγ]
    change Matrix.trace (β.1.map (incA D) * γ.map (incA D)) = _
    rw [← Matrix.map_mul]
    exact (AddMonoidHom.map_trace (incA D).toAddMonoidHom (β.1 * γ)).symm
  rw [e]
  have h2 : -halfTr (incA D (Matrix.trace (β.1 * γ))) = halfTr (incA D (-(Matrix.trace (β.1 * γ)))) := by
    simp only [halfTr, map_neg, mul_neg]
  rw [h2]
  exact GlobalTheory.CompanionTheory.EisUnfold.Summand.psi_halfTr_incA ψ hψ _

theorem nbTauP : NbTauP := by
  intro D n ψ θ τ ι hψ hθ hι nb hnb nb' hnb'
  refine ⟨fun x => ?_, fun β => ?_⟩
  · obtain ⟨b, hb, -⟩ := nbTau hθ hι nb hnb nb' hnb' x
    exact ⟨b, hb⟩
  obtain ⟨l, hl⟩ := GlobalTheory.StdUnn.exists_realPar_of_isCharAF D ψ hψ θ hθ
  have hβh : (β.1.map (tauE D τ)).IsHermitian := by
    ext i j
    have h1 : (β.1.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = β.1 := β.2
    have h2 : D.sp.cm.sig (β.1 j i) = β.1 i j := by
      have := congrFun (congrFun h1 i) j
      simpa [Matrix.transpose_apply, Matrix.map_apply] using this
    have h3 : tauE D τ (D.sp.cm.sig (β.1 j i)) = starRingEnd ℂ (tauE D τ (β.1 j i)) := D.sp.cm.cmUnram.2.1 _ _
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← h2, h3]
    rfl
  refine ⟨((l τ : ℝ) : ℂ) • β.1.map (tauE D τ), ?_, ?_, ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hβh.eq, Complex.star_def, Complex.conj_ofReal]
  · intro h0
    have h4 : (β.1.map (tauE D τ)).det = tauE D τ β.1.det := (RingHom.map_det (tauE D τ) β.1).symm
    rw [Matrix.det_smul, h4, h0, map_zero, mul_zero]
  · intro x b hb
    obtain ⟨b0, hb0, hfin, hτ, hoth, -⟩ := nbTau hθ hι nb hnb nb' hnb' x
    have hbb : b = b0 := by
      have h3 : nb b = nb b0 := hb.symm.trans hb0
      have hm := congrArg mat h3
      rw [hnb b, hnb b0] at hm
      have := congrArg PlaceFactsH.bOf hm
      rw [PlaceFactsH.upper_right_entry_block_matrix, PlaceFactsH.upper_right_entry_block_matrix] at this
      exact Subtype.ext this
    subst hbb
    set t := Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n) with ht
    have htfin : finPart D t = 0 := GlobalTheory.PhaseReal.finPart_trace _ _ hfin
    have hT := GlobalTheory.PhaseReal.trace_real htfin
    have hH : halfTr t = pairA D.host.F (fstA D.host.F (halfTr t)) 0 := by
      refine Prod.ext rfl ?_
      have h2 : (Algebra.trace (AF D.host.F) (AE D) t).2 = 0 := by rw [hT]; rfl
      show (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) t).2 = 0
      rw [show (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) t).2 =
        (algebraMap D.host.F (AF D.host.F) (1 / 2)).2 * (Algebra.trace (AF D.host.F) (AE D) t).2 from rfl, h2, mul_zero]
    rw [hH]
    have hpsi := hl (fstA D.host.F (halfTr t))
    rw [show psiInf D.host.F ψ (fstA D.host.F (halfTr t)) = ψ (pairA D.host.F (fstA D.host.F (halfTr t)) 0) from rfl]
      at hpsi
    rw [hpsi]

    have hθv : ∀ ρ, θ ρ (fstA D.host.F (halfTr t) ⊗ₜ[D.host.F] (1 : D.host.E)) = ((θ ρ (infPart D t)).re : ℂ) := by
      intro ρ
      have h2t : Algebra.trace (AF D.host.F) (AE D) t = algebraMap D.host.F (AF D.host.F) 2 * halfTr t := by
        show _ = algebraMap D.host.F (AF D.host.F) 2 *
          (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) t)
        rw [← mul_assoc, ← map_mul]
        norm_num
      have hf : fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) = 2 * fstA D.host.F (halfTr t) := by
        rw [h2t, map_mul, AlgHom.commutes, map_ofNat]
      have hT2 := GlobalTheory.PhaseReal.theta_trace θ hθ ρ t
      rw [hf] at hT2
      have hmul : θ ρ ((2 * fstA D.host.F (halfTr t)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
          2 * θ ρ (fstA D.host.F (halfTr t) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
        have e : (2 * fstA D.host.F (halfTr t)) ⊗ₜ[D.host.F] (1 : D.host.E) =
            2 * (fstA D.host.F (halfTr t) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
          rw [two_mul, TensorProduct.add_tmul, two_mul]
        rw [e, map_mul, map_ofNat]
      rw [hmul] at hT2
      push_cast at hT2
      linear_combination hT2 / 2
    simp_rw [hθv]
    have hpair : ∀ ρ, θ ρ (infPart D t) = Matrix.trace (β.1.map (tauE D ρ) * compAt θ ρ b.1) :=
      fun ρ => GlobalTheory.PhaseReal.theta_pair θ hθ ρ β.1 b.1
    rw [Finset.sum_eq_single τ]
    · rw [hpair, hτ]
      have hreal : (((Matrix.trace (β.1.map (tauE D τ) * herm x)).re : ℝ) : ℂ) =
          Matrix.trace (β.1.map (tauE D τ) * herm x) := by
        apply Complex.conj_eq_iff_re.1
        rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
          PlaceFactsH.herm_conjTranspose, hβh.eq, Matrix.trace_mul_comm]
      rw [hreal]
      simp only [eTr, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    · intro ρ _ hρ
      rw [hpair, hoth ρ hρ, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, Complex.ofReal_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ τ) h

end LamTopH

open LamTopH

theorem gLsing_of (hFZ : FourierZeroN) (hTS : TwoSided) (hD : DenseTau) : GLsing :=
  gLsing_core hFZ hTS hD _root_.GlobalTheory.CompanionTheory.SWCoef.coefDataExists nbFacts charFacts hermCocompact splitTauP nbTauP chiPer

theorem gLsing (hTS : TwoSided) (hD : DenseTau) : GLsing := gLsing_of fourierZeroN hTS hD

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RhoTSq
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacJ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF PositivityTheory.Rg.Sw.Glob.VacG PositivityTheory.Rg.Sw.Glob.VacH
  PositivityTheory.Rg.Sw.Glob.VacI

variable {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
  {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
  {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}

theorem rhoT_sq {m : ℕ} (t : ℝ) (ε : Fin m → Bool) (a : Fin m) : (rhoT t ε a) ^ 2 = 1 := by
  unfold rhoT; split_ifs <;> norm_num

theorem rot_gen (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (hl0 : l τ ≠ 0) (hN : LawN) (hNb : LawNbar) (hLM : LocMul)
    (hGZ : GZSch) (L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ))
    (hL : IsLocFact ω τ fr ι L) (e : ℤ)
    (hlev : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f)
    (φ : Fin n → ℝ) (hφ : ∀ j, -(Real.pi / 2) < φ j ∧ φ j ≤ Real.pi / 2) (K : ℂ) :
    L (mkG (kth φ) (inK_kth φ).1) (DG K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (K * ∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ)))
        (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
  have hc : ∀ j, 0 < Real.cos (φ j / 2) := fun j =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [(hφ j).1, Real.pi_pos], by linarith [(hφ j).2, Real.pi_pos]⟩
  have hk : mkG (kth φ) (inK_kth φ).1 = mkG (kth fun j => φ j / 2) (inK_kth _).1 * mkG (kth fun j => φ j / 2) (inK_kth _).1 := by
    apply Subtype.ext; apply Units.ext; exact kth_half φ
  have hf0 : IsSch (DG (n := n) K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) :=
    isSch_DG hGZ ε (tLoc l τ) (cLoc l τ) (cpos hl0) tabs K
  rw [hk, hLM D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL _ _ _ hf0,
    rot_DG hC hl0 hN hNb hLM hGZ L hL e hlev _ hc K, rot_DG hC hl0 hN hNb hLM hGZ L hL e hlev _ hc _]
  congr 1
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact dbl_angle _ _ (rhoT_sq _ _ a)

end PositivityTheory.Rg.Sw.Glob.VacJ
end
end

