module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0032
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0037
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0047
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0011
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentPartBlockMatrix
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0021
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0038
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0044
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0041
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0040
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0030
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0010
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0039
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ValZeroOfTens
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0019
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0026
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TwoSided

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussTop
section
namespace PositivityTheory.Rg.Sw.Glob

theorem gaussLaw_of' (hV : VacK) (hG : GZSch) : GaussLaw := by
  have hT : TensInj := tensInj_of awayIn
  exact gaussLaw_of hT (lawN_of unipTau hT) (lawM_of hT) hV (locMul_of hT) hG lNe

end PositivityTheory.Rg.Sw.Glob
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.InvEqWww
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP PositivityTheory.Rg.Sw.Glob.PlaceFactsH
open Classical

variable {D : D7} {n m : ℕ}

theorem Aw_away {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D V.rank n)) (Ψ : Mx D V.rank n → ℂ) (x x' : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D)) :
    Aw ψ V θ τ fr μ Ψ x = Aw ψ V θ τ fr μ Ψ x' := by
  have e : Bw ψ V θ τ fr Ψ x = Bw ψ V θ τ fr Ψ x' := by
    funext y
    unfold Bw
    rw [inner_away hθ x x' _ hx hf (compAt_sub_sIns hθ hdet y)]
  unfold Aw
  rw [e]

set_option maxHeartbeats 800000 in
theorem mat_ww (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : mat (w * w) = blk4 (-1) 0 0 (-1) := by
  rw [mat_mul', hw, submatrix_fromBlocks_mul]
  simp

set_option maxHeartbeats 800000 in
theorem inv_eq_www (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : w⁻¹ = w * w * w := by
  apply mat_inj
  rw [GlobalTheory.CompanionTheory.EisCovar.Weyl.mat_inv_eq w hw, mat_mul', mat_ww w hw, hw, submatrix_fromBlocks_mul]
  simp

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SchDeriv
section
noncomputable section

open Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.Glob

open SchDH

theorem schDeriv : SchDeriv := by
  intro m n c hc X P
  obtain ⟨φ0, hφ0⟩ := exists_fP (m := m) (n := n) c hc P
  obtain ⟨φ1, hφ1⟩ := exists_fP (m := m) (n := n) c hc (vfX c X P)
  set A : ℝ → (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) :=
    fun t => matL (NormedSpace.exp ((t : ℂ) • X)) with hAdef
  have hA : ContDiff ℝ ∞ A := contDiff_A X
  have hinv : ∀ t y, A (-t) (A t y) = y := by
    intro t y
    simp only [hAdef]
    rw [← matL_mul, ← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)]
    rw [← add_smul, Complex.ofReal_neg, neg_add_cancel, zero_smul, NormedSpace.exp_zero, matL_one]
  let Aeq : ℝ → (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ) := fun t =>
    ContinuousLinearEquiv.equivOfInverse (A t) (A (-t)) (fun y => hinv t y)
      (fun y => by have h := hinv (-t) y; rwa [neg_neg] at h)
  have hAeq : ∀ t y, Aeq t y = A t y := fun t y => rfl
  let S : ℝ → SchwartzMap (Fin m → Fin n → ℂ) ℂ := fun t => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Aeq t) φ0
  have hS : ∀ t y, S t y = φ0 (A t y) := fun t y => by
    simp only [S, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hAeq]
  refine ⟨S, φ1, fun t y => ?_, fun y => hφ1 y, ?_⟩
  · rw [hS, hφ0]
    congr 1
  · set F : ℝ × (Fin m → Fin n → ℂ) → ℂ := fun q => φ0 (A q.1 q.2) with hFdef
    have hF : ContDiff ℝ ∞ F := (φ0.smooth ⊤).comp ((hA.comp contDiff_fst).clm_apply contDiff_snd)
    have hR : ∀ p, ⇑(S p) = fun x => F (p, x) := fun p => by funext x; rw [hS]
    have hder : ∀ x, HasDerivAt (fun t : ℝ => F (t, x)) (φ1 x) 0 := fun x => by
      have h := hasDerivAt_curve c X P x
      rw [hφ1]
      have e : (fun t : ℝ => F (t, x)) = fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x) := by
        funext t; simp only [hFdef, hAdef, hφ0]
      rw [e]; exact h
    have hD : ∀ v : ℝ, ⇑(v • φ1) = fun x => fderiv ℝ F ((0 : ℝ), x) (v, 0) := by
      intro v
      funext x
      have hFd : HasFDerivAt F (fderiv ℝ F ((0 : ℝ), x)) ((0 : ℝ), x) :=
        ((hF.differentiable (by simp)) _).hasFDerivAt
      have hc : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × (Fin m → Fin n → ℂ))) ((1 : ℝ), (0 : Fin m → Fin n → ℂ)) 0 :=
        (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x)
      have h1 := hFd.comp_hasDerivAt (0 : ℝ) hc
      have h2 := (hder x).unique h1
      have e : ((v, 0) : ℝ × (Fin m → Fin n → ℂ)) = v • ((1 : ℝ), (0 : Fin m → Fin n → ℂ)) := by
        ext <;> simp
      rw [SchwartzMap.smul_apply, e, map_smul]
      change v • φ1 x = v • (fderiv ℝ F ((0 : ℝ), x)) ((1 : ℝ), (0 : Fin m → Fin n → ℂ))
      rw [h2]
    have hb : ∀ k N : ℕ, ∃ C, ∀ p : ℝ, ‖p - 0‖ ≤ 1 → ∀ x : Fin m → Fin n → ℂ,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ N F (p, x)‖ ≤ C := fun k N => bound_comp φ0 A hA hinv k N
    rw [(schwartz_withSeminorms ℂ (Fin m → Fin n → ℂ) ℂ).tendsto_nhds]
    rintro ⟨k, N⟩ ε hε
    obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.OM.SchDiff.seminorm_remainder hF (0 : ℝ) hb S (fun v => v • φ1) hR hD k N
    set C' := max C 1 with hC'
    have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| < min 1 (ε / C') := by
      have h := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      rw [abs_zero] at h
      exact h (Iio_mem_nhds (lt_min one_pos (div_pos hε hC'0)))
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htne
    have htne' : t ≠ 0 := htne
    have ht1 : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact (lt_of_lt_of_le ht (min_le_left _ _)).le
    have key : t⁻¹ • (S t - S 0) - φ1 = ((t⁻¹ : ℝ) : ℂ) • (S (0 + t) - S 0 - t • φ1) := by
      rw [Complex.coe_smul, zero_add]
      simp only [smul_sub, smul_smul, inv_mul_cancel₀ htne', one_smul]
    change SchwartzMap.seminorm ℂ k N (t⁻¹ • (S t - S 0) - φ1) < ε
    rw [key, map_smul_eq_mul, Complex.norm_real, norm_inv]
    have hCt := hC t ht1
    have hpos : 0 < ‖t‖ := norm_pos_iff.2 htne'
    calc ‖t‖⁻¹ * (SchwartzMap.seminorm ℂ k N) (S (0 + t) - S 0 - t • φ1)
        ≤ ‖t‖⁻¹ * (C * ‖t‖ ^ 2) := by gcongr
      _ = C * ‖t‖ := by field_simp
      _ ≤ C' * ‖t‖ := by gcongr; exact le_max_left _ _
      _ < C' * (ε / C') := by
          gcongr
          rw [Real.norm_eq_abs]; exact lt_of_lt_of_le ht (min_le_right _ _)
      _ = ε := by field_simp

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VanishTop
section
namespace PositivityTheory.Rg.Sw.Glob

theorem top (hA : AbsThm) (hLF : LocFact) (hAA : AwayAct)
    (hLi : LocInst) (hTA : PositivityTheory.PfSWUS.ThetaAuto) (hLC : LieComm) (hDO : DerivOne) (hId : GIdil)
    (hE : EisStrong) (hC : PositivityTheory.PfSWUS.CoefND)
    (hW : GlobalTheory.Published.WeilThetaConvergence) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) := by
  have hTM := tensMem
  have hTL := thLin_of hW
  exact main hA sFrame sEmb sigOK splitFock hTM (locOpEx_of_locFact hLF) hLi (linSec_of hTL)
    (gSplit_of gIwasawa hAA hLF awayIn schFP hTM lNZ) (gIauto_of hTA hTM) gIk
    (gIinv_of hTM hTL hLC hDO) hId hE gLamBd (gLsing PositivityTheory.Rg.Sw.twoSided' denseTau) hC
    (convRight_of hE) hTL lNZ

end PositivityTheory.Rg.Sw.Glob
end

