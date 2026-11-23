module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmBpAtEqOfShiftR
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0283
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0274
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0284

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CellIdentityShifted
section
namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section swap

variable {k r : ℕ} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']

theorem isDFrame_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ γ : B.Mat k r) :
    D.IsDFrame Ds' ν' m₀ γ ↔ D.IsDFrame Ds ν' m₀ γ := by
  simp only [D.IsDFrame, D.cofR, D.cofL, hz, hz']

theorem muR_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (_hz' : Ds'.z' = Ds.z') (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1))) :
    D.muR Ds' γ w = D.muR Ds γ w := by
  unfold D.muR D.rhoOfU
  rw [hz]

theorem inSS_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (q : B.SS k r) : Ds'.inSS q ↔ Ds.inSS q := by
  simp only [B.RealPlaceData.inSS, hz, hz']

theorem isNormCut_congr (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (γ : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ) :
    D.IsNormCut Ds' γ μR θ ↔ D.IsNormCut Ds γ μR θ := by
  simp only [D.IsNormCut, inSS_swap Ds Ds' hz hz']

theorem isRelevant_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (γ : B.Mat k r) : C6.IsRelevant Ds' γ ↔ C6.IsRelevant Ds γ := by
  simp only [C6.IsRelevant, hz, hz']

theorem muSS_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hW : Ds'.μW = Ds.μW)
    (hN : Ds'.μN = Ds.μN) (hW' : Ds'.μW' = Ds.μW') : Ds'.μSS = Ds.μSS := by
  simp only [B.RealPlaceData.μSS, hW, hN, hW']

theorem orbIntegrand_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (hπ : Ds'.π = Ds.π) (A : B.Mat k r → (Wq' →L[ℂ] Wq))
    (hA : WigEquiv Ds.z Ds.z' Ds.π' Ds'.π' A) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r)
    (hγ : γ ∈ B.GV k r) (hGγ : 0 < Gf k r Ds.z Ds.z' γ) (q : B.SS k r) (hq : Ds.inSS q) :
    D.orbIntegrand Ds' γ (fun g => (f g).comp (A g)) q = (D.orbIntegrand Ds γ f q).comp (A γ) := by
  obtain ⟨h1m, n1m, h2m, n2m⟩ := hq
  have o1 : ∀ w : Fin (2 * r + k + 1) → ℂ, Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ UWset k r w := by
    intro w
    rw [Matrix.of.apply_symm_apply]
    exact PBO.one_mem_UWset w
  have hq1 : Ds.inSS ((Matrix.of.symm (1 : B.Mat k r), q.1.2), (Matrix.of.symm (1 : B.Mat k r), q.2.2)) :=
    ⟨o1 Ds.z, n1m, o1 Ds.z', n2m⟩
  have hq0 : Ds.inSS ((q.1.1, q.1.2), (Matrix.of.symm (1 : B.Mat k r), q.2.2)) :=
    ⟨h1m, n1m, o1 Ds.z', n2m⟩
  have e1 : B.sgs ((Matrix.of.symm (1 : B.Mat k r), q.1.2), (Matrix.of.symm (1 : B.Mat k r), q.2.2)) γ
      = (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 := by
    simp only [B.sgs, Matrix.of.apply_symm_apply, inv_one, one_mul, mul_one]
  have e0 : B.sgs ((q.1.1, q.1.2), (Matrix.of.symm (1 : B.Mat k r), q.2.2)) γ
      = (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 := by
    simp only [B.sgs, Matrix.of.apply_symm_apply, inv_one, one_mul, mul_one]
  have g1GV : (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 ∈ B.GV k r :=
    Dx2.DF.mul_UH (Dx2.DF.mul_UH (WeylGroupFacts.uh_inv (B6.Nset_sub k r n1m)) hγ) (B6.Nset_sub k r n2m)
  have g0GV : (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 ∈ B.GV k r := by
    have := Dx2.DF.mul_UH (WeylGroupFacts.uh_inv (B6.UWset_sub k r Ds.z h1m)) g1GV
    simpa only [mul_assoc] using this
  have hG1 : 0 < Gf k r Ds.z Ds.z' ((Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2) := by
    rw [← e1, TBBx2.Gf_sgs Ds _ hq1]
    exact hGγ
  have hG0 : 0 < Gf k r Ds.z Ds.z' ((Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2) := by
    rw [← e0, TBBx2.Gf_sgs Ds _ hq0]
    exact hGγ
  have hAs : A (B.sgs q γ)
      = Ds.π' (Matrix.of q.2.1)⁻¹ ∘SL A γ ∘SL Ds'.π' (Matrix.of q.2.1) := by
    have s1 : B.sgs q γ
        = (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 * Matrix.of q.2.1 := rfl
    rw [s1, hA.2.2 _ g0GV hG0 _ h2m]
    have s2 : (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2
        = (Matrix.of q.1.1)⁻¹ * ((Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2) := by
      simp only [mul_assoc]
    rw [s2, hA.2.1 _ g1GV hG1 _ (WeylGroupFacts.uw_inv h1m),
      hA.1 γ hγ hGγ _ (WeylGroupFacts.mem_n_inv n1m) _ n2m]
  have h2m' : Matrix.of q.2.1 ∈ UWset k r Ds'.z' := by
    rw [hz']
    exact h2m
  have hcanc : Ds'.π' (Matrix.of q.2.1) ∘SL Ds'.π' (Matrix.of q.2.1)⁻¹ = 1 := by
    rw [← Ds'.π'_rep.2 _ h2m' _ (WeylGroupFacts.uw_inv h2m'), NFRadRedS.uw_mul_inv h2m', Ds'.π'_rep.1]
  have hxi : B.xiTau Ds' (1, 1) q = B.xiTau Ds (1, 1) q := by
    simp only [B.xiTau, hz, hz']
  simp only [D.orbIntegrand, B.rho, hxi, hπ]
  ext v
  have hv := congrArg (fun T => (T : Wq' →L[ℂ] Wq') v) hcanc
  have hv2 := congrArg (fun T => (T : Wq' →L[ℂ] Wq) ((Ds'.π' (Matrix.of q.2.1)⁻¹) v)) hAs
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at hv hv2
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [hv2, hv]

theorem orbJ_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (hπ : Ds'.π = Ds.π) (hW : Ds'.μW = Ds.μW) (hN : Ds'.μN = Ds.μN)
    (hW' : Ds'.μW' = Ds.μW') (A : B.Mat k r → (Wq' →L[ℂ] Wq)) (hA : WigEquiv Ds.z Ds.z' Ds.π' Ds'.π' A)
    (f : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (hγ : γ ∈ B.GV k r) (hGγ : 0 < Gf k r Ds.z Ds.z' γ)
    (μR : Measure (Mt k r)) (hrel : C6.IsRelevant Ds γ)
    (hH : B.IsHaarOn (C6.Rset γ) μR) (θ : B.SS k r → ℝ) (hθ : D.IsNormCut Ds γ μR θ)
    (hi : Integrable (fun q => θ q • D.orbIntegrand Ds γ f q) Ds.μSS) :
    D.orbJ Ds' γ μR (fun g => (f g).comp (A g)) = (D.orbJ Ds γ μR f).comp (A γ) := by
  set F' : B.Mat k r → Wq' →L[ℂ] Wp := fun g => (f g).comp (A g) with hF'
  have hθ' : D.IsNormCut Ds' γ μR θ := (isNormCut_congr Ds Ds' hz hz' γ μR θ).2 hθ
  have hrel' : C6.IsRelevant Ds' γ := (isRelevant_swap Ds Ds' hz hz' γ).2 hrel
  have hμ : Ds'.μSS = Ds.μSS := muSS_swap Ds Ds' hW hN hW'
  let L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq' →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq' Wq Wp).flip (A γ)
  have hL : ∀ X, L X = X.comp (A γ) := fun X => rfl
  have hae : ∀ᵐ q ∂Ds.μSS,
      θ q • D.orbIntegrand Ds' γ F' q = L (θ q • D.orbIntegrand Ds γ f q) := by
    filter_upwards [TBBx2.ae_inSS Ds] with q hq
    rw [hL, ContinuousLinearMap.smul_comp, orbIntegrand_swap Ds Ds' hz hz' hπ A hA f γ hγ hGγ q hq]
  have hi' : Integrable (fun q => θ q • D.orbIntegrand Ds' γ F' q) Ds'.μSS := by
    rw [hμ]
    exact (L.integrable_comp hi).congr (hae.mono fun q hq => hq.symm)
  have hex' : ∃ θ' : B.SS k r → ℝ, D.IsNormCut Ds' γ μR θ' ∧
      Integrable (fun p => θ' p • D.orbIntegrand Ds' γ F' p) Ds'.μSS := ⟨θ, hθ', hi'⟩
  have hex : ∃ θ' : B.SS k r → ℝ, D.IsNormCut Ds γ μR θ' ∧
      Integrable (fun p => θ' p • D.orbIntegrand Ds γ f p) Ds.μSS := ⟨θ, hθ, hi⟩
  unfold D.orbJ
  rw [dif_pos hex', dif_pos hex]
  rw [P.orbital_integral_indep_choice k r Wp Wq' Ds' γ μR hrel' hH F' _ θ hex'.choose_spec.1 hθ'
      hex'.choose_spec.2 hi',
    P.orbital_integral_indep_choice k r Wp Wq Ds γ μR hrel hH f _ θ hex.choose_spec.1 hθ hex.choose_spec.2 hi]
  rw [hμ, integral_congr_ae hae]
  exact L.integral_comp_comm hi

end swap

theorem cell_identity_shifted : CellIdSh := by
  obtain ⟨c₃, hc⟩ := Formalism.FourierDecayAlt.P.orbital_integral_converges
  refine ⟨c₃, ?_⟩
  intro Pa Wp Wq Wq' _ _ _ _ _ _ _ _ _ u u' p q f A A₀ hT hA hA₀ hf γ hγ hG
  obtain ⟨hz, hz', hπ, hW, hN, hW', hν, hm⟩ := hT
  have hG' : 0 < D.ptG (Tz Pa.k Pa.r p.T.base.z * Tz Pa.k Pa.r p.T.base.z') Pa.r γ := hG
  have hGq : 0 < D.ptG (Tz Pa.k Pa.r q.T.base.z * Tz Pa.k Pa.r q.T.base.z') Pa.r γ := by
    rw [hz, hz']
    exact hG'
  by_cases hex : ∃ g ∈ B.GV Pa.k Pa.r, Zhat Pa.k Pa.r p.T.base.z p.T.base.z' g = D.ptMatN γ (Pa.r + 1) ∧
      D.IsDFrame p.T.base p.ν' p.m₀ g
  · have hrep : ptRep p γ = hex.choose := dif_pos hex
    obtain ⟨hgGV, hZ, hF⟩ := hex.choose_spec
    rw [hrep]
    generalize hex.choose = g at hgGV hZ hF ⊢
    obtain ⟨hw, hd⟩ := Dx2.VV.ptMatN_monoP' γ (Pa.r + 1) hγ.2 hγ.1
    have hZq : Zhat Pa.k Pa.r q.T.base.z q.T.base.z' g = D.ptMatN γ (Pa.r + 1) := by
      rw [hz, hz']
      exact hZ
    have hFq : D.IsDFrame q.T.base q.ν' q.m₀ g := by
      rw [hν, hm]
      exact (isDFrame_swap p.T.base q.T.base hz hz' p.ν' p.m₀ g).2 hF
    have hZm := hZ.trans hw
    have hGf : 0 < Gf Pa.k Pa.r p.T.base.z p.T.base.z' g := by
      rw [TBBx2.Gf_of_Zhat _ _ g γ hZ]
      exact hG'
    have hrel := Final.d_ptRelevant _ _ _ _ p.T.base γ g hγ hgGV hZ
    have hH := Formalism.FourierDecayAlt.P.radial_measure_is_haar _ _ _ _ p.T.base g _ _ hgGV hd hZm
    obtain ⟨θ, hθ, hi⟩ := hc Pa.k Pa.r Wp Wq p.T.base g _ _ A₀ f hgGV hrel hd hZm hGf hA₀ hf
    simp only [KB.Pl.V]
    rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep _ _ _ _ q.T.base q.ν' q.m₀ _ γ hγ g q.hF hGq hgGV hZq hFq,
      Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep _ _ _ _ p.T.base p.ν' p.m₀ f γ hγ g p.hF hG' hgGV hZ hF]
    convert orbJ_swap p.T.base q.T.base hz hz' hπ hW hN hW' A hA f g hgGV hGf _ hrel hH θ hθ hi using 2
    congr 1
    exact muR_swap p.T.base q.T.base hz hz' g _
  · have h1 : ¬ ∃ g ∈ B.GV Pa.k Pa.r, Zhat Pa.k Pa.r q.T.base.z q.T.base.z' g = D.ptMatN γ (Pa.r + 1) ∧
        D.IsDFrame q.T.base q.ν' q.m₀ g := by
      rintro ⟨g, hg1, hg2, hg3⟩
      apply hex
      refine ⟨g, hg1, ?_, ?_⟩
      · rw [← hz, ← hz']
        exact hg2
      · rw [hν, hm] at hg3
        exact (isDFrame_swap p.T.base q.T.base hz hz' p.ν' p.m₀ g).1 hg3
    simp only [KB.Pl.V, D.vecV]
    rw [dif_pos ⟨hγ, hGq⟩]
    conv_rhs => rw [dif_pos ⟨hγ, hG'⟩, dif_neg hex, ContinuousLinearMap.zero_comp]
    exact dif_neg h1

end

end Formalism.FourierDecayAlt.P.CutBPEq
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFBddPtw
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

theorem pointwise_bound_normal_form_holds : NFBddPtw := by
  intro P L hTT hL b hb
  obtain ⟨C, Mx, hSA, hC, hM⟩ := Formalism.FourierDecayAlt.P.MAx3.AD.SAB_closure (hTTp := hTT) (hL := hL)
    (hLaw := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT.le) hb
  refine ⟨(Fintype.card (M.Ty P) : ℝ) * ((Fintype.card (M.Ty P) : ℝ) * C ^ 2), fun u q => ?_⟩
  have key : ∀ ρ, ‖MA.evQ P (MA.actA P b u ρ) q‖ ^ 2 ≤
      (Fintype.card (M.Ty P) : ℝ) * (C ^ 2 * ∑ ρ', ‖MA.evQ P (u ρ') q‖ ^ 2) := by
    intro ρ
    rw [hSA.1 u q ρ]
    have h1 : ‖∑ π', Mx q ρ π' * MA.evQ P (u π') q‖ ≤ ∑ π', C * ‖MA.evQ P (u π') q‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π' _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM q ρ π') (norm_nonneg _)
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (M.Ty P)))
      (f := fun π' => C * ‖MA.evQ P (u π') q‖)
    calc _ ≤ (∑ π', C * ‖MA.evQ P (u π') q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ = _ := by
        rw [Finset.card_univ]
        simp only [mul_pow, ← Finset.mul_sum]
  calc _ ≤ ∑ ρ : M.Ty P, (Fintype.card (M.Ty P) : ℝ) * (C ^ 2 * ∑ ρ', ‖MA.evQ P (u ρ') q‖ ^ 2) :=
        Finset.sum_le_sum fun ρ _ => key ρ
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFCoreNExt
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

theorem nf_coef_unique {E : Type*} [AddCommGroup E] [Module ℂ E] (M : ℕ) (a : ℕ → E) (S : Set ℂ)
    (hS : S.Infinite) (h : ∀ s ∈ S, ∑ i ∈ Finset.range M, s ^ i • a i = 0) : ∀ i < M, a i = 0 := by
  intro i hi
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (a i)).mp fun f => ?_
  have hp : (∑ j ∈ Finset.range M, Polynomial.C (f (a j)) * Polynomial.X ^ j) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ hS
    intro s hs
    have hfs := congrArg f (h s hs)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, smul_eq_mul] at hfs
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hfs]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hc := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q i) hp
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Finset.mem_range.mpr hi] using hc

section scoef

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nf_sum_pad {E : Type*} [AddCommGroup E] [Module ℂ E] {Q M : ℕ} (hQ : Q + 1 ≤ M) (x : ℂ)
    (u : Fin (Q + 1) → E) :
    ∑ i ∈ Finset.range M, x ^ i • (if h : i < Q + 1 then u ⟨i, h⟩ else 0) = ∑ q : Fin (Q + 1), x ^ (q : ℕ) • u q := by
  have h1 : ∑ i ∈ Finset.range (Q + 1), x ^ i • (if h : i < Q + 1 then u ⟨i, h⟩ else 0) =
      ∑ q : Fin (Q + 1), x ^ (q : ℕ) • u q := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [q.isLt]
  rw [← h1]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _ hi
    have hi' : ¬ i < Q + 1 := by simpa using hi
    rw [dite_eq_right hi', smul_zero]

theorem nf_scoef_unique (p : KB.Pl P Wp Wq) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) {Q Q' : ℕ}
    {L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq} {L' : Fin (Q' + 1) → B.DiffOp P.k P.r Wp Wq}
    (hS : IsSCoef p w e Q L) (hS' : IsSCoef p w e Q' L') (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (g : B.Mat P.k P.r) (hg : g ∈ C6.domL p.T.base ∅) (qq : Fin (Q + 1)) :
    B.opApply (L qq) F g = if h : (qq : ℕ) ≤ Q' then B.opApply (L' ⟨qq, by omega⟩) F g else 0 := by
  have hq1 : Q + 1 ≤ max Q Q' + 1 := Nat.succ_le_succ (le_max_left _ _)
  have hq2 : Q' + 1 ≤ max Q Q' + 1 := Nat.succ_le_succ (le_max_right _ _)
  have key : ∀ s : ℝ, ∑ q : Fin (Q + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L q) F g =
      ∑ q : Fin (Q' + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L' q) F g := by
    intro s
    have h1 := hS s F hF g hg
    have h2 := hS' s F hF g hg
    rw [h1] at h2
    simpa [Complex.ofReal_pow] using h2
  have hz := nf_coef_unique (max Q Q' + 1)
    (fun i => (if h : i < Q + 1 then B.opApply (L ⟨i, h⟩) F g else 0) -
      (if h : i < Q' + 1 then B.opApply (L' ⟨i, h⟩) F g else 0))
    (Set.range (fun s : ℝ => (s : ℂ))) (Set.infinite_range_of_injective Complex.ofReal_injective) ?_ qq
    (lt_of_lt_of_le qq.isLt hq1)
  · simp only [sub_eq_zero] at hz
    rw [dite_eq_left qq.isLt] at hz
    by_cases hq : (qq : ℕ) ≤ Q'
    · rw [dite_eq_left hq]
      rw [dite_eq_left (by omega : (qq : ℕ) < Q' + 1)] at hz
      exact hz
    · rw [dite_eq_right hq]
      rw [dite_eq_right (by omega : ¬ (qq : ℕ) < Q' + 1)] at hz
      exact hz
  · rintro _ ⟨s, rfl⟩
    have e1 : ∑ i ∈ Finset.range (max Q Q' + 1),
        (s : ℂ) ^ i • (if h : i < Q + 1 then B.opApply (L ⟨i, h⟩) F g else 0) =
        ∑ q : Fin (Q + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L q) F g :=
      nf_sum_pad hq1 (s : ℂ) (fun q => B.opApply (L q) F g)
    have e2 : ∑ i ∈ Finset.range (max Q Q' + 1),
        (s : ℂ) ^ i • (if h : i < Q' + 1 then B.opApply (L' ⟨i, h⟩) F g else 0) =
        ∑ q : Fin (Q' + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L' q) F g :=
      nf_sum_pad hq2 (s : ℂ) (fun q => B.opApply (L' q) F g)
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [e1, e2, key s, sub_self]

end scoef

section extract

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nf_xD_pow (b : ℕ) : xD (fun x : ℝ => x ^ b) = fun x => (b : ℝ) * x ^ b := by
  funext x
  show x * deriv (fun x : ℝ => x ^ b) x = (b : ℝ) * x ^ b
  rw [(hasDerivAt_pow b x).deriv]
  rcases b with _ | b
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring

theorem nf_xD_const_mul (c : ℝ) (φ : ℝ → ℝ) : xD (fun x => c * φ x) = fun x => c * xD φ x := by
  funext x
  show x * deriv (fun x => c * φ x) x = c * (x * deriv φ x)
  rw [deriv_const_mul_field]
  ring

theorem nf_xD_iter_pow (b q : ℕ) : xD^[q] (fun x : ℝ => x ^ b) = fun x => (b : ℝ) ^ q * x ^ b := by
  induction q with
  | zero => funext x; simp
  | succ q ih =>
    rw [Function.iterate_succ_apply', ih]
    have h1 := nf_xD_const_mul ((b : ℝ) ^ q) (fun x => x ^ b)
    rw [h1, nf_xD_pow]
    funext x
    push_cast
    ring

private theorem sum_pow_mul_choose_eq_add_pow (Q' p₀ : ℕ) (s : ℂ) (j : Fin (Q' + 1)) :
    ∑ q : Fin (Q' + 1), s ^ (q : ℕ) * ((Nat.choose j q * p₀ ^ ((j : ℕ) - q) : ℕ) : ℂ) =
      ((p₀ : ℂ) + s) ^ (j : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun q => s ^ q * ((Nat.choose j q * p₀ ^ ((j : ℕ) - q) : ℕ) : ℂ)),
    show (p₀ : ℂ) + s = s + p₀ from add_comm _ _, add_pow]
  have hterm : ∀ m, s ^ m * ((Nat.choose j m * p₀ ^ ((j : ℕ) - m) : ℕ) : ℂ) =
      s ^ m * (p₀ : ℂ) ^ ((j : ℕ) - m) * (Nat.choose j m : ℂ) := by
    intro m
    push_cast
    ring
  simp only [hterm]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _ hi
    have hji : (j : ℕ) < i := by simpa using hi
    simp [Nat.choose_eq_zero_of_lt hji]

private theorem coeff_eq_zero_of_sum_pow_smul_eq_zero_nat {E : Type*} [AddCommGroup E] [Module ℂ E] {Q' : ℕ}
    (w : Fin (Q' + 1) → E) (h : ∀ s : ℕ, ∑ q : Fin (Q' + 1), ((s : ℂ) ^ (q : ℕ)) • w q = 0)
    (qq : Fin (Q' + 1)) : w qq = 0 := by
  have hS : (Set.range (Nat.cast : ℕ → ℂ)).Infinite :=
    Set.infinite_range_of_injective Nat.cast_injective
  have := nf_coef_unique (Q' + 1) (fun i => if hi : i < Q' + 1 then w ⟨i, hi⟩ else 0) _ hS
    (fun x hx => by
      obtain ⟨s, rfl⟩ := hx
      rw [nf_sum_pad le_rfl]
      exact h s) qq qq.isLt
  simpa [Nat.lt_succ_iff.mp qq.isLt] using this

theorem nf_vExtract (p : KB.Pl P Wp Wq) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) {Q' : ℕ}
    (L' : Fin (Q' + 1) → B.DiffOp P.k P.r Wp Wq) (CcL : ℝ)
    (hLe : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ),
      B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
      CcL * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
        p.V (p.Θ.Θ w e (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g)) γ =
          ∑ q : Fin (Q' + 1), (((xD^[(q : ℕ)] φ) (TBB.Gp p γ) : ℝ) : ℂ) • p.V (B.opApply (L' q) F) γ)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (hf : B.CkOn ⊤ (B.GV P.k P.r) f)
    (hcc : ∀ m : ℕ, B.InCC A₀ m f)
    (hthr : CcL * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ))
    (γ : C.LPt) (hl : D.IsLocPt γ (P.r + 1)) (hG : 0 < TBB.Gp p γ) (qq : Fin (Q' + 1)) :
    p.V (B.opApply (L' qq) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀)) γ =
      ((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) • ∑ j : Fin (Q' + 1),
        (((Nat.choose j qq * p₀ ^ ((j : ℕ) - qq) : ℕ) : ℂ)) • p.V (B.opApply (L' j) f) γ := by
  have hfp := fpm_id p f p₀
  rw [hfp]
  have hthr0 : CcL * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ := hthr.trans (sub_le_self _ (Nat.cast_nonneg _))
  have hck : B.CkOn ⊤ (B.GV P.k P.r)
      (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f g) :=
    ckOn_Gpow_smul _ _ p₀ hf
  have hcc' := inCC_fpm_id p p₀ hcc
  rw [hfp] at hcc'
  have hG0 : ((TBB.Gp p γ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  have hsum_c : ∀ s : ℕ, ∑ q : Fin (Q' + 1), ((s : ℂ) ^ (q : ℕ)) •
      (((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) • ∑ j : Fin (Q' + 1),
        (((Nat.choose j q * p₀ ^ ((j : ℕ) - q) : ℕ) : ℂ)) • p.V (B.opApply (L' j) f) γ) =
      ((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) • ∑ j : Fin (Q' + 1),
        (((p₀ : ℂ) + s) ^ (j : ℕ)) • p.V (B.opApply (L' j) f) γ := by
    intro s
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_pow_mul_choose_eq_add_pow Q' p₀ (s : ℂ) j, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    ring
  have key : ∀ s : ℕ, ∑ q : Fin (Q' + 1), ((s : ℂ) ^ (q : ℕ)) •
      (p.V (B.opApply (L' q) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f g)) γ -
        ((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) • ∑ j : Fin (Q' + 1),
          (((Nat.choose j q * p₀ ^ ((j : ℕ) - q) : ℕ) : ℂ)) • p.V (B.opApply (L' j) f) γ) = 0 := by
    intro s
    have e1 := hLe (fun x => x ^ s) (contDiff_id.pow s) _ _ hck hcc' hthr γ hl hG
    have e2 := hLe (fun x => x ^ (p₀ + s)) (contDiff_id.pow _) f A₀ hf hcc hthr0 γ hl hG
    simp only [nf_xD_iter_pow] at e1 e2
    have hH : (fun g => (((Gf P.k P.r p.T.base.z p.T.base.z' g) ^ s : ℝ) : ℂ) •
        ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f g) =
        (fun g => (((Gf P.k P.r p.T.base.z p.T.base.z' g) ^ (p₀ + s) : ℝ) : ℂ) • f g) := by
      funext g
      rw [smul_smul, ← Complex.ofReal_mul, ← pow_add, add_comm]
    rw [hH, e2] at e1
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [hsum_c s, sub_eq_zero]
    apply smul_right_injective _ (pow_ne_zero s hG0)
    simp only [Finset.smul_sum, smul_smul]
    have h3 : ∀ x : Fin (Q' + 1), ((TBB.Gp p γ : ℝ) : ℂ) ^ s * (s : ℂ) ^ (x : ℕ) =
        (((s : ℝ) ^ (x : ℕ) * TBB.Gp p γ ^ s : ℝ) : ℂ) := by
      intro x
      push_cast
      ring
    have h4 : ∀ x : Fin (Q' + 1), ((TBB.Gp p γ : ℝ) : ℂ) ^ s *
        (((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) * ((p₀ : ℂ) + s) ^ (x : ℕ)) =
        (((((p₀ + s : ℕ) : ℝ)) ^ (x : ℕ) * TBB.Gp p γ ^ (p₀ + s) : ℝ) : ℂ) := by
      intro x
      push_cast
      ring
    simp only [h3, h4]
    exact e1.symm
  have := coeff_eq_zero_of_sum_pow_smul_eq_zero_nat _ key qq
  exact sub_eq_zero.mp this

end extract

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDMAll
section
namespace Formalism.FourierDecayAlt.P.CutBP.TDM

theorem topDMeasCpt_of_typeNormMeas (h : TypeNormMeas) : TopDMeasCpt :=
  topDMeasCpt_of_parts h vector_positive_cone diff_operator_in_class_CC scalar_point_measurability_holds empty_list_measurability_holds

end Formalism.FourierDecayAlt.P.CutBP.TDM
end

