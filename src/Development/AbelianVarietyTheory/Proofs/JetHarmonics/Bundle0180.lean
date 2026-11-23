module

public import Mathlib
public import Formalism.HermitianCurvature.Bundle0010
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPowSmulCompPolyFamilyEigenSu
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0174
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0280
public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0281
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqShift
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormaliserAcrossPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormCutoffTendstoOfDensityDomination

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EnergyBoundPolynomialWeightPowCapelliEigen
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem energy_bound_gfPow_smul_comp_polyOp : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wf : Type) [NormedAddCommGroup Wf] [InnerProductSpace ℂ Wf] [FiniteDimensional ℂ Wf] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wf →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq →L[ℂ] Wf)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq →L[ℂ] Wf)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → (p.RR (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g))).re := by
  intro hXi Wp Wq _ _ _ _ _ _ Wf _ _ _ P p lam lam' cs A₀ p₀ dA nn f Aop Y N hA hC hI hE hgap hcl hAB hnn
    w hw hN
  have hgap' : ∀ s t, s ≠ t →
      2 * (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) < |lam' s - lam' t| := by
    intro s t hst
    have h1 := hgap s t hst
    have h2 := hcl s
    have h3 := hcl t
    have h4 : |lam s - lam t| ≤ |lam' s - lam' t| + |lam' s - lam s| + |lam' t - lam t| := by
      have e : lam s - lam t = (lam' s - lam' t) - (lam' s - lam s) + (lam' t - lam t) := by ring
      rw [e]
      have a1 := abs_add_le ((lam' s - lam' t) - (lam' s - lam s)) (lam' t - lam t)
      have a2 := abs_sub (lam' s - lam' t) (lam' s - lam s)
      linarith
    linarith
  have hes := _root_.GlobalTheory.gfPow_smul_comp_polyOp_eigenSum P.k P.r Wp Wf Wq p.T.base.z p.T.base.z' lam' A₀ p₀ dA f Aop hgap'
    ⟨hC, hI⟩ hE hA
  refine GlobalTheory.levelZero_form_le_normC_of_eigen_sum hXi Wp Wq P p lam' ((2 * P.r + 2) * p₀ + dA) _ nn _ Y N hAB hes ?_ w hw hN
  intro y
  refine le_trans (Finset.prod_le_prod₀ (fun s _ => by positivity) (fun s _ => ?_)) (hnn y)
  have h2 := hcl s
  have e : y + lam' s = (y + lam s) + (lam' s - lam s) := by ring
  have a1 := abs_add_le (y + lam s) (lam' s - lam s)
  rw [e]
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.JetBoundEqualTypesThreePlacesOfXiIntegrable
section
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.JetBoundEqualTypesReg

theorem of_compact : P5.ThmPActualCpt → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) → LimEvT pp χ (fpmSh pp f Ap p₀) Yp N → LimEvT pm χ (fpmSh pm f Am p₀) Ym N → LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro hA Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₂, Cc, hC₂, hPt⟩ := GlobalTheory.PointwiseBoundDecay.main hA Cb
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.JetBoundShifted.main C₃ CΛ C₀ C₂ hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, Cc, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₀ n₀ p₀ d χ nnp nnm
    Yp Ym K N hb hΛ hΛb hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf hfA hAp hAm hth
    hAms hReg hWGp hLGp hWGm hLGm hI5p hI5m hDp hDm hBdp hBdm
  have hNorm := normaliser_across_places P Wp Wq Wqp Wqm up up' um um' p pp pm f Ap Am ApPt AmPt b n₀ p₀
    hzp hzp' hzm hzm' hAms
  have hdp := shifted_decay P Wp Wq Wqp up up' pp f Ap A₀ d p₀ hfA hAp
  have hdm := shifted_decay P Wp Wq Wqm um um' pm f Am A₀ d p₀ hfA hAm
  have hPp := hPt Wp Wqp (shP P up up') pp (fpmSh pp f Ap p₀) Λ _ χ nnp Yp K N hΛ hK hKN hχ hnnp hDDp
    (ckOn_fpmSh pp p₀ hf (ckOn_of_polyOp hAp)) hdp hth hWGp hLGp hI5p hDp hBdp
  have hPm := hPt Wp Wqm (shP P um um') pm (fpmSh pm f Am p₀) Λ _ χ nnm Ym K N hΛ hK hKN hχ hnnm hDDm
    (ckOn_fpmSh pm p₀ hf (ckOn_of_polyOp hAm)) hdm hth hWGm hLGm hI5m hDm hBdm
  exact hC₄ P Wp Wq Wqp Wqm up up' um um' p pp pm f _ _ b Λ n₀ p₀ hb hΛ hΛb hn₀ hp₀
    (ttp_eq p pp hzp hzp') (ttp_eq p pm hzm hzm') hNorm hPp hPm hReg

theorem main : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) → LimEvT pp χ (fpmSh pp f Ap p₀) Yp N → LimEvT pm χ (fpmSh pm f Am p₀) Ym N → LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N → TBB.ThmBpAt p f b C₄ n₀ p₀ :=
  fun _ => of_compact

end GlobalTheory.JetBoundEqualTypesReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TendstoLevelZeroFormCutoffPowMulOfDomination
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory

namespace GlobalTheory


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem limEvT_pow_mul_of_topDomination : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ), NFHyp Cb Cc p f A₀ p₀ χ N → LimEvT p χ (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N := by
  intro hX hP hDom Cb
  obtain ⟨C1, h1⟩ := _root_.GlobalTheory.levelZeroForm_cutoff_tendsto_of_domination hX hP Cb
  obtain ⟨C2, h2⟩ := hDom Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
  have hpos : (0 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 4 := by positivity
  have hpos' : (0 : ℝ) ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by
    positivity
  have hC1 := le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left C1 C2) hpos) hpos') a5
  have hC2 := le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right C1 C2) hpos) hpos') a5
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) :=
    fun g₀ _ => ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial,
      contDiffOn_const, fun _ _ _ => rfl⟩
  exact h1 Wp Wq P p _ χ _ N Y a2 a1 (ckOn_fpm p p₀ a3 hid) (inCC_fpm_id p p₀ a4) hC1
    (fun w hw hN => h2 Wp Wq P p f A₀ p₀ χ Y N ⟨a1, a2, a3, a4, hC2, a6⟩ w hw hN)

end GlobalTheory
end

