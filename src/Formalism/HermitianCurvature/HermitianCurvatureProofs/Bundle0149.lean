module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurePreservingProdPermThree
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0144
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0147

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiCStarMul
section
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section pw

variable {k r : ℕ}

theorem hMat_monoP (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) : U.hMat σ d = C2.monoP σ.symm d := by
  ext i a
  simp only [U.hMat, U.wP, C2.monoP, Matrix.mul_diagonal, Matrix.of_apply]
  by_cases h : σ i = a
  · have h' : i = σ.symm a := by rw [← h, Equiv.symm_apply_apply]
    simp [h, h']
  · have h' : ¬ i = σ.symm a := fun hh => h (by rw [hh, Equiv.apply_symm_apply])
    simp [h, h']

theorem headH_eq (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (v : U.LW σ → ℂ) (u : G.UT r → ℂ) :
    U.headH σ d v u = StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)) * C2.monoP σ.symm d * G.upper u := by
  have h := StabilizerDisintegration.UC.permutationMatrix_mul_lowerUnipotent (σ := σ) (fun q => v (StabilizerDisintegration.UC.iota σ q))
  simp only [Equiv.apply_symm_apply] at h
  rw [U.headH, h, Matrix.mul_assoc (StabilizerDisintegration.lowP σ.symm _) (U.wP σ), ← U.hMat, hMat_monoP]

theorem psiC_add (c x y : ℂ) : C2.psiC c (x + y) = C2.psiC c x * C2.psiC c y := by
  unfold C2.psiC
  rw [← Complex.exp_add]
  congr 1
  simp only [mul_add, Complex.add_re, Complex.ofReal_add]

theorem psiC_star_mul (c x : ℂ) : C2.psiC c x * star (C2.psiC c x) = 1 := by
  have key : ∀ t : ℝ, Complex.exp (Complex.I * t) * star (Complex.exp (Complex.I * t)) = 1 := by
    intro t
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [show Complex.I * (t : ℂ) + -Complex.I * (t : ℂ) = 0 by ring, Complex.exp_zero]
  exact key _

end pw

section pwmain

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def Amat (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (x0 : C2.Lstidx σ.symm → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  (C2.monoP σ.symm d)⁻¹ * StabilizerDisintegration.lowS σ.symm x0 * C2.monoP σ.symm d

private theorem mul_mem_utset_of_mem {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m)
    (hB : B ∈ C2.UTset m) : A * B ∈ C2.UTset m := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_or_ge l i with hl | hl
    · rw [hA.1 i l hl, zero_mul]
    · rw [hB.1 l j (lt_of_lt_of_le hji hl), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, mul_one]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with hl' | hl'
      · rw [hA.1 i l hl', zero_mul]
      · rw [hB.1 l i hl', mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

theorem integrand_pw (S : B.RealPlaceData k r Wp Wq) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (h h' : Mt k r) (hh : Matrix.of h ∈ UWset k r S.z) (hh' : Matrix.of h' ∈ UWset k r S.z')
    (p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ) :
    theta0 S.z σ.symm (TN k r ((h, (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).1),
        (h', (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).2))) •
      D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F
        (TN k r ((h, (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).1),
          (h', (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).2))) =
    chiL σ.symm p.1 • ((S.π (Matrix.of h)).comp
      ((U.psiStar k 0 σ S.z S.z' p.2 • F (U.gaXi k 0 σ d p.2 (fun a => a.elim0)
        ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h')))).comp (S.π' (Matrix.of h')⁻¹))) := by
  obtain ⟨x0, ⟨⟨y, y'⟩, ⟨⟨a, b⟩, ⟨v, u⟩⟩⟩⟩ := p
  have hhL : Matrix.of h ∈ UWset k (r + 0) (liftVec k r 0 z0) := hz ▸ hh
  have hhL' : Matrix.of h' ∈ UWset k (r + 0) (liftVec k r 0 z0') := hz' ▸ hh'
  have hY := uw_mid r 0 z0 _ hhL
  have hY' := uw_mid r 0 z0' _ hhL'
  have hYu : IsUnit (midB r 0 (Matrix.of h)).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hY.1
  have hY'u : IsUnit (midB r 0 (Matrix.of h')).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hY'.1
  have hAm : Amat σ d x0 ∈ C2.UTset r := conjS_UT hd x0
  have hAmi : (Amat σ d x0)⁻¹ ∈ C2.UTset r := ut_inv_mem hAm
  have hup : G.upper u ∈ C2.UTset r := StabilizerDisintegration.UC.upper_mem u
  have hprod : (Amat σ d x0)⁻¹ * G.upper u ∈ C2.UTset r := mul_mem_utset_of_mem hAmi hup
  have hV' : G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)) = (Amat σ d x0)⁻¹ * G.upper u := ut_of_mem hprod
  have hAmu : IsUnit (Amat σ d x0).det := ut_det hAm
  have hZu : IsUnit (U.hMat σ d).det := by
    rw [U.hMat, Matrix.det_mul, Matrix.det_diagonal]
    exact (Formalism.FourierDecayAlt.P.Dx2.SL.isUnit_wP σ).mul
      (isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => hd a))
  have hγ0u : IsUnit γ0.det := gv_unit hγ0
  have hmat : (G.upper (StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q)))))ᴴ * U.hMat σ d * G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)) = U.headH σ d v u := by
    rw [hMat_monoP, orbit_split hd, headH_eq, hV']
    show _ * _ * G.upper (StabilizerDisintegration.utc (Amat σ d x0 * ((Amat σ d x0)⁻¹ * G.upper u))) = _
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAmu, Matrix.one_mul, StabilizerDisintegration.UC.utc_upper]
  have hsgs : B.sgs ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) (U.mMap k r 0 (U.hMat σ d) γ0) =
      U.gaXi k 0 σ d ((y, y'), ((a, b), (v, u))) (fun a => a.elim0) ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h')) := by
    rw [sgs_formula z0 z0' h h' hhL hhL', rnAct_inv_rnAct hYu, rnAct_inv_rnAct hY'u, hmat, gaXi_zero]
  have hθ : theta0 S.z σ.symm ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = chiL σ.symm x0 := by
    simp only [theta0, psiR, Equiv.apply_symm_apply, blkU_uMap_muP_Rn, x0c, StabilizerDisintegration.UC.utc_upper]
    show chiL σ.symm ((StabilizerDisintegration.UC.eSp σ.symm).symm (StabilizerDisintegration.UC.eSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))).1 = chiL σ.symm x0
    rw [MeasurableEquiv.symm_apply_apply]
  have hUU : ∀ w : G.UT r → ℂ, Formalism.DoubleCosetMeasures.IsUpUni (G.upper w) := fun w =>
    ⟨fun i j hij => (StabilizerDisintegration.UC.upper_mem w).1 i j hij, (StabilizerDisintegration.UC.upper_mem w).2⟩
  have hr1 : psi k r S.z cStd (U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h)) y)) = psi k r S.z cStd (U.Rn k r 0 y) := by
    have e := psi_rnAct z0 cStd _ hY (rnAct (midB r 0 (Matrix.of h)) y)
    rw [rnAct_inv_rnAct hYu] at e
    rw [hz]
    exact e.symm
  have hr2 : psi k r S.z' cStd (U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h')) y')) = psi k r S.z' cStd (U.Rn k r 0 y') := by
    have e := psi_rnAct z0' cStd _ hY' (rnAct (midB r 0 (Matrix.of h')) y')
    rw [rnAct_inv_rnAct hY'u] at e
    rw [hz']
    exact e.symm
  have hs1 : C2.simpleUp (G.upper (StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))) = C2.simpleUp (StabilizerDisintegration.lowS σ.symm x0)ᴴ +
      C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ := by
    rw [StabilizerDisintegration.UC.upper_fSp]
    exact simpleUp_mul (StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowS_mem σ.symm x0).1)
      (StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowerUnipotent_mem σ.symm _).1)
  have hs2 : C2.simpleUp (G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u))) = C2.simpleUp (Amat σ d x0)⁻¹ + C2.simpleUp (G.upper u) := by
    rw [hV']
    exact simpleUp_mul hAmi hup
  have hMu : IsUnit (C2.monoP σ.symm d).det := hMat_monoP σ d ▸ hZu
  have hinv : (U.hMat σ d)⁻¹ * ((StabilizerDisintegration.lowS σ.symm x0)ᴴᴴ)⁻¹ * U.hMat σ d = (Amat σ d x0)⁻¹ := by
    rw [Matrix.conjTranspose_conjTranspose, hMat_monoP]
    show _ = ((C2.monoP σ.symm d)⁻¹ * StabilizerDisintegration.lowS σ.symm x0 * C2.monoP σ.symm d)⁻¹
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hMu]
    simp only [Matrix.mul_assoc]
  have hrelU : C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowS σ.symm x0)ᴴ) =
      C2.psiC cStd (C2.simpleUp (Amat σ d x0)⁻¹) := by
    have hQ : (StabilizerDisintegration.lowS σ.symm x0)ᴴ ∈ C2.UTset r := StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowS_mem σ.symm x0).1
    have hQ' : (U.hMat σ d)⁻¹ * ((StabilizerDisintegration.lowS σ.symm x0)ᴴᴴ)⁻¹ * U.hMat σ d ∈ C2.UTset r := by
      rw [hinv]
      exact hAmi
    rw [relevance_U S (U.hMat σ d) hZu γ0 hγ0u hrel _ hQ hQ', hinv]
  have hw : U.wP σ * U.lowW σ v * (U.wP σ)⁻¹ = StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)) := by
    have e := StabilizerDisintegration.UC.conj_lowW σ (fun q => v (StabilizerDisintegration.UC.iota σ q))
    simp only [Equiv.apply_symm_apply] at e
    exact e
  have hright : G.psi U.betaU (U.subS (U.wP σ * U.lowW σ v * (U.wP σ)⁻¹) + U.supS (G.upper u)) =
      C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper u))) := by
    rw [StabilizerDisintegration.UC.psi_conj, map_add (f := _), psiC_add, hw, ← StabilizerDisintegration.UC.subS_eq, ← StabilizerDisintegration.UC.psi_conj,
      StabilizerDisintegration.UC.psi_star, StabilizerDisintegration.UC.supS_eq]
  have hstar := psiC_star_mul cStd (C2.simpleUp (Amat σ d x0)⁻¹)
  have hxi : B.xiTau S (1, 1) ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = U.psiStar k 0 σ S.z S.z' ((y, y'), ((a, b), (v, u))) := by
    rw [xiTau_one, psiStar_zero]
    simp only [psiR, Equiv.apply_symm_apply]
    rw [Formalism.FourierDecayAlt.P.PBG.psi_mul_nset S.z S.z_mem cStd (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ (hUU _))
        (Formalism.FourierDecayAlt.P.Ux3.rn_nset _),
      Formalism.FourierDecayAlt.P.PBG.psi_mul_nset S.z' S.z'_mem cStd (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ (hUU _))
        (Formalism.FourierDecayAlt.P.Ux3.rn_nset _),
      psi_muP S.z S.z_mem, psi_muP S.z' S.z'_mem, hr1, hr2, hs1, hs2, psiC_add, psiC_add, hrelU, hright,
      star_mul', star_mul']
    linear_combination (C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ) *
      psi k r S.z cStd (U.Rn k r 0 y) * star (C2.psiC cStd (C2.simpleUp (G.upper u))) *
      star (psi k r S.z' cStd (U.Rn k r 0 y'))) * hstar
  have hphi : phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) (x0, ((y, y'), ((a, b), (v, u)))) =
      ((rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q)))), (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u))) := rfl
  rw [hphi]
  dsimp only
  rw [show TN k r ((h, (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) from rfl,
    D.orbIntegrand, B.rho]
  dsimp only
  rw [hθ, hxi, hsgs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end pwmain

end Formalism.FourierDecayAlt.P.PBM
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.QuadAOf
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

set_option maxHeartbeats 800000 in
theorem quadA_of (hSch : SchurH) (hNIs : NormIdSm) (hNI : NormInv) (hGG : GrowthG)
    (hDD : DecDD) (hBC : BeConv) (hIn : Inputs) {k r : ℕ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    {u u' : Fin k → ℝ} {νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hS1 : Side k r ε lam h σ w0 D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq)
    (hS2 : Side k r ε lam h σ w0 D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq')
    {l : H → Wp} {l' : H → Wq}
    (hbe : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z Formalism.QuantumDeterminants.cStd D.π σ D.μW D.μN x y = (innerSL ℂ (l y)).smulRight (l x))
    (hbe' : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z' Formalism.QuantumDeterminants.cStd D.π' σ D.μW' D.μN x y = (innerSL ℂ (l' y)).smulRight (l' x))
    {γ : Mx k r} (hγ : γ ∈ Formalism.FourierDecayAlt.JF.Om k r D.z D.z') :
    ∫⁻ zz, ∫⁻ zz', ∫⁻ s, ∫⁻ s',
      ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
        ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l' (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
      ∂(muSof D.μW' D.μN) ∂(muSof D.μW D.μN) ∂νq' ∂νq < ⊤ := by
  have hS1' := hS1
  obtain ⟨hl, hds, -, hG, hw0, hz1, hT, -, hπ, hW, hN, hGm, hq⟩ := hS1'
  have hS2' := hS2
  obtain ⟨-, -, -, -, -, hz2, hT', -, hπ', hW', -, -, hq'⟩ := hS2'
  have : SigmaFinite D.μW := hW.1
  have : SigmaFinite D.μN := hN.1
  have : SigmaFinite D.μW' := hW'.1
  have : SigmaFinite D.μG := hGm.1
  have hGc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hGm.2.2.1
  have hw0DD := cmHalfIntegralGenerator_mem_algebraicClosure hds w0
  have hf1 := DDSmoothness.muSof_facts hW hN
  have hf2 := DDSmoothness.muSof_facts hW' hN
  have hae1 := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hf1.1 hf1.2 hq
  have hae2 := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hf2.1 hf2.2 hq'
  have hγU : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := hγ.1

  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  swap
  · push Not at hA
    calc _ ≤ ∫⁻ zz, (0 : ℝ≥0∞) ∂νq := by
          apply lintegral_mono_ae
          filter_upwards [hae1] with zz hzz
          simp [hA _ (dd_stable hds hzz w0 hw0DD)]
      _ < ⊤ := by simp
  by_cases hA' : ∃ v ∈ DDsp σ w0, l' v ≠ 0
  swap
  · push Not at hA'
    calc _ ≤ ∫⁻ zz, (0 : ℝ≥0∞) ∂νq := by
          apply lintegral_mono
          intro zz
          calc _ ≤ ∫⁻ zz', (0 : ℝ≥0∞) ∂νq' := by
                apply lintegral_mono_ae
                filter_upwards [hae2] with zz' hzz'
                simp [hA' _ (dd_stable hds hzz' w0 hw0DD)]
            _ = 0 := by simp
      _ < ⊤ := by simp
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨v', hv', hlv'⟩ := hA'
  obtain ⟨e0, he0, hee0⟩ := coef_ext hds w0 w0
  obtain ⟨e1, he1, hee1⟩ := coef_ext hds v w0
  obtain ⟨e2, he2, hee2⟩ := coef_ext hds v' w0
  obtain ⟨C0, hC0⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD
    w0 hw0DD
  obtain ⟨C1, hC1⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD v hv
  obtain ⟨C2, hC2⟩ := hDD hIn k r ε lam h H σ w0 Wq D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq' hS2 w0 hw0DD
    v' hv'
  have hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee0 y hy]; exact hC0 y hy
  have hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee1 y hy]; exact hC1 y hy
  have hb2 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e2 y‖ ≤ C2 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee2 y hy]; exact hC2 y hy
  have h4 := gap4 hG
  have hAG := ag_nonneg k r
  have hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hb0 : 0 < aOf r h - AG k r - 1 := by linarith
  have hba : aOf r h - AG k r - 1 ≤ aOf r h := by linarith
  have hab : aOf r h - (aOf r h - AG k r - 1) = AG k r + 1 := by ring
  have hThrb : JF.TransportedAlt k r (aOf r h - AG k r - 1) 0 := by
    unfold JF.TransportedAlt
    have hpos : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hpos]
    linarith
  have hKg : ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG < ⊤ :=
    (hGG k r D.μG _ hGm (by rw [hab]; linarith)).hasFiniteIntegral
  have hLa0 := la_fin hNI D hThrb hb0.ne' hγ
  obtain ⟨La, hLadef⟩ : ∃ La : ℝ≥0∞, La = ∫⁻ p, ∫⁻ q, ‖B.gN ((Matrix.of p.1 * Matrix.of p.2) * γ *
    (Matrix.of q.1 * Matrix.of q.2)⁻¹) ^ (-(aOf r h - AG k r - 1))‖ₑ ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) :=
    ⟨_, rfl⟩
  have hLa : La < ⊤ := by
    have hmG := meas_G (k := k) (r := r) γ (aOf r h - AG k r - 1)
    have e : La = ∫⁻ pp, ‖B.gN (Matrix.of pp.1.1 * Matrix.of pp.1.2 * γ * (Matrix.of pp.2.2)⁻¹ *
        (Matrix.of pp.2.1)⁻¹) ^ (-(aOf r h - AG k r - 1))‖ₑ ∂D.μSS := by
      rw [show D.μSS = (D.μW.prod D.μN).prod (D.μW'.prod D.μN) from rfl, lintegral_prod _ hmG.aemeasurable, hLadef]
      apply lintegral_congr; intro p; apply lintegral_congr; intro q
      rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
    rw [e]; exact hLa0
  have hpUH : ∀ᵐ p ∂(D.μW.prod D.μN), Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    (prod_ae hW hN).mono fun p hp => DDSmoothness.uh_mul hp.1.1 hp.2.1
  have hqUH : ∀ᵐ q ∂(D.μW'.prod D.μN), Matrix.of q.1 * Matrix.of q.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    (prod_ae hW' hN).mono fun q hq => DDSmoothness.uh_mul hq.1.1 hq.2.1
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ≥0∞, K1 = ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ≥0∞, K2 = ‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ := ⟨_, rfl⟩
  have hK : K1 * K2 ≠ ⊤ := by rw [hK1, hK2]; simp [ENNReal.mul_eq_top]
  have hA1m := Aext_meas he1
  have hA2m := Aext_meas he2
  have hI2m := Iint_meas hA2m (D.μW'.prod D.μN)
  have hLm := meas_lam he0 γ (D.μW.prod D.μN) (D.μW'.prod D.μN)
  obtain ⟨LL, hLL⟩ : ∃ LL : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞,
      LL = abelian₂ e0 γ (D.μW.prod D.μN) (D.μW'.prod D.μN) := ⟨_, rfl⟩
  have hLLm : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => LL t.1 t.2) := by rw [hLL]; exact hLm

  have step1 : ∀ᵐ zz ∂νq, ∀ᵐ zz' ∂νq', ∫⁻ s, ∫⁻ s',
      ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
        ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l' (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
      ∂(muSof D.μW' D.μN) ∂(muSof D.μW D.μN) ≤
      (K1 * K2) * (Iint (Aext e1) (D.μW.prod D.μN) zz * (Iint (Aext e2) (D.μW'.prod D.μN) zz' * LL zz zz')) := by
    filter_upwards [hae1] with zz hzz
    filter_upwards [hae2] with zz' hzz'
    have bl : ‖l (σ (Matrix.of zz) w0)‖ₑ ≤ K1 * Iint (Aext e1) (D.μW.prod D.μN) zz := by
      rw [hK1]; exact l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hee1 hzz
    have bl' : ‖l' (σ (Matrix.of zz') w0)‖ₑ ≤ K2 * Iint (Aext e2) (D.μW'.prod D.μN) zz' := by
      rw [hK2]; exact l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT' hπ' hW' hN hbe' hv' hlv' hw0DD hee2 hzz'
    have hc : ‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l' (σ (Matrix.of zz') w0)‖ₑ ≠ ⊤ :=
      ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
    have hqi := quad_inner hds w0 he0 hee0 hγU hf1.2 hf2.2 hzz hzz'
    rw [← hLL] at hqi
    simp only [← enorm_eq_nnnorm]
    calc ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ *
          ‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l' (σ (Matrix.of zz') w0)‖ₑ ∂(muSof D.μW' D.μN) ∂(muSof D.μW D.μN)
        = ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ *
          (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l' (σ (Matrix.of zz') w0)‖ₑ) ∂(muSof D.μW' D.μN) ∂(muSof D.μW D.μN) :=
          lintegral_congr fun s => lintegral_congr fun s' => mul_assoc _ _ _
      _ = (∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ
            ∂(muSof D.μW' D.μN) ∂(muSof D.μW D.μN)) *
          (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l' (σ (Matrix.of zz') w0)‖ₑ) := by
          rw [← lintegral_mul_const' _ _ hc]
          apply lintegral_congr; intro s
          rw [lintegral_mul_const' _ _ hc]
      _ = LL zz zz' * (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l' (σ (Matrix.of zz') w0)‖ₑ) := by rw [hqi]
      _ ≤ LL zz zz' * ((K1 * Iint (Aext e1) (D.μW.prod D.μN) zz) * (K2 * Iint (Aext e2) (D.μW'.prod D.μN) zz')) := by
          gcongr
      _ = (K1 * K2) * (Iint (Aext e1) (D.μW.prod D.μN) zz * (Iint (Aext e2) (D.μW'.prod D.μN) zz' * LL zz zz')) := by
          ring
  have hinvR : ∀ zz, ∀ᵐ z ∂νq', ∀ᵐ q ∂(D.μW'.prod D.μN),
      LL zz (fun i j => (Matrix.of q.1 * Matrix.of q.2 * Matrix.of z) i j) = LL zz z := by
    intro zz
    rw [hLL]
    exact Filter.Eventually.of_forall fun z => (prod_ae hW' hN).mono
      fun q hq0 => lam_right he0 γ hW' hN hz2 (D.μW.prod D.μN) hq0.1 hq0.2 zz z
  have hinvL : ∀ᵐ z ∂νq, ∀ᵐ p ∂(D.μW.prod D.μN),
      (∫⁻ y, Aext e2 y * LL (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) y ∂D.μG) =
        ∫⁻ y, Aext e2 y * LL z y ∂D.μG := by
    rw [hLL]
    exact Filter.Eventually.of_forall fun z => (prod_ae hW hN).mono
      fun p hp0 => lintegral_congr fun y => by rw [lam_left he0 γ hW hN hz1 (D.μW'.prod D.μN) hp0.1 hp0.2 z y]
  have hLz : ∀ zz, Measurable (fun y => LL zz y) := fun zz => hLLm.comp (measurable_const.prodMk measurable_id)
  have hΦm : Measurable (fun x => ∫⁻ y, Aext e2 y * LL x y ∂D.μG) :=
    ((hA2m.comp measurable_snd).mul hLLm).lintegral_prod_right'
  obtain ⟨bb, hbbdef⟩ : ∃ bb : ℝ, bb = aOf r h - AG k r - 1 := ⟨_, rfl⟩
  rw [← hbbdef] at hba hb0 hLadef
  obtain ⟨Fx, hFx⟩ : ∃ Fx : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, Fx = fun x => ‖B.gN (Matrix.of x) ^ (-(aOf r h - bb))‖ₑ :=
    ⟨_, rfl⟩
  have hFxm : Measurable Fx := by
    rw [hFx]; exact (((gN_cont.comp mt_cont).measurable).pow_const _).enorm
  have hKg' : ∫⁻ x, Fx x ∂D.μG < ⊤ := by rw [hFx, hbbdef]; exact hKg
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ≥0∞, c = ENNReal.ofReal |C1| * ENNReal.ofReal |C2| * (ENNReal.ofReal |C0| * La) :=
    ⟨_, rfl⟩
  have hc : c ≠ ⊤ := by
    rw [hcdef]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLa.ne)
  have hgpos : ∀ x : Mx k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → 0 < B.gN x :=
    fun x hx => lt_of_lt_of_le one_pos ((hNI k r).2 x hx).2
  have hpt : ∀ᵐ x ∂D.μG, Aext e1 x * ∫⁻ y, Aext e2 y * LL x y ∂D.μG ≤ ∫⁻ y, c * (Fx x * Fx y) ∂D.μG := by
    filter_upwards [hGc] with x hx
    rw [← lintegral_const_mul' (Aext e1 x) _ (by unfold Aext; exact enorm_ne_top)]
    apply lintegral_mono_ae
    filter_upwards [hGc] with y hy
    have hL := lam_bound hNI hb0e hb0.le hba hγU hpUH hqUH hx hy
    rw [← hLL, ← hLadef] at hL
    have hx0 := hgpos _ hx
    have hy0 := hgpos _ hy
    have w1 := e_weight (b := bb) hb1 hx hx0
    have w2 := e_weight (b := bb) hb2 hy hy0
    have split : ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ bb) =
        ENNReal.ofReal |C0| * (ENNReal.ofReal (B.gN (Matrix.of x) ^ bb) * ENNReal.ofReal (B.gN (Matrix.of y) ^ bb)) := by
      rw [Real.mul_rpow hx0.le hy0.le, ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hx0.le _)]
    have hFxx : Fx x = ‖B.gN (Matrix.of x) ^ (-(aOf r h - bb))‖ₑ := by rw [hFx]
    have hFxy : Fx y = ‖B.gN (Matrix.of y) ^ (-(aOf r h - bb))‖ₑ := by rw [hFx]
    calc Aext e1 x * (Aext e2 y * LL x y)
        ≤ Aext e1 x * (Aext e2 y * (ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ bb) * La)) := by
          gcongr
      _ = (Aext e1 x * ENNReal.ofReal (B.gN (Matrix.of x) ^ bb)) *
            (Aext e2 y * ENNReal.ofReal (B.gN (Matrix.of y) ^ bb)) * (ENNReal.ofReal |C0| * La) := by
          rw [split]; ring
      _ ≤ (ENNReal.ofReal |C1| * Fx x) * (ENNReal.ofReal |C2| * Fx y) * (ENNReal.ofReal |C0| * La) := by
          rw [hFxx, hFxy]
          exact mul_le_mul' (mul_le_mul' w1 w2) le_rfl
      _ = c * (Fx x * Fx y) := by rw [hcdef]; ring
  calc _ ≤ ∫⁻ zz, ∫⁻ zz', (K1 * K2) * (Iint (Aext e1) (D.μW.prod D.μN) zz *
          (Iint (Aext e2) (D.μW'.prod D.μN) zz' * LL zz zz')) ∂νq' ∂νq :=
        lintegral_mono_ae (step1.mono fun zz h => lintegral_mono_ae h)
    _ = (K1 * K2) * ∫⁻ zz, Iint (Aext e1) (D.μW.prod D.μN) zz *
          ∫⁻ zz', Iint (Aext e2) (D.μW'.prod D.μN) zz' * LL zz zz' ∂νq' ∂νq :=
        pull2 _ _ _ hK (fun zz => hI2m.mul (hLz zz))
    _ = (K1 * K2) * ∫⁻ zz, Iint (Aext e1) (D.μW.prod D.μN) zz * ∫⁻ y, Aext e2 y * LL zz y ∂D.μG ∂νq := by
        congr 1; apply lintegral_congr; intro zz; congr 1
        exact unfold_Iint hq' hA2m (hLz zz) (hinvR zz)
    _ = (K1 * K2) * ∫⁻ x, Aext e1 x * ∫⁻ y, Aext e2 y * LL x y ∂D.μG ∂D.μG := by
        congr 1
        exact unfold_Iint hq hA1m hΦm hinvL
    _ ≤ (K1 * K2) * ∫⁻ x, ∫⁻ y, c * (Fx x * Fx y) ∂D.μG ∂D.μG := by
        gcongr 1
        exact lintegral_mono_ae hpt
    _ = (K1 * K2) * (c * ((∫⁻ x, Fx x ∂D.μG) * ∫⁻ y, Fx y ∂D.μG)) := by rw [final2 Fx hFxm hc]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK)
          (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) (ENNReal.mul_lt_top hKg' hKg'))

end Formalism.FourierDecayAlt.P.S3dx4
end
end

