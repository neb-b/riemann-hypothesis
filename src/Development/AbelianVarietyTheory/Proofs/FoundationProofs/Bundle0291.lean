module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryThetaConstantEqInverseDeterminantPhase
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfGaussSign
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardMulCardOrth
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Formalism.FormalDegreeBessel.StatementG
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FrobStick

open PowerSeries

def colA (Λ : AddSubgroup ℂ) (z : ℂ) : ℂ := sgStar Λ z ^ 3

def colB (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ := sgStar Λ z * (sqTh Λ v z + wpF Λ v * sgStar Λ z ^ 2)

def colC (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ :=
  sgStar Λ z * deriv (sqTh Λ v) z - 2 * deriv (sgStar Λ) z * sqTh Λ v z

def tay (F : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk (coef1 F)

def defect {R : Type*} [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R) :
    MvPowerSeries (Fin 3) R :=
  Matrix.det (Matrix.of fun i j =>
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) (f j) : MvPowerSeries (Fin 3) R)) -
    2 * PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 1 - MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 2 - MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) s

end GlobalTheory.FrobStick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateJetBoundVacuumTorsionTranslate
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.jet

theorem jet_bound_fix (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) (hGT : G ∈ Th D (tor0 D cc δ) L L')
    (y : VC D a d) (hy : LaQ D (tor0 D cc δ) L L' y)
    (n : D.what₂.Tau → ℕ) (B : ℝ) (hB : 1 ≤ B) (hn : ∀ τ, (n τ : ℝ) ≤ 2 * B)
    (ρ : Qbar →ₐ[ℚ] ℂ) (hρ : FixK D Qbar ρ) (T : Tup D a d n) :
    GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧
    ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤
      ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 *
        (3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) *
          normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
            (fnConj D Qbar ρ G) *
          (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (a * ∑ τ, n τ)) := by
  have hg1 : admG1 D := (_root_.GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hdata, htors⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg1).2 cc δ hc
  obtain ⟨hA, hAU, -⟩ := GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := _root_.GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨t', ht'⟩ := (_root_.GlobalTheory.TwoTorsionPt.exists_point D cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2
  obtain ⟨hN, -⟩ := _root_.GlobalTheory.ConjNorm.useNorm_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t' ht'
  obtain ⟨cc', δ', hc', -, hΛ⟩ := _root_.GlobalTheory.ConjCurve.galCurve_holds D cc δ hc Qbar ρ hρ hdata.2.1 hdata.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := (_root_.GlobalTheory.InducedType.induced_type D).2 Qbar ρ hρ hdata.1
  have hne : fnConj D Qbar ρ G ≠ 0 := by
    intro h
    rw [h, hΛ] at hN
    rw [hΛ] at ht'
    refine pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hg1 cc' δ' t' hc' ht') (hN.symm.trans ?_)
    simp [normSq]
  obtain ⟨m, hm, hmy⟩ := id hy
  obtain ⟨y', hy', -⟩ := _root_.GlobalTheory.GalExist.galEx_all D cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y (2 * m) hy
    (by omega)
  have hgal := (_root_.GlobalTheory.GalTheta.gal_all D cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1) (fun _ => 0) G y y' m
    hGT hm hmy (fun _ => by simp) hy' (by rw [GlobalTheory.ConjJet.comb_one]; exact hA)
    (by rw [GlobalTheory.ConjJet.comb_one]; exact hAU y hy)).1
  rw [GlobalTheory.ConjJet.comb_one] at hgal
  have hdiff := GlobalTheory.ConjJet.U_diff D (torConj D (tor0 D cc δ) Qbar ρ) y' _ hTh.1
  obtain ⟨hmem, hcj⟩ := (GlobalTheory.ConjSeries.taylor_fnConj D a d Qbar ρ (U D (tor0 D cc δ) y G)
    (by rw [hgal]; exact hdiff) (by rw [hgal]; exact GlobalTheory.ConjJet.U_ne_zero D _ _ _ hne)).2 (hAU y hy) n T
  refine ⟨hmem, ?_⟩
  rw [hcj, hgal]
  have hr : 0 ≤ D.host.rdE := Real.rpow_nonneg (abs_nonneg _) _
  refine (GlobalTheory.MinorBound.minor_bound D a d n _ _ (area (lamConj Qbar ρ (lamOf D cc δ))) B
    (by rw [hΛ]; exact GlobalTheory.ConjJet.area_pos D hg1 cc' δ' hc') hB ?_ hn hdiff fun z => ?_).2 T
  · have := GlobalTheory.ConjJet.normSq_nonneg D (torConj D (tor0 D cc δ) Qbar ρ)
      (La D (torConj D (tor0 D cc δ) Qbar ρ) L L') (fnConj D Qbar ρ G)
    positivity
  · have := GlobalTheory.ConjJet.sup_perm D hg1 cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _
      hTh y' z
    rw [GlobalTheory.ConjJet.Hf_re, ← mul_div_assoc] at this
    exact this

theorem vacuum_mem_thetaSpace_pair (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) : G ∈ Th D (tor0 D cc δ) L L' := by
  obtain ⟨b, κ, hb, -, rfl⟩ := hG
  obtain ⟨-, ⟨hd, hinv⟩, -⟩ := _root_.GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc a d _ _ (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inr ⟨L, L', h1, h2, rfl⟩) _
    (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D (_root_.GlobalTheory.InducedType.induced_type D).1 cc δ t0 hc ht b hb.1)
  refine ⟨hd.const_mul κ, fun x hx z => ?_⟩
  have := hinv x hx z
  simp only [U] at this ⊢
  rw [show (tor0 D cc δ).abelian₂ = lamOf D cc δ from rfl, ← this]
  ring

theorem conj_jet_bound : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L', SD D L → SD D L' → Even (a * d) → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ∀ y, LaQ D (tor0 D cc δ) L L' y → ∀ (n : D.what₂.Tau → ℕ) (B : ℝ), 1 ≤ B → (∀ τ, (n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ T : Tup D a d n, GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧ ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 * (3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * a * d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (a * ∑ τ, n τ)) := by
  intro D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy n B hB hn ρ t0' ht' T
  have hGT := vacuum_mem_thetaSpace_pair D cc δ t0 hc ht a d L L' h1 h2 G hG
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D (_root_.GlobalTheory.InducedType.induced_type D).1).2 cc δ hc
  obtain ⟨hA, -⟩ := GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hN, -⟩ := _root_.GlobalTheory.ConjNorm.useNorm_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t0' ht'
  rw [← hN]
  obtain ⟨hfix | hfix, htor, hbar⟩ := _root_.GlobalTheory.ThetaConj.useBar_holds D cc δ hc Qbar ρ hdata
  · exact jet_bound_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG hGT y hy n B hB hn ρ hfix T
  · obtain ⟨hmem, hle⟩ := jet_bound_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG hGT y hy n B hB
      hn (rhoBar Qbar ρ) hfix T
    refine ⟨hmem, ?_⟩
    obtain ⟨hTh, -⟩ := _root_.GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
    have hn2 := ((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0
    rw [GlobalTheory.ConjJet.U_zero] at hn2
    have hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) =
        (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom :=
      congrArg Tor.abelian₂ htor
    rw [GlobalTheory.ConjJet.cj_bar, (hbar a d L L' G).1, htor, hn2, hL, GlobalTheory.ConjJet.area_conj] at hle
    exact hle

end GlobalTheory.ArchFree.jet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfEquivariant
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.EquivConst

theorem const_of_equivariant : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → (∀ (b : 𝓞 D.host.E), ∀ x ∈ A, scal D N N' (b : D.host.E) x ∈ A) → (∀ (b : D.host.E) x, u (scal D N N' b x) = scal D N N' b (u x)) → ∀ th ∈ ThSp D (tor0 D cc δ) A, (fun z => th (u.symm z)) = (sgn D ((A.map (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')).toAddMonoidHom).relIndex A) * ((‖LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))‖ : ℂ) / LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')))) • Iop D (tor0 D cc δ) A A₁ th :=
  fun D => const_of_gaussSign D (GlobalTheory.HermGauss.gauss_sum_sign D)

end GlobalTheory.EquivConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemPrime

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7}

theorem mul_mem_int {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem isIntegral_star {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  map_isIntegral_int (starRingEnd D.host.E) hx

theorem evalV_algebraMap_mem (v : HeightOneSpectrum (𝓞 D.host.F)) (t : D.host.F) (ht : IsIntegral ℤ t) :
    evalV D.host.F v (algebraMap D.host.F (Af D.host.F) t) ∈ v.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes]
  have h2 : Valued.v (algebraMap D.host.F (Fv D.host.F v) t) = v.valuation D.host.F t :=
    v.valuedAdicCompletion_eq_valuation' _
  show Valued.v (algebraMap D.host.F (Fv D.host.F v) t) ≤ 1
  rw [h2]
  exact v.valuation_le_one (K := D.host.F) (⟨t, ht⟩ : 𝓞 D.host.F)

theorem exists_trace {z : Formalism.L2.Theta.AE D} (hz : z ∈ intL D) :
    ∃ β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, z + cA D z = fj D β := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    obtain ⟨t, ht⟩ := exists_of_star_eq D (x := (o : D.host.E) + star (o : D.host.E))
      (by rw [star_add, star_star, add_comm])
    have hti : IsIntegral ℤ t := by
      rw [← isIntegral_algebraMap_iff (B := D.host.E), ht]
      exact o.2.add (isIntegral_star o.2)
    refine ⟨algebraMap D.host.F (Af D.host.F) t * α, fun v => ?_, ?_⟩
    · rw [map_mul]; exact mul_mem (evalV_algebraMap_mem v t hti) (hα v)
    · rw [cA_tmul, ← TensorProduct.tmul_add, ← ht, tmul_algebraMap_eq, fj_eq]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  | zero => exact ⟨0, fun v => by rw [map_zero]; exact zero_mem _, by rw [map_zero, map_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, h1⟩ := hx
    obtain ⟨b, hb, h2⟩ := hy
    exact ⟨a + b, fun v => by rw [map_add]; exact add_mem (ha v) (hb v), by
      rw [RingHom.map_add (f := _), map_add (fj D), ← h1, ← h2, add_add_add_comm]⟩
  | neg x _ hx =>
    obtain ⟨a, ha, h1⟩ := hx
    exact ⟨-a, fun v => by rw [map_neg]; exact neg_mem (ha v), by
      rw [RingHom.map_neg, map_neg (fj D), ← h1, neg_add]⟩

theorem finPart_mem {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) : finPart D e ∈ intAE D :=
  GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])

theorem mem_iff {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) (y : Fv D.host.F v) :
    finPart D (fj D (singleV D.host.F v y) * e) ∈ intAE D ↔ Valued.v y ≤ 1 := by
  constructor
  · intro h
    have h1 := inF_mem h
    rw [inF_finPart, ← mul_assoc, ← map_mul, one_mul] at h1
    obtain ⟨β, hβ, h2⟩ := exists_trace h1
    rw [map_mul, cA_fj, ← mul_add, he.2.2, ← map_mul] at h2
    have h3 := congrArg (evalV D.host.F v) (fj_inj D h2)
    rw [map_mul, evalV_singleV_same, evalV_singleV_same, mul_one] at h3
    rw [h3]
    exact hβ v
  · intro h
    rw [RingHom.map_mul]
    exact mul_mem_int (AddSubgroup.subset_closure
      ⟨singleV D.host.F v y, singleV_mem_intAf D.host.F v ⟨y, h⟩, 1, rfl⟩) (finPart_mem he)

theorem singleV_add (v : HeightOneSpectrum (𝓞 D.host.F)) (x y : Fv D.host.F v) :
    singleV D.host.F v (x + y) = singleV D.host.F v x + singleV D.host.F v y := by
  rw [← sub_eq_iff_eq_add, ← singleV_sub, add_sub_cancel_right]

theorem scalar_eq {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) {a b : Fv D.host.F v}
    (h : fj D (singleV D.host.F v a) * e = fj D (singleV D.host.F v b) * e) : a = b := by
  have := he.scalar_inj h
  rwa [evalV_singleV_same, evalV_singleV_same] at this

theorem exists_hom {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) :
    ∃ φ : D.host.E →+* Fv D.host.F v, ∀ x, e * incA D x = fj D (singleV D.host.F v (φ x)) * e := by
  choose f hf using fun x => he.exists_scalar (incA D x)
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := fun x y => ?_, map_zero' := ?_, map_add' := fun x y => ?_ }, hf⟩
  · refine scalar_eq he ?_
    rw [← hf, map_one, mul_one, he.pl_mul]
  · refine scalar_eq he ?_
    have h : singleV D.host.F v (f x * f y) = singleV D.host.F v (f x) * singleV D.host.F v (f y) := by
      rw [singleV_mul, evalV_singleV_same]
    rw [← hf, map_mul, h, map_mul, ← mul_assoc, hf, mul_assoc, hf, mul_assoc]
  · refine scalar_eq he ?_
    rw [← hf, map_zero, mul_zero, ← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self, map_zero, zero_mul]
  · refine scalar_eq he ?_
    rw [← hf, map_add (f := _), singleV_add, map_add (f := _), mul_add, add_mul, hf, hf]

theorem hom_algebraMap {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) {φ : D.host.E →+* Fv D.host.F v}
    (hφ : ∀ x, e * incA D x = fj D (singleV D.host.F v (φ x)) * e) (t : D.host.F) :
    φ (algebraMap D.host.F D.host.E t) = algebraMap D.host.F (Fv D.host.F v) t := by
  refine scalar_eq he ?_
  have h1 : incA D (algebraMap D.host.F D.host.E t) =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (algebraMap D.host.F (AF D.host.F) t * 1) :=
    tmul_algebraMap_eq (1 : AF D.host.F) t
  have h2 : evalV D.host.F v (algebraMap D.host.F (AF D.host.F) t * 1).2 * 1 =
      algebraMap D.host.F (Fv D.host.F v) t := by
    rw [mul_one, mul_one]
    exact (evalV D.host.F v).commutes t
  rw [← hφ, h1, ← h2, ← singleV_mul, ← algebraMap_mul_fj, mul_assoc, he.pl_mul, mul_comm]

theorem exists_isIdemAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : Formalism.L2.Theta.AE D), GlobalTheory.IdemModTwo.SplitAt D v e → ∃ PP : HeightOneSpectrum (𝓞 D.host.E), Formalism.L2.NTheta.IsIdemAt e PP ∧ PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := by
  intro D v e he
  obtain ⟨φ, hφ⟩ := exists_hom he
  have hint : ∀ x : 𝓞 D.host.E, Valued.v (φ x) ≤ 1 := fun x => by
    rw [← mem_iff he, ← hφ, RingHom.map_mul]
    exact mul_mem_int (finPart_mem he) (AddSubgroup.subset_closure
      ⟨1, fun w => by rw [map_one]; exact one_mem _, x, rfl⟩)
  let I : Ideal (𝓞 D.host.E) :=
    { carrier := {x | Valued.v (φ x) < 1}
      add_mem' := fun {a b} ha hb => by
        show Valued.v (φ ((a : D.host.E) + b)) < 1
        rw [map_add (f := _)]
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by
        show Valued.v (φ 0) < 1
        rw [map_zero, map_zero]; exact zero_lt_one
      smul_mem' := fun c x hx => by
        show Valued.v (φ ((c : D.host.E) * x)) < 1
        rw [map_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint c)) hx }
  have hI : ∀ x, x ∈ I ↔ Valued.v (φ x) < 1 := fun x => Iff.rfl
  have hcomap : I.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := by
    ext t
    rw [Ideal.mem_comap, hI]
    have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F t) := rfl
    have h2 : Valued.v (algebraMap D.host.F (Fv D.host.F v) (algebraMap (𝓞 D.host.F) D.host.F t)) =
        v.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F t) :=
      v.valuedAdicCompletion_eq_valuation' _
    rw [h1, hom_algebraMap he hφ, h2]
    exact v.valuation_lt_one_iff_mem _
  have hprime : I.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : 𝓞 D.host.E) ∈ I := by rw [h]; trivial
      have h2 : Valued.v (φ 1) < 1 := h1
      rw [map_one, map_one] at h2
      exact lt_irrefl _ h2
    · have h2 : Valued.v (φ ((a : D.host.E) * b)) < 1 := hab
      rw [map_mul, map_mul] at h2
      by_contra hn
      rw [not_or, hI, hI, not_lt, not_lt] at hn
      exact absurd h2 (not_lt.2 (one_le_mul hn.1 hn.2))
  have hne : I ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [← hcomap, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  refine ⟨⟨I, hprime, hne⟩, ⟨(isSplitIdem_iff e).2 ⟨v, he⟩, fun x hx => ?_⟩, hcomap⟩
  have hx0 : Valued.v (φ x) ≠ 0 := by
    rw [Valuation.ne_zero_iff, map_ne_zero]
    exact fun h => hx (Subtype.ext h)
  show x ∈ I ↔ _
  rw [hI, hφ, mem_iff he, map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]

end GlobalTheory.IdemPrime

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
section
noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def placeOf (D : D7) (ρ : D.what₂.Tau) : InfinitePlace D.host.F :=
  InfinitePlace.mk ((tauE D ρ).comp (algebraMap D.host.F D.host.E))

theorem placeOf_bijective (D : D7) : Function.Bijective (placeOf D) := GlobalTheory.CMTypePlaces.places_bijective D

def embOverOf (D : D7) (ρ : D.what₂.Tau) : EmbOver D.host.E (placeOf D ρ) :=
  ⟨tauE D ρ, by
    have := (isCMExt_host D).1
    exact (InfinitePlace.embedding_mk_eq_of_isReal
      (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (placeOf D ρ)))).symm⟩

@[simp] theorem embOverOf_val (D : D7) (ρ : D.what₂.Tau) : (embOverOf D ρ).1 = tauE D ρ := rfl

theorem isInfFam_infProj (D : D7) : IsInfFam (D := D) fun ρ : D.what₂.Tau => infProj (embOverOf D ρ) :=
  fun ρ => isInfEmb_infProj (embOverOf D ρ)

theorem exists_isInfFam (D : D7) : ∃ θ, IsInfFam (D := D) θ := ⟨_, isInfFam_infProj D⟩

variable {D : D7}

theorem eq_placeOf {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F} (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) :
    w = placeOf D ρ := by
  rw [placeOf, ← hτ, τ.2, InfinitePlace.mk_embedding]

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem eq_infProj (hθ : IsInfFam θ) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F} (τ : EmbOver D.host.E w)
    (hτ : τ.1 = tauE D ρ) : θ ρ = infProj τ :=
  GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hθ ρ) (hτ ▸ isInfEmb_infProj τ)

theorem isAtTau_embArch (hθ : IsInfFam θ) (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) (x : GArch D.sp.cm.sig V.gram w) :
    IsAtTau θ V ρ (archEquiv V.gram (isCMExt_host D) τ x).1.1 (embArch D.sp.cm.sig V.gram w x) := by
  refine ⟨mem_infPts.2 (projFin_embArch _ _ w x), ?_, fun ρ' h => ?_⟩
  · rw [eq_infProj hθ τ hτ, infMat_infProj V.gram (isCMExt_host D), projArch_embArch_self]
  · have hw : placeOf D ρ' ≠ w := fun e => h ((placeOf_bijective D).1 (e.trans (eq_placeOf τ hτ)))
    rw [eq_infProj hθ (embOverOf D ρ') rfl, infMat_infProj V.gram (isCMExt_host D), projArch_embArch_ne _ _ hw,
      map_one]
    rfl

theorem archEquiv_mem_UH (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) (x : GArch D.sp.cm.sig V.gram w) :
    (archEquiv V.gram (isCMExt_host D) τ x).1.1 ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  have h := (archEquiv V.gram (isCMExt_host D) τ x).2
  rw [gramAt, ← hτ]
  exact h

theorem exists_archEquiv_eq (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) :
    ∃ x : GArch D.sp.cm.sig V.gram w, (archEquiv V.gram (isCMExt_host D) τ x).1.1 = g := by
  obtain ⟨θ, hθ⟩ := exists_isInfFam D
  obtain ⟨h, hh, -⟩ := GlobalTheory.PointAtPlace.existsUnique_isAtTau V ρ θ hθ g hg
  refine ⟨projArch _ _ w h, ?_⟩
  rw [← infMat_infProj, ← eq_infProj hθ τ hτ]
  exact hh.2.1

theorem atTau_archEquiv (hθ : IsInfFam θ) (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) (x : GArch D.sp.cm.sig V.gram w) :
    atTau θ V ρ (archEquiv V.gram (isCMExt_host D) τ x).1.1 = embArch D.sp.cm.sig V.gram w x := by
  have hu := GlobalTheory.PointAtPlace.existsUnique_isAtTau V ρ θ hθ _ (archEquiv_mem_UH V τ hτ x)
  refine hu.unique ?_ (isAtTau_embArch hθ V τ hτ x)
  unfold atTau
  rw [dite_eq_left hu.exists]
  exact hu.exists.choose_spec

end GlobalTheory.AdelicU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOrderParameterSeriesBoundedStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOrder_parameterSeries_bounded : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → ∀ (k : ℕ) (G : ℂ → ℂ), AlgEnt G → (∀ ω ∈ g.abelian₂, ∀ z, G (z + ω) * sgStar g.abelian₂ z ^ k = G z * sgStar g.abelian₂ (z + ω) ^ k) → ∃ B : PowerSeries ℂ_[p], BddSer B ∧ g.atU G = ePhi1 g.lam g.abelian₂ g.C g.wq ^ k * B := by
  first | exact @GlobalTheory.ThetaOrderBdd.order_bdd | exact GlobalTheory.ThetaOrderBdd.order_bdd | (intros; apply GlobalTheory.ThetaOrderBdd.order_bdd <;> assumption)
end

