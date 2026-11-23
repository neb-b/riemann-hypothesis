module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Formalism.LocalToGlobal.GlobalTheory.GL3.DeterminantNormOneOfUnitDisc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubTwoOmegaSq
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
public import ReciprocityTheory.ClassFieldTheory.GlobalClassField.Bundle0001
public import ReciprocityTheory.Chebotarev.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AnalyticOnNhdOfDifferentiableVc
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

variable {D : D7}

theorem analyticOnNhd_of_differentiable_vc {N N' : ℕ} (H : TaylorLogMetric.VC D N N' → ℂ) (hH : Differentiable ℂ H) :
    AnalyticOnNhd ℂ H Set.univ := by
  let e : TaylorLogMetric.VC D N N' ≃L[ℂ] (Fin (Module.finrank ℂ (TaylorLogMetric.VC D N N')) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_fin_fun])
  have h1 : AnalyticOnNhd ℂ (H ∘ e.symm) Set.univ :=
    ReciprocityTheory.AnForm.Osgood.osgood _ Set.univ (H ∘ e.symm) isOpen_univ
      (hH.comp e.symm.differentiable).differentiableOn
  have h2 : H = (H ∘ e.symm) ∘ e := by
    funext z
    simp
  rw [h2]
  exact h1.comp (e.toContinuousLinearMap.analyticOnNhd Set.univ) (Set.mapsTo_univ _ _)

theorem entire_algCoef_comb : ∀ (D : D7) {N N' m : ℕ} (c : Fin m → ℂ) (G : Fin m → TaylorLogMetric.VC D N N' → ℂ), (∀ k, c k ∈ TaylorLogMetric.Qbar) → (∀ k, Differentiable ℂ (G k) ∧ TaylorLogMetric.CoefIn D (G k) TaylorLogMetric.Qbar) → Differentiable ℂ (fun z => ∑ k, c k * G k z) ∧ TaylorLogMetric.CoefIn D (fun z => ∑ k, c k * G k z) TaylorLogMetric.Qbar := by
  intro D N N' m c G hc hG
  have hd : ∀ k, Differentiable ℂ (G k) := fun k => (hG k).1
  refine ⟨by fun_prop, fun α => ?_⟩
  have hsm : ∀ k (n : ℕ), ContDiff ℂ n (G k) := fun k n =>
    Formalism.L2.KerInert.ie_smooth (analyticOnNhd_of_differentiable_vc (G k) (hd k)) n
  rw [Formalism.L2.KerInert.ie_taylor_lin c G hsm α]
  exact sum_mem fun k _ => mul_mem (hc k) ((hG k).2 α)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiDetIdAndChiFacAlg
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SelfDualChiAlg

theorem chi_detId_and_chiFac_alg : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ →
    (∀ (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → IsSDLat D.host.E N L →
      χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ∈ TaylorLogMetric.Qbar) ∧
    ∀ {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      TaylorLogMetric.admitted D N N' L L' → Base.chiFac χ N N' L L' ∈ TaylorLogMetric.Qbar ∧ Base.chiFac χ N N' L L' ≠ 0 := by
  intro D χ hχ
  refine ⟨fun N L hN hL => ?_, fun L L' hA => ⟨GlobalTheory.MomT.FromComb.chiFac_mem hχ hA, ?_⟩⟩
  · exact GlobalTheory.MomT.FromComb.chi_mem hχ
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N _ L hN (GlobalTheory.FourthRootStd.stdL_isSD D N) hL)
  · exact GlobalTheory.Mem.NatEqui.chiFac_ne_zero hχ hA.2.2.1 hA.2.2.2

end GlobalTheory.SelfDualChiAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassC0PrimeNotExceptional
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.HalfDiffInt

theorem prime_not_dvd_discr (D : D7) {p : ℕ} (hp : p.Prime) (h2 : p ∉ D.host.small) (hq : p ≠ D.host.q) (hd : p ≠ D.host.d) :
    ¬ p ∣ (discr D.host.E).natAbs :=
  UpperTheory.Ram.not_dvd_natAbs_discr D.host hp h2 hq hd

theorem absNorm_dvd_discr (D : D7) : Ideal.absNorm D.host.𝔟 ∣ (discr D.host.E).natAbs := by
  have htow := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow D.host.K (𝓞 D.host.K)
    D.host.E (𝓞 D.host.E)
  rw [htow, D.host.𝔟_spec.1, map_mul, mul_assoc]
  exact Dvd.intro _ rfl

theorem absNorm_coprime (D : D7) {p : ℕ} (hp : p.Prime) (h2 : p ∉ D.host.small) (hq : p ≠ D.host.q) (hd : p ≠ D.host.d) :
    Nat.Coprime (Ideal.absNorm D.host.𝔟) p := by
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  exact prime_not_dvd_discr D hp h2 hq hd (dvd_trans h (absNorm_dvd_discr D))

theorem inv_integral_off (D : D7) {p : ℕ} (hp : p.Prime) (h2 : p ∉ D.host.small) (hq : p ≠ D.host.q) (hd : p ≠ D.host.d) :
    ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧
      (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  intro a ha
  have hcop := absNorm_coprime D hp h2 hq hd
  have hne : D.host.𝔟 ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.absNorm_bot, Nat.coprime_zero_left] at hcop
    exact hp.one_lt.ne' hcop
  refine ⟨Ideal.absNorm D.host.𝔟, hcop, ?_⟩
  have ha' : a ∈ ((D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
    have : a ∈ D.host.AA0 := ha
    rwa [Host.AA0] at this
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hne)] at ha'
  have hs := ha' _ (FractionalIdeal.mem_coeIdeal_of_mem (S := nonZeroDivisors (𝓞 D.host.E)) (P := D.host.E)
    (Ideal.absNorm_mem D.host.𝔟))
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).1 hs
  refine ⟨x, ?_⟩
  rw [hx, map_natCast, mul_comm]

theorem class_c0_prime_not_exceptional {R : Ranks} (H : Host R) {p : ℕ} (h : H.cls p = .inertClass) : p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d :=
  let k := (primeClass_eq_inert_iff H.toHostRaw).1 h
  ⟨k.1, k.2.1, k.2.2.1⟩

end GlobalTheory.TwV.HalfDiffInt

namespace GlobalTheory.TwV

theorem halfDiffInv_integral_at_split : ∀ (D : D7) (T p : ℕ), GIdx D.host T p → (∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) := by
  intro D T p hg
  obtain ⟨h2, hq, hd⟩ := HalfDiffInt.class_c0_prime_not_exceptional D.host hg.2.2.1
  exact HalfDiffInt.inv_integral_off D hg.1 h2 hq hd

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColSpanMapMulVecLin
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem colSpan_map_mulVecLin {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (A g : Matrix (Fin k) (Fin k) K) :
    (Formalism.MainNotions.G.colSpan R g).map (A.mulVecLin.restrictScalars R) = Formalism.MainNotions.G.colSpan R (A * g) := by
  unfold Formalism.MainNotions.G.colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2

theorem locSp_reindex : ∀ {E : Type} [Field E] [NumberField E] (σ : E →+* E) (W K : Type) [CommRing W] [Field K] [Algebra W K] (ρ : E →+* K) {n N : ℕ} (h : n = N) (J : Matrix (Fin N) (Fin N) E) (B : GL (Fin N) E) (g : GL (Fin n) K) (Λ : Submodule (𝓞 E) (Fin N → E)) (Λ' : Submodule (𝓞 E) (Fin n → E)), HEq Λ' Λ → locSp W ρ Λ = colSpan W ((LinearMap.toMatrix' (stdCo σ J).toLinearMap * B.1).map ρ * (castGL h K g : Matrix (Fin N) (Fin N) K)) → locSp W ρ Λ' = (colSpan W (g : Matrix (Fin n) (Fin n) K)).map (((((LinearMap.toMatrix' (stdCo σ (J.reindex (finCongr h.symm) (finCongr h.symm))).toLinearMap * (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h.symm) B).1).map ρ).submatrix (finCongr (rfl : n = n)) (finCongr (rfl : n = n))).mulVecLin).restrictScalars W) := by
  intro E _ _ σ W K _ _ _ ρ n N h J B g Λ Λ' hΛ hs
  subst h
  obtain rfl := eq_of_heq hΛ
  rw [colSpan_map_mulVecLin, hs]
  rfl

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatLocHomRe
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem datLoc_homRe : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (M : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin b' → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a' b' → ℂ), HEq N M → HEq N' M' → DatLoc D cc SS cl M M' Ξ → DatLoc D cc SS cl N N' (fun z => Ξ (homRe ha hb z)) := by
  intro D cc SS cl a b a' b' ha hb N N' M M' Ξ hN hN' h
  subst ha hb
  cases eq_of_heq hN
  cases eq_of_heq hN'
  have hx : (fun z => Ξ (homRe rfl rfl z)) = Ξ := by
    funext z
    congr 1
  rw [hx]
  exact h

end GlobalTheory.TwU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryAdelicPointGramStepNormOne
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem det_unitary_adelic_point_gram_step_norm_one : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), Matrix.GeneralLinearGroup.det x.1 ∈ Formalism.L2.DIV.U1 (sigD D) := by
  intro D i hi x
  exact Formalism.L2.DIV.det_in_unitary_one D.host.F D.host.E (sigD D) _ (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) x.1 x.2

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalBasisCoordsAgainstBlockAction
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Act

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem substR_substR (R : Type) [CommRing R] (G G' : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)
    (Q : XR P R) : substR P R G (substR P R G' Q) = substR P R (fun v s => G' v s * G v s) Q := by
  have hc : (substR P R G).comp (substR P R G') = substR P R (fun v s => G' v s * G v s) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, substR, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, ← MvPolynomial.C_mul]
  exact congrArg (fun φ : XR P R →ₐ[R] XR P R => φ Q) hc

theorem natActR_natActR (R : Type) [Field R] (g g' : ∀ v, Fin (P.n' v) → GL (Fin (P.m + 1)) R) (Q : XR P R) :
    natActR P R g (natActR P R g' Q) = natActR P R (fun v s => g v s * g' v s) Q := by
  unfold natActR
  simp only [LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, substR_substR]
  congr 1
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Units.val_mul, Matrix.det_mul, mul_zpow, mul_comm]

theorem natActR_one (R : Type) [Field R] (Q : XR P R) : natActR P R (fun _ _ => 1) Q = Q := by
  have hs : substR P R (fun _ _ => 1) = AlgHom.id R (XR P R) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    simp only [substR, MvPolynomial.aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]
    simp [ite_mul, Finset.sum_ite_eq]
  unfold natActR
  simp only [inv_one, Units.val_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul,
    LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [hs]
  rfl

end Act

theorem invT_mul {k : Type} [Fintype k] [DecidableEq k] (A B : GL k ℂ) : invT (A * B) = invT A * invT B := by
  ext : 1
  simp only [invT, Units.val_mk, Units.val_mul, mul_inv_rev, Matrix.transpose_mul]

theorem invT_one {k : Type} [Fintype k] [DecidableEq k] : invT (1 : GL k ℂ) = 1 := by
  ext : 1
  simp [invT]

variable {p : ℕ} [Fact p.Prime]

theorem evC_crdB_actC (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ}
    (h : (X.Pj i).m + 1 = n) (Gr : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B M : GL (Fin n) D.host.E)
    (V : XR (X.Pj i) ℂ) (z : Frames Gr) (f : Fr1 D n)
    (hf : ∀ τ, f.1 τ = (atR D (M * B⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * z.1 τ) :
    evC (X.Pj i) h (posJ X D pos i) Gr (crdB (embT D) B) V z = ev1 X D pos i h (actC X D pos i h M V) f ∧
      actC X D pos i h M (actC X D pos i h M⁻¹ V) = V := by
  have hcr : ∀ τ, crdB (embT D) B τ = (atR D B⁻¹ τ : Matrix (Fin n) (Fin n) ℂ) := fun τ => rfl
  let y : Fr1 D n := ⟨fun τ => crdB (embT D) B τ * z.1 τ, fun τ => by
    rw [Matrix.det_mul, hcr]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (atR D B⁻¹ τ).isUnit).mul (z.2 τ)⟩
  refine ⟨?_, ?_⟩
  · have hz : ∀ v s, zAt (X.Pj i) h (posJ X D pos i) (crdB (embT D) B) z.1 v s =
        zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) y.1 v s := by
      intro v s
      simp only [zAt, y, one_mul]
    have h1 : evC (X.Pj i) h (posJ X D pos i) Gr (crdB (embT D) B) V z = ev1 X D pos i h V y := by
      show (∏ v, ∏ s : Fin ((X.Pj i).n' v), (_ : ℂ)) * (_ : ℂ) = (∏ v, ∏ s : Fin ((X.Pj i).n' v), (_ : ℂ)) * (_ : ℂ)
      simp only [hz]
    have hy : IsTr (fun τ => (atR D M τ : Matrix (Fin n) (Fin n) ℂ)) y f := by
      intro τ
      rw [hf τ]
      show _ = (atR D M τ : Matrix (Fin n) (Fin n) ℂ) * (crdB (embT D) B τ * z.1 τ)
      rw [hcr, ← Matrix.mul_assoc, ← Units.val_mul]
      unfold atR
      rw [map_mul]
    have h2 := evC_natAct (X.Pj i) h (posJ X D pos i) (fun _ => 1) (fun _ => 1) (atR D M) y f hy V
    rw [h1]
    exact h2.symm
  · unfold actC
    rw [natActR_natActR]
    have he : (fun v s => hAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) (atR D M) v s *
        hAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) (atR D M⁻¹) v s) = fun _ _ => 1 := by
      funext v s
      have hm : ∀ τ, ((1 : GL (Fin n) ℂ) * atR D M τ * (1 : GL (Fin n) ℂ)⁻¹) * ((1 : GL (Fin n) ℂ) * atR D M⁻¹ τ * (1 : GL (Fin n) ℂ)⁻¹) = (1 : GL (Fin n) ℂ) := by
        intro τ
        simp only [one_mul, inv_one, mul_one, atR, ← map_mul, mul_inv_cancel, map_one]
      unfold hAt
      split_ifs
      · rw [← map_mul, hm, map_one]
      · rw [← invT_mul, ← map_mul, hm, map_one, invT_one]
    rw [he, natActR_one]

end GlobalTheory.TwV.DelA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalModelPolynomialOnStdFramesInjective
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem eq_zero_of_ev1_eq_zero_on_frames : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ), (∀ f : Fr1 D n, ev1 X D pos i h R f = 0) → R = 0 := by
  intro p _ X D pos i n h R hR
  refine Formalism.L2.G.evC_inj (X.Pj i) h (posJ X D pos i) (fun _ => 1) (fun _ => 1) (fun _ => by simp) R ?_
  funext f
  exact hR f

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalStdFramesEqDetPowerMulBlockValue
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

theorem zAt_eq_zT {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ)
    {n : ℕ} (h : (X.Pj i).m + 1 = n) (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (v : Fin (X.Pj i).nV) (s : Fin ((X.Pj i).n' v)) :
    zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) f v s =
      (zT X D pos f (posJ X D pos i ⟨v, s⟩)).submatrix (finCongr h) (finCongr h) := by
  subst h
  have hp : ((pos.symm (posJ X D pos i ⟨v, s⟩)).2 : ℕ) = s.val := by
    cases i <;> exact congrArg (fun x => (x.2 : ℕ)) (pos.symm_apply_apply _)
  have ho : IsOddPos (pos.symm (posJ X D pos i ⟨v, s⟩)).2 ↔ ¬ Even s.val := by
    unfold IsOddPos; rw [hp, Nat.not_even_iff_odd, Nat.odd_iff]
  unfold zAt zT reM
  by_cases hs : Even s.val
  · have : ¬ IsOddPos (pos.symm (posJ X D pos i ⟨v, s⟩)).2 := fun h' => (ho.1 h') hs
    simp [hs, this]
  · have : IsOddPos (pos.symm (posJ X D pos i ⟨v, s⟩)).2 := ho.2 hs
    simp [hs, this]

theorem ev1_eq_prod_det_pow_mul_valZ : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ) (f : Fr1 D n), ev1 X D pos i h R f = (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R f.1 := by
  intro p _ X D pos i n h R f
  show (∏ v, ∏ s : Fin ((X.Pj i).n' v), (zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) f.1 v s).det ^ (eAt (X.Pj i) v s)) *
      MvPolynomial.eval (fun x : Var (X.Pj i) => zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) f.1 x.1 x.2.1 x.2.2.1 x.2.2.2) R = _
  congr 1
  · simp_rw [zAt_eq_zT, Matrix.det_submatrix_equiv_self]
    rw [← Equiv.prod_comp (posJ X D pos i), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    unfold eT
    rw [Equiv.symm_apply_apply]
  · unfold valZ
    congr 2
    funext x
    rw [zAt_eq_zT]
    rfl

end GlobalTheory.TwV.DelA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGenusOneFormalIsoOfUnramifiedGoodReduction
section
namespace GlobalTheory.TwV.Lt

theorem curveEx_of_cm (h2 : Formalism.L2.Th1.CM.CM2) (h3 : Formalism.L2.Th1.CM.CM3) : CurveEx := by
  intro D cc δ B χ hc hd hχ p _ hcop h5 hIn lam
  obtain ⟨g, hgl, hAt, hM, hLT⟩ :=
    GlobalTheory.InertGenusOne.datum_exists_coprime h2 h3 D cc δ hc hd p hcop h5 hIn lam
  exact ⟨g, hLT, h5, hAt, hIn, hM, hc, hd, hχ, hgl.symm, hAt.2.2.2.1⟩

theorem exists_genusOne_formal_iso_of_unramified_good_reduction (h : Formalism.L2.Th1.CM.CM2) : CurveEx :=
  curveEx_of_cm h GlobalTheory.HondaCM3.cm3

end GlobalTheory.TwV.Lt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryPt
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem exists_unitary_pt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {A : LocAt F E n G}, LocGood σ J A → ∀ (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)), ∃ x, A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  intro F E _ _ _ _ _ n p G σ J A H i g
  exact ⟨_, H.isPt_sec i g, Subgroup.mul_mem _ (H.yG_mem i) (H.sec _).2⟩

end GlobalTheory.TwU
end

