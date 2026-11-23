module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0851
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0726
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0816
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0835
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0859

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageMulInvariantContinuous
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

namespace GlobalTheory.GoodMul

theorem good_mul_invariant : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ) (ψ : AddChar (Ad E) ℂ) (f c : GA E a → ℂ),
    Good ψ m f → Continuous c → (∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, c (ratGL E a γ * g) = c g) →
    (∀ (r l : ℕ) (y : UnipotentBlockColumnIndex a r l → Ad E) (g : GA E a), c (blkU y * g) = c g) → Good ψ m (fun g => c g * f g) := by
  intro E _ _ a m ψ f c hf hc hl hu
  refine ⟨hc.mul hf.cont, fun γ hγ g => ?_, fun k hk y g => ?_, fun r hr hrm g => ?_⟩
  · show c _ * f _ = c g * f g
    rw [hl γ hγ g, hf.left γ hγ g]
  · show c _ * f _ = _ * (c g * f g)
    rw [hu k k y g, hf.law k hk y g]; ring
  · have h : (fun x : UnipotentBlockColumnIndex a r m → Ad E => c (blkU x * g) * f (blkU x * g)) =
        fun x => c g * f (blkU x * g) := by
      funext x; rw [hu r m x g]
    show avg _ (fun x : UnipotentBlockColumnIndex a r m → Ad E => c (blkU x * g) * f (blkU x * g)) = 0
    rw [h, avg_const_mul, hf.van r hr hrm g, mul_zero]

end GlobalTheory.GoodMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageTopOfVanishingBlockAver
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

noncomputable section

namespace GlobalTheory.CuspGeneric

theorem good_top : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E (m + 1) → ℂ),
    Continuous f → (∀ γ g, f (ratGL E (m + 1) γ * g) = f g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => f (blkU x * g)) = 0) → Good ψ m f := by
  intro E _ _ m ψ f hc hl hv
  refine ⟨hc, fun γ _ g => hl γ g, by
    intro k hk y g
    have he : IsEmpty (UnipotentBlockColumnIndex (m + 1) k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast (m + 1) k) (0 : UnipotentBlockColumnIndex (m + 1) k k → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul], hv⟩

end GlobalTheory.CuspGeneric

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieModelFiniteBaseChange
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.ThetaSqLow

section Bound

open Matrix GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic.GJMatrix
open scoped nonZeroDivisors Classical

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_mul_pow_le {G : (Fin a → Ad E) → ℂ} (hG : G ∈ schwartzBruhatPi (K := E) (ι := Fin a)) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖G y‖ * (1 + ‖fun i => pInf E (y i)‖) ^ M ≤ K := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
    set ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (toMixedPi E a) φ with hψ
    set K₀ : ℝ := 2 ^ M * (Finset.Iic (M, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ with hK₀
    have hK : 0 ≤ K₀ := by positivity
    refine ⟨K₀ * |B|, by positivity, fun y => ?_⟩
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (M, 0)) (k := M) (n := 0) le_rfl le_rfl ψ
      (fun i => pInf E (y i))
    rw [norm_iteratedFDeriv_zero] at h1
    have h2 : ψ (fun i => pInf E (y i)) = φ (infPartPi y) := by
      rw [hψ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, toMixedPi_pInf]
    rw [h2] at h1
    simp only [schwartzBruhatTensorPi, norm_mul]
    calc _ = ((1 + ‖fun i => pInf E (y i)‖) ^ M * ‖φ (infPartPi y)‖) * ‖g (finPartPi y)‖ := by ring
      _ ≤ _ := mul_le_mul h1 ((hB _).trans (le_abs_self _)) (norm_nonneg _) hK
  | zero => exact ⟨0, le_rfl, fun y => by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨K₁, h₁, hG⟩ := hG
    obtain ⟨K₂, h₂, hH⟩ := hH
    refine ⟨K₁ + K₂, by positivity, fun y => le_trans ?_ (add_le_add (hG y) (hH y))⟩
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  | smul c G _ hG =>
    obtain ⟨K, h, hG⟩ := hG
    refine ⟨‖c‖ * K, by positivity, fun y => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hG y) (norm_nonneg _)

theorem exists_latt {G : (Fin a → Ad E) → ℂ} (hG : G ∈ schwartzBruhatPi (K := E) (ι := Fin a)) :
    ∃ J : (FractionalIdeal (𝓞 E)⁰ E)ˣ, ∀ y, (fun i => pFin E (y i)) ∉ latt a J → G y = 0 := by
  obtain ⟨⟨L, hL, hs⟩, -⟩ := GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments E a G hG
  obtain ⟨J, hJ⟩ := exists_subset_idealFiniteAdeles
    (isCompact_iUnion fun i : Fin a => hL.image (continuous_apply i))
  refine ⟨J, fun y hy => by_contra fun h => hy fun i => hJ (Set.mem_iUnion.2 ⟨i, _, hs y h, rfl⟩)⟩

theorem exists_bound {π' : CuspSub E a} (hπ : π'.IsUnitary) {φ' : GA E a → ℂ} (hφ : φ' ∈ GlobalTheory.JSW.mspanR π')
    {G : (Fin a → Ad E) → ℂ} (hG : G ∈ schwartzBruhatPi (K := E) (ι := Fin a)) :
    ∃ C : ℝ, ∀ g : GA E a, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) ≤
        ENNReal.ofReal (C * (GlobalTheory.RSnm.detAbs g)⁻¹) := by
  obtain ⟨J, hJ⟩ := exists_latt hG
  obtain ⟨M, C₁, h₁⟩ := GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest E a J (a * Module.finrank ℚ E)
    GlobalTheory.RSTheta.finrank_pi_Cinf.le
  obtain ⟨K, hK, hGK⟩ := norm_mul_pow_le hG M
  obtain ⟨ψ, rfl, -, -, B, hB⟩ := GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded E a GlobalTheory.CuspOrth.cuspFormsBounded π' hπ φ' hφ
  obtain ⟨C₂, h₂⟩ := GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector E a π' hπ ψ (Or.inr hφ) [] (latt a J) (GlobalTheory.RSTheta.isCompact_latt J) {1}
    isCompact_singleton 1
  refine ⟨C₁ * (K * |B| * |C₂|), fun g => ?_⟩
  have hδ := GlobalTheory.RSnm.detAbs_pos g
  obtain ⟨hs, hle⟩ := h₁ g (K * |B| * |C₂| * (GlobalTheory.RSnm.detAbs g)⁻¹)
    (fun ξ => ψ.1 g ^ 2 * G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ j)) g.val)) (by positivity)
    (fun ξ hξ => mul_eq_zero_of_right _ (hJ _ hξ))
    (fun ξ ξ' h0 hξ' => by
      have h3 := h₂ g 1 rfl ξ' h0 hξ'
      simp only [GlobalTheory.GLFin.word, mul_one, pow_one] at h3
      set r := ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* g.val) i)‖ ^ (a * Module.finrank ℚ E)
      have hr : 0 ≤ r := by positivity
      have h4 : ‖ψ.1 g‖ ≤ |C₂| * (r / GlobalTheory.RSnm.detAbs g) :=
        le_trans h3 (mul_le_mul_of_nonneg_right (le_abs_self _) (div_nonneg hr hδ.le))
      rw [norm_mul, norm_pow, mul_assoc, sq]
      calc _ ≤ (|B| * (|C₂| * (r / GlobalTheory.RSnm.detAbs g))) * K :=
            mul_le_mul (mul_le_mul ((hB g).trans (le_abs_self _)) h4 (norm_nonneg _) (abs_nonneg _)) (hGK _)
              (by positivity) (by positivity)
        _ = _ := by ring)
  rw [← ENNReal.tsum_mul_left, mul_assoc C₁]
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hle)
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
  refine tsum_congr fun ξ => ?_
  rw [ofReal_norm, eNorm_mul, eNorm_pow]

end Bound

set_option synthInstance.maxHeartbeats 100000 in
theorem lintegral_low_ne_top : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ, 1 < x →
      ∫⁻ g in 𝓕 ∩ {g | GlobalTheory.RSnm.detAbs g ≤ 1}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  intro E _ _ _ m π' hπ φ' hφ G hG μ _ 𝓕 h𝓕 x hx
  obtain ⟨C, hC⟩ := exists_bound hπ hφ hG
  have hi : IntegrableOn (fun g : GA E (m + 1) => GlobalTheory.RSnm.detAbs g ^ (x - 1))
      (𝓕 ∩ {g | GlobalTheory.RSnm.detAbs g ≤ 1}) μ := _root_.GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low E (m + 1) m.succ_pos μ 𝓕 h𝓕 (x - 1) (by linarith)
  refine ne_top_of_le_ne_top (hi.const_mul C).2.ne (lintegral_mono fun g => ?_)
  have hδ := GlobalTheory.RSnm.detAbs_pos g
  refine (mul_le_mul_left (hC g) _).trans ?_
  rw [mul_comm, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), Real.eNorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) (le_abs_self _))
  beta_reduce
  rw [Real.rpow_sub_one hδ.ne']
  ring

end GlobalTheory.ThetaSqLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoCharacterOffsetUnramified
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cut

namespace GlobalTheory.UnrNoChi

variable {D : D7} (i : D.nd.Loc)

theorem mapM_twistM' {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ)
    (g : GE D.nd) :
    mapM (toK D.nd i) (twistM M χ) g = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) M g := by
  ext a b
  simp [mapM, twistM, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem chi_one_eq_one (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (hρ : GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ)
    {γ : GE D.nd} (hγ : r π γ = 1) : chiU D.nd i 1 γ = 1 := by
  obtain ⟨-, e, he⟩ := hρ
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set u := e.symm (0, Pi.single (⟨0, ht⟩ : Fin D.R.t) 1) with hu
  have h := congrArg (fun p => p.2 (⟨0, ht⟩ : Fin D.R.t)) (he γ u)
  simp only [hγ, Units.val_one, Matrix.map_one (toK D.nd i) (map_zero _) (map_one _), Matrix.one_mulVec, hu,
    LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at h
  apply Units.ext
  apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
  simpa using h.symm

end GlobalTheory.UnrNoChi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerMapFlatSemiabelian
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.SBThetaUpper

open GroundTheory.Automorphic.GJMatrix GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GlobalTheory.ShortVecDecay GlobalTheory.RSTheta

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_norm_mul_pow_le {G : (Fin a → Ad E) → ℂ} (hG : G ∈ schwartzBruhatPi (K := E) (ι := Fin a)) (M : ℕ) :
    ∃ B : ℝ, ∀ y, ‖G y‖ * (1 + ‖fun i => pInf E (y i)‖) ^ M ≤ B := by
  classical
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi E).mp hg
    obtain ⟨B, hB⟩ := h1.continuous.bounded_above_of_compact_support h2
    set S := (toMixedPi E a).symm
    set C := ‖(S : (Fin a → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin a → Cinf E))‖
    have hC : 0 ≤ C := norm_nonneg _
    obtain ⟨A₀, -, hA₀⟩ := φ.decay 0 0
    obtain ⟨A₁, -, hA₁⟩ := φ.decay M 0
    refine ⟨(1 + C) ^ M * 2 ^ M * (A₀ + A₁) * B, fun y => ?_⟩
    rw [GlobalTheory.SchwartzBruhatMoments.pInfPi_eq, schwartzBruhatTensorPi, norm_mul]
    have hBy := hB (finPartPi y)
    generalize finPartPi y = z at hBy
    generalize infPartPi y = u
    have a0 := hA₀ u
    have a1 := hA₁ u
    rw [norm_iteratedFDeriv_zero] at a0 a1
    rw [pow_zero, one_mul] at a0
    have h1 : ‖S u‖ ≤ C * ‖u‖ := (S : (Fin a → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin a → Cinf E)).le_opNorm u
    have h2 : 1 + ‖S u‖ ≤ (1 + C) * (1 + ‖u‖) := by nlinarith [norm_nonneg u, norm_nonneg (S u)]
    have h3 : (1 + ‖S u‖) ^ M ≤ (1 + C) ^ M * (2 ^ M * (1 + ‖u‖ ^ M)) := by
      calc (1 + ‖S u‖) ^ M ≤ ((1 + C) * (1 + ‖u‖)) ^ M := pow_le_pow_left₀ (by positivity) h2 M
        _ = (1 + C) ^ M * (1 + ‖u‖) ^ M := mul_pow _ _ _
        _ ≤ (1 + C) ^ M * (2 ^ M * (1 + ‖u‖ ^ M)) :=
          mul_le_mul_of_nonneg_left (GlobalTheory.SchwartzBruhatMoments.one_add_pow_le (norm_nonneg u) M) (by positivity)
    have h4 : ‖φ u‖ * (1 + ‖S u‖) ^ M ≤ (1 + C) ^ M * 2 ^ M * (A₀ + A₁) := by
      calc ‖φ u‖ * (1 + ‖S u‖) ^ M ≤ ‖φ u‖ * ((1 + C) ^ M * (2 ^ M * (1 + ‖u‖ ^ M))) :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ = ((1 + C) ^ M * 2 ^ M) * (‖φ u‖ + ‖u‖ ^ M * ‖φ u‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add a0 a1) (by positivity)
    calc ‖φ u‖ * ‖g z‖ * (1 + ‖S u‖) ^ M = ‖φ u‖ * (1 + ‖S u‖) ^ M * ‖g z‖ := by ring
      _ ≤ _ := mul_le_mul h4 hBy (norm_nonneg _) (le_trans (by positivity) h4)
  | zero => exact ⟨0, fun y => by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨B₁, h1⟩ := hG
    obtain ⟨B₂, h2⟩ := hH
    refine ⟨B₁ + B₂, fun y => le_trans ?_ (add_le_add (h1 y) (h2 y))⟩
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  | smul c G _ hG =>
    obtain ⟨B, h⟩ := hG
    refine ⟨‖c‖ * B, fun y => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)

theorem isSmallKernel_sq_mul {φ : GA E a → ℂ} (h : Decays φ) {G : (Fin a → Ad E) → ℂ}
    (hG : G ∈ schwartzBruhatPi (K := E) (ι := Fin a)) : IsSmallKernel fun g y => φ g ^ 2 * G y := by
  obtain ⟨L, hL, hs⟩ := (GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments E a G hG).1
  refine ⟨⟨L, hL, fun g y hy => hs y (right_ne_zero_of_mul hy)⟩, fun L hL N M => ?_⟩
  obtain ⟨C, hC⟩ := h L hL {1} isCompact_singleton N
  obtain ⟨C', hC'⟩ := h L hL {1} isCompact_singleton 0
  obtain ⟨B, hB⟩ := exists_norm_mul_pow_le hG M
  refine ⟨|C| * |C'| * |B|, fun g ξ hξ hm y => ?_⟩
  have hΔ : 0 < (GroundTheory.Global.IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det g) : ℝ) :=
    (GroundTheory.Global.IdeleGroup.ideleModule E _).2
  have h1 := (hC g 1 rfl ξ hξ hm).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have h2 := (hC' g 1 rfl ξ hξ hm).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity))
  rw [mul_one] at h1 h2
  have h3 : ‖G y‖ ≤ |B| * (1 + ‖fun i => pInf E (y i)‖) ^ (-(M : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact (hB y).trans (le_abs_self B)
  beta_reduce
  rw [norm_mul, sq, norm_mul]
  refine (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _) (by positivity)).trans_eq ?_
  ring

set_option synthInstance.maxHeartbeats 400000 in
theorem lintegral_theta_upper_ne_top : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ,
      ∫⁻ g in 𝓕 ∩ {g | 1 ≤ GlobalTheory.RSnm.detAbs g}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  intro E _ _ _ m π' hπ' φ' hφ' G hG μ _ 𝓕 h𝓕 x
  have hd : Decays φ' := GlobalTheory.MSpanDecay.Good.decays (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ' hφ')
  obtain ⟨C, hC⟩ := (isSmallKernel_sq_mul hd hG).tsum_le (N := ⌈x⌉₊ + 1) (by omega)
  have hI := ((integrableOn_absDet_rpow_neg (Nat.succ_pos m) μ h𝓕 (s := (⌈x⌉₊ + 1 : ℕ) - x)
      (by push_cast; linarith [Nat.le_ceil x])).const_mul C).lintegral_lt_top
  refine ne_top_of_le_ne_top hI.ne (lintegral_mono fun g => ?_)
  obtain ⟨hs, hle⟩ := hC g
  have h0 := GlobalTheory.RSnm.detAbs_pos g
  change _ ≤ C * GlobalTheory.RSnm.detAbs g ^ _ at hle
  change _ ≤ ENNReal.ofReal (C * GlobalTheory.RSnm.detAbs g ^ _)
  rw [← ENNReal.tsum_mul_left]
  simp only [← eNorm_pow, ← eNorm_mul]
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs,
    ← ENNReal.ofReal_mul (tsum_nonneg fun _ => norm_nonneg _), neg_sub, sub_eq_neg_add, Real.rpow_add h0, ← mul_assoc]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle (by positivity))

end GlobalTheory.SBThetaUpper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralRsHatZero
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors

open GlobalTheory.RSTheta GlobalTheory.ThetaPoisson GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix GroundTheory.Global
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.RSResidue

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rsHat_zero {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (F F' : Sm E a) (hΦ : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ) (g : GA E a) :
    adelicFourierPi E (rsPsi ℓ F.1 F'.1 Φ J η g) 0 =
      (∫ x, rsInf ℓ F.1 F'.1 Φ g x ∂infMeasure E a) * ((finiteMeasurePi E (latt a J)).toReal : ℂ) := by
  have h := rsHat_eq J η F F' hΦ g 0
  simp only [rsHat] at h
  rw [h]
  have h0 : (fun i => pFin E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have h1 : (fun i => pInf E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have h2 : (latt a (traceDualIdeal E J)).indicator (1 : (Fin a → Af E) → ℂ) 0 = 1 :=
    Set.indicator_of_mem (s := latt a (traceDualIdeal E J)) (show (0 : Fin a → Af E) ∈ latt a (traceDualIdeal E J) from
      fun i => (idealFiniteAdeles (traceDualIdeal E J)).zero_mem) _
  rw [h0, h1, h2]
  simp [infFourier]

theorem setIntegral_mul_right {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (latticeGL E a) 𝓕 μ) {f : GA E a → ℂ}
    (hf : ∀ γ ∈ latticeGL E a, ∀ g, f (γ * g) = f g) (h : GA E a) :
    ∫ g in 𝓕, f (g * h) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  haveI := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hmp : MeasurePreserving (fun g => g * h) μ μ := measurePreserving_mul_right μ h
  have e1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight h) f ((fun g => g * h⁻¹) ⁻¹' 𝓕)
  have e2 : (fun g => g * h) ⁻¹' ((fun g => g * h⁻¹) ⁻¹' 𝓕) = 𝓕 := by ext; simp
  rw [e2] at e1
  rw [e1]
  have h2 : IsFundamentalDomain (latticeGL E a) ((fun g => g * h⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ h⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  haveI : DiscreteTopology (latticeGL E a) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL
  haveI : SecondCountableTopology (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E a
  have hI : GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) f := hf
  have A := (GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h2 (GlobalTheory.AutomorphicL2Unitary.descend (latticeGL E a) f)).trans
    (integral_congr_ae (Eventually.of_forall hI.descend_mk))
  have B := (GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕 (GlobalTheory.AutomorphicL2Unitary.descend (latticeGL E a) f)).trans
    (integral_congr_ae (Eventually.of_forall hI.descend_mk))
  exact A.symm.trans B

end GlobalTheory.RSResidue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupMove
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move

theorem setup_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) (ρ : Setup D.ntw), ρ.Good → RealPin X.R X.cG ρ →
    ∃ ρ' : Setup D'.ntw, SameSetup ρ ρ' ∧ ρ'.Good ∧ RealPin X'.R X'.cG ρ' :=
  fun h _ _ m ρ g p => setup_move_data h m ρ g p

end GlobalTheory.TwInputs.Move
end

