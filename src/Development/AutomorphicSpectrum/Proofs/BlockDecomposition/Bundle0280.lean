module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0269
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0190
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHBijOfRes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0233
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0232
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0126
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0152
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdSomeZero
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0160
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0159
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0149
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIsAdicComplete
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0164
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0270
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0271
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0272
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0273

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNormSqLeToRealLintegralEnormSq
section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Dblock

theorem integral_norm_sq_le_toReal_lintegral_enorm_sq {α : Type} [MeasurableSpace α] (μ : Measure α) (f : α → ℂ) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal := by
  by_cases h : Integrable (fun x => ‖f x‖ ^ 2) μ
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity) h.aestronglyMeasurable]
    apply le_of_eq
    congr 1
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  · rw [integral_undef h]
    exact ENNReal.toReal_nonneg

end GlobalTheory.CompanionTheory.Dblock
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackOfKernelSupStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_pullback_of_kernel_sup : ∀ {X A B Z : Scheme.{0}} (a : A ⟶ X) (b : B ⟶ X) (f : Z ⟶ A) (g : Z ⟶ B)
    [IsClosedImmersion a] [IsClosedImmersion b] [IsClosedImmersion (f ≫ a)], f ≫ a = g ≫ b →
    Scheme.Hom.ker (f ≫ a) = Scheme.Hom.ker a ⊔ Scheme.Hom.ker b → IsPullback f g a b := by
  first | exact @GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup | exact GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup | (intros; apply GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOfBasicOpenTop
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B CrystallineSemistableComparison.Pb DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.KMVan

section Sc

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']

structure Sc (Φ : PDF R C) (Λ : Type) [CommRing Λ] where
  ρ : ∀ T : C, Λ →+* Φ.A.obj T
  nat : ∀ {T T' : C} (φ : T ⟶ T') (a : Λ), (Φ.A.map φ).hom (ρ T a) = ρ T' a

variable {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end Sc

end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section Loc
open TensorProduct
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end Loc
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct

end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct
section D
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end D
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct
section LT
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end LT
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section FV
variable {R : Type} [CommRing R]

end FV
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section PS
open CrystallineSemistableComparison.Pb.Site GlobalTheory.PDA GlobalTheory.CompanionTheory.ChartLocBc
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

end PS

section Res
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

end Res

section Fr
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ}

end Fr
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section CL
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V V' : X.Opens} {d : ℕ}

end CL
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section TAU
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU (⊤ : X.Opens) T := fun _ _ => trivial

def evT (T : Thick (nlFun γ p X q κ)) : Γ(X, ⊤) →+* T.B ⧸ T.J := ev T (inU_top T)

theorem evT_nat {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (f : Γ(X, ⊤)) :
    evT T' f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X)
      (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ ⊤), GlobalTheory.Cris.evalAt y ⊤ hh f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
    intro y hy hh
    subst hy
    exact evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) (inU_top T) hh f
  exact key _ (pt_hom φ) (inU_top T')

end TAU
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section TAU2
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

end TAU2
end GlobalTheory.CompanionTheory.KMVan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLatticeBase
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCBase

theorem dividedPowerFiltration_anti {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {k s : ℕ} (h : k ≤ s) :
    pdP δ s ≤ pdP δ k := by
  unfold CrystallineSemistableComparison.Pb.pdP
  refine Ideal.span_mono ?_
  rintro z ⟨L, hL, hs, rfl⟩
  exact ⟨L, hL, h.trans hs, rfl⟩

theorem latBase_lev : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ), 1 ≤ k → ∀ s, k ≤ s → LatBase (lev h k).γ l s := by
  intro l hl K M h k hk s hks
  have H := GlobalTheory.CompanionTheory.LatCHyp.hyp_k l k hk
  show CrystallineSemistableComparison.Pb.LatBase (CrystallineSemistableComparison.Pb.Lat.γ (CrystallineSemistableComparison.Pb.Lat.fk l k) (CrystallineSemistableComparison.xi0 l) l M (h.hc k)) l s
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_bot_iff.mp ((dividedPowerFiltration_anti _ hks).trans
      (GlobalTheory.CompanionTheory.LatNil.dividedPowerFiltration_eq_bot _ _ l M k H (h.hc k)).le)
  · exact GlobalTheory.CompanionTheory.Lat.quot_pdP_no_torsion _ _ l M k H (h.hc k)
  · exact GlobalTheory.CompanionTheory.LatticeUnit.natCast_dvd_pow _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatFG.dividedPowerFiltration_fg _ _ l M k H (h.hc k)
  · exact GlobalTheory.CompanionTheory.LatPrime.I_isPrime _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatVal.val _ _ l M k H
  · exact GlobalTheory.CompanionTheory.Lat.pow_mem_span_sup_I _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatCpl.isAdicComplete_A M H
  · exact GlobalTheory.CompanionTheory.LatClosed.closed _ _ l M k H (h.hc k)

end GlobalTheory.CompanionTheory.LatCBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisAStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_system_transition_galois_A : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ m g a, (levSys h).dA m (((levSys h).L (m + 1)).σA g a) = ((levSys h).L m).σA g ((levSys h).dA m a) := by
  first | exact @GlobalTheory.CompanionTheory.LatLevel.levSys_dA_σA | exact GlobalTheory.CompanionTheory.LatLevel.levSys_dA_σA | (intros; apply GlobalTheory.CompanionTheory.LatLevel.levSys_dA_σA <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionIsDPMorphismStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_system_transition_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ m, IsDPMorphism ((levSys h).L (m + 1)).γ ((levSys h).L m).γ ((levSys h).dA m) := by
  first | exact @GlobalTheory.CompanionTheory.LatC.levSys_ddp | exact GlobalTheory.CompanionTheory.LatC.levSys_ddp | (intros; apply GlobalTheory.CompanionTheory.LatC.levSys_ddp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelXiMemIdealAndThetaCompatStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_xi_mem_ideal_and_theta_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), (lev h k).lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ (lev h k).I ∧ ∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a → algebraMap (OK l K) (lev h k).A a - (lev h k).lam (algebraMap (Ainf l) (Acris l) w) ∈ (lev h k).I := by
  first | exact @GlobalTheory.CompanionTheory.LatC.Red.xi_and_sub_mem_I | exact GlobalTheory.CompanionTheory.LatC.Red.xi_and_sub_mem_I | (intros; apply GlobalTheory.CompanionTheory.LatC.Red.xi_and_sub_mem_I <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralEnormSqLe
section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Dblock

theorem lintegral_enorm_sq_le {α : Type} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ≥0∞)
    (hg : AEMeasurable g μ) :
    (∫⁻ x, g x ∂μ) ^ 2 ≤ μ Set.univ * ∫⁻ x, g x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hg
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have h1 : (∫⁻ a, ((g * fun _ => (1 : ℝ≥0∞)) : α → ℝ≥0∞) a ∂μ) = ∫⁻ x, g x ∂μ := by simp
  have h2 : (∫⁻ _a, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂μ) = μ Set.univ := by simp
  have h3 : (∫⁻ a, g a ^ (2 : ℝ) ∂μ) = ∫⁻ x, g x ^ 2 ∂μ := by
    refine lintegral_congr fun x => ?_
    exact ENNReal.rpow_two _
  rw [h1, h2, h3] at h
  calc (∫⁻ x, g x ∂μ) ^ 2
      ≤ ((∫⁻ x, g x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * (μ Set.univ) ^ (1 / (2 : ℝ))) ^ 2 := by
        gcongr
    _ = μ Set.univ * ∫⁻ x, g x ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
        rw [mul_comm]

theorem enorm_mean_sq_mul_le {α : Type} [MeasurableSpace α] (ν : Measure α) (s : Set α)
    (f : α → ℂ) :
    ‖((ν.real s : ℝ) : ℂ)⁻¹ * ∫ x in s, f x ∂ν‖ₑ ^ 2 * ν s ≤ ∫⁻ x in s, ‖f x‖ₑ ^ 2 ∂ν := by
  by_cases h0 : ν s = 0
  · simp [h0]
  by_cases htop : ν s = ⊤
  · simp [Measure.real, htop]
  by_cases hf : IntegrableOn f s ν
  · have hcs := lintegral_enorm_sq_le (ν.restrict s) (fun x => ‖f x‖ₑ) hf.1.enorm
    rw [Measure.restrict_apply_univ] at hcs
    have hz : ‖∫ x in s, f x ∂ν‖ₑ ≤ ∫⁻ x in s, ‖f x‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
    have hc : ‖((ν.real s : ℝ) : ℂ)⁻¹‖ₑ = (ν s)⁻¹ := by
      have hne : ((ν.real s : ℝ) : ℂ) ≠ 0 := by
        simp [Measure.real, ENNReal.toReal_eq_zero_iff, h0, htop]
      rw [enorm_inv hne]
      congr 1
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg,
        Measure.real, ENNReal.ofReal_toReal htop]
    rw [enorm_mul, hc]
    calc ((ν s)⁻¹ * ‖∫ x in s, f x ∂ν‖ₑ) ^ 2 * ν s
        ≤ ((ν s)⁻¹ * ∫⁻ x in s, ‖f x‖ₑ ∂ν) ^ 2 * ν s := by gcongr
      _ = ((ν s)⁻¹) ^ 2 * (∫⁻ x in s, ‖f x‖ₑ ∂ν) ^ 2 * ν s := by rw [mul_pow]
      _ ≤ ((ν s)⁻¹) ^ 2 * (ν s * ∫⁻ x in s, ‖f x‖ₑ ^ 2 ∂ν) * ν s := by gcongr
      _ = ((ν s)⁻¹ * ν s) ^ 2 * ∫⁻ x in s, ‖f x‖ₑ ^ 2 ∂ν := by ring
      _ = ∫⁻ x in s, ‖f x‖ₑ ^ 2 ∂ν := by
        rw [ENNReal.inv_mul_cancel h0 htop]; simp
  · rw [integral_undef hf]
    simp

end GlobalTheory.CompanionTheory.Dblock
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedClassRepresentative
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal

theorem loc_coef : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s →
    (∀ c : HQ (KS q s {W}) r (r + 1) m, ∃ y : Idx m d → Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) c) ∧
    ∀ y : Idx m d → Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) 0 → y = 0 := by
  intro K _ _ X q W d t s E ε hL σ m r hr hs
  obtain ⟨hc, h1, -⟩ := hL
  obtain ⟨PQ, hPQ⟩ := _root_.GlobalTheory.CompanionTheory.PolyTfCon.polyTf (dividedPowersBot K) q (Ideal.Quotient.mk ⊥) 1 s {W}
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {W})
  have key := _root_.GlobalTheory.CompanionTheory.LocGrStep.loc_gr PQ hF E σ hc r (fun r' hr' => (hPQ r' (by omega)).1) m
  obtain ⟨ha, hb⟩ := key.2 0 (by simpa using hr)
  refine ⟨fun c => ?_, fun y hy => ?_⟩
  · obtain ⟨x, -, hx⟩ := ha c
    refine ⟨fun I => ε.symm (x I), ?_⟩
    simpa only [RingEquiv.apply_symm_apply] using hx
  · have h0 : ∀ I, ε (y I) ∈ (sFil (KS q s {W}) ((0 : ℕ) : ℤ)).S E.D := fun I => by
      have e : (sFil (KS q s {W}) ((0 : ℕ) : ℤ)).S E.D = ⊤ := E.D.obj.pdPow_zero
      rw [e]
      trivial
    have := hb (fun I => ε (y I)) h0 hy
    funext I
    have h2 := h1 _ (this I)
    simpa using h2

end GlobalTheory.CompanionTheory.ConeLocal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardIdealPowerShiftStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_ideal_power_shift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {G : Z.Modules}, IsCoherent G → ∀ (V : X.Opens), IsAffineOpen V → ∃ c : ℕ, ∀ (n : ℕ) (s : Γ(G, φ ⁻¹ᵁ V)), s ∈ Set.range ((idealPowι I G (n + c)).app (φ ⁻¹ᵁ V)) → (show Γ((Scheme.Modules.pushforward φ).obj G, V) from s) ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pushforward φ).obj G, V)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.FormalShift.formal_shift | exact GlobalTheory.CompanionTheory.GE.FormalShift.formal_shift | (intros; apply GlobalTheory.CompanionTheory.GE.FormalShift.formal_shift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFundamentalDomainDiff
section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Unfolding

theorem setLIntegral_le_mul_fundamentalDomain_diff {G : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (F S T : Set G) (hF : IsFundamentalDomain Γ F μ) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (h : G → ℝ≥0∞) (hh : Measurable h)
    (hinv : ∀ γ ∈ Γ, ∀ x, h (γ * x) = h x) (N : ℕ)
    (hN : ∀ x, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (hST : ∀ γ ∈ Γ, ∀ x, γ * x ∈ S → x ∉ T) :
    ∫⁻ x in S, h x ∂μ ≤ N * ∫⁻ x in F \ T, h x ∂μ := by
  have hmeas : ∀ γ : Γ, Measurable (fun x : G => S.indicator h (γ • x)) := fun γ =>
    (hh.indicator hS).comp (measurable_const_smul γ)
  have h1 : ∫⁻ x in S, h x ∂μ = ∑' γ : Γ, ∫⁻ x in F, S.indicator h (γ • x) ∂μ := by
    rw [← lintegral_indicator hS]
    exact hF.lintegral_eq_tsum'' _
  have hpt : ∀ x, ∑' γ : Γ, S.indicator h (γ • x) ≤ N * Tᶜ.indicator h x := by
    intro x
    by_cases hx : x ∈ T
    · have hz : ∀ γ : Γ, S.indicator h (γ • x) = 0 := fun γ => by
        apply Set.indicator_of_notMem
        intro hmem
        exact hST γ γ.2 x (by simpa [Subgroup.smul_def] using hmem) hx
      simp [hz]
    · have hrew : ∀ γ : Γ, S.indicator h (γ • x) =
          ({γ : Γ | (γ : G) * x ∈ S}).indicator (fun _ => h x) γ := fun γ => by
        by_cases hg : (γ : G) * x ∈ S
        · rw [Set.indicator_of_mem (s := {γ : Γ | (γ : G) * x ∈ S}) (by exact hg),
            Subgroup.smul_def, smul_eq_mul, Set.indicator_of_mem hg, hinv γ γ.2 x]
        · rw [Set.indicator_of_notMem (s := {γ : Γ | (γ : G) * x ∈ S}) (by exact hg),
            Subgroup.smul_def, smul_eq_mul, Set.indicator_of_notMem hg]
      simp_rw [hrew]
      rw [← tsum_subtype, ENNReal.tsum_set_const,
        Set.indicator_of_mem (show x ∈ Tᶜ from hx)]
      gcongr
      have hc := ENat.toENNReal_le.mpr (hN x)
      simpa using hc
  calc ∫⁻ x in S, h x ∂μ = ∑' γ : Γ, ∫⁻ x in F, S.indicator h (γ • x) ∂μ := h1
    _ = ∫⁻ x in F, ∑' γ : Γ, S.indicator h (γ • x) ∂μ :=
        (lintegral_tsum fun γ => (hmeas γ).aemeasurable).symm
    _ ≤ ∫⁻ x in F, (N : ℝ≥0∞) * Tᶜ.indicator h x ∂μ := lintegral_mono hpt
    _ = N * ∫⁻ x in F, Tᶜ.indicator h x ∂μ :=
        lintegral_const_mul _ (hh.indicator hT.compl)
    _ = N * ∫⁻ x in F \ T, h x ∂μ := by
        rw [setLIntegral_indicator hT.compl, Set.inter_comm, Set.diff_eq]

end GlobalTheory.CompanionTheory.Unfolding
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousFormStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_section_homogeneous_form : ∀ {R : Type} [CommRing R] (I : Ideal R) (N e : ℕ) (k : Fin (N + 1)),
    (∀ s ∈ (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩,
      ∃ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
        t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ∧
        s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht) ∧
    (∀ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
      t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) →
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht ∈
        (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩) := by
  first | exact @GlobalTheory.CompanionTheory.GE.ker_thickι_chart | exact GlobalTheory.CompanionTheory.GE.ker_thickι_chart | (intros; apply GlobalTheory.CompanionTheory.GE.ker_thickι_chart <;> assumption)
end

