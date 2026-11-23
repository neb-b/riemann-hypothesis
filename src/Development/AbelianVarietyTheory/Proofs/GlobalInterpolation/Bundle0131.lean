module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0129
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Formalism.LocalRingCardinality.DataLevel
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0130

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdicIntegersCharacterDualIndexEqResidueCardZpow
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.DualIndexPow

theorem nIdx_eq_zpow : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (c : ℤ), (∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp c) → LocalAdditiveCharacterDual.nIdx F ψ v = (PlaceSplittingTypes.resCard F v : ℝ) ^ c := by
  intro F _ _ ψ v c h
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective F v
    (WithZero.exp (-c))
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  have hu : ∀ hx : WithZero.exp (-c) ≠ 0, Multiplicative.toAdd (WithZero.unzero hx) = -c :=
    fun _ => rfl

  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.psiDual F ψ v = GlobalTheory.LocalDensityProduct.colonV v a := by
    ext t
    rw [GlobalTheory.LocalDensityProduct.mem_colonV]
    change (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ _
    rw [h t, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, ha,
      WithZero.exp_neg, mul_inv_le_iff₀ (by simp), one_mul]
  have hi : GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.intV F v = GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.intV F v := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.nIdx
  rw [hd, hi, (GlobalTheory.LocalDensityProduct.index_colonV v a ha0).2,
    NumberField.FinitePlace.norm_def, ha,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.resCard]
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, WithZero.log_exp]
  simp [_root_.zpow_neg]

end GlobalTheory.DualIndexPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLatticeBasisExists
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.HomLocBasis

open GlobalTheory.PlaceInt.LocBasis Module

theorem exists_basis_primeTo {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (m : ℕ) (hm : 0 < m) (L : Submodule (𝓞 K) V) (hfg : L.FG) :
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, ∃ k : ℕ, Nat.Coprime k m ∧ k • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  first
  | exact @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
  | exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
  | (apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime ..)


open Formalism.MainNotions.TaylorLogMetric in
theorem exists_nnBasis : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), p.Prime → Nat.Coprime (Ideal.absNorm cc) p → TaylorLogMetric.admitted D N N' L L' → ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.NNBasis D (TaylorLogMetric.tor0 D cc δ) δ p L L' b := by
  intro D cc δ p N N' L L' hp hcc hA
  have hL : StandardLatticesGL3.SD D L := hA.2.2.1
  have hL' : StandardLatticesGL3.SD D L' := hA.2.2.2
  obtain ⟨s, y, y', hy, hy', hexp⟩ := GlobalTheory.HomDual.exists_dual_family_hom D
    (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
  let Y : Submodule (𝓞 D.host.K) (Matrix (Fin N') (Fin N) D.host.E) :=
    Submodule.span (𝓞 D.host.K) (Set.range y)
  have hYle : ∀ x ∈ Y, x ∈ YYl D L L' := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    exact (YYl D L L').sum_mem fun i _ => GlobalTheory.ThetaConj.smul_mem_YYl D L L' (c i) (hy i)
  have hYge : ∀ x ∈ YYl D L L', x ∈ Y := by
    intro x hx
    have hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i) := fun i =>
      GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i)
    choose t ht using hi
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨t, ?_⟩
    conv_rhs => rw [hexp x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ht]; rfl
  obtain ⟨r, b, hli, hb, hw⟩ := exists_basis_primeTo p hp.pos Y (Submodule.fg_span (Set.finite_range y))
  set n : ℕ := Ideal.absNorm cc with hn
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, Nat.coprime_zero_left] at hcc
    exact hp.one_lt.ne' hcc
  have hnK : (n : D.host.K) ≠ 0 := by exact_mod_cast hn0
  refine ⟨r, fun i => n • b i, ⟨?_, fun i => ?_, fun w hwY => ?_⟩, fun i => ?_⟩
  · have := hli.units_smul fun _ => Units.mk0 _ hnK
    have e : (fun i => n • b i) = (fun _ : Fin r => Units.mk0 _ hnK) • b := by
      funext i
      simp [Units.smul_def, Nat.cast_smul_eq_nsmul]
    rw [e]; exact this
  · refine ⟨1, by simp, ?_⟩
    rw [Nat.cast_one, one_smul]
    exact nsmul_mem (hYle _ (hb i)) n
  · obtain ⟨k, hk, hkw⟩ := hw w (hYge w hwY)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hkw
    refine ⟨n * k, Nat.Coprime.mul_left hcc hk, c, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, mul_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]; rfl
  · refine AddSubgroup.subset_closure ⟨δ * n, AddSubgroup.subset_closure ⟨(n : 𝓞 D.host.K), Ideal.absNorm_mem cc, ?_⟩,
      b i, hYle _ (hb i), ?_⟩
    · simp
    · funext τ j k
      change δ * embT D τ ((n • b i) j k) = δ * n * embT D τ (b i j k)
      rw [Matrix.smul_apply, map_nsmul, nsmul_eq_mul, mul_assoc]

end GlobalTheory.HomLocBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmLocalDensitiesProductFormula
section
namespace GlobalTheory.Proof.cm_localDensities_productFormula

theorem densityProduct : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.DensityProduct :=
  fun F E _ _ _ _ _ _ σ h₁ h₂ h₃ =>
    ⟨_root_.GlobalTheory.StdCharUnique.existsUnique_isStdChar_cm F E σ h₁ h₂ h₃, GlobalTheory.T.dual_lattice_different_index F E σ h₁ h₂ h₃, _root_.GlobalTheory.LocalDifferentProduct.prod_normDifferentV F E σ h₁ h₂ h₃,
      _root_.GlobalTheory.AdelicCharDilate.exists_eq_std_dilate F E σ h₁ h₂ h₃, GlobalTheory.T.hasProd_quadExtLocalEulerFactorInv_inv F E σ h₁ h₂ h₃, _root_.GlobalTheory.LocalDensityProduct.density_product F E σ h₁ h₂ h₃⟩

end GlobalTheory.Proof.cm_localDensities_productFormula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsArchimedeanExponentsAdeleCharacter
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.LamExists

theorem re_mul_of_isReal {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (a : F) (x : Ainf F)
    (w : InfinitePlace F) : re (algebraMap F (Ainf F) a * x) w = re (algebraMap F (Ainf F) a) w * re x w := by
  have hr : (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w)).im = 0 := by
    rw [InfiniteAdeleRing.algebraMap_apply]
    rw [InfinitePlace.Completion.extensionEmbedding_coe]
    have := InfinitePlace.isReal_iff.1 (hF.isReal w)
    exact Complex.conj_eq_iff_im.1 (RingHom.congr_fun this a)
  show (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w * x w)).re = _
  rw [map_mul, Complex.mul_re, hr, zero_mul, sub_zero]
  rfl

theorem re_ne_zero {F : Type} [Field F] [NumberField F] (a : F) (ha : a ≠ 0) (w : InfinitePlace F)
    (hF : IsTotallyReal F) : re (algebraMap F (Ainf F) a) w ≠ 0 := by
  have hr : (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w)).im = 0 := by
    rw [InfiniteAdeleRing.algebraMap_apply]
    rw [InfinitePlace.Completion.extensionEmbedding_coe]
    have := InfinitePlace.isReal_iff.1 (hF.isReal w)
    exact Complex.conj_eq_iff_im.1 (RingHom.congr_fun this a)
  intro h0
  have : InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w) = 0 :=
    Complex.ext h0 hr
  rw [InfiniteAdeleRing.algebraMap_apply] at this
  rw [InfinitePlace.Completion.extensionEmbedding_coe, map_eq_zero] at this
  exact ha this

end GlobalTheory.SWQ.LamExists

theorem GlobalTheory.SWQ.exists_isLam : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ lam, IsLam ψ lam := by
  intro F _ _ hF ψ hψ
  haveI := hF
  obtain ⟨ψ₀, h₀⟩ := GlobalTheory.SnMass.Inhab.exists_isStdChar F
  obtain ⟨a, ha, h⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ₀ ψ h₀.1 hψ
  refine ⟨fun w => re (algebraMap F (Ainf F) a) w, fun w => GlobalTheory.SWQ.LamExists.re_ne_zero a ha w hF, fun x => ?_⟩
  rw [GlobalTheory.GaugeEx.CharLoc.psiInf_twist h, h₀.2.1]
  exact congrArg (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))
    (Finset.sum_congr rfl fun w _ => GlobalTheory.SWQ.LamExists.re_mul_of_isReal hF a x w)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMeasurableRealOrbitMapOfAdelicOrbitStatement
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_realOrbitMap_of_adelicOrbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)), IsCMFam τ → ∀ (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ) (J : Matrix (Fin M) (Fin M) E) (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ), (∀ ρ, N ρ * A ρ = 1) → (∀ ρ, A ρ * N ρ = 1) → ∀ x : Fin 1 → Fin M → E, AllSome (fun pt : (I → UpqT P Q) → (Fin 1 → Fin M → Ainf F ⊗[F] E) => ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) = UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) fun pt => Measurable pt ∧ (∀ g g', (∀ ρ, UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i)) = UpqT.mat (g' ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) → pt g = pt g') ∧ ∀ (h : HA (AF F) σ J) (t : I → UpqT P Q), (∀ ρ, UpqT.mat (t ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) → pt t = projInf (h⁻¹ • ratTup (F := F) (AF F) x) := by
  first | exact @GlobalTheory.RealOrbitMap.realOrbit | exact GlobalTheory.RealOrbitMap.realOrbit | (intros; apply GlobalTheory.RealOrbitMap.realOrbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinPartInvSmulMemLatHatIffStabMulLevelStatement
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finPart_inv_smul_mem_latHat_iff_stab_mul_level : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → ∀ x : Fin 1 → Fin M → E, x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ h : HA (AF F) σ J, projFin (h⁻¹ • ratTup (F := F) (AF F) x) 0 ∈ latHat F E (L : Set (Fin M → E)) ↔ ∃ a ∈ Hstab (AF F) σ J x, a⁻¹ * h ∈ stab σ J (L : Set (Fin M → E)) := by
  first | exact @GlobalTheory.AdelicOrbit.mem_latHat_iff | exact GlobalTheory.AdelicOrbit.mem_latHat_iff | (intros; apply GlobalTheory.AdelicOrbit.mem_latHat_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemIntVIffOfSplitting
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.SplitIntegers

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem conj_tmul (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] (a : E) (y : R) :
    Formalism.UG.sigR hc.sig R (a ⊗ₜ[F] y) = star a ⊗ₜ[F] y := rfl

omit [NumberField F] [NumberField E] [StarRing E] in
theorem algebraMap_tmul {R : Type} [CommRing R] [Algebra F R] (c : F) (y : R) :
    (algebraMap F E c) ⊗ₜ[F] y = (1 : E) ⊗ₜ[F] (algebraMap F R c * y) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]

theorem exists_add_conj (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] (z : E ⊗[F] R) :
    ∃ p : R, z + Formalism.UG.sigR hc.sig R z = (1 : E) ⊗ₜ[F] p := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a y =>
    obtain ⟨c, h⟩ := (hc.fixed (a + star a)).1 (by simp [add_comm])
    exact ⟨algebraMap F R c * y, by rw [conj_tmul, ← TensorProduct.add_tmul, ← h, algebraMap_tmul]⟩
  | add x y hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    refine ⟨p + q, ?_⟩
    rw [map_add (f := _), TensorProduct.tmul_add, ← hp, ← hq]; ring

theorem exists_of_conj_eq (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] {z : E ⊗[F] R}
    (hz : Formalism.UG.sigR hc.sig R z = z) : ∃ p : R, (1 : E) ⊗ₜ[F] p = z := by
  obtain ⟨p, hp⟩ := exists_add_conj hc z
  rw [hz, ← two_smul F z] at hp
  refine ⟨(2⁻¹ : F) • p, ?_⟩
  rw [TensorProduct.tmul_smul, ← hp, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem exists_diag (hc : CMData F E) {K : Type} [Field K] [Algebra F K]
    (φ : E ⊗[F] K ≃+* K × K) (hφ : ∀ x, φ (Formalism.UG.sigR hc.sig K x) = swapR _ (φ x)) :
    ∃ θ : K ≃+* K, ∀ y, φ ((1 : E) ⊗ₜ[F] y) = (θ y, θ y) := by
  let f : K →+* K := ((RingHom.fst K K).comp φ.toRingHom).comp
    (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := K)).toRingHom
  have hf : ∀ y, φ ((1 : E) ⊗ₜ[F] y) = (f y, f y) := fun y => by
    have h := hφ ((1 : E) ⊗ₜ[F] y)
    rw [conj_tmul, star_one] at h
    have h2 := congrArg Prod.snd h
    exact Prod.ext rfl h2
  refine ⟨RingEquiv.ofBijective f ⟨f.injective, fun b => ?_⟩, hf⟩
  obtain ⟨p, hp⟩ := exists_of_conj_eq hc (z := φ.symm (b, b)) (φ.injective (by
    rw [hφ, φ.apply_symm_apply]; rfl))
  refine ⟨p, ?_⟩
  have := hf p
  rw [hp, φ.apply_symm_apply] at this
  exact (congrArg Prod.fst this).symm

theorem mem_of_isIntegral (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F}
    (hx : IsIntegral ℤ x) : x ∈ v.adicCompletionIntegers F := by
  have hi : IsIntegral (v.adicCompletionIntegers F) x := hx.tower_top
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact b.2

omit [NumberField E] [StarRing E] [Algebra F E] in
theorem map_mem {S : Type} (v : HeightOneSpectrum (𝓞 F)) [FunLike S E (v.adicCompletion F)]
    [RingHomClass S E (v.adicCompletion F)] (g : S) (a : 𝓞 E) :
    g (algebraMap (𝓞 E) E a) ∈ v.adicCompletionIntegers F :=
  mem_of_isIntegral v (a.isIntegral_coe.map_of_comp_eq (RingHom.id ℤ)
    (g : E →+* v.adicCompletion F) (RingHom.ext_int _ _))

end GlobalTheory.SplitIntegers

namespace GlobalTheory

open SplitIntegers

theorem mem_intV_iff_of_splitting : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (v : HeightOneSpectrum (𝓞 F)), (∀ (θ : v.adicCompletion F ≃+* v.adicCompletion F) (x : v.adicCompletion F), θ x ∈ v.adicCompletionIntegers F ↔ x ∈ v.adicCompletionIntegers F) → ∀ (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, φ (Formalism.UG.sigR hc.sig (v.adicCompletion F) x) = swapR _ (φ x)) → ∀ x, x ∈ intV E v ↔ (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ _ hc v hθ φ hφ
  obtain ⟨θ, hd⟩ := exists_diag hc φ hφ
  have hθ' : ∀ y ∈ v.adicCompletionIntegers F, θ.symm y ∈ v.adicCompletionIntegers F :=
    fun y hy => (hθ θ.symm y).2 hy
  let ι : E →+* v.adicCompletion F × v.adicCompletion F := φ.toRingHom.comp
    (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E) (B := v.adicCompletion F))
  have hι : ∀ a : 𝓞 E,
      (φ (algebraMap (𝓞 E) E a ⊗ₜ[F] 1)).1 ∈ v.adicCompletionIntegers F ∧
      (φ (algebraMap (𝓞 E) E a ⊗ₜ[F] 1)).2 ∈ v.adicCompletionIntegers F := fun a =>
    ⟨map_mem v ((RingHom.fst _ _).comp ι) a, map_mem v ((RingHom.snd _ _).comp ι) a⟩
  intro x
  constructor
  · intro hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩
      · exact hι a
      · beta_reduce
        rw [hd]
        exact ⟨(hθ θ y).2 y.2, (hθ θ y).2 y.2⟩
    | zero => rw [map_zero]; exact ⟨zero_mem _, zero_mem _⟩
    | one => rw [map_one]; exact ⟨one_mem _, one_mem _⟩
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | neg x _ hx => rw [map_neg]; exact ⟨neg_mem hx.1, neg_mem hx.2⟩
    | mul x y _ _ hx hy => rw [map_mul]; exact ⟨mul_mem hx.1 hy.1, mul_mem hx.2 hy.2⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨P, hP, hPv⟩ := GlobalTheory.Mass.Genus.exists_over (E := E) v
    obtain ⟨w, t, ht, hwt⟩ := hc.cmUnram.2.2 P hP
    obtain ⟨s, hs⟩ := (hc.fixed (algebraMap (𝓞 E) E ((w - t) * (w - t)))).1 (by
      rw [map_mul, map_sub, ht, star_mul, star_sub, star_star]; ring)
    have hsi : IsIntegral ℤ s := by
      have := ((w - t) * (w - t)).isIntegral_coe
      rw [← hs] at this
      exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 this
    let s' : 𝓞 F := ⟨s, hsi⟩
    have hs' : algebraMap (𝓞 F) (𝓞 E) s' = (w - t) * (w - t) := RingOfIntegers.ext hs
    have hsv : s' ∉ v.asIdeal := fun h => by
      rw [← hPv, Ideal.mem_comap, hs'] at h
      exact hwt ((hP.isPrime.mem_or_mem h).elim id id)
    obtain ⟨u, hu⟩ := ((SelfDualGenus.isUnit_algebraMap_iff v s').2 hsv).exists_left_inv
    have hu' : (u : v.adicCompletion F) * algebraMap F (v.adicCompletion F) s = 1 :=
      congrArg Subtype.val hu
    obtain ⟨hα, hβ⟩ := hι w
    have e1 := hφ (algebraMap (𝓞 E) E w ⊗ₜ[F] 1)
    rw [conj_tmul, ← ht] at e1
    have e2 := hd (algebraMap F (v.adicCompletion F) s * 1)
    rw [← algebraMap_tmul, hs, mul_one, ← mul_one (1 : v.adicCompletion F), map_mul,
      ← Algebra.TensorProduct.tmul_mul_tmul, map_sub, TensorProduct.sub_tmul, map_mul, map_sub,
      e1] at e2
    generalize hW : φ (algebraMap (𝓞 E) E w ⊗ₜ[F] 1) = W at hα hβ e2
    obtain ⟨α, β⟩ := W
    have e3 : (α - β) * (α - β) = θ (algebraMap F (v.adicCompletion F) s) := congrArg Prod.fst e2
    have e4 : θ u * ((α - β) * (α - β)) = 1 := by rw [e3, ← map_mul, hu', map_one]
    have hθu : θ u ∈ v.adicCompletionIntegers F := (hθ θ u).2 u.2
    set c := ((φ x).1 - (φ x).2) * (θ u * (α - β)) with hcdef
    have hcm : c ∈ v.adicCompletionIntegers F :=
      mul_mem (sub_mem ha hb) (mul_mem hθu (sub_mem hα hβ))
    have hx : x = (1 : E) ⊗ₜ[F] θ.symm ((φ x).1 - c * α) +
        ((1 : E) ⊗ₜ[F] θ.symm c) * (algebraMap (𝓞 E) E w ⊗ₜ[F] 1) := by
      apply φ.injective
      rw [map_add (f := _), map_mul, hd, hd, hW, θ.apply_symm_apply, θ.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · change (φ x).1 = (φ x).1 - c * α + c * α
        ring
      · change (φ x).2 = (φ x).1 - c * α + c * β
        rw [hcdef]
        linear_combination ((φ x).1 - (φ x).2) * e4
    rw [hx]
    refine add_mem (Subring.subset_closure (Or.inr ⟨⟨_, hθ' _ (sub_mem ha (mul_mem hcm hα))⟩, rfl⟩))
      (mul_mem (Subring.subset_closure (Or.inr ⟨⟨_, hθ' _ hcm⟩, rfl⟩))
        (Subring.subset_closure (Or.inl ⟨⟨_, w, rfl⟩, rfl⟩)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedThetaVectorIsometryIsTheta
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.IsomTheta

theorem isTheta_eNat_comp : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → δ ≠ 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D B.tor x y) → S.IsTheta (fun z => B.eNat χ N N' L L' (e.symm z)) := by
  intro D cc δ B χ hcc hδ hχ h0 N N' L L' hA g S e hd hLa hH
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  have hmem := (B.vec_mem_ne hcc hδ h0 hS χ hχ N N' L L' hA).1
  have hQ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B N N' L L' hA
  simp only [Th, ThSp, Set.mem_setOf_eq] at hmem
  refine ⟨?_, ?_⟩
  · have hdiff : Differentiable ℂ (fun z => B.eNat χ N N' L L' (e.symm z)) :=
      hmem.1.comp e.symm.differentiable
    exact ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_differentiable hdiff
  · intro x hx
    have hx0 : e.symm x ∈ La D B.tor L L' := by
      rw [← hLa]; simpa using hx
    obtain ⟨m, hm⟩ := hQ _ hx0
    funext z
    have key := hmem.2 (e.symm x) hx0 (e.symm z)
    have h1 : JMB.hf S.Hm z x = Hf D B.tor (e.symm z) (e.symm x) := by
      simpa using hH (e.symm z) (e.symm x)
    have h2 : JMB.hf S.Hm x x = Hf D B.tor (e.symm x) (e.symm x) := by
      simpa using hH (e.symm x) (e.symm x)
    have hre : (JMB.beta S.d S.Hm x x).re = (m : ℝ) := by
      rw [JMB.beta, h2, hd, Complex.re_ofReal_mul]; exact hm
    have hal : al D B.tor (e.symm x) = (-1 : ℂ) ^ m := by
      rw [al, hm, round_intCast]
    have hph : Complex.exp ((Real.pi : ℂ) * Complex.I * (((JMB.beta S.d S.Hm x x).re : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
      rw [hre, show (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
        Complex.exp_int_mul, Complex.exp_pi_mul_I]
    show Complex.exp ((Real.pi : ℂ) * Complex.I * (((JMB.beta S.d S.Hm x x).re : ℝ) : ℂ)) *
        (B.eNat χ N N' L L' (e.symm (z + x)) *
          Complex.exp (-(Real.pi : ℂ) * JMB.hf S.Hm z x - (Real.pi : ℂ) / 2 * JMB.hf S.Hm x x)) =
      B.eNat χ N N' L L' (e.symm z)
    rw [← key, hph, ← hal, h1, h2, map_add (f := _)]
    unfold U
    ring_nf

end GlobalTheory.IsomTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbitStatement
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_vectors_same_length_one_unitary_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → Function.Injective (ratTup (F := F) (AF F) : (Fin 1 → Fin M → E) → _) ∧ ∀ y : Fin 1 → Fin M → AF F ⊗[F] E, (∃ x' : Fin 1 → Fin M → E, hE σ J (x' 0) (x' 0) = hE σ J (x 0) (x 0) ∧ ratTup (F := F) (AF F) x' = y) ↔ ∃ γ ∈ ratPts (AF F) σ J, γ • ratTup (F := F) (AF F) x = y := by
  first | exact @GlobalTheory.RatOrbit.rational_sphere_orbit | exact GlobalTheory.RatOrbit.rational_sphere_orbit | (intros; apply GlobalTheory.RatOrbit.rational_sphere_orbit <;> assumption)
end

