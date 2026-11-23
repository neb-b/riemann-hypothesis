module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0195
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0291
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBridge
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0854
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulScaleRoots
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.GalCut.AwayMono

open Polynomial

theorem charpoly_smul_scaleRoots {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {c : ℂ} (hc : c ≠ 0) : (c • f).charpoly = f.charpoly.scaleRoots c := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul,
    ← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]
  generalize LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f = M
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpTw (x : WD h) (s : ℝ) (g : Weil h) :
    (x.lpTw s).charPol g = (x.charPol g).scaleRoots (unrChar h (qPow w s) g : ℂ) := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTw, WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk, WDRep.twist_ρ,
    charpoly_smul_scaleRoots _ (Units.ne_zero _)]

theorem isGeneric_nu {x : IrrGL (k := w.adicCompletion E)} (hx : IsGeneric x.rep) (s : ℂ) : IsGeneric (x.nu s).rep :=
  (isGeneric_congr (IrrGL.twEquiv x _ _)).1 ((isGeneric_twist_iff _).2 hx)

end GlobalTheory.GalCut.AwayMono

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousDefiniteThetaIntegralVectorForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.ThetaIntegralCont

theorem continuous_theta_integral_vector : ∀ {D : D7} (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (V W : Formalism.BasicNotions.TH.HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
    IsWeilDatumO ψ V W χS χT om → (∀ τ, (gramAt D V τ).PosDef) →
    ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν →
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO V W → ℂ)),
    (∀ x, IsThetaFunO ψ V W (L x)) → ∀ u : GA D V → X, Continuous u → (∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) →
    Continuous (fun g => ∫ h in 𝓕, thetaKO om h g (L (u h)) ∂ν) := by
  intro D ψ V W χS χT om hom hV ν 𝓕 hν h𝓕 X _ _ _ L hL u hu hinv
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact V hV
  let b := Module.finBasis ℂ X
  have e : ∀ g h, thetaKO om h g (L (u h)) = ∑ k, b.coord k (u h) * om (h, g) (L (b k)) 0 := by
    intro g h
    conv_lhs => rw [← b.sum_repr (u h)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
  have hK : Continuous fun p : GA D W × GA D V => thetaKO om p.2 p.1 (L (u p.2)) := by
    simp only [e]
    refine continuous_finsetSum _ fun k _ => Continuous.mul ?_ ?_
    · exact (b.coord k).continuous_of_finiteDimensional.comp (hu.comp continuous_snd)
    · exact (hom.om_cont _ (hL (b k)) 0).comp (continuous_snd.prodMk continuous_fst)
  have hKinv : ∀ γ ∈ GQ V, ∀ g h, thetaKO om (γ * h) g (L (u (γ * h))) = thetaKO om h g (L (u h)) := by
    intro γ hγ g h
    have e : (γ * h, g) = ((γ, 1) : GA D V × GA D W) * (h, g) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [hinv γ hγ, e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hL _))
  exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ V) ν 𝓕 C h𝓕 hC hcov
    (fun g h => thetaKO om h g (L (u h))) hK hKinv

end GlobalTheory.ThetaIntegralCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformizerBlockEqDiagonalPowMulIntegralGL
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.DiagUnifFactor

theorem getD_pattern (k m i : ℕ) :
    (List.replicate k (1 : ℤ) ++ List.replicate m 0).getD i 0 = if i < k then 1 else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2 h2
  · simp [List.getElem?_replicate, h2]
  · simp at h1; omega
  · simp at h1; omega
  · simp [List.getElem?_replicate]
    split_ifs <;> rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ)
    (ϖ π : v.adicCompletion F), Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v π = WithZero.exp (-1 : ℤ) →
    ∃ T ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), Formalism.UG.diagJ n ϖ k =
      Matrix.diagonal (fun i : Fin n => π ^ ((List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0).getD i.1 0)) *
        (T : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  intro F _ _ v n k ϖ π hϖ hπ
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπ; exact WithZero.zero_ne_coe hπ
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hu : Valued.v (ϖ / π) = 1 := by
    rw [map_div₀, hϖ, hπ, div_self (WithZero.coe_ne_zero)]
  have hu' : Valued.v (π / ϖ) = 1 := by
    rw [map_div₀, hϖ, hπ, div_self (WithZero.coe_ne_zero)]
  let d : Fin n → v.adicCompletion F := fun i => if (i : ℕ) < k then ϖ / π else 1
  let d' : Fin n → v.adicCompletion F := fun i => if (i : ℕ) < k then π / ϖ else 1
  have hdd' : Matrix.diagonal d * Matrix.diagonal d' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; simp only [d, d']
    split_ifs
    · rw [div_mul_div_comm, mul_comm ϖ π, div_self (mul_ne_zero hπ0 hϖ0)]
    · exact one_mul 1
  have hd'd : Matrix.diagonal d' * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; simp only [d, d']
    split_ifs
    · rw [div_mul_div_comm, mul_comm π ϖ, div_self (mul_ne_zero hϖ0 hπ0)]
    · exact one_mul 1
  let T : GL (Fin n) (v.adicCompletion F) := ⟨Matrix.diagonal d, Matrix.diagonal d', hdd', hd'd⟩
  have hmem : ∀ (e : Fin n → v.adicCompletion F), (∀ i, Valued.v (e i) ≤ 1) →
      ∀ a b, Matrix.diagonal e a b ∈ Formalism.UG.Ov F v := by
    intro e he a b
    show Matrix.diagonal e a b ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hab : a = b
    · subst hab; rw [Matrix.diagonal_apply_eq]; exact he a
    · rw [Matrix.diagonal_apply_ne _ hab, map_zero]; exact zero_le'
  have hle : ∀ (x : v.adicCompletion F), Valued.v x = 1 → ∀ i : Fin n,
      Valued.v (if (i : ℕ) < k then x else 1) ≤ 1 := by
    intro x hx i; split_ifs
    · exact hx.le
    · rw [map_one]
  refine ⟨T, ?_, ?_⟩
  · have inj : Function.Injective ((Formalism.UG.Ov F v).subtype.mapMatrix (m := Fin n)) :=
      fun A B h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
    let A : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v) := fun i j => ⟨Matrix.diagonal d i j, hmem d (hle _ hu) i j⟩
    let B : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v) := fun i j => ⟨Matrix.diagonal d' i j, hmem d' (hle _ hu') i j⟩
    have hA : (Formalism.UG.Ov F v).subtype.mapMatrix A = Matrix.diagonal d := rfl
    have hB : (Formalism.UG.Ov F v).subtype.mapMatrix B = Matrix.diagonal d' := rfl
    refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
    · rw [map_mul, hA, hB, map_one, hdd']
    · rw [map_mul, hA, hB, map_one, hd'd]
  · show Matrix.diagonal _ = _ * Matrix.diagonal d
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [getD_pattern]
    simp only [d]
    split_ifs
    · rw [zpow_one, mul_div_cancel₀ _ hπ0]
    · rw [zpow_zero, one_mul]

end GlobalTheory.DiagUnifFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSectionSplitPlaceComponentMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.SplitComp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_integralSection_splitPlace_componentMap_cast {E : Type} [Field E] [NumberField E] [IsCMField E] (F1 : Subfield E)
    (hF : F1 = maximalRealSubfield E) (sp : SplitPlace E) :
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield E) → FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E,
      (∀ t, sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield E),
        sec t ∈ AddSubgroup.closure {y | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F1, ∃ x : 𝓞 E, y = a ⊗ₜ[F1] (x : E)}) ∧
      (∀ x ∈ AddSubgroup.closure {y | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F1, ∃ x : 𝓞 E, y = a ⊗ₜ[F1] (x : E)},
        sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield E)) ∧
      ∀ x : E, sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x)) = sp.i x := by
  classical
  subst hF
  have hc : ∀ (a : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (x : E),
      Formalism.IndefR.principalLevelFrame.tensCastR (rfl : maximalRealSubfield E = maximalRealSubfield E)
        (a ⊗ₜ[maximalRealSubfield E] x) = x ⊗ₜ[maximalRealSubfield E] a := fun a x => rfl
  have hp : ∀ (a : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (x : E),
      sp.proj (x ⊗ₜ[maximalRealSubfield E] a) = sp.i x * a sp.v := fun a x => rfl
  refine ⟨fun t => singleV (maximalRealSubfield E) sp.v t ⊗ₜ[maximalRealSubfield E] (1 : E), ?_, ?_, ?_, ?_⟩
  · intro t
    rw [hc, hp, map_one, one_mul]
    exact RestrictedProduct.single_eq_same _ _ _
  · intro t ht
    apply AddSubgroup.subset_closure
    refine ⟨singleV (maximalRealSubfield E) sp.v t, ?_, 1, by simp⟩
    intro w
    show (singleV (maximalRealSubfield E) sp.v t) w ∈ _
    by_cases h : w = sp.v
    · subst h
      have e : (singleV (maximalRealSubfield E) sp.v t) sp.v = t := RestrictedProduct.single_eq_same _ _ _
      rw [e]
      exact ht
    · have e : (singleV (maximalRealSubfield E) sp.v t) w = 0 := RestrictedProduct.single_eq_of_ne _ _ h
      rw [e]
      exact zero_mem _
  · intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, z, rfl⟩ := hy
      rw [hc, hp]
      refine mul_mem ?_ (ha sp.v)
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (sp.split_le_one z)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem hy hz
    | neg y _ hy =>
      rw [map_neg, map_neg]
      exact neg_mem hy
  · intro x
    rw [hc, hp]
    show sp.i x * 1 = sp.i x
    exact mul_one _

theorem proj_tensCast_section : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E),
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) ∧
      (∀ x ∈ Formalism.L2.Theta.intAE D,
        sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) ∧
      ∀ x : D.host.E, sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x))) = sp.i x := by
  intro D sp hF
  obtain ⟨sec, h1, h2, h3, h4⟩ := exists_integralSection_splitPlace_componentMap_cast D.host.F hF sp
  refine ⟨sec, h1, h2, h3, fun x => ?_⟩
  have e : Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := by
    simp [Formalism.L2.Theta.finPart, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
  rw [e]
  exact h4 x

end GlobalTheory.SplitComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsModelOfMem
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst

noncomputable section

namespace GlobalTheory.AboveLRes

theorem exists_model_of_mem {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ} (T : FinExt l)
    (ρ : Γ →* GL (Fin a) (Om l))
    (hρ : ∀ g i k, ((ρ g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ T.1) :
    ∃ ρ' : Γ →* GL (Fin a) ↥T.1, mapRep (algebraMap ↥T.1 (Om l)) ρ' = ρ := by
  let f : GL (Fin a) ↥T.1 →* GL (Fin a) (Om l) := Units.map ((algebraMap ↥T.1 (Om l)).mapMatrix : Matrix (Fin a) (Fin a) ↥T.1 →+* Matrix (Fin a) (Fin a) (Om l)).toMonoidHom
  have hmi : Function.Injective ((algebraMap ↥T.1 (Om l)).mapMatrix : Matrix (Fin a) (Fin a) ↥T.1 → _) :=
    Matrix.map_injective (algebraMap ↥T.1 (Om l)).injective
  have hf : Function.Injective f := Units.map_injective hmi
  let lift : Γ → Matrix (Fin a) (Fin a) ↥T.1 := fun g => Matrix.of fun i k => ⟨_, hρ g i k⟩
  have hlift : ∀ g, (algebraMap ↥T.1 (Om l)).mapMatrix (lift g) = ((ρ g : GL (Fin a) (Om l)) : Matrix _ _ _) :=
    fun g => by ext i k; rfl
  have hm : ∀ g, ρ g ∈ f.range := by
    intro g
    refine ⟨⟨lift g, lift g⁻¹, hmi ?_, hmi ?_⟩, Units.ext (hlift g)⟩
    · rw [map_mul, hlift, hlift, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    · rw [map_mul, hlift, hlift, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  refine ⟨(MonoidHom.ofInjective hf).symm.toMonoidHom.comp (ρ.codRestrict f.range hm), ?_⟩
  exact MonoidHom.ext fun g => MonoidHom.apply_ofInjective_symm hf ⟨ρ g, hm g⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes

theorem exists_decRes_eq {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L]
    [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] {A : ValuationSubring Ω} (σ : ↥(Dec (F := K) A))
    (hσ : ∀ x : L, (σ : G K Ω) (algebraMap L Ω x) = algebraMap L Ω x) :
    ∃ σ' : ↥(Dec (F := L) A), decRes A σ' = σ := by
  let τ : G L Ω := { (σ : G K Ω).toRingEquiv with commutes' := hσ }
  have hτ : τ ∈ Dec (F := L) A := by
    have hg := mem_Dec.mp σ.2
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    conv_rhs => rw [← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  exact ⟨⟨τ, hτ⟩, Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes


open GlobalTheory.AboveL in
theorem exists_model_dec {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) {l : ℕ}
    [Fact l.Prime] {a : ℕ} (r : G K Ω →* GL (Fin a) (Om l)) (LL' B : FinExt l)
    (r' : ↥(Dec (F := L) A) →* GL (Fin a) ↥LL'.1)
    (hm' : mapRep (algebraMap ↥LL'.1 (Om l)) r' = (resTo L r).comp (Dec (F := L) A).subtype) :
    ∃ (T : FinExt l) (r₁ : ↥(Dec (F := K) A) →* GL (Fin a) ↥T.1), B.1 ≤ T.1 ∧
      mapRep (algebraMap ↥T.1 (Om l)) r₁ = r.comp (Dec (F := K) A).subtype := by
  let M : IntermediateField K Ω := (IsScalarTower.toAlgHom K L Ω).fieldRange
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : FiniteDimensional K M :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L Ω)).toLinearEquiv.finiteDimensional
  haveI : Finite (G K Ω ⧸ M.fixingSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.fixingSubgroup_isOpen
  haveI : M.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set H : Subgroup ↥(Dec (F := K) A) := M.fixingSubgroup.subgroupOf (Dec (F := K) A) with hH
  haveI : Finite (↥(Dec (F := K) A) ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  set S : Set (Om l) := Set.range fun x : (↥(Dec (F := K) A) ⧸ H) × Fin a × Fin a =>
    ((r (x.1.out : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) x.2.1 x.2.2 with hS
  have hSf : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  obtain ⟨T, hT⟩ : ∃ T : FinExt l, T.1 = IntermediateField.adjoin ℚ_[l] S ⊔ LL'.1 ⊔ B.1 :=
    ⟨supExt (supExt ⟨_, hSf⟩ LL') B, rfl⟩
  have hET : IntermediateField.adjoin ℚ_[l] S ≤ T.1 := hT ▸ le_sup_left.trans le_sup_left
  have hLT : LL'.1 ≤ T.1 := hT ▸ le_sup_right.trans le_sup_left
  have hBT : B.1 ≤ T.1 := hT ▸ le_sup_right
  have hfix : ∀ σ : ↥(Dec (F := K) A), σ ∈ H → ∀ i k,
      ((r (σ : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ LL'.1 := by
    intro σ hσ i k
    have hσ' : ∀ x : L, (σ : G K Ω) (algebraMap L Ω x) = algebraMap L Ω x := fun x =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_subgroupOf.1 hσ) _ ⟨x, rfl⟩
    obtain ⟨τ, hτ⟩ := exists_decRes_eq σ hσ'
    have e1 : (r (σ : G K Ω)) = ((resTo L r).comp (Dec (F := L) A).subtype) τ := by
      rw [← hτ]; rfl
    rw [e1, ← hm']
    exact ((r' τ : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1) i k |>.2
  have hent : ∀ (g : ↥(Dec (F := K) A)) i k,
      (((r.comp (Dec (F := K) A).subtype) g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ T.1 := by
    intro g i k
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    have hg : g = (QuotientGroup.mk g : ↥(Dec (F := K) A) ⧸ H).out * ((h⁻¹ : H) : ↥(Dec (F := K) A)) := by
      rw [hh, Subgroup.coe_inv, mul_inv_cancel_right]
    rw [MonoidHom.comp_apply, hg, map_mul, map_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun m _ => mul_mem (hET (IntermediateField.subset_adjoin _ _ ⟨⟨_, i, m⟩, rfl⟩)) ?_
    exact hLT (hfix _ (h⁻¹).2 m k)
  obtain ⟨r₁, hr₁⟩ := exists_model_of_mem T _ hent
  exact ⟨T, r₁, hBT, hr₁⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes


open GlobalTheory.AboveL in
theorem isPstAt_of_resTo : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : G K Ω →* GL (Fin a) (Om l)), Continuous r → ∀ (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → IsPstAt P Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) → IsPstAt P Bw (r.comp (Dec (F := K) A).subtype) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A l _ P AI hT a r hr O O' _ _ _ _ _ _ Bw Bw' hj hj' hL
  have hcL : Continuous fun g : ↥(Dec (F := L) A) =>
      ((((resTo L r).comp (Dec (F := L) A).subtype) g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) :=
    Units.continuous_val.comp ((hr.comp (UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω)).comp continuous_subtype_val)
  obtain ⟨LL', r', hm', hV'⟩ := hL
  obtain ⟨T, r₁, hBT, hr₁⟩ := exists_model_dec A r LL' Bw.LL r' hm'.2

  obtain ⟨S'', Bw'', hjj, hTS, hle⟩ := exists_bridge (L := L) Bw hj T
  have hj'' : GlobalTheory.Pst.Induces Bw'' := fun x => by rw [hjj]; exact hj x
  obtain ⟨LL₃, r₃, hm₃, hV₃⟩ := GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge l P AI hT L Ω A O' _ Bw' Bw'' hj' hj'' a _
    hcL ⟨LL', r', hm', hV'⟩
  have h1 : Bw''.LL.1 ≤ (supExt Bw''.LL LL₃).1 := le_sup_left
  have h3 : LL₃.1 ≤ (supExt Bw''.LL LL₃).1 := le_sup_right
  have hTT : T.1 ≤ (supExt Bw''.LL LL₃).1 := hTS.trans h1
  have hr₁' : mapRep (algebraMap ↥(supExt Bw''.LL LL₃).1 (Om l))
      (mapRep (IntermediateField.inclusion hTT).toRingHom r₁) = r.comp (Dec (F := K) A).subtype := by
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := K) A) →* GL (Fin a) (Om l) =>
      ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hmL : IsModel Bw'' ((resTo L r).comp (Dec (F := L) A).subtype) (supExt Bw''.LL LL₃)
      ((mapRep (IntermediateField.inclusion hTT).toRingHom r₁).comp (decRes A)) := by
    refine ⟨h1, ?_⟩
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := K) A) →* GL (Fin a) (Om l) =>
      ((f (decRes A g) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁'
  have hm₃' : IsModel Bw'' ((resTo L r).comp (Dec (F := L) A).subtype) (supExt Bw''.LL LL₃)
      (mapRep (IntermediateField.inclusion h3).toRingHom r₃) := by
    refine ⟨hm₃.1.trans h3, ?_⟩
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := L) A) →* GL (Fin a) (Om l) =>
      ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hm₃.2
  have heq := IsModel.unique Bw'' _ hm₃' hmL
  have hp := GlobalTheory.PstExt.isPst_enlarge P Bw'' h3 r₃ hV₃
  rw [heq, repE_decRes Bw Bw'' hjj hle] at hp
  exact ⟨_, _, ⟨hBT.trans hTT, hr₁'⟩, (GlobalTheory.PstLaws.isPst_resTo_iff P _ hle).1 hp⟩

end GlobalTheory.AboveLRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnramOfFixedIwahori
section
open GlobalTheory.LocGL GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RoadU

namespace GlobalTheory.IwahoriSupport

theorem hasSupport_chars {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) k) V} (hi : ρ.IsIrreducible) (χ : Fin n → kˣ →* ℂˣ)
    (hχ : ∀ i, IsSmoothChar (χ i)) (h : GlobalTheory.SmGL.IsSubquotient ρ (prinSeries χ)) :
    HasSupport ρ (chars χ hχ) := by
  have H : GlobalTheory.SmGL.IsCuspSupport ρ (fun _ : Fin n => 1) fun a => detRep (Fin 1) (χ a) :=
    ⟨hi, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hχ a)⟩, _,
      h.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ)⟩
  exact hasSupport_of_isCuspSupport H

end GlobalTheory.IwahoriSupport
end

