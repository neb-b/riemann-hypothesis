module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0509
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0586
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairLocalAuxiliaryStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0547
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0621
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiagonalDoubleCosets
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0441
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalSwapConvolution
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0623
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIndicatorIntegralIndex
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HintInd

theorem finsum_out_indicator {A : Type} [AddCommGroup A] (S Λ : AddSubgroup A) (hSΛ : S ≤ Λ)
    (K : Subgroup (Multiplicative A)) (hK : ∀ X, X ∈ K ↔ Multiplicative.toAdd X ∈ S) :
    ∑ᶠ q : Multiplicative A ⧸ K, (if Multiplicative.toAdd q.out ∈ Λ then (1 : ℂ) else 0) =
      ((S.relIndex Λ : ℕ) : ℂ) := by
  have hrep : ∀ x : Multiplicative A,
      Multiplicative.toAdd ((x : Multiplicative A ⧸ K).out) ∈ Λ ↔ Multiplicative.toAdd x ∈ Λ := by
    intro x
    have h1 : ((x : Multiplicative A ⧸ K).out)⁻¹ * x ∈ K :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (x : Multiplicative A ⧸ K))
    have h2 : -Multiplicative.toAdd ((x : Multiplicative A ⧸ K).out) + Multiplicative.toAdd x ∈ Λ :=
      hSΛ ((hK _).1 h1)
    constructor
    · intro h
      have := Λ.add_mem h h2
      simpa using this
    · intro h
      have := Λ.add_mem h (Λ.neg_mem h2)
      simpa using this
  let T : Set (Multiplicative A ⧸ K) := {q | Multiplicative.toAdd q.out ∈ Λ}
  have hsame : ∀ x y : Multiplicative A, (x : Multiplicative A ⧸ K) = y ↔
      -Multiplicative.toAdd x + Multiplicative.toAdd y ∈ S := by
    intro x y
    rw [QuotientGroup.eq, hK]
    rfl
  let f : Λ → T := fun x => ⟨((Multiplicative.ofAdd (x : A) : Multiplicative A) : Multiplicative A ⧸ K),
    (hrep _).2 x.2⟩
  let g : Λ ⧸ S.addSubgroupOf Λ → T := fun y => Quotient.liftOn' y f (by
    intro x y hxy
    have h : -(x : A) + (y : A) ∈ S := by
      have := QuotientAddGroup.leftRel_apply.1 hxy
      simpa [AddSubgroup.mem_addSubgroupOf] using this
    exact Subtype.ext ((hsame _ _).2 h))
  have hg : Function.Bijective g := by
    constructor
    · intro y₁ y₂
      induction y₁ using QuotientAddGroup.induction_on with | H x =>
      induction y₂ using QuotientAddGroup.induction_on with | H y =>
      intro h
      have h' : ((Multiplicative.ofAdd (x : A) : Multiplicative A) : Multiplicative A ⧸ K) =
          ((Multiplicative.ofAdd (y : A) : Multiplicative A) : Multiplicative A ⧸ K) :=
        congrArg Subtype.val h
      refine QuotientAddGroup.eq.2 ?_
      rw [AddSubgroup.mem_addSubgroupOf]
      simpa using (hsame _ _).1 h'
    · rintro ⟨q, hq⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨((⟨Multiplicative.toAdd x, (hrep x).1 hq⟩ : Λ) : Λ ⧸ S.addSubgroupOf Λ), rfl⟩
  have hcard : Nat.card T = S.relIndex Λ := (Nat.card_congr (Equiv.ofBijective g hg)).symm
  have hfun : (fun q : Multiplicative A ⧸ K => if Multiplicative.toAdd q.out ∈ Λ then (1 : ℂ) else 0) =
      T.indicator 1 := by
    funext q
    by_cases h : q ∈ T
    · rw [Set.indicator_of_mem h]; exact if_pos h
    · rw [Set.indicator_of_notMem h]; exact if_neg h
  rw [hfun, ← hcard]
  by_cases hT : T.Finite
  · rw [← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hT, Nat.card_coe_set_eq,
      Set.ncard_eq_toFinset_card T hT]
    simp
  · rw [finsum_of_infinite_support (by simpa using hT)]
    haveI : Infinite T := Set.Infinite.to_subtype hT
    simp

theorem mem_intMat_iff {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    X ∈ intMat a b w ↔ Multiplicative.toAdd X ∈ intSub a b w := by
  constructor
  · intro hX
    induction hX using Subgroup.closure_induction with
    | mem x hx => exact fun i j => hx i j
    | one => exact isInt_zero w _ _
    | mul x y _ _ hx hy => exact IsInt.add hx hy
    | inv x _ hx => exact IsInt.neg hx
  · intro hX
    exact Subgroup.subset_closure fun i j => hX i j

theorem hint_indicator_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (Λ : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E))), intSub a b w ≤ Λ → hint (intMat a b w) (fun X => if Multiplicative.toAdd X ∈ Λ then (1 : ℂ) else 0) = (((intSub a b w).relIndex Λ : ℕ) : ℂ) := by
  intro E _ _ _ a b w Λ h
  have hstab : intMat a b w ≤
      rStab (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        if Multiplicative.toAdd X ∈ Λ then (1 : ℂ) else 0) := by
    intro k hk x
    have hkΛ : Multiplicative.toAdd k ∈ Λ := h ((mem_intMat_iff a b w k).1 hk)
    have e : (Multiplicative.toAdd (x * k) ∈ Λ) ↔ Multiplicative.toAdd x ∈ Λ := by
      rw [toAdd_mul]
      exact Λ.add_mem_cancel_right hkΛ
    simp only [e]
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (intMat a b w) (intMat a b w) _ le_rfl hstab
    (by simp [Subgroup.relIndex_self])]
  rw [Subgroup.relIndex_self]
  simp only [Nat.cast_one, inv_one, one_mul]
  exact finsum_out_indicator (intSub a b w) Λ h (intMat a b w) (mem_intMat_iff a b w)

end GlobalTheory.CompanionTheory.HintInd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieDerivativeConvolutionKernel
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

noncomputable section

namespace GlobalTheory.CompanionTheory.LieConv

theorem mMap_surjective (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Function.Surjective (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a) := fun X =>
  ⟨(fun i j => ((0, fun w => X i j w.1) : mixedEmbedding.mixedSpace E) :
    Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)), rfl⟩

theorem exists_kernel_basis (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
    (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ : Sm E a) (hφ : IsAutForm φ)
    (j : Fin (CuspidalSpectrum.archDim E a)) :
    ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : GA E a,
      (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a (CuspidalSpectrum.archBasis E a j)) φ).1 g =
        ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂ν := by
  obtain ⟨D, hD, hDc, h⟩ := GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv E a φ (GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ) hφ ν 1
    (fun _ => j)
  refine ⟨D, hD, hDc, fun g => ?_⟩
  rw [← h g, CuspidalSpectrum.uAction_uJ_succ]
  have e := GlobalTheory.CompanionTheory.HCRep.smL_liB (E := E) (a := a) (CuspidalSpectrum.lieOf (CuspidalSpectrum.archBasis E a j)) φ
  have e2 := congrArg (fun ψ : AutomorphicForm.archSmooth E a => ψ.1 g) e
  have e0 : ∀ ψ : AutomorphicForm.archSmooth E a,
      AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := E) (n := a) 0 (Fin.tail fun _ => j)) ψ = ψ := fun ψ => by
    rw [CuspidalSpectrum.uJ, map_one]
    rfl
  rw [e0]
  exact e2

theorem hasCompactSupport_sum {G ι : Type*} [TopologicalSpace G] (s : Finset ι) (c : ι → ℂ) (D : ι → G → ℂ)
    (h : ∀ j, HasCompactSupport (D j)) : HasCompactSupport fun y => ∑ j ∈ s, c j * D j y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact ((h j).mul_left (f := fun _ => c j)).add ih

theorem lie_eq_conv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ : Sm E a), IsAutForm φ → ∀ X : Lie E a, ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : GA E a, (lie E a X φ).1 g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂ν := by
  intro E _ _ _ a _ _ ν _ φ hφ X
  obtain ⟨Y, rfl⟩ := mMap_surjective E a X
  choose D hD hDc hconv using exists_kernel_basis E a ν φ hφ
  set b := CuspidalSpectrum.archBasis E a with hb
  set c : Fin (CuspidalSpectrum.archDim E a) → ℂ := fun j => ((b.repr Y j : ℝ) : ℂ) with hc
  refine ⟨fun y => ∑ j, c j * D j y, continuous_finsetSum _ fun j _ => continuous_const.mul (hD j),
    hasCompactSupport_sum _ c D hDc, fun g => ?_⟩
  have hf : Continuous fun y => φ.1 (g * AutomorphicForm.infEmb E a y) :=
    IsExpLieAlgebra.continuous_of_isSmoothFun (GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ g)
  have hint : ∀ j, Integrable (fun y => φ.1 (g * AutomorphicForm.infEmb E a y) * D j y) ν := fun j =>
    (hf.mul (hD j)).integrable_of_hasCompactSupport ((hDc j).mul_left)
  have hY : (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a Y) φ).1 g =
      ∑ j, c j * (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a (b j)) φ).1 g := by
    conv_lhs => rw [← b.sum_repr Y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply,
      Complex.real_smul, hc]
  rw [hY]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hconv j g, ← integral_const_mul]
    congr 1
    funext y
    ring
  · exact ((hint j).const_mul (c j)).congr (Filter.Eventually.of_forall fun y => by ring)

end GlobalTheory.CompanionTheory.LieConv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonSplit
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses

namespace GlobalTheory.CompanionTheory.LcSplit

theorem level_pick {H : Type} [Group H] [TopologicalSpace H] (σ : H →* H) (hc : Continuous σ) (hi : ∀ g, σ (σ g) = g)
    (K A₁ A₂ : Subgroup H) (f₁ f₂ : H → ℂ) (ho₁ : IsOpen (A₁ : Set H)) (ho₂ : IsOpen (A₂ : Set H)) (hK : A₁ ≤ K)
    (h₁ : IsHecke A₁ f₁) (h₂ : IsHecke A₂ f₂) :
    ∃ L : Subgroup H, IsOpen (L : Set H) ∧ L ≤ K ∧ (∀ k ∈ L, σ k ∈ L) ∧ IsHecke L f₁ ∧ IsHecke L f₂ := by
  have hAo : IsOpen ((A₁ ⊓ A₂ : Subgroup H) : Set H) := by
    rw [Subgroup.coe_inf]; exact ho₁.inter ho₂
  refine ⟨(A₁ ⊓ A₂) ⊓ (A₁ ⊓ A₂).comap σ, ?_, fun x hx => hK hx.1.1, fun k hk => ⟨hk.2, ?_⟩,
    ⟨h₁.1, fun k hk => h₁.2 k hk.1.1⟩, ⟨h₂.1, fun k hk => h₂.2 k hk.1.2⟩⟩
  · rw [Subgroup.coe_inf]
    exact hAo.inter (hAo.preimage hc)
  · show σ (σ k) ∈ A₁ ⊓ A₂
    rw [hi]; exact hk.1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_level (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (hφ₁ : IsTestP φ₁) (hφ₂ : IsTestP φ₂) (w : Pl E) :
    ∃ L : Subgroup (GLw a w × GLw b w), IsOpen (L : Set (GLw a w × GLw b w)) ∧ L ≤ K2 a b w ∧ (∀ k ∈ L, sgP a b w k ∈ L) ∧
      IsHecke L (φ₁ w) ∧ IsHecke L (φ₂ w) := by
  obtain ⟨hc, hi, hk⟩ := sgP_facts E a b w
  obtain ⟨K₁, K₂, hl₁, hl₂, ht⟩ := hφ₁
  obtain ⟨K₁', K₂', hl₁', hl₂', ht'⟩ := hφ₂
  refine level_pick (sgP a b w) hc hi (K2 a b w) ((K₁ w).prod (K₂ w)) ((K₁' w).prod (K₂' w)) _ _ ?_ ?_ ?_ (ht.1 w) (ht'.1 w)
  · rw [Subgroup.coe_prod]; exact (hl₁.1 w).1.prod (hl₂.1 w).1
  · rw [Subgroup.coe_prod]; exact (hl₁'.1 w).1.prod (hl₂'.1 w).1
  · exact Subgroup.prod_mono (hl₁.1 w).2.1 (hl₂.1 w).2.1

theorem fv_split (S : Set (Pl E)) (hS : IsSection S) (w : Pl E) (hw : w ∈ S) (hs : IsSplitAt w)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    fv S φ₁ φ₂ _ y = φ₁ w (evw ⟨w, rfl⟩ y) * φ₂ w (evw ⟨w, rfl⟩ (thv a b _ y)) := by
  unfold fv
  have key : ∀ u : Above (w.under (𝓞 (maximalRealSubfield E))), u.1 ∈ S → u = ⟨w, rfl⟩ := by
    intro u hu
    exact Subtype.ext ((hS w).unique ⟨hu, u.2⟩ ⟨hw, rfl⟩)
  rw [finprod_eq_single _ (⟨w, rfl⟩ : Above (w.under (𝓞 (maximalRealSubfield E))))]
  · rw [finprod_eq_if, if_pos hw, if_pos hs]
  · intro u hu
    rw [finprod_eq_if, if_neg (fun h => hu (key u h))]

theorem th_split (a b : ℕ) (w : Pl E) (hs : IsSplitAt w) :
    (thL a w).prodMap (thL b w) = MonoidHom.id (GLw a w × GLw b w) := by
  unfold thL
  rw [if_pos hs, if_pos hs]
  ext x <;> rfl

theorem seen_split (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (w : Pl E) (hs : IsSplitAt w) :
    seen φ₁ φ₂ w = fun y => hint (K2 a b w) fun z => φ₁ w z * φ₂ w (z⁻¹ * y) := by
  funext y
  unfold seen
  rw [if_pos hs]

theorem locEl_sep {n : ℕ} (w : Pl E) (hs : IsSplitAt w) (δ : GL (Fin n) E) (h : polE δ ∈ Ell E n) :
    (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  have : (nrmL n w (locEl n w δ)).val.charpoly = (polE δ).map (algebraMap E (w.adicCompletion E)) := by
    unfold nrmL locEl polE
    rw [if_pos hs, if_pos hs]
    exact Matrix.charpoly_map _ _
  rw [this]
  exact h.2.2.1.map

theorem target_side (hU : GlobalTheory.BCT.Unr E) (w : Pl E) (hs : IsSplitAt w)
    (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (hδ₁ : polE δ₁ ∈ Ell E a) (hδ₂ : polE δ₂ ∈ Ell E b) :
    Good (MonoidHom.id _) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) ∧
    ∀ C : Set (GLw a w × GLw b w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (GLw a w × GLw b w)) (locEl a w δ₁, locEl b w δ₂) : Set _)
      (K2 (E := E) a b w : Set (GLw a w × GLw b w)) | ∃ k ∈ K2 (E := E) a b w,
        (Quotient.out q * k)⁻¹ * (locEl a w δ₁, locEl b w δ₂) * MonoidHom.id (GLw a w × GLw b w) (Quotient.out q * k) ∈ C}.Finite := by
  have h1 := GlobalTheory.CompanionTheory.LocGoodProof.locGood E hU a b w (locEl a w δ₁, locEl b w δ₂) (locEl_sep w hs δ₁ hδ₁) (locEl_sep w hs δ₂ hδ₂)
  have h2 := (GlobalTheory.CompanionTheory.TwistOrbit.locSupp E hU a b w (locEl a w δ₁, locEl b w δ₂) (locEl_sep w hs δ₁ hδ₁) (locEl_sep w hs δ₂ hδ₂)).1
  rw [th_split a b w hs] at h1 h2
  exact ⟨h1, h2⟩

theorem pair_integral_points_open_compact (a b : ℕ) (w : Pl E) :
    IsOpen ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) ∧ IsCompact ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
  obtain ⟨hKo₁, hKc₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨hKo₂, hKc₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  rw [Subgroup.coe_prod]
  exact ⟨hKo₁.prod hKo₂, hKc₁.prod hKc₂⟩

theorem locCompareSplit : LocCompareSplit := by
  intro hCj E _ _ _ hU a b S hS φ₁ φ₂ hφ₁ hφ₂ δ₁ δ₂ hδ₁ hδ₂ w hw hs
  obtain ⟨e, he1, he3, he4, heδ⟩ := GlobalTheory.CompanionTheory.SplitIso.split_iso hCj E a b _ ⟨w, rfl⟩ hs
  obtain ⟨hc, hi, hk⟩ := sgP_facts E a b w
  obtain ⟨L, hLo, hLK, hLs, hH₁, hH₂⟩ := exists_level φ₁ φ₂ hφ₁ hφ₂ w
  obtain ⟨hKo, hKc⟩ := pair_integral_points_open_compact (E := E) a b w
  obtain ⟨hG, hF⟩ := target_side hU w hs δ₁ δ₂ hδ₁ hδ₂
  set y := pv a b (w.under (𝓞 (maximalRealSubfield E))) (ratF E a δ₁, ratF E b δ₂) with hy
  have hN : (e y).1 * sgP a b w (e y).2 = (locEl a w δ₁, locEl b w δ₂) := by
    rw [hy, heδ]
    exact Prod.ext (GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL E a w δ₁ hs) (GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL E b w δ₂ hs)
  have ht := GlobalTheory.EulerTw.Transport.twOrb_transport _ _ e (thv a b _) (swTw (sgP a b w))
    (Kv a b _) ((K2 a b w).prod (K2 a b w)) y (fv S φ₁ φ₂ _) (fun z => φ₁ w z.1 * φ₂ w (sgP a b w z.2))
    he3 he4 (fun g => by
      have h2 : evw ⟨w, rfl⟩ (thv a b _ g) = sgP a b w (e g).2 := by
        rw [← he1, he3]; rfl
      show φ₁ w (e g).1 * φ₂ w (sgP a b w (e g).2) = _
      rw [he1, ← h2, fv_split S hS w hw hs])
  rw [ht, seen_split φ₁ φ₂ w hs, th_split a b w hs]
  have hsc := _root_.GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite _ (sgP a b w) (K2 a b w) hc hi hk hKo hKc (e y).1 (e y).2 (φ₁ w) (φ₂ w) L hLo hLK hLs hH₁ hH₂
    (by rw [hN]; exact hG) (by rw [hN]; exact hF)
  rw [hN] at hsc
  exact hsc

end GlobalTheory.CompanionTheory.LcSplit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionary
section
noncomputable section

namespace GlobalTheory.CompanionTheory.EisDict

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open PositivityTheory.RgEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def sec : (Af F ⊗[F] E) →+ AE F E :=
  (TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) (LinearMap.id : E →ₗ[F] E)).toAddMonoidHom

theorem sec_tmul (a : Af F) (x : E) : sec F E (a ⊗ₜ[F] x) = ((0, a) : AF F) ⊗ₜ[F] x := rfl

theorem sec_finPart (z : AE F E) : sec F E (HeckeCharacterZeroLocus.ThmBIn.finPart F E z) = finOne F • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | tmul a x =>
    change sec F E (HeckeCharacterZeroLocus.ThmBIn.sndA F a ⊗ₜ[F] x) = _
    rw [sec_tmul, TensorProduct.smul_tmul']
    congr 1
    refine Prod.ext ?_ ?_
    · change (0 : Ainf F) = 0 * a.1
      simp
    · change a.2 = 1 * a.2
      simp

theorem finPart_finOne_smul (z : AE F E) :
    HeckeCharacterZeroLocus.ThmBIn.finPart F E (finOne F • z) = HeckeCharacterZeroLocus.ThmBIn.finPart F E z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x =>
    rw [TensorProduct.smul_tmul']
    change HeckeCharacterZeroLocus.ThmBIn.sndA F (finOne F • a) ⊗ₜ[F] x = HeckeCharacterZeroLocus.ThmBIn.sndA F a ⊗ₜ[F] x
    congr 1
    change 1 * a.2 = a.2
    simp

theorem sec_mem {y : Af F ⊗[F] E} (hy : y ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) : sec F E y ∈ intHat F E := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    refine AddSubgroup.subset_closure ⟨(0, a), ?_, fun v => ha v, x, ?_⟩
    · exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    · rw [sec_tmul]
      change _ = pairA F 0 a • ((1 : AF F) ⊗ₜ[F] (x : E))
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
  | zero => simpa using (intHat F E).zero_mem
  | add x y _ _ hx hy => simpa using (intHat F E).add_mem hx hy
  | neg x _ hx => simpa using (intHat F E).neg_mem hx

theorem finPart_mem {z : AE F E} (hz : z ∈ intHat F E) : HeckeCharacterZeroLocus.ThmBIn.finPart F E z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z h =>
    obtain ⟨a, -, ha, o, rfl⟩ := h
    refine AddSubgroup.subset_closure ⟨HeckeCharacterZeroLocus.ThmBIn.sndA F a, fun v => ha v, o, ?_⟩
    change HeckeCharacterZeroLocus.ThmBIn.finPart F E (a • ((1 : AF F) ⊗ₜ[F] (o : E))) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  | zero => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).zero_mem
  | add x y _ _ hx hy => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).add_mem hx hy
  | neg x _ hx => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).neg_mem hx

theorem mem_intAd_iff (z : AE F E) :
    eqv F E z ∈ intAd E ↔ HeckeCharacterZeroLocus.ThmBIn.finPart F E z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  rw [GroundTheory.BlockD.ThmBHecke.mem_intAE_iff, ← GroundTheory.BlockD.ThmBHecke.adeleEquiv_snd,
    GroundTheory.Global.mem_integralFiniteAdeles]
  simp only [intAd, Subring.mem_iInf, Subring.mem_comap]
  rfl

theorem dict : Dict := by
  intro F E _ _ _ _ _
  refine ⟨GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv, GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv_symm,
    GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA, fun z => ?_, fun x => ?_⟩
  · rw [mem_intAd_iff]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← sec_finPart]
      exact sec_mem h
    · rw [← finPart_finOne_smul]
      exact finPart_mem h
  · exact (PositivityTheory.ThKCT.Tate.absE_eq x).symm

end GlobalTheory.CompanionTheory.EisDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleaveStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_occurs_product_interleave : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (x y : IrrGL (k := k)) (u v w : List (IrrGL (k := k))), (∀ c ∈ u, c.IsCusp) → (∀ c ∈ v, c.IsCusp) → Wd x.rep u → Wd y.rep v → Zc.Comb.Interleave u v w → Wd (prod₂ x.rep y.rep) w := by
  first | exact @GlobalTheory.CompanionTheory.WordProd.wd_prod₂_of_interleave | exact GlobalTheory.CompanionTheory.WordProd.wd_prod₂_of_interleave | (intros; apply GlobalTheory.CompanionTheory.WordProd.wd_prod₂_of_interleave <;> assumption)
end

