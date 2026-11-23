module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicHeightGrowthOfCosetGrowthUnitaryPair
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftGrow

theorem reduction_unif {D : D7} {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) :
    ∃ M : ℕ, ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) →
      ∃ (S : Finset (GA D V)) (C : ℝ), 0 ≤ C ∧ ∀ g, ∃ γ ∈ GQ V, ∃ x ∈ S, ∃ a ∈ GinfC V, ∃ k ∈ U, k ∈ GfC V ∧
        γ * g = x * a * k ∧ 1 + normInf θ V a ≤ C * (height θ V g : ℝ) ^ M := by
  obtain ⟨d, C, M, hd, h⟩ := _root_.GlobalTheory.SmoothForms.Reduce.reduction D θ V hθ
    (GlobalTheory.T.orthogonalFrame_of_anisotropicFiniteLengths _ (GlobalTheory.T.anisotropicFiniteLengths_of_shortLatticeVector _ (GlobalTheory.T.shortLatticeVectorBoundedSize_of_orthogonalFrame _ (_root_.GlobalTheory.SmoothForms.frameSmall _)))) (_root_.GlobalTheory.SmoothForms.denomBound D θ V)
  refine ⟨M + 1, fun U hU => ?_⟩
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.SmoothForms.Cover.exists_finset_cover D V U hU d hd
  obtain ⟨hm, C', hC'⟩ := _root_.GlobalTheory.SmoothForms.normInf_mul_le_and_le_height D θ V
  obtain ⟨-, -, -, r4, r5, r6, r7, r8⟩ := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  refine ⟨S, 1 + |C * C'|, by positivity, fun g => ?_⟩
  obtain ⟨γ, hγ, h1, h2⟩ := h g
  obtain ⟨k, hk, a, ha, e⟩ := r7 (γ * g)
  have e' : (γ * g)⁻¹ = k⁻¹ * a⁻¹ := by rw [e, ← r6 a ha k hk, _root_.mul_inv_rev]
  obtain ⟨x, hx, h3, h4⟩ := hS k hk fun i j => by
    have := h1 i j
    rwa [e', e, r8 _ _ ha, r8 _ _ (inv_mem ha)] at this
  refine ⟨γ, hγ, x, hx, a, ha, _, h3, h4, ?_, ?_⟩
  · rw [mul_assoc, r6 a ha _ h4, e, ← mul_assoc, mul_inv_cancel_left]
  · have h5 : normInf θ V a = normInf θ V (γ * g) := by
      unfold normInf
      rw [e', e]
      simp only [r4, r5 k hk, r5 _ (inv_mem hk), one_mul]
    have h6 : normInf θ V a ≤ C * C' * (height θ V g : ℝ) ^ (M + 1) := by
      rw [h5]
      refine (hm γ g).trans ((mul_le_mul h2 (hC' g) (GlobalTheory.SmoothForms.normInf_nonneg g)
        ((GlobalTheory.SmoothForms.normInf_nonneg γ).trans h2)).trans_eq ?_)
      ring
    have h7 : (1 : ℝ) ≤ (height θ V g : ℝ) ^ (M + 1) :=
      one_le_pow₀ (by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ V g)
    rw [add_mul, one_mul]
    exact add_le_add h7 (h6.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (zero_le_one.trans h7)))

theorem growth_pair : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (N : ℕ), ∃ N' : ℕ, ∀ K : GA D V → GA D W → ℂ, (∀ γ ∈ GQ V, ∀ δ ∈ GQ W, ∀ g h, K (γ * g) (δ * h) = K g h) → (∃ (U : Subgroup (GA D V)) (U' : Subgroup (GA D W)), IsOpen (U : Set (GA D V)) ∧ IsOpen (U' : Set (GA D W)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ k' ∈ U', k' ∈ GfC W → ∀ g h, K (g * k) (h * k') = K g h) → (∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC V, ∀ b ∈ GinfC W, ‖K (x * a) (y * b)‖ ≤ C * ((1 + normInf θ V a) * (1 + normInf θ W b)) ^ N) → ∃ C : ℝ, ∀ g h, ‖K g h‖ ≤ C * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ N' := by
  intro D θ hθ V W N
  obtain ⟨M, hM⟩ := reduction_unif hθ V
  obtain ⟨M', hM'⟩ := reduction_unif hθ W
  refine ⟨(M + M') * N, ?_⟩
  rintro K hL ⟨U, U', hU, hU', hR⟩ hG
  obtain ⟨S, A, hA, hS⟩ := hM U hU
  obtain ⟨S', A', hA', hS'⟩ := hM' U' hU'
  choose C hC using hG
  refine ⟨(∑ p ∈ S ×ˢ S', |C p.1 p.2|) * (A * A') ^ N, fun g h => ?_⟩
  obtain ⟨γ, hγ, x, hx, a, ha, k, hk, hk2, e, hb⟩ := hS g
  obtain ⟨δ, hδ, y, hy, b, hb', k', hk', hk2', e', hb2⟩ := hS' h
  have g1 : (1 : ℝ) ≤ (height θ V g : ℝ) := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ V g
  have h1 : (1 : ℝ) ≤ (height θ W h : ℝ) := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ W h
  have na : 0 ≤ 1 + normInf θ V a := add_nonneg zero_le_one (GlobalTheory.SmoothForms.normInf_nonneg a)
  have nb : 0 ≤ 1 + normInf θ W b := add_nonneg zero_le_one (GlobalTheory.SmoothForms.normInf_nonneg b)
  have key : (1 + normInf θ V a) * (1 + normInf θ W b) ≤
      A * A' * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ (M + M') := by
    have p1 : (height θ V g : ℝ) ^ M ≤ (height θ V g : ℝ) ^ (M + M') := pow_le_pow_right₀ g1 (Nat.le_add_right _ _)
    have p2 : (height θ W h : ℝ) ^ M' ≤ (height θ W h : ℝ) ^ (M + M') := pow_le_pow_right₀ h1 (Nat.le_add_left _ _)
    have q1 := hb.trans (mul_le_mul_of_nonneg_left p1 hA)
    have q2 := hb2.trans (mul_le_mul_of_nonneg_left p2 hA')
    refine (mul_le_mul q1 q2 nb (na.trans q1)).trans_eq ?_
    rw [mul_pow]; ring
  rw [← hL γ hγ δ hδ g h, e, e', hR k hk hk2 k' hk' hk2', pow_mul, mul_assoc, ← mul_pow]
  refine (hC x y a ha b hb').trans (mul_le_mul ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun p : GA D V × GA D W => |C p.1 p.2|) (fun _ _ => abs_nonneg _)
      (Finset.mk_mem_product hx hy)))
    (pow_le_pow_left₀ (mul_nonneg na nb) key N) (pow_nonneg (mul_nonneg na nb) N)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _))

end GlobalTheory.Mem.LiftGrow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuous
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem adicCompletion_trace_norm_continuous : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), Continuous f → letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) → Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) := by
  intro K L _ _ _ _ v v' f hf
  letI := f.toAlgebra
  intro hfd
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ _
  haveI : CompleteSpace (v.adicCompletion K) := inferInstance
  haveI : ContinuousSMul (v.adicCompletion K) (v'.adicCompletion L) := continuousSMul_of_algebraMap _ _ hf
  refine ⟨LinearMap.continuous_of_finiteDimensional _, ?_⟩
  let b := Module.finBasis (v.adicCompletion K) (v'.adicCompletion L)
  have hn : (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) = fun y => (Algebra.leftMulMatrix b y).det := by
    funext y; exact Algebra.norm_eq_matrix_det b y
  rw [hn]
  have hl : Continuous (fun y => Algebra.leftMulMatrix b y) :=
    (LinearMap.continuous_of_finiteDimensional (Algebra.leftMulMatrix b).toLinearMap)
  exact hl.matrix_det

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormOfBasisImage
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.adicCompletion_trace_norm_of_basis_image : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L) (b' : Module.Basis (Fin n) (v.adicCompletion K) (v'.adicCompletion L)), (∀ i, b' i = algebraMap L _ (b i)) → ∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z) ∧ Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z) := by
  intro K L _ _ _ _ _ v v' f hf
  letI := f.toAlgebra
  intro n b b' hb z
  have hM : Algebra.leftMulMatrix b' (algebraMap L (v'.adicCompletion L) z) =
      (Algebra.leftMulMatrix b z).map (algebraMap K (v.adicCompletion K)) := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
    have key : algebraMap L (v'.adicCompletion L) z * b' j =
        ∑ k, (algebraMap K (v.adicCompletion K) (b.repr (z * b j) k)) • b' k := by
      rw [hb, ← map_mul]
      conv_lhs => rw [← b.sum_repr (z * b j)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, hf]
    rw [key, b'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace b', Algebra.norm_eq_matrix_det b', hM,
    Algebra.trace_eq_matrix_trace b, Algebra.norm_eq_matrix_det b]
  refine ⟨?_, ?_⟩
  · exact (AddMonoidHom.map_trace (algebraMap K (v.adicCompletion K)).toAddMonoidHom _).symm
  · exact (RingHom.map_det _ _).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineSpaceCoveredSmoothOfRelativeDimensionAdd
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

theorem affSmooth_mvPolynomial (R : Type) [CommRing R] [Nontrivial R] (r : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension r R (MvPolynomial (Fin r) R) := by
  have : Algebra.IsStandardSmooth R (MvPolynomial (Fin r) R) :=
    Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential.2
      ⟨inferInstance, _, KaehlerDifferential.mvPolynomialBasis R _, by
        rintro _ ⟨i, rfl⟩
        exact ⟨MvPolynomial.X i, (KaehlerDifferential.mvPolynomialBasis_apply R _ i).symm⟩⟩
  exact (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth _).2 (by
    rw [rank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis R _), Fintype.card_fin])

theorem affSmooth_of_range_eq {R S K : Type} [CommRing R] [Nontrivial R] [CommRing S] [CommRing K] {r : ℕ}
    (ψ : R →+* S) (j : S →+* K) (hj : Function.Injective j) (t : Fin r → K)
    (hg : Function.Injective (MvPolynomial.eval₂Hom (j.comp ψ) t))
    (h : (MvPolynomial.eval₂Hom (j.comp ψ) t).range = j.range) :
    ψ.IsStandardSmoothOfRelativeDimension r := by
  let g := MvPolynomial.eval₂Hom (j.comp ψ) t
  let e : MvPolynomial (Fin r) R ≃+* S :=
    (RingEquiv.ofBijective g.rangeRestrict
      ⟨fun _ _ h => hg (congrArg Subtype.val h), g.rangeRestrict_surjective⟩).trans
      ((RingEquiv.subringCongr h).trans (RingEquiv.ofBijective j.rangeRestrict
        ⟨fun _ _ h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩).symm)
  have he : ∀ P, j (e P) = g P := fun P =>
    congrArg Subtype.val ((RingEquiv.ofBijective j.rangeRestrict
        ⟨fun _ _ h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩).apply_symm_apply _)
  have : ψ = e.toRingHom.comp (algebraMap R (MvPolynomial (Fin r) R)) :=
    RingHom.ext fun a => hj (by
      show _ = j (e (MvPolynomial.C a))
      rw [he]
      exact (MvPolynomial.eval₂Hom_C (j.comp ψ) t a).symm)
  rw [this]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ e
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2 (affSmooth_mvPolynomial R r))

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

theorem AffCover.smoothOfRelativeDimension {M : RatModel F Ω} {M' : RatModel F Ω'} {φ : Ω →ₐ[F] Ω'}
    {f : M'.Z ⟶ M.Z} {r : ℕ} (h : AffCover M M' φ f r) : SmoothOfRelativeDimension r f := by
  refine ⟨fun z => ?_⟩
  obtain ⟨U, W, t, hU, hW, hz, hUW, hind, hR⟩ := h.2 z
  have e : U ≤ f ⁻¹ᵁ W := hUW
  have nU : (U : Set M'.Z).Nonempty := ⟨z, hz⟩
  have nW : (W : Set M.Z).Nonempty := ⟨f z, hUW z hz⟩
  have : Nontrivial Γ(M.Z, W) := (M.res W nW).domain_nontrivial
  have hc : (M'.res U nU).comp (f.appLE W U e).hom = (φ : Ω →+* Ω').comp (M.res W nW) := RingHom.ext fun a => by
    show M'.res U nU _ = φ (M.res W nW a)
    rw [M.res_apply, M'.res_apply, ← h.1.valF_app nW a]
    exact M'.valF_resG e nU (f.app W a)
  refine ⟨W, hW, U, hU, hz, e, affSmooth_of_range_eq _ (M'.res U nU) (M'.res_injective U nU) t ?_ ?_⟩
  · rw [hc, injective_iff_map_eq_zero]
    intro P hP
    apply MvPolynomial.map_injective _ (M.res_injective W nW)
    rw [map_zero]
    apply hind
    rw [MvPolynomial.eval₂_map]
    exact hP
  · rw [hc, M'.range_res, hR]
    have hm : ∀ a, (φ : Ω →+* Ω').comp (M.res W nW) a ∈ φ '' (M.ringOn W : Set Ω) := fun a =>
      ⟨_, (RatModel.mem_ringOn_iff_exists nW).2 ⟨a, (M.res_apply W nW a).symm⟩, rfl⟩
    have hm' : ∀ x ∈ M.ringOn W,
        φ x ∈ (MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp (M.res W nW)) t).range := fun x hx => by
      obtain ⟨a, rfl⟩ := (RatModel.mem_ringOn_iff_exists nW).1 hx
      exact ⟨MvPolynomial.C a, by rw [MvPolynomial.eval₂Hom_C, ← M.res_apply W nW]; rfl⟩
    apply le_antisymm
    · rintro _ ⟨P, rfl⟩
      rw [Subalgebra.mem_toSubring]
      induction P using MvPolynomial.induction_on with
      | C a => rw [MvPolynomial.eval₂Hom_C]; exact Algebra.subset_adjoin (Or.inl (hm a))
      | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
      | mul_X P i hP =>
        rw [map_mul, MvPolynomial.eval₂Hom_X']
        exact mul_mem hP (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))
    · intro x hx
      rw [Subalgebra.mem_toSubring] at hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        rcases hx with ⟨y, hy, rfl⟩ | ⟨i, rfl⟩
        · exact hm' y hy
        · exact ⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ i⟩
      | algebraMap c => rw [← φ.commutes]; exact hm' _ (Subalgebra.algebraMap_mem _ c)
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy

theorem affCover_smooth (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r d : ℕ)
    (h : AffCover M M' φ f r) (hd : SmoothOfRelativeDimension d M.s) :
    SmoothOfRelativeDimension (d + r) M'.s := by
  have := h.smoothOfRelativeDimension
  rw [← h.1.inducedModelMorphism_comp_structureMap, Nat.add_comm]
  infer_instance

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeNonempty
section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem nonempty_nbc_of_isEmpty_loc :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (nd : NData R H what₂) (A : NAut nd),
      IsEmpty nd.Loc → Nonempty (NBC A) := by
  intro R H what₂ nd A hL
  exact ⟨{
    AU := fun _ => Empty
    multAU := fun _ x => x.elim
    sphAU := fun _ x => x.elim
    locAU := fun _ x => x.elim
    satAU := fun _ x => x.elim
    satAU_card := fun _ x => x.elim
    Wt := fun _ => Empty
    infW := fun _ x => x.elim
    infW_card := fun _ x => x.elim
    wtAU := fun _ x => x.elim
    infW_alg := fun _ x => x.elim
    embAV := fun i => hL.elim i
    embAV_inj := fun i => hL.elim i
    embAV_loc := fun i => hL.elim i
    embAV_sat := fun i => hL.elim i
    embAV_sph := fun i => hL.elim i
    embAV_inf := fun i => hL.elim i }⟩

end GlobalTheory.MemN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BddAboveSubDegsOfJointlyMono
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (IsFiniteQC)

namespace GlobalTheory.VB

variable {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C]

theorem IsProjCurve.bddAbove_subDegs_of_kernel (hC : IsProjCurve k C) {B Q : C.Modules}
    [IsFiniteQC Q] (p : B ⟶ Q) (hK : BddAbove (subDegs k (kernel p)))
    (hQ : BddAbove (subDegs k Q)) : BddAbove (subDegs k B) := by
  have := hC.isNoetherian
  obtain ⟨a, ha⟩ := hK
  obtain ⟨b, hb⟩ := hQ
  refine ⟨a + b, ?_⟩
  rintro _ ⟨G, i, hi, rfl⟩
  have := hi.mono
  have := hi.isFiniteQC
  let q : G ⟶ Q := i ≫ p
  have hKG : IsFiniteQC (kernel q) := .of_mono (kernel.ι q)
  have hm : Mono (Abelian.factorThruCoimage q) := inferInstance
  have hc : IsFiniteQC (cokernel (kernel.ι q)) := .of_mono (Abelian.factorThruCoimage q)
  let j : kernel q ⟶ kernel p := kernel.lift p (kernel.ι q ≫ i) (by
    rw [Category.assoc]; exact kernel.condition q)
  have hj : Mono j := mono_of_mono_fac (kernel.lift_ι p (kernel.ι q ≫ i) _)
  have h₁ : deg k (kernel q) ≤ a := ha (IsCohSub.deg_mem (i := j) ⟨hj, hKG⟩)
  have h₂ : deg k (cokernel (kernel.ι q)) ≤ b :=
    hb (IsCohSub.deg_mem (i := Abelian.factorThruCoimage q) ⟨hm, hc⟩)
  rw [hC.deg_cokernel] at h₂
  omega

theorem IsProjCurve.bddAbove_subDegs_of_jointly_mono (hC : IsProjCurve k C) {D : C.Modules}
    [IsFiniteQC D] (hD : BddAbove (subDegs k D)) (n : ℕ) :
    ∀ (Z : C.Modules) [IsFiniteQC Z] (ψ : Fin n → (Z ⟶ D)),
      (∀ (W : C.Modules) (g : W ⟶ Z), (∀ j, g ≫ ψ j = 0) → g = 0) →
      BddAbove (subDegs k Z) := by
  have := hC.isNoetherian
  induction n with
  | zero =>
    intro Z _ ψ h
    have hZ : IsZero Z := (IsZero.iff_id_eq_zero Z).2 (h Z (𝟙 Z) fun j => j.elim0)
    refine ⟨0, ?_⟩
    rintro _ ⟨G, i, hi, rfl⟩
    have := hi.mono
    exact (deg_eq_zero_of_isZero k (hZ.of_mono i)).le
  | succ n ih =>
    intro Z _ ψ h
    have : IsFiniteQC (kernel (ψ 0)) := .of_mono (kernel.ι (ψ 0))
    refine hC.bddAbove_subDegs_of_kernel (ψ 0)
      (ih (kernel (ψ 0)) (fun j => kernel.ι (ψ 0) ≫ ψ j.succ) fun W g hg => ?_) hD
    have h0 : g ≫ kernel.ι (ψ 0) = 0 := h W _ fun j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [Category.assoc, kernel.condition, comp_zero]
      · rw [Category.assoc]; exact hg j
    exact (cancel_mono (kernel.ι (ψ 0))).1 (h0.trans (zero_comp).symm)

theorem dualMap_sum {F G : C.Modules} {ι : Type} (s : Finset ι) (f : ι → (F ⟶ G)) :
    dualMap (∑ j ∈ s, f j) = ∑ j ∈ s, dualMap (f j) :=
  map_sum (AddMonoidHom.mk' (dualMap (F := F) (G := G)) dualMap_add) f s

theorem bddAbove_subDegs_of_isVB : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]
    [IsIntegral C], IsProjCurve k C → ∀ (F : C.Modules) (r : ℕ), IsVB F r →
    BddAbove (subDegs k F) := by
  intro k _ C _ _ hC F r hF
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hC.isProjOver
  have := hF.isFiniteQC
  have := hF.dual.isFiniteQC
  obtain ⟨m, n, φ, hφ⟩ := (hA.eventually_exists_epi_sigma (dual F)).exists
  have hL := Twist.isLB_lbZPow hA.isLB (-m)
  have hT := isVB_toMod hL
  let T := GlobalTheory.LB.toMod (lbZPow A (-m))
  have hD : IsVB (dual T) 1 := hT.dual
  have := hD.isFiniteQC
  have := Abelian.hasFiniteBiproducts (C := C.Modules)
  let φ' : (⨁ fun _ : Fin n => T) ⟶ dual F := (biproduct.isoCoproduct _).hom ≫ φ
  have hφ' : Epi φ' := inferInstance
  have hb := hF.isIso_toBidual_of_local_frames
  refine hC.bddAbove_subDegs_of_jointly_mono (hC.isMaxSubDeg_of_rank_one hD).bddAbove n F
    (fun j => cartierDualToBidual F ≫ dualMap (biproduct.ι (fun _ : Fin n => T) j ≫ φ')) fun W g hg => ?_
  have h0 : (g ≫ cartierDualToBidual F) ≫ dualMap φ' = 0 := by
    rw [← Category.comp_id ((g ≫ cartierDualToBidual F) ≫ dualMap φ'), ← dualMap_id,
      ← biproduct.total, dualMap_sum, Preadditive.comp_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := hg j
    rw [dualMap_comp, dualMap_comp] at *
    simp only [Category.assoc] at *
    rw [reassoc_of% this, zero_comp]
  have h1 : g ≫ cartierDualToBidual F = 0 := (cancel_mono (dualMap φ')).1 (h0.trans zero_comp.symm)
  exact (cancel_mono (cartierDualToBidual F)).1 (h1.trans zero_comp.symm)

end GlobalTheory.VB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ}

def Reps {X Y : GlobalTheory.ProjVar.Var F} (Eb : Fr (ratOf X) m 0) (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn)
    (f : Y.X ⟶ X.X) : Prop :=
  (ratOf X).IsHom (ratOf Y) φ f ∧
    (∀ z', ∀ A' ∈ S.S z', ∀ A ∈ Eb.S (f z'), Par 0 ((ratOf Y).O z').toSubring (A' * (A.map φ)⁻¹)) ∧
    ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), ∀ A ∈ Eb.S (x (IsLocalRing.closedPoint K)), ∀ h : Mat m K,
      Par 0 ⊤ h → ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ Bears S φ A h p

theorem Refines.reps {X Y : GlobalTheory.ProjVar.Var F} {Eb : Fr (ratOf X) m 0} {S : Fr (ratOf Y) m m}
    {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (h : Refines Eb S φ f) : Reps Eb S φ f :=
  ⟨h.hom, h.sub, h.lifts⟩

def CoBear {X Y₁ Y₂ : GlobalTheory.ProjVar.Var F} (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) {K : Type} [Field K] (x : Sp K ⟶ X.X) (p₁ : Sp K ⟶ Y₁.X)
    (p₂ : Sp K ⟶ Y₂.X) : Prop :=
  ∃ A ∈ Eb.S (x (IsLocalRing.closedPoint K)), ∃ h : Mat m K, Par 0 ⊤ h ∧ Bears S₁ φ₁ A h p₁ ∧ Bears S₂ φ₂ A h p₂

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CovolumeUnitDetNormSlabLatticeAutLtTopStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_unitDetNormSlab_latticeAut_lt_top : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → GlobalTheory.FlagMeas.covol (GlobalTheory.FlagMeas.autGL E j Λ) (GlobalTheory.FlagMeas.haarGL E j) {x | 1 ≤ GlobalTheory.FlagMeas.detNorm E j x ∧ GlobalTheory.FlagMeas.detNorm E j x < Real.exp 1} < ⊤ := by
  intro E _ _ hE j hj Λ hΛ
  letI : Submodule.IsFullLattice E Λ := hΛ
  apply GlobalTheory.SlabFinVol.covol_unitSlab_lt_top <;> first | assumption | infer_instance
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtensionPow
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DenseCompl


open scoped WithZeroTopology in
theorem exists_extension_pow (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ) (he : 0 < e)
    (hv : ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e) :
    ∃ f : v.adicCompletion K →+* v'.adicCompletion L, Continuous f ∧
      (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧
      ∀ y, Valued.v (f y) = Valued.v y ^ e := by
  first
  | exact @_root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom
  | exact _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom
  | (apply _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom ..)

end GlobalTheory.DenseCompl
end

