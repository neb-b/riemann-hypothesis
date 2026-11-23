module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0079
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmTypeEigenMultiplicityOfDensePrimes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0082
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwBack

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalOfTranscendenceDegreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birational_of_transcendence_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) [Nonempty K] [CharZero Ω] (d : ℕ), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → Algebra.trdeg ℤ Ω = d → Birational y ∧ IsArithVar (mCoordIdeal y) (d + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.coordTie_birational_isArithVar | exact GlobalTheory.CompanionTheory.Ar.coordTie_birational_isArithVar | (intros; apply GlobalTheory.CompanionTheory.Ar.coordTie_birational_isArithVar <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharpolySplitsOfEmbeddingsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_splits_of_embeddings : ∀ (E : Type) [Field E] [NumberField E] (Ω : Type) [Field Ω] [CharZero Ω] (O : Type) [CommRing O] [Algebra O Ω] (K : Type) [Field K] (g : O →+* K), Function.Injective (algebraMap O Ω) → Nat.card (E →+* Ω) = Module.finrank ℚ E → (∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) → ∀ a : 𝓞 E, ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegZ.charpoly_lmul_splits_of_conjugates | exact GlobalTheory.CompanionTheory.Ar.Flat.DegZ.charpoly_lmul_splits_of_conjugates | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegZ.charpoly_lmul_splits_of_conjugates <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpIntegersValuationRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cp_integers_valuation_ring : ∀ p : Nat.Primes, (NormedField.valuation (K := ℂ_[p])).Integers (OCp p) ∧
    (∃ x : ℂ_[p], 0 < NormedField.valuation (K := ℂ_[p]) x ∧ NormedField.valuation (K := ℂ_[p]) x < 1) ∧
    ∀ x : ℂ_[p], x ∈ (algebraMap (OCp p) ℂ_[p]).range ↔ ‖x‖ ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ocp_integers | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ocp_integers | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ocp_integers <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveDegreeUnique
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem curveIn_isDeg_unique_of_isCptGen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (Λ : Lat ξ Ω) (n n' : ℤ), IsCptGen ξ → Y.IsDeg Λ n → Y.IsDeg Λ n' → n = n' :=
  @PositivityTheory.HtPt.Ch.isdeg_unique

end GlobalTheory.CompanionTheory.Ar.Crv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLatticeDegreeFormula
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem isDeg_coordDeg : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (w : (Σ k, J k) → K) (Λ : Lat ξ Ω) (S : Set (Cpt ξ)) (a : B → ℤ) (e₀ : Ω) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordTie ℤ ξ (segre y) → CoordsAt ξ y z w → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → Λ.IsDegOn S y a e₀ → Y.IsDeg Λ (coordDeg C w a) :=
  PositivityTheory.HtPt.Ci.isdeg_coord

end GlobalTheory.CompanionTheory.Ar.Crv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenDecompositionExactSequence
section
open NumberField GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EigExact

theorem mem_eigSp_iff {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]
    {ρ : O →+* Module.End k V} {τ : O →+* k} {x : V} : x ∈ eigSp ρ τ ↔ ∀ a, ρ a x = τ a • x := by
  simp [eigSp, sub_eq_zero]

theorem eigSp_eq_eigenSub {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]
    (ρ : O →+* Module.End k V) (τ : O →+* k) : eigSp ρ τ = EigenSplit.eigenSub ρ τ := by
  ext x
  rw [mem_eigSp_iff, EigenSplit.mem_eigenSub]

theorem map_eigSp_eq {E : Type} [Field E] [NumberField E] {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V₂ V₃ : Type} [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    {ρ₂ : 𝓞 E →+* Module.End k V₂} {ρ₃ : 𝓞 E →+* Module.End k V₃} {g : V₂ →ₗ[k] V₃}
    (hg : Function.Surjective g) (hgρ : ∀ a x, g (ρ₂ a x) = ρ₃ a (g x)) (τ : 𝓞 E →+* k) :
    (eigSp ρ₂ τ).map g = eigSp ρ₃ τ := by
  classical
  obtain ⟨φ, rfl⟩ := GlobalTheory.TraceSpread.exists_embedding τ
  have hs := GlobalTheory.TraceSpread.isSplitting_embeddings (E := E) k
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_eigSp_iff] at hx
    rw [mem_eigSp_iff]
    intro a
    rw [← hgρ, hx, map_smul]
  · intro y hy
    obtain ⟨x, rfl⟩ := hg y
    rw [eigSp_eq_eigenSub] at hy
    refine ⟨EigenSplit.proj hs ρ₂ φ x, ?_, ?_⟩
    · rw [SetLike.mem_coe, eigSp_eq_eigenSub]
      exact EigenSplit.proj_mem hs ρ₂ φ x
    · have he : EigenSplit.IsEquivariant ρ₂ ρ₃ g := hgρ
      rw [he.proj hs φ x]
      exact EigenSplit.proj_of_mem hs hy

theorem eigSp_inf_ker {O k V₁ V₂ V₃ : Type} [CommRing O] [Field k] [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    {ρ₁ : O →+* Module.End k V₁} {ρ₂ : O →+* Module.End k V₂} {f : V₁ →ₗ[k] V₂} {g : V₂ →ₗ[k] V₃}
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g)
    (hfρ : ∀ a x, f (ρ₁ a x) = ρ₂ a (f x)) (τ : O →+* k) :
    eigSp ρ₂ τ ⊓ LinearMap.ker g = (eigSp ρ₁ τ).map f := by
  apply le_antisymm
  · rintro x ⟨hx, hk⟩
    rw [SetLike.mem_coe, mem_eigSp_iff] at hx
    have hk' : x ∈ LinearMap.range f := by rw [hfg]; exact hk
    obtain ⟨z, rfl⟩ := hk'
    refine ⟨z, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_eigSp_iff]
    intro a
    apply hf
    rw [hfρ, hx, map_smul]
  · rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_eigSp_iff] at hz
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, mem_eigSp_iff]
      intro a
      rw [← hfρ, hz, map_smul]
    · change f z ∈ LinearMap.ker g
      rw [← hfg]
      exact ⟨z, rfl⟩

theorem finrank_map_add_inf_ker {k V W : Type} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (g : V →ₗ[k] W) (S : Submodule k V) [FiniteDimensional k S] :
    Module.finrank k (S.map g) + Module.finrank k ↥(S ⊓ LinearMap.ker g) = Module.finrank k S := by
  have h := LinearMap.finrank_range_add_finrank_ker (g.domRestrict S)
  rw [LinearMap.range_domRestrict] at h
  rw [← h, LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq S (Submodule.comap S.subtype (LinearMap.ker g)),
    Submodule.map_comap_subtype]

theorem exists_basis_eigSp_quot : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (V₁ V₂ V₃ : Type) [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃] (ρ₁ : 𝓞 E →+* Module.End k V₁) (ρ₂ : 𝓞 E →+* Module.End k V₂) (ρ₃ : 𝓞 E →+* Module.End k V₃) (f : V₁ →ₗ[k] V₂) (g : V₂ →ₗ[k] V₃), Function.Injective f → Function.Surjective g → LinearMap.range f = LinearMap.ker g → (∀ a x, f (ρ₁ a x) = ρ₂ a (f x)) → (∀ a x, g (ρ₂ a x) = ρ₃ a (g x)) → ∀ (τ : 𝓞 E →+* k) (r n : ℕ) (b₁ : Fin r → V₁) (b₂ : Fin n → V₂), LinearIndependent k b₁ → Submodule.span k (Set.range b₁) = eigSp ρ₁ τ → LinearIndependent k b₂ → Submodule.span k (Set.range b₂) = eigSp ρ₂ τ → r ≤ n ∧ ∃ b₃ : Fin (n - r) → V₃, LinearIndependent k b₃ ∧ Submodule.span k (Set.range b₃) = eigSp ρ₃ τ := by
  intro E _ _ k _ _ _ V₁ V₂ V₃ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ f g hf hg hfg hfρ hgρ τ r n b₁ b₂ hb₁ hs₁ hb₂ hs₂
  have hr : Module.finrank k (eigSp ρ₁ τ) = r := by
    rw [← hs₁, finrank_span_eq_card hb₁, Fintype.card_fin]
  have hn : Module.finrank k (eigSp ρ₂ τ) = n := by
    rw [← hs₂, finrank_span_eq_card hb₂, Fintype.card_fin]
  haveI : FiniteDimensional k (eigSp ρ₂ τ) := by
    rw [← hs₂]
    exact FiniteDimensional.span_of_finite k (Set.finite_range b₂)
  have hsum := finrank_map_add_inf_ker g (eigSp ρ₂ τ)
  rw [map_eigSp_eq hg hgρ τ, eigSp_inf_ker hf hfg hfρ τ, ← (Submodule.equivMapOfInjective f hf (eigSp ρ₁ τ)).finrank_eq, hr, hn] at hsum
  haveI : FiniteDimensional k (eigSp ρ₃ τ) := by
    rw [← map_eigSp_eq hg hgρ τ]
    infer_instance
  have h3 : Module.finrank k (eigSp ρ₃ τ) = n - r := by omega
  refine ⟨by omega, ?_⟩
  let B := Module.finBasisOfFinrankEq k (eigSp ρ₃ τ) h3
  refine ⟨fun i => (B i : V₃), ?_, ?_⟩
  · exact B.linearIndependent.map' (eigSp ρ₃ τ).subtype (Submodule.ker_subtype _)
  · have : Set.range (fun i => (B i : V₃)) = (eigSp ρ₃ τ).subtype '' Set.range B := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, B.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.CompanionTheory.Ar.EigExact
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldCoordsGenerated
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChartFrac

theorem exists_eq_div_chart : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω),
    CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ a : Ω, ∃ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ t ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), t ≠ 0 ∧ a = s / t := by
  intro X Ω _ ξ κ x h c hc a
  have hchart : InChart ξ x c (TieArith.genCpt ξ) :=
    ⟨hc, fun c' => TieArith.mem_regAt_genCpt ξ h.gen _⟩
  obtain ⟨t, ht, hu, hta⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x h c (TieArith.genCpt ξ) hchart a).mp
    (TieArith.mem_regAt_genCpt ξ h.gen a)
  exact ⟨t * a, hta, t, ht, hu.1, (mul_div_cancel_left₀ a hu.1).symm⟩

end GlobalTheory.CompanionTheory.Ar.ChartFrac
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldModelExists
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Crv.Field

theorem curve_field : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (W : Ideal (MRing J)) (p : ℕ) [Fact p.Prime], IsMultiProjPrime W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card B : ℕ) : WithBot ℕ∞) → ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod p) K) (_ : GroundTheory.FunctionField.IsFunctionField (ZMod p) K) (w : (Σ k, J k) → K), mCoordIdeal w = W ∧ Birational w ∧ ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0 :=
  PositivityTheory.HtPt.Ci.curve_field

end GlobalTheory.CompanionTheory.Ar.Crv.Field
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeneratorRatioUnitExists
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Ratio

variable {X Y F Y' Z : Scheme.{0}} {L : LB X} {M : LB Y} {f : F ⟶ X} {g : F ⟶ Y}

theorem gm_pull_g (N : LB X) (f : F ⟶ X) (ψ : Z ⟶ F) (z : Z) (a b : N.ι) (ha : f (ψ z) ∈ N.U a)
    (hb : f (ψ z) ∈ N.U b) :
    gm ψ z ((N.pull f).U (fun _ => a) ⊓ (N.pull f).U (fun _ => b)) ((N.pull f).g (fun _ => a) (fun _ => b)) =
      gm (ψ ≫ f) z _ (N.g a b) := by
  have hp : ψ z ∈ (N.pull f).U (fun _ => a) ⊓ (N.pull f).U (fun _ => b) := ⟨mem_pull.2 ha, mem_pull.2 hb⟩
  show gm ψ z _ (∏ _k : PUnit, (res _ (pullU f _ (N.g a b))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res ψ z _ hp _).trans (gm_pull ψ f z (N.U a ⊓ N.U b) ⟨ha, hb⟩ _)

theorem gm_w_trans {w : LB.Iso (L.pull f) (M.pull g)} (hw : w.IsGen) (ψ : Z ⟶ F) (z : Z) {a a' : L.ι} {b b' : M.ι}
    (ha : f (ψ z) ∈ L.U a) (ha' : f (ψ z) ∈ L.U a') (hb : g (ψ z) ∈ M.U b) (hb' : g (ψ z) ∈ M.U b') :
    gm ψ z ((M.pull g).U (fun _ => b) ⊓ (L.pull f).U (fun _ => a)) (w.s (fun _ => b, fun _ => a)) =
      gm (ψ ≫ g) z _ (M.g b b') * (gm (ψ ≫ f) z _ (L.g a a'))⁻¹ *
        gm ψ z ((M.pull g).U (fun _ => b') ⊓ (L.pull f).U (fun _ => a')) (w.s (fun _ => b', fun _ => a')) := by
  have hm : ψ z ∈ (M.pull g).U (fun _ => b) ⊓ (L.pull f).U (fun _ => a) ⊓
      ((M.pull g).U (fun _ => b') ⊓ (L.pull f).U (fun _ => a')) :=
    ⟨⟨mem_pull.2 hb, mem_pull.2 ha⟩, mem_pull.2 hb', mem_pull.2 ha'⟩
  have e := congrArg (gm ψ z ((M.pull g).U (fun _ => b) ⊓ (L.pull f).U (fun _ => a) ⊓
      ((M.pull g).U (fun _ => b') ⊓ (L.pull f).U (fun _ => a')))) (hw (fun _ => b, fun _ => a) (fun _ => b', fun _ => a'))
  refine (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res ψ z _ hm _))))
  show gm ψ z _ (res _ ((M.pull g).g (fun _ => b) (fun _ => b')) * (res _ ((L.pull f).g (fun _ => a) (fun _ => a')))⁻¹) = _
  rw [map_mul, map_inv, gm_res ψ z _ hm, gm_res ψ z _ hm, gm_pull_g M g ψ z b b' hb hb', gm_pull_g L f ψ z a a' ha ha']

variable {K : Type} [Fintype K]

def rW (L : LB X) (M : LB Y) (f : F ⟶ X) (g : F ⟶ Y) (φ : K → (Y' ⟶ F)) (p : K → L.ι) (q : K → M.ι) : Y'.Opens :=
  LB.wchart L (fun k => φ k ≫ f) p ⊓ LB.wchart M (fun k => φ k ≫ g) q

theorem rW_le (φ : K → (Y' ⟶ F)) (p : K → L.ι) (q : K → M.ι) (k : K) :
    rW L M f g φ p q ≤ φ k ⁻¹ᵁ ((M.pull g).U (fun _ => q k) ⊓ (L.pull f).U (fun _ => p k)) :=
  fun _ hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy.2 k), mem_pull.2 (Set.mem_iInter.1 hy.1 k)⟩

def rLoc (w : LB.Iso (L.pull f) (M.pull g)) (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)) (b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε))
    (p : K → L.ι) (q : K → M.ι) : Γ(Y', rW L M f g φ p q)ˣ :=
  res inf_le_left (c.s p) *
    (∏ k, res (rW_le φ p q k) (pullU (φ k) _ (w.s (fun _ => q k, fun _ => p k))) ^ ε k) *
    (res inf_le_right (b.s q))⁻¹

def rVal (w : LB.Iso (L.pull f) (M.pull g)) (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)) (b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε))
    (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → M.ι) : (Z.presheaf.stalk z)ˣ :=
  gm r z (LB.wchart L (fun k => φ k ≫ f) p) (c.s p) *
    (∏ k, gm (r ≫ φ k) z ((M.pull g).U (fun _ => q k) ⊓ (L.pull f).U (fun _ => p k)) (w.s (fun _ => q k, fun _ => p k)) ^ ε k) *
    (gm r z (LB.wchart M (fun k => φ k ≫ g) q) (b.s q))⁻¹

theorem gm_rLoc (w : LB.Iso (L.pull f) (M.pull g)) (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)) (b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε))
    (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → M.ι) (hz : r z ∈ rW L M f g φ p q) :
    gm r z _ (rLoc w φ ε c b p q) = rVal w φ ε c b r z p q := by
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) ?_))
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _ hz _))))
  exact (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
    ((gm_res r z _ hz _).trans (gm_pull r (φ k) z _ (rW_le φ p q k hz) _))))

theorem comm_group_ratio_cancel {A : Type} [CommGroup A] (tl tm c' w' b' tm' tl' : A) (h1 : tl = tl') (h2 : tm = tm') :
    (tl * c') * (tm' * tl'⁻¹ * w') * (tm * b')⁻¹ = c' * w' * b'⁻¹ := by
  subst h1 h2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem rVal_indep {w : LB.Iso (L.pull f) (M.pull g)} (hw : w.IsGen)
    (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    {c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)} {b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε)}
    (hc : c.IsGen) (hb : b.IsGen) (r : Z ⟶ Y') (z : Z) {p p' : K → L.ι} {q q' : K → M.ι}
    (hz : r z ∈ rW L M f g φ p q) (hz' : r z ∈ rW L M f g φ p' q') :
    rVal w φ ε c b r z p q = rVal w φ ε c b r z p' q' := by
  have e : ∀ k, gm (r ≫ φ k) z ((M.pull g).U (fun _ => q k) ⊓ (L.pull f).U (fun _ => p k)) (w.s (fun _ => q k, fun _ => p k)) =
      gm ((r ≫ φ k) ≫ g) z _ (M.g (q k) (q' k)) * (gm ((r ≫ φ k) ≫ f) z _ (L.g (p k) (p' k)))⁻¹ *
        gm (r ≫ φ k) z ((M.pull g).U (fun _ => q' k) ⊓ (L.pull f).U (fun _ => p' k)) (w.s (fun _ => q' k, fun _ => p' k)) :=
    fun k => gm_w_trans hw (r ≫ φ k) z (Set.mem_iInter.1 hz.1 k) (Set.mem_iInter.1 hz'.1 k)
      (Set.mem_iInter.1 hz.2 k) (Set.mem_iInter.1 hz'.2 k)
  unfold rVal
  rw [gen_trans hc r z hz.1 hz'.1, gen_trans hb r z hz.2 hz'.2, Finset.prod_congr rfl fun k _ => by rw [e k]]
  simp only [mul_zpow, Finset.prod_mul_distrib, inv_zpow, Finset.prod_inv_distrib]
  refine comm_group_ratio_cancel _ _ _ _ _ _ _ ?_ ?_
  · simp only [trF, Category.assoc]
  · simp only [trF, Category.assoc]

theorem exists_unit_ratio_of_generators (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull f) (M.pull g)} (hw : w.IsGen)
    (φ : K → (Y' ⟶ F)) (ε : K → ℤ)
    {c : LB.Gen (LB.LinComb L (fun k => φ k ≫ f) ε)} {b : LB.Gen (LB.LinComb M (fun k => φ k ≫ g) ε)}
    (hc : c.IsGen) (hb : b.IsGen) : ∃ u : Γ(Y', ⊤)ˣ, Tr w φ _ _ ε c b u := by
  obtain ⟨u, hu⟩ := glue_unit (X := Y') ⊤ (fun i : (K → L.ι) × (K → M.ι) => rW L M f g φ i.1 i.2) (fun _ => le_top)
    (fun y _ => by
      choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
      choose I' hI' using fun χ : Y' ⟶ Y => exists_chart hM (χ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun k => I (φ k ≫ f), fun k => I' (φ k ≫ g)),
        Set.mem_iInter.2 fun k => hI _, Set.mem_iInter.2 fun k => hI' _⟩)
    (fun i => rLoc w φ ε c b i.1 i.2)
    (fun i j y hy => by
      rw [gm_rLoc w φ ε c b (𝟙 Y') y _ _ hy.1, gm_rLoc w φ ε c b (𝟙 Y') y _ _ hy.2]
      exact rVal_indep hw φ ε hc hb (𝟙 Y') y hy.1 hy.2)
  refine ⟨u, fun Z r z JL JM hJL hJM => ?_⟩
  have hz : r z ∈ rW L M f g φ (fun k => JL ((r ≫ φ k) ≫ f)) (fun k => JM ((r ≫ φ k) ≫ g)) :=
    ⟨Set.mem_iInter.2 fun k => hJL _, Set.mem_iInter.2 fun k => hJM _⟩
  have e := gm_rLoc w φ ε c b r z _ _ hz
  rw [← hu (_, _), gm_res r z _ hz] at e
  rw [val_of c r z JL (fun k => JL ((r ≫ φ k) ≫ f)) (fun k => by rw [Category.assoc]),
    val_of b r z JM (fun k => JM ((r ≫ φ k) ≫ g)) (fun k => by rw [Category.assoc])]
  exact mul_inv_eq_iff_eq_mul.1 e.symm

theorem exists_ratio_iso : ∀ (X Y F : Scheme.{0}) (L : LB X) (M : LB Y) (f : F ⟶ X) (g : F ⟶ Y), L.IsLB → M.IsLB →
    ∀ (w : LB.Iso (L.pull f) (M.pull g)), w.IsGen → ∀ (Y' : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y' ⟶ F))
    (φL : K → (Y' ⟶ X)) (φM : K → (Y' ⟶ Y)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φL ε))
    (b : LB.Gen (LB.LinComb M φM ε)), (∀ i, φ i ≫ f = φL i) → (∀ i, φ i ≫ g = φM i) → c.IsGen → b.IsGen →
    ∃ u : Γ(Y', ⊤)ˣ, Tr w φ φL φM ε c b u := by
  intro X Y F L M f g hL hM w hw Y' K _ φ φL φM ε c b h₁ h₂ hc hb
  obtain rfl : (fun k => φ k ≫ f) = φL := funext h₁
  obtain rfl : (fun k => φ k ≫ g) = φM := funext h₂
  exact exists_unit_ratio_of_generators hL hM hw φ ε hc hb

end Ratio

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicFamilyConjugateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_family_conjugate : ∀ (X : Scheme.{0}) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsHolTo B y → IsHolTo (star ⁻¹' B) (fun b => spMap (starRingEnd ℂ) ≫ y (star b)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.isHolTo_conj | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.isHolTo_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.isHolTo_conj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiLinearCombinationDetStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iota_multi_linear_combination_det : ∀ (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] (p : ℕ) (P : Matrix (Fin p) (Fin p) Ω) (v : Fin p → Vs),
    exteriorPower.ιMulti Ω p (fun i => ∑ k, P i k • v k) = P.det • exteriorPower.ιMulti Ω p v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ιMulti_matrix_transform | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ιMulti_matrix_transform | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ιMulti_matrix_transform <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistInverseIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem twBack : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H) (a : TwIso D g), ∃ a' : TwIso D g.symm, ∀ (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), (∀ (h : TwOK o g a) (h' : TwOK (twistObj o g a h) g.symm a'), Nonempty (ObjMap (twistObj (twistObj o g a h) g.symm a' h') o (𝟙 S))) ∧ ∀ (h : TwOK o g.symm a') (h' : TwOK (twistObj o g.symm a' h) g a), Nonempty (ObjMap (twistObj (twistObj o g.symm a' h) g a h') o (𝟙 S)) :=
  @PositivityTheory.UnitarySelfGeneration.tw_back

end GlobalTheory.CompanionTheory.Ar
end

