module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0370
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0260
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLTorsionEqPowOfTateSimilitudeStatement
section
open scoped NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_lTorsion_eq_pow_of_tateSimilitude : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) (l : ℕ),
    l.Prime → l ≠ p → Nat.card {q : Q // q ^ l = 1} = l ^ (D.m * D.n * Module.finrank ℚ D.F) := by
  first | (exact @GlobalTheory.UPel.HT.TateIsoO.card_pow_eq_one) | (exact GlobalTheory.UPel.HT.TateIsoO.card_pow_eq_one) | (intros; apply GlobalTheory.UPel.HT.TateIsoO.card_pow_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTwistedNormOneMulCardFixedUnitsStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_twistedNorm_one_mul_card_fixed_units : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')), (∀ x ∈ B, x.map s ∈ B) → Nat.card {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1} * Nat.card {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B} = Nat.card {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} := by
  first | (exact @GlobalTheory.Shin.card_nrm_one_mul_card_fixed) | (exact GlobalTheory.Shin.card_nrm_one_mul_card_fixed) | (intros; apply GlobalTheory.Shin.card_nrm_one_mul_card_fixed  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyLaEqPowStatement
section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_la_eq_pow (p : ℕ) [Fact p.Prime]
    (D : GlobalTheory.UPel.HT.Datum p) (c : 𝓞 D.F) :
    haveI := D.freeLa
    haveI := D.finLa
    LinearMap.charpoly (DistribSMul.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c)) =
      (LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ (D.m * D.n) :=
  GlobalTheory.UPel.HT.Datum.charpoly_La_eq_pow p D c
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityChangeFormula
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Set Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

namespace GlobalTheory.GlueCover

open GlobalTheory.ChartGlue

variable {n : ℕ}

section Null

variable {X ι : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

end Null

section Cover

variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}


set_option autoImplicit false in
open MeasureTheory Set Topology in
open scoped ENNReal in
variable {n : ℕ} in
variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A} in
omit [T2Space A] [T2Space B] in
theorem _root_.GlobalTheory.GlueCover.exists_sheet
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (_root_.ReciprocityTheory.L2DbarEstimates.Y.ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖_root_.GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (_root_.ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖_root_.GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {z : B}
    (hch : ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {U : Set B} (hUo : IsOpen U) (hzU : z ∈ U) :
    ∃ M : Set B, M ⊆ U ∧ IsOpen M ∧ z ∈ M ∧ IsOpen (m '' M) ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ m '' M →
        _root_.GlobalTheory.ChartGlue.glueMeas e' ρ' (M ∩ m ⁻¹' Q) = _root_.GlobalTheory.ChartGlue.glueMeas e ρ Q := by
  obtain ⟨i, j, hzj, hzi, hcompat⟩ := hch
  have hMo : IsOpen (U ∩ (e' j).source ∩ m ⁻¹' (e i).source) :=
    (hUo.inter (e' j).open_source).inter ((e i).open_source.preimage hm)
  refine ⟨U ∩ (e' j).source ∩ m ⁻¹' (e i).source, fun w hw => hw.1.1, hMo,
    ⟨⟨hzU, hzj⟩, hzi⟩, ?_, ?_⟩
  · have hm_eq : ∀ w ∈ U ∩ (e' j).source ∩ m ⁻¹' (e i).source,
        (e i).symm (e' j w) = m w := by
      intro w hw
      rw [(hcompat w hw.1.2 hw.2).1, (e i).left_inv hw.2]
    have himage : m '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source) =
        (e i).symm '' (e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source)) := by
      rw [Set.image_image]
      exact (Set.image_congr hm_eq).symm
    rw [himage]
    have hS : IsOpen (e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source)) :=
      (e' j).isOpen_image_of_subset_source hMo (fun w hw => hw.1.2)
    refine (e i).symm.isOpen_image_of_subset_source hS ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [OpenPartialHomeomorph.symm_source, (hcompat w hw.1.2 hw.2).1]
    exact (e i).map_source hw.2
  · intro Q hQ hQM
    have hQi : Q ⊆ (e i).source := by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := hQM hq
      exact hw.2
    have hPm : MeasurableSet (U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q) :=
      hMo.measurableSet.inter (hm.measurable hQ)
    have hPj : U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q ⊆ (e' j).source :=
      fun w hw => hw.1.1.2
    rw [_root_.GlobalTheory.ChartGlue.glueMeas_apply e' ρ' hd' hρ' j hPm hPj,
      _root_.GlobalTheory.ChartGlue.glueMeas_apply e ρ hd hρ i hQ hQi,
      _root_.GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hPm hPj,
      _root_.GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hQ hQi]
    have himg : e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q) = e i '' Q := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨m w, hw.2, ((hcompat w hw.1.1.2 hw.1.2).1).symm⟩
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨w, hw, rfl⟩ := hQM hq
        exact ⟨w, ⟨hw, hq⟩, (hcompat w hw.1.2 hw.2).1⟩
    rw [himg]
    refine setLIntegral_congr_fun (_root_.GlobalTheory.ChartGlue.measurableSet_image _ hQ hQi) ?_
    rintro v ⟨q, hq, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hQM hq
    beta_reduce
    rw [(e i).left_inv hw.2, ← (hcompat w hw.1.2 hw.2).1, (e' j).left_inv hw.1.2]
    exact (hcompat w hw.1.2 hw.2).2

end Cover

end GlobalTheory.GlueCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryTranslationInvariantPTorsionStatement
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_translation_invariant_pTorsion : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (x : G.A (n + 1)) (b : G.A 1), G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b → ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 ∧ ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 := by
  first | exact @GlobalTheory.PDivGroup.cobOne_transl_invariant | exact GlobalTheory.PDivGroup.cobOne_transl_invariant | (intros; apply GlobalTheory.PDivGroup.cobOne_transl_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleOneFormsCoboundaryOfRestrict
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory

theorem cocycle_one_forms_coboundary_of_restrict : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (ω : Ω[F.obj T⁄R]), (∀ t (u : T ⟶ G.obj t), p1 F u ω = 0) → ω = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → Ω[F.obj (G.obj t)⁄R]), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 F (G.map a) (s t u)) → ∃ ω : Ω[F.obj T⁄R], ∀ t u, p1 F u ω = s t u) → ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) → ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T) := by
  intro R _ C _ C' _ F G hSep hGlue κ hκ θ' hθ'
  have key : ∀ T : C, ∃ ω : Ω[F.obj T⁄R], ∀ t (u : T ⟶ G.obj t),
      p1 F u ω = θ' t - κ T (G.obj t) u := by
    intro T
    refine hGlue T (fun t u ↦ θ' t - κ T (G.obj t) u) ?_
    intro t t' u a
    simp only [map_sub]
    rw [hκ u (G.map a), hθ' a]
    abel
  choose θ hθ using key
  refine ⟨θ, fun T T' φ ↦ ?_⟩
  have h0 : κ T T' φ - θ T' + p1 F φ (θ T) = 0 := by
    refine hSep T' _ (fun t u ↦ ?_)
    have e1 := hκ φ u
    have e2 := hθ T' t u
    have e3 := hθ T t (φ ≫ u)
    rw [oneFormsMapOfFunctorMorphism_comp] at e3
    simp only [map_add (f := _), map_sub, e2, e3]
    rw [e1]
    abel
  rw [← sub_eq_zero]
  rw [← h0]
  abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOfSqZeroAgreePairsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comp_eq_of_sqZero_agree_pairs : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (K G : Over (Sp C)) (g g' : K ⟶ G), (∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ K), y ≫ g = y ≫ g') → ∀ (T : Over (Sp C)) (w w' : T ⟶ K), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ w = j ≫ w') → w' ≫ g = w' ≫ g' → w ≫ g = w ≫ g' := by
  first | (exact @GlobalTheory.comp_eq_of_sqZero_agree) | (exact GlobalTheory.comp_eq_of_sqZero_agree) | (intros; apply GlobalTheory.comp_eq_of_sqZero_agree  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatFamilyExtend
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory

theorem compat_family_extend : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) → ∀ g' : ∀ t, F.obj (G.obj t), (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' = mp F (G.map a) (g' t)) → ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ t, g (G.obj t) = g' t := by
  intro R _ C _ C' _ F G hsep hglue g' hg'
  choose g hg using fun T : C ↦ hglue T (fun t _ ↦ g' t) fun t t' _ a ↦ hg' a
  refine ⟨g, fun T T' φ ↦ ?_, fun t ↦ ?_⟩
  · refine sub_eq_zero.1 (hsep T' _ fun t u ↦ ?_)
    rw [map_sub, ← mp_comp, hg, hg, sub_self]
  · have h := hg (G.obj t) t (𝟙 _)
    rwa [mp_id] at h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFunctorDegreeTermAugmentedExactResolution
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem wExact_term_HC (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T]
    (Φ : T ⥤ Spcᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X)
    (h : Hyp R Φ a) (n : ℤ) : WExact (term (Φ ⋙ HC R F) n) a := by
  obtain ⟨π, hπ⟩ := GlobalTheory.T.bijective_HC_component_eval_of_maps R F n
  exact GlobalTheory.EtC.WExactProd.wexact_of_prod T U X a ℕ
    (fun k => Φ ⋙ ((evaluation _ PSh).obj (op (SimplexCategory.mk k))).op ⋙ (free R).op ⋙
      preadditiveYoneda.obj ((res R F).X (n - k)))
    (term (Φ ⋙ HC R F) n) (fun k => Functor.whiskerLeft Φ (π k)) (fun V => hπ (Φ.obj V))
    (fun k => wExact_preadditiveYoneda_of_injective R T (Φ ⋙ ((evaluation _ PSh).obj (op (SimplexCategory.mk k))).op)
      U X a ((res R F).X (n - k)) ((_root_.GlobalTheory.EtC.res_basic R F).1 (n - k)) (h (op (SimplexCategory.mk k))))

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvSmoothCompactSupport
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.ConvSmooth

theorem secondCountable_units (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] : SecondCountableTopology 𝔸ˣ := by
  haveI : ProperSpace 𝔸 := FiniteDimensional.proper ℝ 𝔸
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem isSmoothFun_density {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) {L : Set G} (hL : IsCompact L)
    {κ : G → ℂ} (hκ : h.IsSmoothFun κ) {p : G → NNReal} (hp : Measurable p)
    (hpi : Integrable (fun y => (p y : ℝ)) μ) (hpL : ∀ y ∉ L, p y = 0) :
    h.IsSmoothFun (fun z => ∫ y, κ (z * y) * ((p y : ℝ) : ℂ) ∂μ) := by
  set ν := μ.withDensity (fun y => (p y : ENNReal)) with hν
  have hlt : ∫⁻ y, (p y : ENNReal) ∂μ < ⊤ := by
    have := hpi.lintegral_lt_top
    simpa using this
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hlt⟩
  have hνL : ν Lᶜ = 0 := by
    rw [hν, withDensity_apply _ hL.isClosed.measurableSet.compl]
    have : ∀ y ∈ Lᶜ, (p y : ENNReal) = 0 := fun y hy => by simp [hpL y hy]
    rw [setLIntegral_congr_fun hL.isClosed.measurableSet.compl this]
    simp
  have key := _root_.GlobalTheory.isSmoothFun_integral_mul_right 𝔸 G 𝔤 h ν L hL hνL κ hκ
  convert key using 2 with z
  rw [hν, integral_withDensity_eq_integral_smul hp]
  congr 1
  funext y
  rw [NNReal.smul_def, Complex.real_smul, mul_comm]

end GlobalTheory.ConvSmooth

namespace GlobalTheory.ConvSmooth

theorem posPart_decomp (w : ℂ) :
    w = (((Real.toNNReal w.re : NNReal) : ℝ) : ℂ) - (((Real.toNNReal (-w.re) : NNReal) : ℝ) : ℂ) +
      Complex.I * ((((Real.toNNReal w.im : NNReal) : ℝ) : ℂ) -
        (((Real.toNNReal (-w.im) : NNReal) : ℝ) : ℂ)) := by
  apply Complex.ext <;> simp [Real.coe_toNNReal', max_zero_sub_max_neg_zero_eq_self]

theorem conv_smooth_compactSupport : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K : Set G, IsCompact K → ∀ κ a : G → ℂ, h.IsSmoothFun κ → HasCompactSupport κ → Measurable a → Integrable a μ → (∀ x ∉ K, a x = 0) → h.IsSmoothFun (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) ∧ HasCompactSupport (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) := by
  intro 𝔸 _ _ _ _ G 𝔤 h _ _ μ hμ K hK κ a hκ hκc ha hai haK
  letI : Inv (Set G) := Set.inv
  haveI : LocallyCompactSpace G := IsExpLieAlgebra.locallyCompactSpace (h := h)
  haveI := secondCountable_units 𝔸
  haveI : SecondCountableTopology G := Topology.IsInducing.subtypeVal.secondCountableTopology
  constructor
  · set b : G → ℂ := fun y => a y⁻¹ with hb
    have hbm : Measurable b := ha.comp measurable_inv
    have hbK : ∀ y ∉ K⁻¹, b y = 0 := fun y hy => haK _ (by simpa [Set.mem_inv] using hy)
    have hbi : Integrable b μ := by
      obtain ⟨B, hB⟩ := _root_.GlobalTheory.lintegral_inv_le_of_support_compact G μ hμ K hK
      refine ⟨hbm.aestronglyMeasurable, ?_⟩
      have h1 := hB (fun x => ‖a x‖ₑ) ha.enorm (fun x hx => by simp [haK x hx])
      exact lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.coe_lt_top hai.2)
    have hcv : ∀ z, ∫ x, κ x * a (x⁻¹ * z) ∂μ = ∫ y, κ (z * y) * b y ∂μ := by
      intro z
      rw [← integral_mul_left_eq_self (fun x => κ x * a (x⁻¹ * z)) z]
      congr 1; funext y; simp [hb, mul_inv_rev, mul_assoc]
    have hκcont : Continuous κ := by
      letI := h.chartedSpace
      exact ContMDiff.continuous hκ
    obtain ⟨C, hC⟩ := hκcont.bounded_above_of_compact_support hκc
    have hre : Integrable (fun y => (b y).re) μ := by simpa using hbi.re
    have him : Integrable (fun y => (b y).im) μ := by simpa using hbi.im
    have hpos : ∀ f : G → ℝ, Integrable f μ → Integrable (fun y => ((Real.toNNReal (f y) : NNReal) : ℝ)) μ :=
      fun f hf => by simpa [Real.coe_toNNReal'] using hf.pos_part
    have hK' : IsCompact K⁻¹ := hK.inv
    have hre' : Integrable (fun y => -(b y).re) μ := hre.neg
    have him' : Integrable (fun y => -(b y).im) μ := him.neg
    have S : ∀ f : G → ℝ, Measurable f → Integrable f μ → (∀ y ∉ K⁻¹, f y = 0) →
        h.IsSmoothFun (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (f y) : NNReal) : ℝ) : ℂ) ∂μ) :=
      fun f hfm hf hf0 => isSmoothFun_density h μ hK' hκ hfm.real_toNNReal (hpos f hf)
        (fun y hy => by simp [hf0 y hy])
    have hbre : ∀ y ∉ K⁻¹, (b y).re = 0 := fun y hy => by simp [hbK y hy]
    have hbim : ∀ y ∉ K⁻¹, (b y).im = 0 := fun y hy => by simp [hbK y hy]
    have s1 := S _ (Complex.measurable_re.comp hbm) hre hbre
    have s2 := S _ (Complex.measurable_re.comp hbm).neg hre' (fun y hy => by simp [hbre y hy])
    have s3 := S _ (Complex.measurable_im.comp hbm) him hbim
    have s4 := S _ (Complex.measurable_im.comp hbm).neg him' (fun y hy => by simp [hbim y hy])
    have hI : ∀ (z : G) (f : G → ℝ), Integrable f μ →
        Integrable (fun y => κ (z * y) * (((Real.toNNReal (f y) : NNReal) : ℝ) : ℂ)) μ := by
      intro z f hf
      refine ((hpos f hf).ofReal (𝕜 := ℂ)).bdd_mul (hκcont.comp (continuous_const_mul z)).aestronglyMeasurable (ae_of_all _ fun y => hC _)
    have hsum : (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) =
        (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (b y).re : NNReal) : ℝ) : ℂ) ∂μ) -
        (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (-(b y).re) : NNReal) : ℝ) : ℂ) ∂μ) +
        Complex.I • ((fun z => ∫ y, κ (z * y) * (((Real.toNNReal (b y).im : NNReal) : ℝ) : ℂ) ∂μ) -
        (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (-(b y).im) : NNReal) : ℝ) : ℂ) ∂μ)) := by
      funext z
      rw [hcv z]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have e : (fun y => κ (z * y) * b y) = fun y =>
          (κ (z * y) * (((Real.toNNReal (b y).re : NNReal) : ℝ) : ℂ) -
            κ (z * y) * (((Real.toNNReal (-(b y).re) : NNReal) : ℝ) : ℂ)) +
          Complex.I * (κ (z * y) * (((Real.toNNReal (b y).im : NNReal) : ℝ) : ℂ) -
            κ (z * y) * (((Real.toNNReal (-(b y).im) : NNReal) : ℝ) : ℂ)) := by
        funext y
        conv_lhs => rw [posPart_decomp (b y)]
        ring
      rw [e, integral_add ?_ ?_, integral_sub ?_ ?_, integral_const_mul, integral_sub ?_ ?_]
      all_goals first
        | exact hI z _ hre | exact hI z _ hre' | exact hI z _ him | exact hI z _ him'
        | exact (hI z _ hre).sub (hI z _ hre')
        | exact ((hI z _ him).sub (hI z _ him')).const_mul _
    rw [← h.mem_smoothFuns, hsum]
    exact Submodule.add_mem _ (Submodule.sub_mem _ s1 s2)
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ s3 s4))
  · refine HasCompactSupport.intro (hκc.mul hK) fun z hz => ?_
    have : (fun x => κ x * a (x⁻¹ * z)) = 0 := by
      funext x
      by_cases hx : x ∈ tsupport κ
      · have : x⁻¹ * z ∉ K := fun h' => hz ⟨x, hx, x⁻¹ * z, h', by simp⟩
        simp [haK _ this]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    simp only [this]; exact integral_zero' ..

end GlobalTheory.ConvSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_eq_class_of_isAW : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m), ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ := by
  first | (exact @GlobalTheory.EtC.Pair.cup_spec_full) | (exact GlobalTheory.EtC.Pair.cup_spec_full) | (intros; apply GlobalTheory.EtC.Pair.cup_spec_full  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullbackStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_hypercohomologyPullback : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ} (hk : n + m = k) a b, cpull ((chains R).map f) K k (μ.cup E' hk a b) = μ.cup E hk (cpull ((chains R).map f) I n a) (cpull ((chains R).map f) J m b) := by
  first | (exact @GlobalTheory.EtC.Pair.cup_pull) | (exact GlobalTheory.EtC.Pair.cup_pull) | (intros; apply GlobalTheory.EtC.Pair.cup_pull  <;> assumption)
end

