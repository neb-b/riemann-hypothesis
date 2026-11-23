module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0001
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInvariantVectorFieldsExpCoordsSmoothFrame
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.RealMetaplecticRepresentationHolds

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedSectionUpwardFamilyStandardCover
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

theorem glue_upward_of_cov : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Glue (G ⋙ F) Sg := by
  intro R _ C _ C' _ F G _ _ H hdir t Sg hup hcov s hs
  have key : ∀ (t₁ t₂ : C') (a₁ : t ⟶ t₁) (a₂ : t ⟶ t₂), Sg t₁ a₁ → Sg t₂ a₂ → ∀ (S : C)
      (w₁ : G.obj t₁ ⟶ S) (w₂ : G.obj t₂ ⟶ S), mp F w₁ (s t₁ a₁) = mp F w₂ (s t₂ a₂) := by
    intro t₁ t₂ a₁ a₂ h₁ h₂ S w₁ w₂
    refine sub_eq_zero.1 (Basis.eq_zero_of_local F G H hdir ⟨w₁⟩ ⟨w₂⟩ _
      fun t₃ S' ψ ⟨b₁⟩ ⟨b₂⟩ ⟨g⟩ ↦ ?_)
    have e1 : mp F ψ (mp F w₁ (s t₁ a₁)) = mp F g (s t₃ (a₁ ≫ b₁)) := by
      rw [hs t₁ t₃ a₁ b₁ h₁, ← mp_comp]
      change _ = mp F g (mp F (G.map b₁) _)
      rw [← mp_comp F (G.map b₁) g, Subsingleton.elim (G.map b₁ ≫ g) (w₁ ≫ ψ)]
    have e2 : mp F ψ (mp F w₂ (s t₂ a₂)) = mp F g (s t₃ (a₂ ≫ b₂)) := by
      rw [hs t₂ t₃ a₂ b₂ h₂, ← mp_comp]
      change _ = mp F g (mp F (G.map b₂) _)
      rw [← mp_comp F (G.map b₂) g, Subsingleton.elim (G.map b₂ ≫ g) (w₂ ≫ ψ)]
    have e3 : a₁ ≫ b₁ = a₂ ≫ b₂ := Subsingleton.elim _ _
    rw [map_sub, e1, e2, e3, sub_self]
  obtain ⟨n, b, hb, hb'⟩ := hcov
  have hex : ∀ S (u : G.obj t ⟶ S), ∃ y : F.obj S, (∃ i, IsUnit (mp F u (b i))) →
      ∃ (t' : C') (a : t ⟶ t') (w : G.obj t' ⟶ S), Sg t' a ∧ mp F w (s t' a) = y := by
    intro S u
    by_cases h : ∃ i, IsUnit (mp F u (b i))
    · obtain ⟨i, hi⟩ := h
      obtain ⟨t', a, ha, ⟨w⟩⟩ := hb' i S u hi
      exact ⟨mp F w (s t' a), fun _ ↦ ⟨t', a, w, ha, rfl⟩⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose σ hσ using hex
  obtain ⟨x, hx⟩ := glue_std (H := H) (hb := hb) σ fun S S' u ψ hp ↦ by
    obtain ⟨t₁, a₁, w₁, h₁, e₁⟩ := hσ S u hp
    obtain ⟨i, hi⟩ := hp
    have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi.map _
    obtain ⟨t₂, a₂, w₂, h₂, e₂⟩ := hσ S' (u ≫ ψ) ⟨i, hi'⟩
    rw [← e₁, ← e₂, ← mp_comp]
    exact key _ _ _ _ h₂ h₁ _ _ _
  refine ⟨x, fun t' a ha ↦ ?_⟩
  change mp F (G.map a) x = s t' a
  refine sub_eq_zero.1 (sep_std H (Basis.span_map_eq_top F (G.map a) hb) _ fun S' ψ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F (G.map a ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
  obtain ⟨t₂, a₂, w₂, h₂, e₂⟩ := hσ S' (G.map a ≫ ψ) ⟨i, hi'⟩
  rw [map_sub, ← mp_comp, hx _ _ ⟨i, hi'⟩, ← e₂, key t₂ t' a₂ a h₂ ha S' w₂ ψ, sub_self]

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolUnifPullAlongGroupHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace PullUnifHom

open GlobalTheory.PullHermitian

variable {X Y : Scheme.{0}}

lemma chart_pull_iff' (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (j : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull f).U j ↔ ⊤ ≤ (x ≫ f) ⁻¹ᵁ L.U (j PUnit.unit) :=
  ⟨fun h _ hp => Set.mem_iInter.1 (h hp) PUnit.unit, fun h _ hp => Set.mem_iInter.2 fun _ => h hp⟩

lemma le_left' {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ U :=
  h.trans (fun _ hp => And.left hp)

lemma le_right' {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ V :=
  h.trans (fun _ hp => And.right hp)

lemma valAt'_pull_g' (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (i j : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull f).U i ⊓ (L.pull f).U j)) :
    valAt' x ((L.pull f).U i ⊓ (L.pull f).U j) ((L.pull f).g i j).val =
      valAt' (x ≫ f) (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))
        (L.g (i PUnit.unit) (j PUnit.unit)).val := by
  have hi := (chart_pull_iff' x L f i).1 (le_left' h)
  have hj := (chart_pull_iff' x L f j).1 (le_right' h)
  rw [valAt'_eq_unitVal x h, valAt'_eq_unitVal _ (inf_of _ hi hj)]
  have := unitVal_linComb x L f 1 (i PUnit.unit) (j PUnit.unit) h (inf_of _ hi hj)
  exact congrArg Units.val (this.trans (zpow_one _))

theorem exists_holUnif_pull_hom : ∀ (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B] (φ : A ⟶ B) (L : LB B.left) (g : ℕ) (u' : HolUnif B L g)
    (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ' : u'.Λ → ℂ),
    (∀ z w, ex (z + w) = ex z * ex w) → Function.Surjective ex → (∀ z, ex z = 1 ↔ z ∈ Λ) →
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (ex z).left U f) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U}) →
    (∀ z, ex z ≫ φ = u'.ex z) → Λ ≤ u'.Λ → u'.IsAH Hm χ' →
    ∃ (u : HolUnif A (L.pull φ.left) g) (χ : u.Λ → ℂ), (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧ u.IsAH Hm χ := by
  intro A B _ _ φ L g u' ex Λ Hm χ' hadd honto hker hdisc hfull hhol hφ hΛ hAH
  have keyl : ∀ z, (ex z).left ≫ φ.left = (u'.ex z).left := fun z => by rw [← Over.comp_left, hφ]
  have hch : ∀ (j : (L.pull φ.left).ι) z, (⊤ ≤ (ex z).left ⁻¹ᵁ (L.pull φ.left).U j ↔
      ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)) := fun j z =>
    (chart_pull_iff' _ L _ j).trans (iff_of_eq (by rw [keyl z]))
  let u : HolUnif A (L.pull φ.left) g :=
    ⟨ex, hadd, honto, Λ, hker, hdisc, hfull, hhol, fun j z => u'.fr (j PUnit.unit) z,
     fun j => (u'.fr_hol (j PUnit.unit)).mono (fun z hz => (hch j z).1 hz),
     fun j z hz => u'.fr_ne _ _ ((hch j z).1 hz),
     fun i j z h => by
        have hi := (hch i z).1 (le_left' h)
        have hj := (hch j z).1 (le_right' h)
        show u'.fr (i PUnit.unit) z = _ * u'.fr (j PUnit.unit) z
        rw [valAt'_pull_g' _ L _ i j h, keyl z]
        exact u'.fr_compat _ _ _ (inf_of _ hi hj)⟩
  refine ⟨u, fun l => χ' ⟨l.1, hΛ l.2⟩, fun w => Iff.rfl, ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hAH
  exact ⟨h1, h2, fun l => h3 _, fun l i z hz => h4 ⟨l.1, hΛ l.2⟩ (i PUnit.unit) z ((hch i z).1 hz)⟩

end PullUnifHom
end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImagQuadraticSubfieldOfToricCMFieldData
section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped IntermediateField

namespace GlobalTheory.QuadInHost

theorem exists_quadField : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → d % 4 = 3 → ∀ (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ K : IntermediateField ℚ E, Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ ∃ φK : K →+* ℂ, (∀ i, (φ i).comp (algebraMap K E) = φK) ∧ (starRingEnd ℂ).comp φK ≠ φK ∧ IsLatOf φK 1 Λ := by
  intro E _ _ I _ d φ hF hd4 Λ hΛ
  obtain ⟨hp, hd, -, -, -, hI, -, w, hw, hφw⟩ := hF
  have hd0 : (0 : ℚ) < d := by exact_mod_cast hp.pos
  obtain ⟨i₀⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  have hm : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ) : Polynomial ℚ).Monic := by monicity!
  have he : Polynomial.aeval w (Polynomial.X ^ 2 + Polynomial.C (d : ℚ) : Polynomial ℚ) = 0 := by
    simp [hw]
  have hi : IsIntegral ℚ w := ⟨_, hm, he⟩
  have h2 : Module.finrank ℚ ℚ⟮w⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank hi]
    refine le_antisymm ((Polynomial.natDegree_le_natDegree (minpoly.min ℚ w hm he)).trans
      (by compute_degree)) ((minpoly.two_le_natDegree_iff hi).2 ?_)
    rintro ⟨q, hq⟩
    have h1 : (algebraMap ℚ E q) ^ 2 = -(d : E) := by rw [hq]; exact hw
    have h3 : q ^ 2 = -(d : ℚ) := (algebraMap ℚ E).injective (by simpa using h1)
    nlinarith [sq_nonneg q]
  let r : ℚ⟮w⟯ := IntermediateField.AdjoinSimple.gen ℚ w
  have hr : r ^ 2 = -(d : ℚ⟮w⟯) := Subtype.ext (by simpa [r] using hw)
  let φK : ℚ⟮w⟯ →+* ℂ := (φ i₀).comp (algebraMap ℚ⟮w⟯ E)
  have hφr : ∀ i, (φ i).comp (algebraMap ℚ⟮w⟯ E) r = Complex.I * (Real.sqrt d : ℂ) := fun i => hφw i
  have hsq : (Real.sqrt d : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hp.pos)
    exact_mod_cast this.ne'
  refine ⟨ℚ⟮w⟯, h2, GlobalTheory.discr_eq_neg_of_sq_eq h2 hp.squarefree hd4 hr, φK, ?_, ?_, ?_⟩
  · intro i
    have := (IntermediateField.adjoin.powerBasis hi).algHom_ext
      (f := ((φ i).comp (algebraMap ℚ⟮w⟯ E)).toRatAlgHom) (g := φK.toRatAlgHom)
      (by simp only [IntermediateField.adjoin.powerBasis_gen]; exact (hφr i).trans (hφr i₀).symm)
    exact congrArg AlgHom.toRingHom this
  · intro h
    have := congrArg (fun f => f r) h
    simp only [RingHom.comp_apply] at this
    change starRingEnd ℂ (φK r) = φK r at this
    rw [show φK r = _ from hφr i₀] at this
    simp [Complex.conj_ofReal] at this
    have h0 : (2 * Complex.I) * (Real.sqrt d : ℂ) = 0 := by linear_combination -this
    rcases mul_eq_zero.1 h0 with h0 | h0
    · simp at h0
    · exact hsq h0
  · obtain ⟨ω, hω2, hgen⟩ := GlobalTheory.exists_integer_generator_of_sq_eq_neg h2 hp.squarefree hd4 hr
    have hφω : φK ω = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 := by
      have := congrArg φK hω2
      rw [map_mul, map_add (f := _), map_one, map_ofNat, show φK r = _ from hφr i₀] at this
      linear_combination this / 2
    unfold IsLatOf
    ext x
    rw [SetLike.mem_coe, hΛ x]
    constructor
    · rintro ⟨hx, a, b, rfl⟩
      let y : ℚ⟮w⟯ := a + b * r
      have hy : φK y = a + b * (Complex.I * (Real.sqrt d : ℂ)) := by
        simp only [y, map_add (f := _), map_mul, map_ratCast, show φK r = _ from hφr i₀]
      have hint : IsIntegral ℤ y := by
        rw [← hy] at hx
        exact (isIntegral_algHom_iff φK.toIntAlgHom φK.injective).1 hx
      refine ⟨y, ?_, hy⟩
      rw [SetLike.mem_coe, FractionalIdeal.mem_one_iff]
      exact ⟨⟨y, hint⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, FractionalIdeal.mem_one_iff] at hy
      obtain ⟨c, rfl⟩ := hy
      refine ⟨(RingOfIntegers.isIntegral_coe c).map φK.toIntAlgHom, ?_⟩
      obtain ⟨m, n, rfl⟩ := hgen c
      refine ⟨m + n / 2, n / 2, ?_⟩
      change φK ((m + n * ω : 𝓞 ℚ⟮w⟯) : ℚ⟮w⟯) = _
      push_cast
      simp only [map_add (f := _), map_mul, hφω]
      simp
      ring

end GlobalTheory.QuadInHost
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInteriorEstimateDerivWordPolyLaplacian
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff Manifold

namespace GlobalTheory

open ZetaZeros.D.EllReg GlobalTheory.HCA

theorem foldr_rightDeriv_leftTranslate {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    (F : G → ℂ) (g : G) (l : List 𝔤) :
    l.foldr h.rightDeriv (fun y => F (g * y)) = fun y => l.foldr h.rightDeriv F (g * y) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    funext y
    simp only [IsExpLieAlgebra.rightDeriv, mul_assoc]

theorem interior_word_bound : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∃ Kc : Set G, IsCompact Kc ∧ ∀ l : List 𝔤, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ (g : G) (M : ℝ), (∀ y ∈ Kc, ‖(f : G → ℂ) (g * y)‖ ≤ M) → ‖l.foldr h.rightDeriv (f : G → ℂ) g‖ ≤ C * M := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP
  obtain ⟨r₁, hr₁, m, a, ha, hell, hsol⟩ := GlobalTheory.T.exists_elliptic_weakSol_of_polynomial_laplacian_zero 𝔸 G 𝔤 h d b P hP
  obtain ⟨r₂, hr₂, c, hc⟩ := _root_.GlobalTheory.ExpCoordFrame.leftInvariant_frame 𝔸 G 𝔤 h d b
  refine ⟨(fun x : E d => h.expG (coordEquiv b x)) '' Metric.closedBall 0 r₁,
    (isCompact_closedBall 0 r₁).image (h.continuous_expG.comp (coordEquiv b).continuous), ?_⟩
  intro l
  obtain ⟨al, -, hword⟩ := _root_.GlobalTheory.WordExp.word_apOp 𝔸 G 𝔤 h d b r₂ c hc l
  have hsup : ∀ w : List (Fin d), ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E d → ℂ, ContinuousOn u (Metric.ball 0 r₁) →
      WeakSol (oneSys m a) (Metric.ball 0 r₁) u → ∀ M : ℝ, (∀ x ∈ Metric.ball (0 : E d) r₁, ‖u x‖ ≤ M) →
      ‖dw w u 0‖ ≤ C * M := fun w =>
    _root_.GlobalTheory.HCA.dw_le_sup d Unit (oneSys m a) (Metric.ball 0 r₁) Metric.isOpen_ball (fun _ n w => ha n w)
      (fun x hx ξ hξ => ⟨(), hell x hx ξ hξ⟩) w 0 (Metric.mem_ball_self hr₁)
  choose Cw hCw0 hCw using hsup
  refine ⟨∑ n ∈ Finset.range (l.length + 1), ∑ w : Fin n → Fin d, ‖al n w 0‖ * Cw (List.ofFn w),
    Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun w _ => mul_nonneg (norm_nonneg _) (hCw0 _), ?_⟩
  intro f hf g M hM
  have hfs : h.IsSmoothFun (f : G → ℂ) := f.2
  have hf' : h.IsSmoothFun (fun y : G => (f : G → ℂ) (g * y)) := by
    letI := h.chartedSpace
    haveI := h.lieGroup ∞
    exact ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hfs (contMDiff_const.mul contMDiff_id)
  have key : l.foldr h.rightDeriv (f : G → ℂ) g =
      apOp l.length al (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))) 0 := by
    have := hword _ hf' 0 (Metric.mem_ball_self hr₂)
    rw [foldr_rightDeriv_leftTranslate] at this
    simpa [coordEquiv_zero] using this
  have hu : ContinuousOn (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))) (Metric.ball 0 r₁) :=
    (h.contDiff_comp_coordEquiv hfs g b).continuous.continuousOn
  have hbd : ∀ x ∈ Metric.ball (0 : E d) r₁, ‖(f : G → ℂ) (g * h.expG (coordEquiv b x))‖ ≤ M :=
    fun x hx => hM _ ⟨x, Metric.ball_subset_closedBall hx, rfl⟩
  have hdw : ∀ w : List (Fin d),
      ‖dw w (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))) 0‖ ≤ Cw w * M :=
    fun w => hCw w _ hu (hsol f hf g) M hbd
  rw [key, apOp]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun n _ => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hdw _) (norm_nonneg _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointHol
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.TangentOrigin

namespace GlobalTheory.AnPer

theorem exists_point_hol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens E)
    (X : Scheme.{0}) (e : E → (Sp ℂ ⟶ X)) (U : X.Opens), IsAffineOpen U → IsHolTo (W : Set E) e → (∀ p ∈ W, ⊤ ≤ e p ⁻¹ᵁ U) →
    ∃ x : Sp (Hol W) ⟶ X, ⊤ ≤ x ⁻¹ᵁ U ∧ ∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x = e p := by
  intro E _ _ _ W X e U hU he hW
  have ha : ∀ f : Γ(X, U), AnalyticOnNhd ℂ (fun p => valAt' (e p) U f) W := fun f p hp =>
    SCV.analyticAt_of_differentiableOn (he U f).2 ((he U f).1.mem_nhds ⟨hp, hW p hp⟩)
  have hv : ∀ (f : Γ(X, U)) (p : E) (hp : p ∈ W), (Hol.mk _ (ha f)).fn p = evalPt (e p) U (hW p hp) f :=
    fun f p hp => (Hol.fn_mk _ _ hp).trans (valAt'_eq_evalPt _ _ _ _)
  let ψ : Γ(X, U) →+* Hol W :=
    { toFun := fun f => Hol.mk _ (ha f)
      map_one' := Hol.ext_fn fun p hp => by rw [hv _ p hp, map_one, ← Hol.ev_apply p hp, map_one]
      map_mul' := fun f g => Hol.ext_fn fun p hp => by rw [Hol.fn_mul _ _ hp, hv _ p hp, hv _ p hp, hv _ p hp, map_mul]
      map_zero' := Hol.ext_fn fun p hp => by rw [hv _ p hp, map_zero, ← Hol.ev_apply p hp, map_zero]
      map_add' := fun f g => Hol.ext_fn fun p hp => by rw [Hol.fn_add _ _ hp, hv _ p hp, hv _ p hp, hv _ p hp, map_add (f := _)] }
  obtain ⟨x, hx, hxψ⟩ := exists_evalPt_eq hU ψ
  have h' : ∀ (p : E) (hp : p ∈ W), ⊤ ≤ (spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x) ⁻¹ᵁ U := fun p hp q _ => hx trivial
  refine ⟨x, hx, fun p hp => ext_evalPt hU (h' p hp) (hW p hp) (RingHom.ext fun f => ?_)⟩
  rw [evalPt_spMap_comp _ x U hx, hxψ]
  exact (Hol.ev_apply p hp _).trans (hv f p hp)

theorem point_hol_ext : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E)
    (X S : Scheme.{0}) (s : X ⟶ S) [IsSeparated s] (x x' : Sp (Hol W) ⟶ X), x ≫ s = x' ≫ s →
    (∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x = spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x') → x = x' := by
  intro E _ _ W X S s _ x x' hs h
  have : _root_.IsReduced (Hol W) := isReduced_of_injective (holSub W).val Subtype.val_injective
  suffices IsDominant (equalizer.ι x x') from
    ext_of_isDominant_of_isSeparated s hs (equalizer.ι x x') (equalizer.condition _ _)
  refine ⟨?_⟩
  have hd : Dense (Set.range fun p : W => PrimeSpectrum.comap (Hol.ev p.1 p.2 : Hol W →+* ℂ) default) := by
    rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro f hf
    have : f = 0 := Hol.ext_fn fun p hp => by
      have h1 := (PrimeSpectrum.mem_vanishingIdeal _ _).1 hf _ ⟨⟨p, hp⟩, rfl⟩
      have h2 : Hol.ev p hp f ∈ (default : PrimeSpectrum ℂ).asIdeal := h1
      rw [Ideal.eq_bot_of_prime (default : PrimeSpectrum ℂ).asIdeal, Ideal.mem_bot] at h2
      rw [← Hol.ev_apply p hp, ← Hol.ev_apply p hp, h2, map_zero]
    rw [this]
    exact zero_mem _
  refine Dense.mono ?_ hd
  rintro _ ⟨p, rfl⟩
  refine ⟨equalizer.lift _ (h p.1 p.2) (default : PrimeSpectrum ℂ), ?_⟩
  exact congrArg (fun m : Sp ℂ ⟶ Sp (Hol W) => m (default : PrimeSpectrum ℂ)) (equalizer.lift_ι _ (h p.1 p.2))

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointMemTranslates
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgClosedFibre

theorem exists_point_mem_translates :
    ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IrreducibleSpace (Over.mk t ⊗ P.A).left → ∀ (U : (Over.mk t ⊗ P.A).left.Opens),
      (U : Set (Over.mk t ⊗ P.A).left).Nonempty → ∀ (a c : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)),
      ∃ u : Over.mk t ⟶ P.A, (lift (𝟙 (Over.mk t)) (c * u * a)).left p ∈ U ∧
        (lift (𝟙 (Over.mk t)) (u⁻¹ * a)).left p ∈ U := by
  intro S P K _ _ t hirr U hU a c p
  let T : Over S := Over.mk t
  let E : Over S := T ⊗ P.A
  have hsm : Smooth P.A.hom := P.isAb.smooth
  have hlft : LocallyOfFiniteType (fst T P.A).left := by
    change LocallyOfFiniteType (pullback.fst t P.A.hom)
    infer_instance
  have hJ0 : JacobsonSpace T.left := by
    change JacobsonSpace (PrimeSpectrum K)
    infer_instance
  have hJ : JacobsonSpace E.left := LocallyOfFiniteType.jacobsonSpace (fst T P.A).left
  let g₁ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ c) * snd T P.A * (fst T P.A ≫ a))
  let g₂ : E ⟶ E := lift (fst T P.A) ((snd T P.A)⁻¹ * (fst T P.A ≫ a))
  let h₁ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ c)⁻¹ * snd T P.A * (fst T P.A ≫ a)⁻¹)
  let h₂ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ a) * (snd T P.A)⁻¹)
  have e₁ : h₁ ≫ g₁ = 𝟙 E := by
    ext1
    · simp [g₁, h₁]
    · simp [g₁, h₁, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]
      exact (Category.id_comp _).symm
  have e₂ : h₂ ≫ g₂ = 𝟙 E := by
    ext1
    · simp [g₂, h₂]
    · simp [g₂, h₂, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]
      exact (Category.id_comp _).symm
  have ne : ∀ {f g : E ⟶ E}, g ≫ f = 𝟙 E → ((f.left ⁻¹ᵁ U : E.left.Opens) : Set E.left).Nonempty := by
    intro f g h
    obtain ⟨w, hw⟩ := hU
    refine ⟨g.left w, ?_⟩
    change f.left (g.left w) ∈ U
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
    exact hw
  have hin := nonempty_preirreducible_inter (TopologicalSpace.Opens.isOpen _)
      (TopologicalSpace.Opens.isOpen _) (ne e₁) (ne e₂)
  obtain ⟨z, hz, hc⟩ := nonempty_inter_closedPoints hin
    ((TopologicalSpace.Opens.isOpen _).inter (TopologicalSpace.Opens.isOpen _)).isLocallyClosed
  let q := pointOfClosedPoint (fst T P.A).left z hc
  have hq : q ≫ (fst T P.A).left = 𝟙 _ := pointOfClosedPoint_comp _ z hc
  have hqw : q ≫ E.hom = t := by
    rw [← Over.w (fst T P.A), ← Category.assoc, hq, Category.id_comp]
    rfl
  let Q : T ⟶ E := Over.homMk q hqw
  have hQf : Q ≫ fst T P.A = 𝟙 T := by
    ext1
    exact hq
  have hQf' : ∀ (f : T ⟶ P.A), Q ≫ fst T P.A ≫ f = f := fun f => by
    rw [← Category.assoc, hQf, Category.id_comp]
  have hqp : q p = z := pointOfClosedPoint_apply _ z hc p
  refine ⟨Q ≫ snd T P.A, ?_, ?_⟩
  · have hQ : lift (𝟙 T) (c * (Q ≫ snd T P.A) * a) = Q ≫ g₁ := by
      ext1
      · simp only [lift_fst, Category.assoc, g₁, hQf]
      · simp only [lift_snd, Category.assoc, g₁, MonObj.comp_mul, hQf']
    rw [hQ, Over.comp_left, Scheme.Hom.comp_apply]
    change g₁.left (q p) ∈ U
    rw [hqp]
    exact hz.1
  · have hQ : lift (𝟙 T) ((Q ≫ snd T P.A)⁻¹ * a) = Q ≫ g₂ := by
      ext1
      · simp only [lift_fst, Category.assoc, g₂, hQf]
      · simp only [lift_snd, Category.assoc, g₂, MonObj.comp_mul, GrpObj.comp_inv, hQf']
    rw [hQ, Over.comp_left, Scheme.Hom.comp_apply]
    change g₂.left (q p) ∈ U
    rw [hqp]
    exact hz.2

end GlobalTheory.AlgClosedFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateTwistMulDegreeZeroHomStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateTwist_mul_degreeZero_hom : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), ∃ φ : tw q k ⟶ K.X 0, ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) := by
  first | (exact @GlobalTheory.EtC.twist_mul_map) | (exact GlobalTheory.EtC.twist_mul_map) | (intros; apply GlobalTheory.EtC.twist_mul_map  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAffineLineMorphismToProperAcrossPointStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_affineLine_morphism_to_proper_across_point : ∀ (k : Type) [Field k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k) (c : k), P ≠ 0 → ∀ u : Sp (Localization.Away (P * (Polynomial.X - Polynomial.C c))) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away (P * (Polynomial.X - Polynomial.C c)))) → ∃ v : Sp (Localization.Away P) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (Polynomial.X - Polynomial.C c))) P (Polynomial.X - Polynomial.C c)) ≫ v = u := by
  first | exact @GlobalTheory.AffineLineExt.extend | exact GlobalTheory.AffineLineExt.extend | (intros; apply GlobalTheory.AffineLineExt.extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMetaplecticRepresentationHolds
section
theorem GlobalTheory.Published.realMetaplecticRepresentation_holds : GlobalTheory.Published.RealMetaplecticRepresentation :=
  CompanionTheory.ThKR.realMetaplecticRepresentation_holds
end

