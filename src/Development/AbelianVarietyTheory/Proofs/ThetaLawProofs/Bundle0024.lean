module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.JacNeZeroIffSpanEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSectionOfTransversal
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.HenselZero

theorem exists_factor_stalk {X : Scheme.{0}} {T : CommRingCat.{0}} [IsLocalRing T] (w : Spec T ⟶ X) {y : X}
    (hw : w (closedPoint T) = y) : ∃ χ : X.presheaf.stalk y ⟶ T, Spec.map χ ≫ X.fromSpecStalk y = w := by
  subst hw
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk w⟩

theorem exists_formallySmooth_stalk {O : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec O) [Smooth p] (y : X) :
    ∃ α : O ⟶ X.presheaf.stalk y, α.hom.FormallySmooth ∧ Spec.map α = X.fromSpecStalk y ≫ p := by
  let τ : O ⟶ (Spec O).presheaf.stalk (p y) := StructureSheaf.toStalk O (p y)
  refine ⟨τ ≫ p.stalkMap y, ?_, ?_⟩
  · have hs : (p.stalkMap y).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp (p.smoothLocus_eq_top.ge (Set.mem_univ y))
    letI : Algebra O ((Spec O).presheaf.stalk (p y)) := StructureSheaf.stalkAlgebra O (p y)
    have := (p y).isPrime
    have : IsLocalization.AtPrime ((Spec O).presheaf.stalk (p y)) (p y).asIdeal :=
      StructureSheaf.IsLocalization.to_stalk O (p y)
    have h₀ : Algebra.FormallySmooth O ((Spec O).presheaf.stalk (p y)) :=
      Algebra.FormallySmooth.of_isLocalization (p y).asIdeal.primeCompl
    exact RingHom.FormallySmooth.comp (RingHom.formallySmooth_algebraMap.2 h₀) hs
  · have e : (Spec O).fromSpecStalk (p y) = Spec.map τ := Spec.fromSpecStalk_eq' _ _
    rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk, e]

theorem fromSpecStalk_mem_basicOpen {X : Scheme.{0}} {y : X} {U : X.Opens} (hy : y ∈ U) (f : Γ(X, U))
    (q : Spec (X.presheaf.stalk y)) (hq : (X.presheaf.germ U y hy).hom f ∉ q.asIdeal) :
    X.fromSpecStalk y q ∈ X.basicOpen f := by
  have ht : ⊤ ≤ X.fromSpecStalk y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (X.fromSpecStalk y)
    (by rwa [Scheme.fromSpecStalk_closedPoint])).ge
  rw [← Scheme.Hom.mem_preimage, Scheme.preimage_basicOpen, Scheme.fromSpecStalk_app hy]
  simp only [CommRingCat.comp_apply]
  rw [Scheme.basicOpen_res, basicOpen_eq_of_affine]
  exact ⟨ht trivial, hq⟩

section Fibre

variable {O : Type} [CommRing O] [IsLocalRing O] {X Y : Scheme.{0}} {p : X ⟶ Sp O} {q : Y ⟶ Sp (ResidueField O)}
  {φ : Y ⟶ X} (hφ : IsPullback φ q p (spMap (residue O)))
include hφ

theorem isClosedImmersion_fibre : IsClosedImmersion φ :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) hφ.flip
    (IsClosedImmersion.spec_of_surjective _ residue_surjective)

theorem maximalIdeal_le_span_sup {ι : Type} (y : Y) (α : CommRingCat.of O ⟶ X.presheaf.stalk (φ y))
    (hα : Spec.map α = X.fromSpecStalk (φ y) ≫ p) (f : ι → X.presheaf.stalk (φ y))
    (h : maximalIdeal _ ≤ Ideal.span (Set.range fun i => (φ.stalkMap y).hom (f i))) :
    maximalIdeal _ ≤ Ideal.span (Set.range f) ⊔ (maximalIdeal O).map α.hom := by
  have := isClosedImmersion_fibre hφ
  let I := (maximalIdeal O).map α.hom
  by_cases hI : I = ⊤
  · exact le_sup_of_le_right (le_top.trans hI.ge)
  have : Nontrivial (X.presheaf.stalk (φ y) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have : IsLocalRing (X.presheaf.stalk (φ y) ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk I) := .of_surjective _ Ideal.Quotient.mk_surjective
  let π : X.presheaf.stalk (φ y) ⟶ .of (X.presheaf.stalk (φ y) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let β : ResidueField O →+* X.presheaf.stalk (φ y) ⧸ I := Ideal.quotientMap I α.hom Ideal.le_comap_map
  have hw : (Spec.map π ≫ X.fromSpecStalk (φ y)) ≫ p = spMap β ≫ spMap (residue O) := by
    rw [Category.assoc, ← hα, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨χ, hχ⟩ := exists_factor_stalk (hφ.lift _ _ hw) (y := y) (φ.isClosedEmbedding.injective (by
    refine (congrArg (fun g => g (closedPoint (X.presheaf.stalk (φ y) ⧸ I))) (hφ.lift_fst _ _ hw)).trans ?_
    exact (congrArg (X.fromSpecStalk (φ y)) (comap_closedPoint (Ideal.Quotient.mk I))).trans
      Scheme.fromSpecStalk_closedPoint))
  have e : φ.stalkMap y ≫ χ = π := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (φ y)), Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      reassoc_of% hχ, hφ.lift_fst]
  have e' : ∀ a, χ.hom ((φ.stalkMap y).hom a) = Ideal.Quotient.mk I a := fun a => congrArg (fun g => g.hom a) e
  intro a ha
  obtain hr := Ideal.mem_map_of_mem χ.hom (h (map_nonunit (φ.stalkMap y).hom a ha))
  rw [e', Ideal.map_span, ← Set.range_comp] at hr
  have hr' : Ideal.Quotient.mk I a ∈ (Ideal.span (Set.range f)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, ← Set.range_comp]
    exact (congrArg (fun F => _ ∈ Ideal.span (Set.range F)) (funext fun i => e' (f i))).mp hr
  exact Ideal.mem_quotient_iff_mem_sup.1 hr'

end Fibre

theorem exists_section_of_transversal {O ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Fintype ι] [DecidableEq ι] {X Y : Scheme.{0}} {p : X ⟶ Sp O} [Smooth p]
    {q : Y ⟶ Sp (ResidueField O)} {φ : Y ⟶ X} (hφ : IsPullback φ q p (spMap (residue O)))
    (t : Sp (ResidueField O) ⟶ Y) (ht : t ≫ q = 𝟙 _) (pt : Sp (ResidueField O)) {U : X.Opens} (hU : φ (t pt) ∈ U)
    (f : ι → Γ(X, U)) (hf : ∀ i, valT (t ≫ φ) U (f i) = 0)
    (hm : maximalIdeal _ ≤ Ideal.span (Set.range fun i => gs φ (t pt) U (f i)))
    (w : ι → (Sp (DualNumber (ResidueField O)) ⟶ Y))
    (hw₁ : ∀ k, spMap (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom ≫ w k = t)
    (hw₂ : ∀ k, w k ≫ q = spMap (algebraMap _ _))
    (hd : (Matrix.of fun i k => (valT (w k ≫ φ) U (f i)).snd).det ≠ 0) :
    ∃ z : Sp O ⟶ X, z ≫ p = 𝟙 _ ∧ spMap (residue O) ≫ z = t ≫ φ ∧ (∀ i, valT z U (f i) = 0) ∧
      ∀ y, y ⤳ φ (t pt) → (∀ i, y ∉ X.basicOpen (f i)) → ∃ r, z r = y := by
  obtain rfl : pt = closedPoint (ResidueField O) := Subsingleton.elim (α := PrimeSpectrum (ResidueField O)) _ _
  set y₀ := φ (t (closedPoint (ResidueField O))) with hy₀
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨α, hs, hα⟩ := exists_formallySmooth_stalk p y₀
  obtain ⟨u, hu⟩ := exists_factor_stalk (t ≫ φ) (y := y₀) rfl
  have : IsLocalRing (DualNumber (ResidueField O)) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _
  have hχ := fun k => exists_factor_stalk (w k ≫ φ) (y := y₀) (by
    have h1 : IsLocalHom (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom :=
      ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
    rw [← comap_closedPoint (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom,
      hy₀, ← hw₁ k]
    rfl)
  choose χ hχ using hχ
  letI := α.hom.toAlgebra
  have : Algebra.FormallySmooth O (X.presheaf.stalk y₀) := hs
  have e₁ : α ≫ u = CommRingCat.ofHom (residue O) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hu, hφ.w, reassoc_of% ht]
  have e₂ : ∀ k, χ k ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom = u := fun k => by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk y₀), Spec.map_comp, Category.assoc, hχ, hu, ← hw₁ k, Category.assoc]
  have e₃ : ∀ k, α ≫ χ k = CommRingCat.ofHom (residue O) ≫ CommRingCat.ofHom (algebraMap _ _) := fun k => by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hχ, hφ.w, reassoc_of% hw₂, Spec.map_comp]
  obtain ⟨ψ, hψ, hk⟩ := exists_algHom_ker_eq (O := O) (fun i => (X.presheaf.germ U y₀ hU).hom (f i)) u.hom
    (fun r => congrArg (fun g => g.hom r) e₁)
    (fun i => (JacGen.valT_specMap_fromSpecStalk hU u (f i)).symm.trans (hu ▸ hf i))
    (fun k => (χ k).hom) (fun k a => congrArg (fun g => g.hom a) (e₂ k))
    (fun k r => congrArg (fun g => g.hom r) (e₃ k))
    (by
      refine fun h => hd (Eq.trans ?_ h)
      congr 1
      ext i k
      rw [Matrix.of_apply, Matrix.of_apply, ← hχ, JacGen.valT_specMap_fromSpecStalk hU])
    (maximalIdeal_le_span_sup hφ _ α hα _ (hm.trans_eq (congrArg (fun F => Ideal.span (Set.range F))
      (funext fun i => (gs_eq φ _ U hU _).trans (Scheme.Hom.germ_stalkMap_apply φ U _ hU _).symm))))
  have hs' : Function.Surjective ψ := fun r => ⟨_, ψ.commutes r⟩
  refine ⟨spMap ψ.toRingHom ≫ X.fromSpecStalk y₀, ?_, ?_, fun i => ?_, fun y hy hyf => ?_⟩
  · rw [Category.assoc, ← hα, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact ψ.commutes r
  · rw [← hu, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact hψ a
  · exact (JacGen.valT_specMap_fromSpecStalk hU (CommRingCat.ofHom ψ.toRingHom) (f i)).trans
      (hk.ge (Ideal.subset_span ⟨i, rfl⟩))
  · obtain ⟨r, rfl⟩ : y ∈ Set.range (X.fromSpecStalk y₀) := by
      rw [Scheme.range_fromSpecStalk]
      exact hy
    obtain ⟨r', hr'⟩ : r ∈ Set.range (PrimeSpectrum.comap ψ.toRingHom) := by
      rw [range_comap_of_surjective _ _ hs']
      refine hk.le.trans (Ideal.span_le.2 ?_)
      rintro _ ⟨i, rfl⟩
      by_contra hn
      exact hyf i (fromSpecStalk_mem_basicOpen hU _ r hn)
    exact ⟨r', congrArg (X.fromSpecStalk y₀) hr'⟩

end GlobalTheory.HenselZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLevelIffAut
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.SimilTheta
open Matrix

variable {g : ℕ}

def lat (τ : Matrix (Fin g) (Fin g) ℂ) (k n : Fin g → ℤ) : Fin g → ℂ :=
  (fun i => (k i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))

def aut (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (k n : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a ⬝ᵥ (fun i => (k i : ℂ)) - b ⬝ᵥ (fun i => (n i : ℂ)) -
    ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z))

def tors (τ : Matrix (Fin g) (Fin g) ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (r : Fin 4) :
    Fin g → ℂ := (m : ℂ)⁻¹ • ∑ c, al r c • lat τ (k c) (n c)

def simTheta (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ)
    (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ) : ℂ :=
  (∏ r, thetaChar τ a b (∑ c, al r c • y c + tors τ al m k n r)) *
    Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.aut_ne_zero (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (k n : Fin g → ℤ) (z : Fin g → ℂ) :
    _root_.GlobalTheory.SimilTheta.aut τ a b k n z ≠ 0 :=
  Complex.exp_ne_zero _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.isLevel_iff_aut (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (l : ℕ) (F : (Fin g → ℂ) → ℂ) :
    _root_.GlobalTheory.KeyKa.IsLevel τ a b l F ↔ Differentiable ℂ F ∧ ∀ k n z, F (z + _root_.GlobalTheory.SimilTheta.lat τ k n) = _root_.GlobalTheory.SimilTheta.aut τ a b k n z ^ l * F z :=
  Iff.rfl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.lat_add (τ : Matrix (Fin g) (Fin g) ℂ) (k n k' n' : Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (k + k') (n + n') = _root_.GlobalTheory.SimilTheta.lat τ k n + _root_.GlobalTheory.SimilTheta.lat τ k' n' := by
  have h : (fun i => ((n + n') i : ℂ)) = (fun i => (n i : ℂ)) + fun i => (n' i : ℂ) := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_add]
  ext i
  simp only [Pi.add_apply, Int.cast_add]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.lat_zsmul (τ : Matrix (Fin g) (Fin g) ℂ) (s : ℤ) (k n : Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (s • k) (s • n) = s • _root_.GlobalTheory.SimilTheta.lat τ k n := by
  have h : (fun i => ((s • n) i : ℂ)) = (s : ℂ) • fun i => (n i : ℂ) := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
private theorem lat_zero_zero (τ : Matrix (Fin g) (Fin g) ℂ) :
    _root_.GlobalTheory.SimilTheta.lat τ 0 0 = 0 := by
  have h : (fun i : Fin g => (((0 : Fin g → ℤ) i : ℤ) : ℂ)) = 0 := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_zero]
  ext i
  simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.lat_sum (τ : Matrix (Fin g) (Fin g) ℂ) {K : Type} (s : Finset K) (k n : K → Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (∑ c ∈ s, k c) (∑ c ∈ s, n c) = ∑ c ∈ s, _root_.GlobalTheory.SimilTheta.lat τ (k c) (n c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lat_zero_zero τ
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc, Finset.sum_insert hc, _root_.GlobalTheory.SimilTheta.lat_add, ih]

end GlobalTheory.SimilTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.JacEqUnitMulDetPderiv
section
noncomputable section

namespace GlobalTheory.JacSer

section Algebra

open IsLocalRing MvPowerSeries GlobalTheory.SqZero

variable {O : Type} [CommRing O] [IsLocalRing O]

theorem isLocalRing_trivSqZeroExt (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] :
    IsLocalRing (TrivSqZeroExt O M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _


omit [IsLocalRing O] in
def dirPt {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) :
    MvPowerSeries (Fin n) O →ₐ[O] DualNumber O :=
  addDer ((inlS O O).comp e) (TrivSqZeroExt.inrHom O O ∘ₗ
      ∑ j, c j • (e.toLinearMap ∘ₗ (pderiv (R := O) j).toLinearMap))
    (fun a b => by
      ext
      · simp [TrivSqZeroExt.fst_sum]
      · simp [TrivSqZeroExt.snd_sum, Finset.mul_sum, ← Finset.sum_add_distrib, mul_add]
        exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)

omit [IsLocalRing O] in
theorem dirPt_fst {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) (a : MvPowerSeries (Fin n) O) :
    (dirPt e c a).fst = e a := add_zero (e a)

omit [IsLocalRing O] in
theorem dirPt_snd {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) (a : MvPowerSeries (Fin n) O) :
    (dirPt e c a).snd = ∑ j, c j * e (pderiv (R := O) j a) :=
  (zero_add _).trans ((TrivSqZeroExt.snd_inr _ _).trans (by simp))

omit [IsLocalRing O] in
theorem dirPt_snd_X {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) (i : Fin n) :
    (dirPt e c (X i)).snd = c i := by
  simp [dirPt_snd, pderiv_X, Pi.single_apply, apply_ite e]

variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

theorem snd_eq_sum {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (he : ∀ i, e (X i) ∈ maximalIdeal O)
    (ψ : MvPowerSeries (Fin n) O →ₐ[O] DualNumber O) (hψ : ∀ a, (ψ a).fst = e a) (a : MvPowerSeries (Fin n) O) :
    (ψ a).snd = ∑ j, (ψ (X j)).snd * e (pderiv (R := O) j a) := by
  have := isLocalRing_trivSqZeroExt (O := O) O
  have : Module.Finite O (DualNumber O) := inferInstanceAs (Module.Finite O (O × O))
  have := GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (DualNumber O)
  have h : ψ = dirPt e fun j => (ψ (X j)).snd :=
    mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal (DualNumber O))
      (fun i h => he i (hψ _ ▸ TrivSqZeroExt.isUnit_iff_isUnit_fst.1 h))
      (fun i => TrivSqZeroExt.ext (by rw [hψ, dirPt_fst]) (by rw [dirPt_snd_X]))
  exact (congrArg (fun q => (q a).snd) h).trans (dirPt_snd _ _ _)

omit [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] in
theorem isLocalHom_of_X_mem {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (he : ∀ i, e (X i) ∈ maximalIdeal O) :
    IsLocalHom e.toRingHom := by
  refine ((IsLocalRing.local_hom_tfae _).out 1 4).2 fun g hg => ?_
  have h1 := algHom_sub_constantCoeff_mem e he g
  have h2 := (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff (g := g)).1 hg
  simpa using add_mem h1 h2

end Algebra

section Group

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing MvPowerSeries

attribute [local instance] Over.cartesianMonoidalCategory

variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR O ⟶ G)}

theorem exists_matrix (hv : IsLieBasis v) (j : sp (R₀ := O) (MvPowerSeries (Fin n) O) ⟶ G)
    (inj : ∀ {T : Type} [CommRing T] [Algebra O T] (φ ψ : MvPowerSeries (Fin n) O →ₐ[O] T),
      spMap φ ≫ j = spMap ψ ≫ j → ∀ i, φ (X i) = ψ (X i))
    (z : 𝟙_ _ ⟶ G) (u : MvPowerSeries (Fin n) O →ₐ[O] O) (hu0 : ∀ i, u (X i) ∈ maximalIdeal O)
    (hu : spMap u ≫ j = toUnit _ ≫ z)
    (χ : MvPowerSeries (Fin n) O →ₐ[O] TrivSqZeroExt O (Fin n → O))
    (hχ : spMap χ ≫ j = (toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    ∃ C : Matrix (Fin n) (Fin n) O, IsUnit C.det ∧
      ∀ k, ∃ φ : MvPowerSeries (Fin n) O →ₐ[O] DualNumber O, spMap φ ≫ j = (toUnit _ ≫ z) * v k ∧
        ∀ a, (φ a).snd = ∑ i, u (pderiv (R := O) i a) * C i k := by
  have hz : ∀ {T T' : Type} [CommRing T] [Algebra O T] [CommRing T'] [Algebra O T'] (φ : T →ₐ[O] T'),
      spMap φ ≫ toUnit _ ≫ z = toUnit _ ≫ z := fun φ => by
    rw [← Category.assoc, comp_toUnit]
  have hfst : ∀ a, (χ a).fst = u a := by
    refine fun a => (AlgHom.congr_fun (mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal O) hu0
      (inj u ((TrivSqZeroExt.fstHom O O _).comp χ) ?_)) a).symm
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp,
      lieExp_eq_one hv.1 _ (fun i => by rfl), mul_one, hu]
  let φ : (Fin n → O) → (MvPowerSeries (Fin n) O →ₐ[O] DualNumber O) := fun c =>
    (vecTo (inlS O O) (fun i => inr (c i)) (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ
  have hφ : ∀ c, spMap (φ c) ≫ j = (toUnit _ ≫ z) * tanExp v c := fun c => by
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp]
    exact congrArg _ (lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _)
  have hφ1 : ∀ c a, (φ c a).fst = u a := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]
  have hφ2 : ∀ c a, (φ c a).snd = ∑ k, (χ a).snd k * c k := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]
  obtain ⟨-, hsurj⟩ := isLieBasisOver_self hv
  have hM : ∀ l : Fin n, ∃ c : Fin n → O, ∀ i, ∑ k, (χ (X i)).snd k * c k = (Pi.single l 1 : Fin n → O) i := by
    intro l
    have h1 : (fstS O O).comp (dirPt u (Pi.single l 1)) = u := AlgHom.ext fun a => dirPt_fst _ _ a
    obtain ⟨c, hc⟩ := hsurj ((toUnit _ ≫ z)⁻¹ * (spMap (dirPt u (Pi.single l 1)) ≫ j)) (by
      rw [IsTanOver, MonObj.comp_mul, GrpObj.comp_inv, hz, ← Category.assoc, spMap_comp, h1, hu,
        inv_mul_cancel])
    have h2 := inj (dirPt u (Pi.single l 1)) (φ c) (by rw [hφ, ← hc, mul_inv_cancel_left])
    exact ⟨c, fun i => by rw [← hφ2, ← h2, dirPt_snd_X]⟩
  choose M hM using hM
  refine ⟨Matrix.of fun i k => (χ (X i)).snd k, ?_, fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun k l => M l k) (Matrix.ext fun i l => ?_)
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact (hM l i).trans (Pi.single_apply _ _ _)
  · rw [hφ, tanExp_single hv.1]
  · rw [snd_eq_sum u hu0 _ (hφ1 _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hφ2, mul_comm]
    simp [Pi.single_apply]

end Group

end GlobalTheory.JacSer

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.jac_eq_unit_mul_det_pderiv : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (θ : Sp (MvPowerSeries (Fin x.P.g) O) ⟶ x.P.A.left) (z : Pt x) (e : (MvPowerSeries (Fin x.P.g) O) →ₐ[O] O), θ ≫ x.P.A.hom = spMap (algebraMap O (MvPowerSeries (Fin x.P.g) O)) → (∃ (V : x.P.A.left.Opens) (t : Fin x.P.g → Γ(x.P.A.left, V)), ⊤ ≤ θ ⁻¹ᵁ V ∧ ∀ i, valT (T := (MvPowerSeries (Fin x.P.g) O)) θ V (t i) = MvPowerSeries.X i) → (∀ (T : Type) [CommRing T] [IsLocalRing T] [Algebra O T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T] (w : Sp T ⟶ x.P.A.left), w ≫ x.P.A.hom = spMap (algebraMap O T) → w (IsLocalRing.closedPoint T) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) → ∃ e : (MvPowerSeries (Fin x.P.g) O) →ₐ[O] T, (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal T) ∧ spMap e.toRingHom ≫ θ = w) → (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) → spMap e.toRingHom ≫ θ = z.left → ∃ u : Oˣ, ∀ (n : ℕ) (s : Fin x.P.g → RR x n) (c : x.P.L.ι), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → jac x s z c = u * e (Matrix.of fun i j => MvPowerSeries.pderiv (R := O) j (valT (T := (MvPowerSeries (Fin x.P.g) O)) θ (x.P.L.U c) ((s i).f c))).det := by
  intro O _ _ _ _ x θ z e hθ ⟨V, t, hV, ht⟩ hlift he hz
  let j : Chart.sp (R₀ := O) (MvPowerSeries (Fin x.P.g) O) ⟶ x.P.A := Over.homMk θ hθ
  have hloc := GlobalTheory.JacSer.isLocalHom_of_X_mem e he
  have hcl : z.left (IsLocalRing.closedPoint O) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) := by
    rw [← hz, ← IsLocalRing.comap_closedPoint e.toRingHom]
    rfl
  have hu : Chart.spMap e ≫ j = toUnit _ ≫ z := by
    apply Over.OverMorphism.ext
    have e1 : (toUnit (Chart.sp (R₀ := O) O)).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]
      exact Spec.map_id _
    rw [Over.comp_left, Over.comp_left, e1]
    exact hz.trans (Category.id_comp _).symm
  have := GlobalTheory.JacSer.isLocalRing_trivSqZeroExt (O := O) (Fin x.P.g → O)
  have : Module.Finite O (TrivSqZeroExt O (Fin x.P.g → O)) :=
    inferInstanceAs (Module.Finite O (O × (Fin x.P.g → O)))
  have := GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (TrivSqZeroExt O (Fin x.P.g → O))
  let w : Chart.sp (R₀ := O) (TrivSqZeroExt O (Fin x.P.g → O)) ⟶ x.P.A :=
    (toUnit _ ≫ z) * GlobalTheory.SqZero.lieExp x.v (fun i => TrivSqZeroExt.inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  obtain ⟨χ, -, hχ⟩ := hlift (TrivSqZeroExt O (Fin x.P.g → O)) w.left (Over.w w) (by
    have h1 : IsLocalHom (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)).toRingHom :=
      ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
    have h2 : Chart.spMap (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)) ≫ w = Chart.spMap e ≫ j := by
      rw [hu, MonObj.comp_mul, GlobalTheory.SqZero.comp_lieExp, GlobalTheory.SqZero.lieExp_eq_one x.basis.1 _ (fun i => by rfl),
        _root_.mul_one, ← Category.assoc, comp_toUnit]
    have h3 := congrArg (fun q => q.left (IsLocalRing.closedPoint O)) h2
    rw [← IsLocalRing.comap_closedPoint (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)).toRingHom,
      ← IsLocalRing.comap_closedPoint e.toRingHom]
    exact h3)
  obtain ⟨C, hC, hφ⟩ := GlobalTheory.JacSer.exists_matrix x.basis j (fun φ ψ h i => by
    have h1 : spMap φ.toRingHom ≫ θ = spMap ψ.toRingHom ≫ θ := congrArg (·.left) h
    have h2 := EtBaseChange.valT_spMap φ.toRingHom θ hV (t i)
    rw [h1, EtBaseChange.valT_spMap ψ.toRingHom θ hV, ht] at h2
    exact h2.symm) z e he hu χ (Over.OverMorphism.ext hχ)
  refine ⟨hC.unit, fun n s c hc => ?_⟩
  have hθc : ⊤ ≤ θ ⁻¹ᵁ x.P.L.U c := fun p _ =>
    ((IsLocalRing.specializes_closedPoint p).map θ.continuous).mem_open (x.P.L.U c).isOpen
      (hcl ▸ hc (x := IsLocalRing.closedPoint O) trivial)
  rw [IsUnit.unit_spec, _root_.mul_comm, AlgHom.map_det, ← Matrix.det_mul]
  refine congrArg Matrix.det (Matrix.ext fun i k => ?_)
  obtain ⟨φ, h1, h2⟩ := hφ k
  rw [Matrix.mul_apply, Matrix.of_apply]
  refine Eq.trans (congrArg TrivSqZeroExt.snd ?_) (h2 _)
  exact (congrArg (fun q : epsR O ⟶ x.P.A => valT (T := DualNumber O) q.left (x.P.L.U c) ((s i).f c)) h1.symm).trans
    (EtBaseChange.valT_spMap φ.toRingHom θ hθc _)

end
end
end

