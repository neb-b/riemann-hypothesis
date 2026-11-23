module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EvalEqZeroOfMemVanIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteSetOfHilbertFunctionsFibres
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwayProjectiveFormsThroughPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FormsFamily

theorem exists_const_near {R α : Type} [CommRing R] [PartialOrder α] {P : Set (Ideal R)} (hP : DenseP P)
    (r : ∀ (K : Type) [Field K], (R →+* K) → α) (ρ : α) (g : R)
    (hsc : ∀ (K : Type) [Field K] (x : R →+* K), ∃ f : R, x f ≠ 0 ∧
      ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 → r L y ≤ r K x)
    (hρ : ∀ q ∈ P, g ∉ q → ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ r K x = ρ)
    (K : Type) [Field K] (x : R →+* K) (hg : x g ≠ 0) (hx : r K x = ρ) :
    ∃ f : R, x f ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 → r L y = ρ := by
  obtain ⟨f, hf, h⟩ := hsc K x
  refine ⟨f * g, by rw [map_mul]; exact mul_ne_zero hf hg, fun L _ y hy => ?_⟩
  rw [map_mul] at hy
  refine le_antisymm (hx ▸ h L y (left_ne_zero_of_mul hy)) ?_
  obtain ⟨f', hf', h'⟩ := hsc L y
  have h0 : f' * g ≠ 0 := fun h0 => mul_ne_zero hf' (right_ne_zero_of_mul hy) (by rw [← map_mul, h0, map_zero])
  have h1 : ¬ ∀ q ∈ P, q.IsPrime → f' * g ∈ q := fun h1 => h0 (hP _ h1)
  push Not at h1
  obtain ⟨q, hq, -, hq'⟩ := h1
  obtain ⟨K', _, x', rfl, rfl⟩ := hρ q hq fun h2 => hq' (q.mul_mem_left _ h2)
  exact h' K' x' fun h2 => hq' (Ideal.mul_mem_right _ _ h2)

theorem exists_away_projective_vanIdeal : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (σ Hh : Type) [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : Ideal (MvPolynomial σ K)), RingHom.ker x = q ∧ CutBy I Q d (fun h i => x (p h i))) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ (∀ e ≥ d, Module.Projective (Localization.Away f) (↥(MvPolynomial.homogeneousSubmodule σ (Localization.Away f) e) ⧸ ((vanIdeal d (fun h i => (algebraMap R (Localization.Away f)) (p h i))).restrictScalars (Localization.Away f)).comap (MvPolynomial.homogeneousSubmodule σ (Localization.Away f) e).subtype)) ∧ ∀ (K : Type) [Field K] (x : (Localization.Away f) →+* K), (vanIdeal d (fun h i => (algebraMap R (Localization.Away f)) (p h i))).map (MvPolynomial.map x) = vanIdeal d (fun h i => x ((algebraMap R (Localization.Away f)) (p h i))) := by
  intro R _ _ _ σ Hh _ _ p Q d P hP hcut q₀ hq₀
  classical
  obtain ⟨K₀, _, x₀, I₀, rfl, hc₀⟩ := hcut q₀ hq₀
  have hI := component_mem_vanIdeal d p
  obtain ⟨f₁, hf₁, h₁⟩ := exists_const_near hP
    (fun K _ x => (dimDeg (vanIdeal d fun h i => x (p h i)) d : ℚ)) (Q.eval (d : ℚ)) 1
    (fun K _ x => (exists_dimDeg_vanIdeal_le d p K x).imp fun f hf =>
      ⟨hf.1, fun L _ y hy => Nat.cast_le.2 (hf.2 L y hy)⟩)
    (fun q hq _ => by
      obtain ⟨K, _, x, I, hx, hc⟩ := hcut q hq
      exact ⟨K, _, x, hx, dimDeg_eq_of_cutBy hc le_rfl⟩)
    K₀ x₀ (by simp) (dimDeg_eq_of_cutBy hc₀ le_rfl)
  have h₂ := map_vanIdeal_of_const_away d p _ f₁ h₁
  have h₃ : ∀ e ≥ d, ∃ g : R, x₀ g ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y g ≠ 0 →
      (dimDeg ((vanIdeal d p).map (MvPolynomial.map y)) e : ℚ) = Q.eval (e : ℚ) := by
    intro e he
    obtain ⟨g, hg, h⟩ := exists_const_near hP
      (fun K _ x => -(dimDeg ((vanIdeal d p).map (MvPolynomial.map x)) e : ℚ)) (-Q.eval (e : ℚ)) f₁
      (fun K _ x => (exists_dimDeg_map_le _ hI e K x).imp fun f hf =>
        ⟨hf.1, fun L _ y hy => neg_le_neg (Nat.cast_le.2 (hf.2 L y hy))⟩)
      (fun q hq hq' => by
        obtain ⟨K, _, x, I, rfl, hc⟩ := hcut q hq
        exact ⟨K, _, x, rfl, by rw [h₂ K x hq', dimDeg_eq_of_cutBy hc he]⟩)
      K₀ x₀ hf₁ (by rw [h₂ K₀ x₀ hf₁, dimDeg_eq_of_cutBy hc₀ he])
    exact ⟨g, hg, fun L _ y hy => neg_injective (h L y hy)⟩
  have h₄ : ∀ φ : ℕ → ℕ, ∃ g : R, x₀ g ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y g ≠ 0 →
      φ = dimDeg ((vanIdeal d p).map (MvPolynomial.map y)) → ∀ e ≥ d, (φ e : ℚ) = Q.eval (e : ℚ) := by
    intro φ
    by_cases hφ : ∀ e ≥ d, (φ e : ℚ) = Q.eval (e : ℚ)
    · exact ⟨1, by simp, fun _ _ _ _ _ => hφ⟩
    · push Not at hφ
      obtain ⟨e, he, hne⟩ := hφ
      obtain ⟨g, hg, h⟩ := h₃ e he
      exact ⟨g, hg, fun L _ y hy hφ => absurd (hφ ▸ h L y hy) hne⟩
  choose g hg h₅ using h₄
  have hfin := _root_.GlobalTheory.finite_setOf_dimDeg_map R σ (vanIdeal d p) hI
  let f : R := f₁ * ∏ φ ∈ hfin.toFinset, g φ
  have h₆ : ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 → ∀ e ≥ d,
      (dimDeg (vanIdeal d fun h i => y (p h i)) e : ℚ) = Q.eval (e : ℚ) := by
    intro L _ y hy
    simp only [f, map_mul, map_prod, ne_eq, mul_eq_zero, not_or] at hy
    rw [← h₂ L y hy.1]
    exact h₅ _ L y (Finset.prod_ne_zero_iff.1 hy.2 _ (hfin.mem_toFinset.2 ⟨L, _, y, rfl⟩)) rfl
  have hf : f ∉ RingHom.ker x₀ := by
    rw [RingHom.mem_ker, map_mul, map_prod]
    exact mul_ne_zero hf₁ (Finset.prod_ne_zero_iff.2 fun φ _ => hg φ)
  haveI : IsReduced (Localization.Away f) :=
    isReduced_localizationPreserves (Submonoid.powers f) _ inferInstance
  have h₇ : ∀ (L : Type) [Field L] (y : Localization.Away f →+* L), ∀ e ≥ d,
      (dimDeg (vanIdeal d fun h i => y (algebraMap R (Localization.Away f) (p h i))) e : ℚ) = Q.eval (e : ℚ) :=
    fun L _ y => h₆ L (y.comp (algebraMap R _))
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).map y).ne_zero
  have h₈ := map_vanIdeal_of_const d (fun h i => algebraMap R (Localization.Away f) (p h i)) _
    fun L _ y => h₇ L y d le_rfl
  exact ⟨f, hf, fun e he => projective_of_const _ (component_mem_vanIdeal d _) e (Q.eval (e : ℚ))
    fun L _ y => by rw [h₈ L y]; exact h₇ L y e he, fun K _ x => h₈ K x⟩

end GlobalTheory.ZM.FormsFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompatOfLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.TUniq
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}

def MapBy (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) ∧ ∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left

theorem tMap_iff (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) : TMap t' t f ↔ ∃ φ, MapBy t' t f φ := Iff.rfl

def GeoGood (t t' : TObj g k J b s) (Sg : Set S) : Prop :=
  ∀ (K : Type) [Field K] (x : Sp K ⟶ S), Set.range x ⊆ Sg →
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (su : Sp Ω ⟶ Sp o) (u : TObj g k J b su)
      (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left),
      MapBy u t (spMap i ≫ x) ψ ∧ MapBy u t' (spMap i ≫ x) ψ'

theorem GeoGood.symm {t t' : TObj g k J b s} {Sg : Set S} (h : GeoGood t t' Sg) : GeoGood t' t Sg := fun K _ x hx => by
  obtain ⟨Ω, _, _, i, su, u, ψ, ψ', h₁, h₂⟩ := h K x hx
  exact ⟨Ω, inferInstance, inferInstance, i, su, u, ψ', ψ, h₂, h₁⟩

def Compat (t t' : TObj g k J b s) {X : Scheme.{0}} (c₀ : X ⟶ t.A.left) (f : X ⟶ t'.A.left) : Prop :=
  f ≫ t'.A.hom = c₀ ≫ t.A.hom ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (su : Sp K ⟶ Sp o) (u : TObj g k J b su) (x : Sp K ⟶ S)
      (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left), MapBy u t x ψ → MapBy u t' x ψ' →
      ∀ (B : Type) [Field B] (z : Sp B ⟶ u.A.left) (y : Sp B ⟶ X), y ≫ c₀ = z ≫ ψ → y ≫ f = z ≫ ψ'

theorem epi_spMap {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    letI := i.toAlgebra
    exact (inferInstance : Module.Flat K Ω)
  have : Surjective (spMap i) := ⟨fun p => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem ext_of_geoGood {t t' : TObj g k J b s} {Sg : Set S} (hd : Dense Sg) (hg : GeoGood t t' Sg) {X Y : Scheme.{0}}
    [IsReduced X] (p : X ⟶ S) [Flat p] [LocallyOfFinitePresentation p] (q : Y ⟶ S) [IsSeparated q] {f f' : X ⟶ Y}
    (hf : f ≫ q = p) (hf' : f' ≫ q = p)
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (su : Sp K ⟶ Sp o) (u : TObj g k J b su) (x : Sp K ⟶ S)
      (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left), MapBy u t x ψ → MapBy u t' x ψ' →
      ∀ y : Sp K ⟶ X, y ≫ p = x → y ≫ f = y ≫ f') : f = f' := by
  refine (GlobalTheory.dense_fibres_ext X S p Sg hd).2.1 Y q f f' hf hf' fun K _ _ y hy => ?_
  obtain ⟨Ω, _, _, i, su, u, ψ, ψ', h₁, h₂⟩ := hg K (y ≫ p) hy
  have := epi_spMap i
  rw [← cancel_epi (spMap i), ← Category.assoc, ← Category.assoc]
  exact H Ω su u _ ψ ψ' h₁ h₂ _ (Category.assoc _ _ _)

theorem Compat.unique {t t' : TObj g k J b s} {Sg : Set S} (hd : Dense Sg) (hg : GeoGood t t' Sg) {X : Scheme.{0}}
    [IsReduced X] {c₀ : X ⟶ t.A.left} [Flat (c₀ ≫ t.A.hom)] [LocallyOfFinitePresentation (c₀ ≫ t.A.hom)]
    {f f' : X ⟶ t'.A.left} (h : Compat t t' c₀ f) (h' : Compat t t' c₀ f') : f = f' := by
  have := t'.ab.proper
  refine ext_of_geoGood hd hg (c₀ ≫ t.A.hom) t'.A.hom h.1 h'.1 fun K _ _ su u x ψ ψ' h₁ h₂ y hy => ?_
  have w : (y ≫ c₀) ≫ t.A.hom = 𝟙 _ ≫ x := by rw [Category.assoc, hy, Category.id_comp]
  have e := (h₁.1.1.lift_fst _ _ w).symm
  exact (h.2 K su u x ψ ψ' h₁ h₂ K _ y e).trans (h'.2 K su u x ψ ψ' h₁ h₂ K _ y e).symm

theorem Compat.comp {t t' : TObj g k J b s} {X Y : Scheme.{0}} {c₀ : X ⟶ t.A.left} {f : X ⟶ t'.A.left}
    (h : Compat t t' c₀ f) (j : Y ⟶ X) : Compat t t' (j ≫ c₀) (j ≫ f) :=
  ⟨by rw [Category.assoc, Category.assoc, h.1], fun K _ _ su u x ψ ψ' h₁ h₂ B _ z y e => by
    rw [← Category.assoc] at e ⊢
    exact h.2 K su u x ψ ψ' h₁ h₂ B z _ e⟩

theorem Compat.fibre {t t' : TObj g k J b s} {φ : t.A.left ⟶ t'.A.left} (h : Compat t t' (𝟙 _) φ)
    {K : Type} [Field K] [IsAlgClosed K] {su : Sp K ⟶ Sp o} {u : TObj g k J b su} {x : Sp K ⟶ S}
    {ψ : u.A.left ⟶ t.A.left} {ψ' : u.A.left ⟶ t'.A.left} (h₁ : MapBy u t x ψ) (h₂ : MapBy u t' x ψ') :
    ψ ≫ φ = ψ' := by
  have := u.ab.proper
  have := u.ab.smooth
  have := GlobalTheory.isReduced_of_smooth_of_isReduced u.A.hom
  have w : (ψ ≫ φ) ≫ t'.A.hom = u.A.hom ≫ x := by rw [Category.assoc, h.1, Category.id_comp, h₁.1.1.w]
  have e : h₂.1.1.lift _ _ w = 𝟙 _ :=
    (GlobalTheory.dense_fibres_ext _ _ u.A.hom Set.univ dense_univ).2.1 _ u.A.hom _ _ (h₂.1.1.lift_snd _ _ _)
      (Category.id_comp _) fun B _ _ z _ => by
        apply h₂.1.1.hom_ext
        · rw [Category.assoc, h₂.1.1.lift_fst, Category.comp_id, ← Category.assoc]
          exact h.2 K su u x ψ ψ' h₁ h₂ B z _ (Category.comp_id _)
        · rw [Category.assoc, h₂.1.1.lift_snd, Category.comp_id]
  rw [← h₂.1.1.lift_fst _ _ w, e, Category.id_comp]

theorem exists_compat_of_local [IsReduced S] {t t' : TObj g k J b s} {Sg : Set S} (hd : Dense Sg) (hg : GeoGood t t' Sg)
    (H : ∀ p : t.A.left, ∃ (X : Scheme.{0}) (c₀ : X ⟶ t.A.left) (f : X ⟶ t'.A.left), IsOpenImmersion c₀ ∧
      p ∈ Set.range c₀ ∧ Compat t t' c₀ f) : ∃ φ, Compat t t' (𝟙 _) φ := by
  choose X c₀ f hc₀ hp hf using H
  have := t.ab.smooth
  have := GlobalTheory.isReduced_of_smooth_of_isReduced t.A.hom
  let 𝒰 : t.A.left.OpenCover := Scheme.Cover.mkOfCovers _ X c₀ (fun p => ⟨p, hp p⟩) hc₀
  have hc : ∀ p q, pullback.fst (𝒰.f p) (𝒰.f q) ≫ f p = pullback.snd _ _ ≫ f q := fun p q => by
    have := hc₀ p
    have := hc₀ q
    have : IsReduced (pullback (c₀ p) (c₀ q)) := isReduced_of_isOpenImmersion (pullback.fst (c₀ p) (c₀ q) ≫ c₀ p)
    exact ((hf p).comp (pullback.fst (c₀ p) (c₀ q))).unique hd hg
      (by rw [pullback.condition]; exact (hf q).comp (pullback.snd (c₀ p) (c₀ q)))
  have e : ∀ p, c₀ p ≫ 𝒰.glueMorphisms f hc = f p := fun p => 𝒰.ι_glueMorphisms f hc p
  refine ⟨𝒰.glueMorphisms f hc, 𝒰.hom_ext _ _ fun p => ?_, fun K _ _ su u x ψ ψ' h₁ h₂ B _ z y hy => ?_⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (e p)).trans ((hf p).1.trans
      (congrArg _ (Category.id_comp _).symm)))
  · let p := y (default : PrimeSpectrum B)
    have := hc₀ p
    have hr : Set.range y ⊆ Set.range (c₀ p) := by
      rintro _ ⟨q, rfl⟩
      obtain rfl : q = (default : PrimeSpectrum B) := Subsingleton.elim (α := PrimeSpectrum B) _ _
      exact hp _
    have l := IsOpenImmersion.lift_fac (c₀ p) y hr
    rw [← l, Category.assoc, e]
    exact (hf p).2 K su u x ψ ψ' h₁ h₂ B z _ (l.trans ((Category.comp_id _).symm.trans hy))

end GlobalTheory.TUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnVerticalVectorField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.VertField

theorem differentiableAt_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (z₀ : E) (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀) :
    DifferentiableAt ℂ (fun z => (M z).det) z₀ := by
  simp only [Matrix.det_apply']
  fun_prop

private theorem differentiableAt_adjugate_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (z₀ : E) (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀)
    (i j : Fin g) : DifferentiableAt ℂ (fun z => (M z).adjugate i j) z₀ := by
  simp only [Matrix.adjugate_apply]
  refine differentiableAt_det (fun z => (M z).updateRow j (Pi.single i 1)) z₀ fun k l => ?_
  by_cases hk : k = j <;> simp [Matrix.updateRow_apply, hk, h k l]

theorem differentiableAt_of_mulVec {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (b w : E → Fin g → ℂ) (z₀ : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀) (hb : ∀ i, DifferentiableAt ℂ (fun z => b z i) z₀)
    (hdet : (M z₀).det ≠ 0) (hw : ∀ᶠ z in nhds z₀, (M z).mulVec (w z) = b z) :
    DifferentiableAt ℂ w z₀ := by
  have hd : DifferentiableAt ℂ (fun z => (M z).det) z₀ := differentiableAt_det M z₀ h
  have hne : ∀ᶠ z in nhds z₀, (M z).det ≠ 0 := hd.continuousAt.eventually_ne hdet
  have heq : w =ᶠ[nhds z₀] fun z => ((M z).det)⁻¹ • ((M z).adjugate.mulVec (b z)) := by
    filter_upwards [hne, hw] with z hz hzw
    rw [← hzw, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_smul, inv_mul_cancel₀ hz, one_smul]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  rw [differentiableAt_pi]
  intro i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  have hadj := differentiableAt_adjugate_apply M z₀ h i
  have hi := hd.inv hdet
  fun_prop

theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  have hpre : (x ≫ φ) ⁻¹ᵁ U = x ⁻¹ᵁ φ ⁻¹ᵁ U := by simp
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U
  · rw [dite_eq_left (by rwa [hpre]), dite_eq_left h]
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · rw [dite_eq_right (by rwa [hpre]), dite_eq_right h]

theorem isOpen_dom_and_differentiableOn_fn {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left}
    (u : HolUnif A₀ L₀ g) {X : Scheme.{0}} (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    IsOpen (dom u m W) ∧ DifferentiableOn ℂ (fn u m W f) (dom u m W) := by
  have hcomp : ∀ z, ((u.ex z).left ≫ m) ⁻¹ᵁ W = (u.ex z).left ⁻¹ᵁ m ⁻¹ᵁ W := fun z => by simp
  have hdom : dom u m W = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ m ⁻¹ᵁ W} := by
    ext z
    simp only [dom, Set.mem_ofPred_eq, hcomp]
  have hfn : fn u m W f = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom f) := by
    funext z
    exact valAt'_comp _ _ _ _
  rw [hdom, hfn]
  exact u.8 (m ⁻¹ᵁ W) ((m.app W).hom f)

private theorem clm_apply_eq_sum_single_mul {g : ℕ} (L : (Fin g → ℂ) →L[ℂ] ℂ) (v : Fin g → ℂ) :
    L v = ∑ a, L (Pi.single a 1) * v a := by
  have hv : v = ∑ a, v a • (Pi.single a 1 : Fin g → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem exists_differentiableOn_vertical : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ (n : ℕ) (B : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin P₀.g → ℂ)) (s : (Fin n → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ), IsOpen B → Differentiable ℂ G → (∀ z ∈ B, PtDer ((u.ex (G z)).left ≫ m) (s z) ∧ ∀ r, s z ⊤ (constFn p ⊤ r) = 0) → (∀ W f, DifferentiableOn ℂ (fun z => s z W f) {z ∈ B | G z ∈ dom u m W}) → ∃ w : (Fin n → ℂ) → (Fin P₀.g → ℂ), DifferentiableOn ℂ w B ∧ ∀ z ∈ B, ∀ W f, G z ∈ dom u m W → s z W f = fderiv ℂ (fn u m W f) (G z) (w z) := by
  intro P₀ u Hm χ hU R _ x₀ X p m hsm hpb n B G s hB hGd hs hhol
  have key : ∀ z ∈ B, ∃ v : Fin P₀.g → ℂ, ∀ W f, G z ∈ dom u m W → s z W f = fderiv ℂ (fn u m W f) (G z) v :=
    fun z hz => (_root_.GlobalTheory.KS.VertFamily.existsUnique_vector P₀ u Hm χ hU R x₀ X p m hsm hpb (G z) (s z) (hs z hz).1 (hs z hz).2).exists
  choose! w hw using key
  refine ⟨w, fun z₁ hz₁ => ?_, hw⟩
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨W, t, hW, hdet⟩ := exists_fibre_coords P₀ u Hm χ hU R x₀ X p m hsm hpb (G z₁)
  have hD : IsOpen (dom u m W) := (isOpen_dom_and_differentiableOn_fn u m W 0).1
  have hV : IsOpen {z ∈ B | G z ∈ dom u m W} := hB.inter (hD.preimage hGd.continuous)
  have hz₁V : z₁ ∈ {z ∈ B | G z ∈ dom u m W} := ⟨hz₁, hW⟩
  have hT : Matrix.transpose (Matrix.of fun b a => fderiv ℂ (fn u m W (t b)) (G z₁) (Pi.single a 1)) =
      Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) (G z₁) (Pi.single a 1) := by
    ext a b
    rfl
  refine differentiableAt_of_mulVec (fun z => Matrix.of fun b a => fderiv ℂ (fn u m W (t b)) (G z) (Pi.single a 1))
    (fun z b => s z W (t b)) w z₁ (fun b a => ?_) (fun b => ?_) ?_ ?_
  · have h1 := ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex P₀.g (dom u m W) (fn u m W (t b)) hD).2
      (isOpen_dom_and_differentiableOn_fn u m W (t b)).2).2 (Pi.single a 1)
    exact (h1.differentiableAt (hD.mem_nhds hW)).comp z₁ (hGd z₁)
  · exact (hhol W (t b)).differentiableAt (hV.mem_nhds hz₁V)
  · rw [← Matrix.det_transpose, hT]
    exact hdet
  · filter_upwards [hV.mem_nhds hz₁V] with z hz
    ext b
    exact ((hw z hz.1 W (t b) hz.2).trans (clm_apply_eq_sum_single_mul _ _)).symm

end GlobalTheory.KS.VertField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivOmegaStd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

private theorem omegaStd_single_single_eq_stdSymp {g : ℕ} (a b : Fin g ⊕ Fin g) :
    omegaStd (Pi.single a (1 : ℤ)) (Pi.single b 1) =
      Out.stdSymp g (finCongr (two_mul g).symm (finSumFinEquiv a))
        (finCongr (two_mul g).symm (finSumFinEquiv b)) := by
  unfold Out.stdSymp omegaStd
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, zero_mul,
      sub_zero, zero_sub, mul_ite, ite_mul, mul_one, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_neg_distrib] <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, Fin.coe_cast,
      Fin.coe_castAdd, Fin.coe_natAdd, Fin.ext_iff] <;>
    split_ifs <;> omega

theorem exists_equiv_omegaStd {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M) {g : ℕ}
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] M)
    (h : ∀ i j, B (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j) :
    ∃ bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] M, ∀ x y, B (bas' x) (bas' y) = omegaStd x y := by
  set e : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm) with he
  refine ⟨(LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas, ?_⟩
  have hs : ∀ a, (LinearEquiv.funCongrLeft ℤ ℤ e.symm) (Pi.single a (1 : ℤ)) = Pi.single (e a) 1 := by
    intro a
    funext k
    simp [LinearEquiv.funCongrLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]
  let Ω : LinearMap.BilinForm ℤ (Fin g ⊕ Fin g → ℤ) :=
    LinearMap.mk₂ ℤ omegaStd
      (fun a a' b => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; ext; ring)
      (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
      (fun a b b' => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; ext; ring)
      (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
  have hB : B.compl₁₂ ((LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas).toLinearMap
      ((LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas).toLinearMap = Ω := by
    refine LinearMap.ext_basis (Pi.basisFun ℤ _) (Pi.basisFun ℤ _) fun a b => ?_
    simp only [Pi.basisFun_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, hs, h,
      Ω, LinearMap.mk₂_apply]
    exact (omegaStd_single_single_eq_stdSymp a b).symm
  intro x y
  exact LinearMap.congr_fun₂ hB x y

theorem sympBasis_std : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), IsSympBasis D bas → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La, ∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y := by
  intro E _ _ _ H D g bas hb
  refine ⟨?_, exists_equiv_omegaStd D.EF bas hb⟩
  have h1 := (LinearEquiv.finrank_eq bas).symm
  rw [finrank_int_lattice D, Module.finrank_fin_fun] at h1
  omega

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueFactorThroughEtaleIsogenyReduced
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFactor

lemma ext_of_geometricPoints {T X Z : Scheme.{0}} [IsReduced T] (q : X ⟶ Z) [IsSeparated q]
    (f g : T ⟶ X) (h : f ≫ q = g ≫ q)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), x ≫ f = x ≫ g) : f = g := by
  classical

  let K : T → Type := fun t => AlgebraicClosure (T.residueField t)
  let pts : (∐ fun t : T => Sp (K t)) ⟶ T := Sigma.desc fun t =>
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) (K t))) ≫ T.fromSpecResidueField t

  have : Surjective pts := by
    refine ⟨fun t => ⟨Sigma.ι (fun t : T => Sp (K t)) t (IsLocalRing.closedPoint (K t)), ?_⟩⟩
    have e : (Sigma.ι (fun t : T => Sp (K t)) t ≫ pts) (IsLocalRing.closedPoint (K t)) = t := by
      simp only [pts, Sigma.ι_desc]
      exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e
  refine ext_of_isDominant_of_isSeparated q h pts ?_
  refine Sigma.hom_ext _ _ fun t => ?_
  simpa only [pts, Sigma.ι_desc_assoc] using H (K t) _

theorem exists_unique_factor : ∀ (S : Scheme.{0}) [IsReduced S] (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B'] (ψ : A ⟶ B) (g : A ⟶ B'), IsAbelianScheme A → IsAbelianScheme B → IsSeparated B'.hom → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → IsMonHom g → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ≫ g = 1) → ∃ g' : B ⟶ B', IsMonHom g' ∧ ψ ≫ g' = g ∧ ∀ g'' : B ⟶ B', ψ ≫ g'' = g → g'' = g' := by
  intro S _ A B B' _ _ _ ψ g _ _ hsep hψ hfin het hsurj hg H

  let T : Over S := pullback ψ η[B]
  let i : T ⟶ A := pullback.fst ψ η[B]
  have hker : IsPullback i (toUnit T) ψ η[B] := by
    have hp := IsPullback.of_hasPullback ψ η[B]
    rwa [toUnit_unique (pullback.snd ψ η[B]) (toUnit T)] at hp

  have : IsReduced T.left := by
    have hp : IsPullback i.left (toUnit T).left ψ.left (η[B]).left := hker.map (Over.forget S)
    have : Etale (toUnit T).left := MorphismProperty.of_isPullback hp het
    have : IsReduced (𝟙_ (Over S)).left := by dsimp; infer_instance
    exact GlobalTheory.isReduced_of_smooth_of_isReduced (toUnit T).left
  have := hsep

  have hf : i ≫ g = toUnit T ≫ η[B'] := by
    apply Over.OverMorphism.ext
    refine ext_of_geometricPoints B'.hom _ _ (by rw [Over.w, Over.w]) ?_
    intro k _ _ x
    let xo : Over.mk (x ≫ T.hom) ⟶ T := Over.homMk x
    have e1 : (xo ≫ i) ≫ ψ = 1 := by
      rw [Category.assoc, hker.w, ← Category.assoc, Hom.one_def, toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    have e3 : xo ≫ (i ≫ g) = xo ≫ (toUnit T ≫ η[B']) := by
      rw [← Category.assoc, H k (x ≫ T.hom) (xo ≫ i) e1, Hom.one_def, ← Category.assoc,
        toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    simpa only [xo, Over.comp_left, Over.homMk_left] using congrArg CommaMorphism.left e3
  have := hψ; have := hg; have := hfin; have := het; have := hsurj
  obtain ⟨β, hβ, hψβ⟩ := FlatQuotient.exists_desc ψ i g hker hf
  have : Epi ψ := FlatQuotient.epi_of_flat_surjective ψ
  exact ⟨β, hβ, hψβ, fun g'' h'' => (cancel_epi ψ).1 (h''.trans hψβ.symm)⟩

end GlobalTheory.HkFactor
end

