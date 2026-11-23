module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfDimOfDirectionsLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SmoothDirections

noncomputable def derivationPoint {k R K : Type} [CommRing k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K] {r : ℕ}
    (D : Fin r → Derivation k R K) : R →+* TrivSqZeroExt K (Fin r → K) where
  toFun a := TrivSqZeroExt.inl (algebraMap R K a) + TrivSqZeroExt.inr fun i ↦ D i a
  map_one' := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp
  map_mul' a b := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp [Algebra.smul_def, mul_comm]
  map_zero' := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp
  map_add' a b := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp

theorem finrank_derivation_le {k R K : Type} [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K] {X : Scheme.{0}}
    (s : X ⟶ Sp k) (j : Sp R ⟶ X) [Mono j] (hj : j ≫ s = spMap (algebraMap k R)) {d : ℕ}
    (ht : ∀ (r : ℕ) (β : k →+* K) (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X),
      x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) →
      (∀ lam : (Fin r → K) →ₗ[K] K,
        spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) :
    Module.finrank K (Derivation k R K) ≤ d := by
  obtain ⟨D, hD⟩ := exists_linearIndependent_of_le_finrank
    (le_refl (Module.finrank K (Derivation k R K)))
  refine ht _ (algebraMap k K) (spMap (derivationPoint D) ≫ j) ?_ ?_
  · rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a ↦ TrivSqZeroExt.ext ?_ ?_
    · simp [derivationPoint, ← IsScalarTower.algebraMap_apply, TrivSqZeroExt.algebraMap_eq_inl]
    · funext i
      simp [derivationPoint, TrivSqZeroExt.algebraMap_eq_inl]
  · intro lam h
    simp only [constPt, ← Category.assoc, cancel_mono] at h
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
    have h₁ := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    have h₂ (a : R) : lam (fun i ↦ D i a) = 0 := by
      have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun h₁ a)
      simpa [dirMap, derivationPoint, TrivSqZeroExt.algebraMap_eq_inl] using this
    have h₃ := Fintype.linearIndependent_iff.mp hD (fun i ↦ lam (Pi.single i 1)) (by
      ext a
      have := h₂ a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Finset.univ_sum_single (fun i ↦ D i a), map_sum] at this
      rw [Derivation.zero_apply, ← this]
      refine (congrFun (map_sum (Derivation.coeFnAddMonoidHom (R := k) (A := R) (M := K)) _ _) a).trans ?_
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change lam (Pi.single i 1) • D i a = _
      rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul,
        _root_.mul_one])
    refine (Pi.basisFun K _).ext fun i ↦ ?_
    simpa using h₃ i

theorem smoothOfRelativeDimension_of_forall_finrank_derivation_le (k : Type) [Field k]
    [PerfectField k] (R : Type) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (d : ℕ)
    (hd : ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q))
    (ht : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra k K] [Algebra R K] [IsScalarTower k R K],
      Module.finrank K (Derivation k R K) ≤ d) :
    SmoothOfRelativeDimension d (spMap (algebraMap k R)) := by
  have : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have key (m : Ideal R) (hm : m.IsMaximal) :
      ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f) := by
    have h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
      exact_mod_cast SmoothTangent.le_height_of_forall_minimalPrimes k hd m
    have h₂ : Module.finrank (R ⧸ m) m.Cotangent ≤ d := by
      let := Ideal.Quotient.field m
      exact (SmoothTangent.finrank_cotangent_le_finrank_derivation k m
        (AlgebraicClosure (R ⧸ m))).trans (ht _)
    obtain ⟨-, -, -, h₃, -, h₄⟩ := isSmoothAt_of_finrank_cotangent_le_of_perfectField k m h₁ h₂
    exact exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt k m h₄
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr ?_
  refine ⟨{f | Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f)}, ?_, ?_⟩
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hs⟩ := key m hm
    exact hf (hle (Ideal.subset_span hs))
  · intro f hf
    have := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hf
    rwa [IsScalarTower.algebraMap_eq k R] at this

end GlobalTheory.SmoothDirections

namespace GlobalTheory

open SmoothDirections

theorem smoothOfRelativeDimension_of_dim_of_directions_le :
    ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ),
      LocallyOfFiniteType s →
      (∀ (R : Type) [CommRing R] [Algebra k R] (x : Sp R ⟶ X), IsOpenImmersion x →
        x ≫ s = spMap (algebraMap k R) →
        ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q)) →
      (∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : k →+* K)
        (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X),
        x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) →
        (∀ lam : (Fin r → K) →ₗ[K] K,
          spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) →
      SmoothOfRelativeDimension d s := by
  intro k _ _ X s d _ hd ht
  choose A iA aA j hj q hq hjs using exists_affine_chart_over s
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
  refine IsZariskiLocalAtSource.of_openCover
    (Scheme.Cover.mkOfCovers X (fun x ↦ Sp (A x)) j (fun x ↦ ⟨x, q x, hq x⟩) hj)
    fun (x : X) ↦ ?_
  change SmoothOfRelativeDimension d (j x ≫ s)
  let := iA x
  let := aA x
  have := hj x
  have : Algebra.FiniteType k (A x) := RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap k (A x)))).mp (hjs x ▸ inferInstance)
  rw [hjs]
  exact smoothOfRelativeDimension_of_forall_finrank_derivation_le k (A x) d
    (hd _ (j x) (hj x) (hjs x)) fun K _ _ _ _ _ ↦ finrank_derivation_le s (j x) (hjs x) (ht K)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionAndIsMonHomOfOpenCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens} {A : Over S} [GrpObj A] {G : ∀ i, Over (U i).toScheme}
  [∀ i, GrpObj (G i)] {ψ : ∀ i, (G i).left ⟶ A.left}

private theorem isGrpPullback_one_left {X' X : Scheme.{0}} {H' : Over X'} [GrpObj H'] {H : Over X} [GrpObj H]
    {g : X' ⟶ X} {φ : H'.left ⟶ H.left} (h : IsGrpPullback H' H g φ) (T : Over X') :
    (1 : Over.mk (T.hom ≫ g) ⟶ H).left = (1 : T ⟶ H').left ≫ φ := by
  have hw : ((1 : T ⟶ H').left ≫ φ) ≫ H.hom = (Over.mk (T.hom ≫ g)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let z : Over.mk (T.hom ≫ g) ⟶ H := Over.homMk ((1 : T ⟶ H').left ≫ φ) hw
  have hz : z * z = z := by
    apply Over.OverMorphism.ext
    rw [h.2 T 1 1 z z rfl rfl, _root_.mul_one]
    rfl
  have hz1 : z = 1 := _root_.mul_eq_left.mp hz
  rw [← hz1]
  rfl

private theorem pow_left_eq_pow_left_comp_of_isGrpPullback {X' X : Scheme.{0}} {H' : Over X'} [GrpObj H'] {H : Over X} [GrpObj H]
    {g : X' ⟶ X} {φ : H'.left ⟶ H.left} (h : IsGrpPullback H' H g φ) {T : Over X'} (y : T ⟶ H')
    (z : Over.mk (T.hom ≫ g) ⟶ H) (hz : z.left = y.left ≫ φ) (n : ℕ) :
    (z ^ n).left = (y ^ n).left ≫ φ := by
  induction n with
  | zero => simpa only [_root_.pow_zero] using isGrpPullback_one_left h T
  | succ n ih =>
    rw [_root_.pow_succ, _root_.pow_succ]
    exact h.2 T _ _ _ _ ih hz

theorem pow_eq_one_of_cover (hU : iSup U = ⊤) (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (k : ℕ)
    (x : Out.baseOver S ⟶ A) (x' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i)
    (hx : ∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) (hk : ∀ i, x' i ^ k = 1) : x ^ k = 1 := by
  refine over_ext hU fun i T' r => ?_
  rw [MonObj.comp_pow, MonObj.comp_one]
  have hr : r.left = T'.hom ≫ (U i).ι := by simpa using Over.w r
  let t : T' ⟶ Out.baseOver (U i).toScheme := Over.homMk T'.hom (by simp)
  have hy : (t ≫ x' i) ^ k = 1 := by rw [← MonObj.comp_pow, hk, MonObj.comp_one]
  have key := pow_left_eq_pow_left_comp_of_isGrpPullback (hψ i) (t ≫ x' i) (r ≫ x) (by simp [t, hr, hx]) k
  rw [hy, ← isGrpPullback_one_left (hψ i) T'] at key
  exact Over.OverMorphism.ext key

private theorem mul_comp_of_cover_isGrpPullback_isMonHom (hU : iSup U = ⊤) (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (f : A ⟶ A)
    (f' : ∀ i, G i ⟶ G i) (hf : ∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) (hm : ∀ i, IsMonHom (f' i))
    {T : Over S} (a b : T ⟶ A) : (a * b) ≫ f = (a ≫ f) * (b ≫ f) := by
  refine over_ext hU fun i T' r => ?_
  haveI := hm i
  obtain ⟨a', ha⟩ := exists_lift (hψ i).1 (r ≫ a)
  obtain ⟨b', hb⟩ := exists_lift (hψ i).1 (r ≫ b)
  have e1 := (hψ i).2 T' a' b' (r ≫ a) (r ≫ b) ha hb
  have ha' : (r ≫ a ≫ f).left = (a' ≫ f' i).left ≫ ψ i := by
    have := congrArg (· ≫ f.left) ha
    simp only [Over.comp_left, Category.assoc] at this ⊢
    rw [this, hf]
  have hb' : (r ≫ b ≫ f).left = (b' ≫ f' i).left ≫ ψ i := by
    have := congrArg (· ≫ f.left) hb
    simp only [Over.comp_left, Category.assoc] at this ⊢
    rw [this, hf]
  have e2 := (hψ i).2 T' (a' ≫ f' i) (b' ≫ f' i) (r ≫ a ≫ f) (r ≫ b ≫ f) ha' hb'
  have e3 : (a' * b') ≫ f' i = (a' ≫ f' i) * (b' ≫ f' i) := MonObj.mul_comp _ _ _
  apply Over.OverMorphism.ext
  rw [← Category.assoc, MonObj.comp_mul, MonObj.comp_mul, Over.comp_left, e1, e2, ← e3, Over.comp_left]
  simp only [Category.assoc, hf]

theorem isMonHom_of_cover (hU : iSup U = ⊤) (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (f : A ⟶ A)
    (f' : ∀ i, G i ⟶ G i) (hf : ∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) (hm : ∀ i, IsMonHom (f' i)) :
    IsMonHom f := by
  have hmul : ∀ {T : Over S} (a b : T ⟶ A), (a * b) ≫ f = (a ≫ f) * (b ≫ f) :=
    fun a b => mul_comp_of_cover_isGrpPullback_isMonHom hU hψ f f' hf hm a b
  have hone : ∀ {T : Over S}, (1 : T ⟶ A) ≫ f = 1 := by
    intro T
    have h1 := hmul (1 : T ⟶ A) 1
    rw [_root_.mul_one] at h1
    exact _root_.mul_eq_left.mp h1.symm
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one]
    exact hone
  · rw [MonObj.mul_eq_mul, hmul, MonObj.comp_mul]
    simp

theorem tors_and_isMonHom_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ (k : ℕ) (x : Out.baseOver S ⟶ A) (x' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, x' i ^ k = 1) → x ^ k = 1) ∧ ∀ (f : A ⟶ A) (f' : ∀ i, G i ⟶ G i), (∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) → (∀ i, IsMonHom (f' i)) → IsMonHom f := by
  intro S I U A _ G _ ψ hU hψ _ _
  exact ⟨fun k x x' hx hk => pow_eq_one_of_cover hU hψ k x x' hx hk,
    fun f f' hf hm => isMonHom_of_cover hU hψ f f' hf hm⟩

end GlobalTheory.CoverGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionBasisGeometricFibresOfOpenCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem exists_fac_field {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) (K : Type) [Field K]
    (x : Sp K ⟶ S) : ∃ (i : I) (x' : Sp K ⟶ (U i).toScheme), x' ≫ (U i).ι = x := by
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum K) := inferInstance
  obtain ⟨i, hi⟩ := exists_mem hU (x p)
  have hr : Set.range x.base ⊆ Set.range (U i).ι.base := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hq : q = p := Subsingleton.elim (α := PrimeSpectrum K) q p
    subst hq
    exact hi
  exact ⟨i, IsOpenImmersion.lift (U i).ι x hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem map_linComb {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S} {T' : Over S'}
    (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G')) (c : Fin n → ℕ) :
    ρ (Out.linComb x c) = Out.linComb (fun l => ρ (x l)) c := by
  unfold Out.linComb
  rw [map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, map_pow]

private theorem exists_bijective_monoidHom_points_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {ψ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f ψ) (T : Over S') :
    ∃ ρ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G),
      (∀ z, (ρ z).left = z.left ≫ ψ) ∧ Function.Injective ρ ∧ Function.Surjective ρ := by
  have hw : ∀ z : T ⟶ G', (z.left ≫ ψ) ≫ G.hom = T.hom ≫ f := fun z => by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w z]
  refine ⟨MonoidHom.mk' (fun z => Over.homMk (z.left ≫ ψ) (hw z)) (fun a b => ?_), fun _ => rfl, ?_, ?_⟩
  · exact Over.OverMorphism.ext (h.2 T a b _ _ rfl rfl).symm
  · intro a b hab
    exact lift_ext h.1 (congrArg CommaMorphism.left hab)
  · intro y
    obtain ⟨z, hz⟩ := exists_lift h.1 y
    exact ⟨z, Over.OverMorphism.ext hz.symm⟩

theorem torsionBasis_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (g k : ℕ) (P : Fin (2 * g) → (Out.baseOver S ⟶ A)) (Q : ∀ i, Fin (2 * g) → (Out.baseOver (U i).toScheme ⟶ G i)), (∀ i l, (Q i l).left ≫ ψ i = (U i).ι ≫ (P l).left) → (∀ i (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ (U i).toScheme) (y : Over.mk x ⟶ G i), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (U i).toScheme) ≫ Q i l) (fun l => (c l).val) = y) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ P l) (fun l => (c l).val) = y := by
  intro S I U A _ G _ ψ hU hψ _ _ g k P Q hPQ hQ K _ _ x y hy
  obtain ⟨i, x', rfl⟩ := exists_fac_field hU K x
  obtain ⟨ρ, hρ, hinj, hsurj⟩ := exists_bijective_monoidHom_points_of_isGrpPullback (hψ i) (Over.mk x')
  obtain ⟨y', rfl⟩ := hsurj y
  have hpt : ∀ l, ρ ((Over.homMk x' (by simp) : Over.mk x' ⟶ Out.baseOver (U i).toScheme) ≫ Q i l) =
      (Over.homMk (x' ≫ (U i).ι) (by simp) : Over.mk (x' ≫ (U i).ι) ⟶ Out.baseOver S) ≫ P l := by
    intro l
    apply Over.OverMorphism.ext
    rw [hρ]
    simp [hPQ]
  have hy' : y' ^ k = 1 := hinj (by rw [map_pow, map_one]; exact hy)
  obtain ⟨c, hc, huniq⟩ := hQ i K x' y' hy'
  refine ⟨c, ?_, fun c' hc' => huniq c' (hinj ?_)⟩
  · rw [← hc, map_linComb]
    simp only [hpt]
  · rw [map_linComb]
    simp only [hpt]
    exact hc'

end GlobalTheory.CoverGlue
end

