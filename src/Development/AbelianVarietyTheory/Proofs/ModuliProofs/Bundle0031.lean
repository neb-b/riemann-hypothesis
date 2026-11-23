module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SmoothTangent

theorem exists_section_of_ker_sq_eq_bot {k B F : Type*} [CommRing k] [CommRing B] [CommRing F]
    [Algebra k B] [Algebra k F] [Algebra.FormallySmooth k F] (π : B →ₐ[k] F)
    (hπ : Function.Surjective π) (h : RingHom.ker π.toRingHom ^ 2 = ⊥) :
    ∃ g : F →ₐ[k] B, π.comp g = AlgHom.id k F :=
  ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k F) π hπ ⟨2, h⟩⟩

theorem kerCotangentToTensor_injective (k R F : Type*) [CommRing k] [CommRing R] [CommRing F]
    [Algebra k R] [Algebra k F] [Algebra R F] [IsScalarTower k R F] [Algebra.FormallySmooth k F]
    (hs : Function.Surjective (algebraMap R F)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k R F) := by
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom k R F).kerSquareLift :=
    fun x ↦ by
      obtain ⟨y, rfl⟩ := hs x
      exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hnil : RingHom.ker (IsScalarTower.toAlgHom k R F).kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  obtain ⟨g, hg⟩ := exists_section_of_ker_sq_eq_bot _ hsurj hnil
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := k) hs).symm ⟨g, hg⟩
  exact Function.LeftInverse.injective (g := l) fun x ↦ congr($hl x)

noncomputable def derivationEquivDual (k R C : Type*) [CommRing k] [CommRing R] [CommRing C]
    [Algebra k R] [Algebra k C] [Algebra R C] [IsScalarTower k R C] :
    Derivation k R C ≃ₗ[C] Module.Dual C (C ⊗[R] Ω[R⁄k]) :=
  (({ (KaehlerDifferential.linearMapEquivDerivation k R (M := C)).toAddEquiv with
      map_smul' := fun _ _ ↦ rfl } : (Ω[R⁄k] →ₗ[R] C) ≃ₗ[C] Derivation k R C).symm).trans
    (LinearMap.liftBaseChangeEquiv C)

theorem finrank_cotangent_le_finrank_derivation (k : Type*) [Field k] [PerfectField k]
    {R : Type*} [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (m : Ideal R) [m.IsMaximal]
    (C : Type*) [Field C] [Algebra k C] [Algebra R C] [IsScalarTower k R C]
    [Algebra (R ⧸ m) C] [IsScalarTower R (R ⧸ m) C] :
    Module.finrank (R ⧸ m) m.Cotangent ≤ Module.finrank C (Derivation k R C) := by
  let := Ideal.Quotient.field m
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
  have : Algebra.FormallyEtale k (R ⧸ m) := Algebra.FormallyEtale.of_isSeparable k _
  have hs : Function.Surjective (algebraMap R (R ⧸ m)) := Ideal.Quotient.mk_surjective
  have hinj := kerCotangentToTensor_injective k R (R ⧸ m) hs
  let e : m.Cotangent →ₗ[R] (R ⧸ m) ⊗[R] Ω[R⁄k] :=
    KaehlerDifferential.kerCotangentToTensor k R (R ⧸ m) ∘ₗ
      (Ideal.Cotangent.equivOfEq _ _ Ideal.mk_ker.symm).toLinearMap
  have he : Function.Injective (e.extendScalarsOfSurjective hs) :=
    hinj.comp (Ideal.Cotangent.equivOfEq _ _ Ideal.mk_ker.symm).injective
  rw [(derivationEquivDual k R C).finrank_eq, Subspace.dual_finrank_eq,
    ← (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ m) C C Ω[R⁄k]).finrank_eq,
    Module.finrank_baseChange]
  exact LinearMap.finrank_le_finrank_of_injective he

theorem le_height_of_forall_minimalPrimes (k : Type) [Field k] {R : Type} [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {d : ℕ}
    (hd : ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q))
    (m : Ideal R) [m.IsMaximal] : (d : ℕ∞) ≤ m.height := by
  obtain ⟨p, hp, hpm⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ m)
  have := hp.1.1
  obtain ⟨n, h₁, h₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k (R ⧸ p)
  have hdn : (d : ℕ∞) ≤ n := by
    have := hd p hp
    rw [h₁] at this
    exact_mod_cast this
  have hψ : Function.Surjective (Ideal.Quotient.mk p) := Ideal.Quotient.mk_surjective
  have hcm : (m.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = m := by
    rw [Ideal.comap_map_of_surjective _ hψ, sup_eq_left]
    exact Ideal.mk_ker.le.trans hpm
  have : (m.map (Ideal.Quotient.mk p)).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ hψ inferInstance).resolve_left fun h ↦ ?_
    rw [h, Ideal.comap_top] at hcm
    exact Ideal.IsMaximal.ne_top inferInstance hcm.symm
  have h := height_le_height_comap_of_surjective _ hψ (m.map (Ideal.Quotient.mk p))
  rw [hcm, ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field n h₂] at h
  exact hdn.trans h

end GlobalTheory.SmoothTangent

namespace GlobalTheory

open SmoothTangent

theorem smoothOfRelativeDimension_of_dim_of_finrank_derivation_le :
    ∀ (k : Type) [Field k] [CharZero k] (e : k →+* ℂ) (R : Type) [CommRing R] [Algebra k R] (d : ℕ),
      Algebra.FiniteType k R →
      (∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q)) →
      (∀ [Algebra k ℂ] [Algebra R ℂ] [IsScalarTower k R ℂ], algebraMap k ℂ = e →
        Module.finrank ℂ (Derivation k R ℂ) ≤ d) →
      SmoothOfRelativeDimension d (spMap (algebraMap k R)) := by
  intro k _ _ e R _ _ d _ hd ht
  have : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have key (m : Ideal R) (hm : m.IsMaximal) :
      ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f) := by
    have h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
      exact_mod_cast le_height_of_forall_minimalPrimes k hd m
    have h₂ : Module.finrank (R ⧸ m) m.Cotangent ≤ d := by
      let := Ideal.Quotient.field m
      have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
      let : Algebra k ℂ := e.toAlgebra
      let φ : (R ⧸ m) →ₐ[k] ℂ := (by
        refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
        solve_by_elim* (maxDepth := 2) only [*,
          @_root_.DivisionSemiring.to_moduleIsTorsionFree,
          @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
      let : Algebra (R ⧸ m) ℂ := φ.toRingHom.toAlgebra
      let : Algebra R ℂ := (φ.toRingHom.comp (Ideal.Quotient.mk m)).toAlgebra
      have : IsScalarTower R (R ⧸ m) ℂ := .of_algebraMap_eq fun _ ↦ rfl
      have : IsScalarTower k R ℂ := .of_algebraMap_eq fun x ↦ (φ.commutes x).symm
      exact (finrank_cotangent_le_finrank_derivation k m ℂ).trans (ht rfl)
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

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SympBasis

private theorem sum_inv_mulVec_smul_col_of_det_ne_zero {R : Type} [CommRing R] {g : ℕ} (c : Fin (2 * g) → R) (i j : Fin (2 * g))
    (hij : (i : ℕ) < g ∧ (j : ℕ) = i + g) : ∑ l, c l * (Out.stdSymp g l j : R) = c i := by
  rw [Finset.sum_eq_single i]
  · unfold Out.stdSymp
    rw [if_pos hij]
    simp
  · intro l _ hl
    have h1 : ¬ ((l : ℕ) < g ∧ (j : ℕ) = l + g) := fun h => hl (Fin.ext (by omega))
    have h2 : ¬ ((j : ℕ) < g ∧ (l : ℕ) = j + g) := by omega
    unfold Out.stdSymp
    rw [if_neg h1, if_neg h2]
    simp
  · simp

private theorem sum_mul_stdSymp_eq_neg_of_eq_add {R : Type} [CommRing R] {g : ℕ} (c : Fin (2 * g) → R) (i j : Fin (2 * g))
    (hij : (j : ℕ) < g ∧ (i : ℕ) = j + g) : ∑ l, c l * (Out.stdSymp g l j : R) = - c i := by
  rw [Finset.sum_eq_single i]
  · have h1 : ¬ ((i : ℕ) < g ∧ (j : ℕ) = i + g) := by omega
    unfold Out.stdSymp
    rw [if_neg h1, if_pos hij]
    simp
  · intro l _ hl
    have h1 : ¬ ((l : ℕ) < g ∧ (j : ℕ) = l + g) := by omega
    have h2 : ¬ ((j : ℕ) < g ∧ (l : ℕ) = j + g) := fun h => hl (Fin.ext (by omega))
    unfold Out.stdSymp
    rw [if_neg h1, if_neg h2]
    simp
  · simp

theorem eq_of_sum_stdSymp {R : Type} [CommRing R] {g : ℕ} (a b : Fin (2 * g) → R)
    (h : ∀ j, ∑ i, a i * (Out.stdSymp g i j : R) = ∑ i, b i * (Out.stdSymp g i j : R)) : a = b := by
  funext i
  have hi2 := i.isLt
  by_cases hi : (i : ℕ) < g
  ·
    have h1 := h ⟨i + g, by omega⟩
    rwa [sum_inv_mulVec_smul_col_of_det_ne_zero a i _ ⟨hi, rfl⟩, sum_inv_mulVec_smul_col_of_det_ne_zero b i _ ⟨hi, rfl⟩] at h1
  ·
    have h1 := h ⟨i - g, by omega⟩
    rw [sum_mul_stdSymp_eq_neg_of_eq_add a i _ ⟨by simp; omega, by simp; omega⟩,
      sum_mul_stdSymp_eq_neg_of_eq_add b i _ ⟨by simp; omega, by simp; omega⟩] at h1
    exact neg_inj.mp h1

theorem rel_prod {M U : Type} [CommMonoid M] [CommGroup U] (W : M → U → Prop) (h1 : W 1 1)
    (hm : ∀ x x' c c', W x c → W x' c' → W (x * x') (c * c')) {J : Type} (s : Finset J) (p : J → M) (u : J → U)
    (a : J → ℕ) (hp : ∀ i, W (p i) (u i)) : W (∏ i ∈ s, p i ^ a i) (∏ i ∈ s, u i ^ a i) := by
  classical
  have hpow : ∀ i (n : ℕ), W (p i ^ n) (u i ^ n) := by
    intro i n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact hm _ _ _ _ ih (hp i)
  refine Finset.induction_on s (by simpa using h1) ?_
  intro j t hj ih
  rw [Finset.prod_insert hj, Finset.prod_insert hj]
  exact hm _ _ _ _ (hpow j (a j)) ih

private theorem zpow_finset_sum_divisor {U : Type} [CommGroup U] (z : U) {I : Type} (s : Finset I) (f : I → ℤ) :
    z ^ (∑ i ∈ s, f i) = ∏ i ∈ s, z ^ f i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro j t hj ih
  rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem injective_of_pairing {M U : Type} [CommMonoid M] [CommGroup U] (W : M → M → U → Prop) (k : ℕ) [NeZero k]
    (hu : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) {g : ℕ} (p : Fin (2 * g) → M)
    (hp : ∀ i, p i ^ k = 1) (z : U) (hz : IsPrimitiveRoot z k)
    (hw : ∀ i j, W (p i) (p j) (z ^ Out.stdSymp g i j)) :
    Function.Injective fun c : Fin (2 * g) → ZMod k => ∏ i, p i ^ (c i).val := by
  classical

  have hone : ∀ y, y ^ k = 1 → W 1 y 1 := by
    intro y hy
    obtain ⟨c, hc, huniq⟩ := hu 1 y (one_pow k) hy
    have h2 : W 1 y (c * c) := by simpa using hm 1 1 y c c hc hc
    have hcc : c * c = c := huniq _ h2
    have hc1 : c = 1 := by simpa using hcc
    rw [hc1] at hc
    exact hc

  let e : (Fin (2 * g) → ZMod k) → Fin (2 * g) → ℤ := fun c j => ∑ i, Out.stdSymp g i j * ((c i).val : ℤ)
  have hW : ∀ (c : Fin (2 * g) → ZMod k) j, W (∏ i, p i ^ (c i).val) (p j) (z ^ e c j) := by
    intro c j
    have h := rel_prod (fun x v => W x (p j) v) (hone _ (hp j))
      (fun x x' v v' hx hx' => hm x x' (p j) v v' hx hx') Finset.univ p
      (fun i => z ^ Out.stdSymp g i j) (fun i => (c i).val) (fun i => hw i j)
    have hz' : (∏ i, (z ^ Out.stdSymp g i j) ^ (c i).val) = z ^ e c j := by
      simp only [e, zpow_finset_sum_divisor]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_natCast, ← zpow_mul]
    simpa only [hz'] using h
  have htors : ∀ c : Fin (2 * g) → ZMod k, (∏ i, p i ^ (c i).val) ^ k = 1 := by
    intro c
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, hp i, one_pow]
  intro c c' hcc
  have hcc' : (∏ i, p i ^ (c i).val) = ∏ i, p i ^ (c' i).val := hcc
  have key : ∀ j, z ^ e c j = z ^ e c' j := by
    intro j
    obtain ⟨w, _, huniq⟩ := hu _ (p j) (htors c) (hp j)
    have h1 := huniq _ (hW c j)
    have h2 := huniq _ (hcc' ▸ hW c' j)
    rw [h1, h2]
  apply eq_of_sum_stdSymp (R := ZMod k) c c'
  intro j
  have hd : ((e c j : ℤ) : ZMod k) = ((e c' j : ℤ) : ZMod k) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ← hz.zpow_eq_one_iff_dvd, zpow_sub, key j, mul_inv_cancel]
  simpa [e, mul_comm] using hd

private theorem comp_list_prod_eq_prod_map_comp_over {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T)
    (l : List (T ⟶ A)) : f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp [MonObj.comp_one]
  | cons x l ih => simp [List.prod_cons, MonObj.comp_mul, ih]

theorem comp_linComb {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (a : Fin n → ℕ) : f ≫ Out.linComb y a = Out.linComb (fun i => f ≫ y i) a := by
  unfold Out.linComb
  rw [comp_list_prod_eq_prod_map_comp_over, List.map_ofFn]
  simp [Function.comp_def, MonObj.comp_pow]

end GlobalTheory.SympBasis

namespace GlobalTheory


open SympBasis in
theorem symplectic_system_torsion_basis :
    Out.Laws → ∀ (K₀ : Type) [Field K₀] (P : Out.PolAV (Sp K₀)) (k : ℕ) (ze : K₀ˣ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K₀) ⟶ P.A)), (k : K₀) ≠ 0 → IsPrimitiveRoot ze k → (∀ i, pt i ^ k = 1) → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn ze ^ Out.stdSymp P.g i j)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp K₀) (y : Over.mk x ⟶ P.A), y ^ k = 1 → ∃! c : Fin (2 * P.g) → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K₀)) ≫ pt i) (fun i => (c i).val) = y := by
  intro hL K₀ _ P k ze pt hk hze hpt hw K _ _ x y hy
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk (by simp)
  have : NeZero k := ⟨hk0⟩
  have hsep : IsSeparated P.A.hom := by
    obtain ⟨_, _, _, _⟩ := P.isAb
    infer_instance

  let h : Over.mk x ⟶ Out.baseOver (Sp K₀) := Over.homMk x (by simp)

  have hpre : ∀ s s' : Out.baseOver (Sp K₀) ⟶ P.A, h ≫ s = h ≫ s' → s = s' := by
    intro s s' hss
    have : IsReduced (Out.baseOver (Sp K₀)).left := inferInstanceAs (IsReduced (Sp K₀))
    have : IsDominant (X := Sp K) (Y := (Out.baseOver (Sp K₀)).left) x :=
      inferInstanceAs (IsDominant (X := Sp K) (Y := Sp K₀) x)
    apply Over.OverMorphism.ext
    refine ext_of_isDominant_of_isSeparated P.A.hom ?_ x ?_
    · rw [Over.w s, Over.w s']
    · simpa [h] using congrArg CommaMorphism.left hss

  have hzu : IsPrimitiveRoot (unitOn ze) k := by
    unfold unitOn
    refine hze.map_of_injective (Units.map_injective ?_)
    exact Function.LeftInverse.injective
      (g := (Scheme.ΓSpecIso (CommRingCat.of K₀)).hom.hom) fun a => by simp

  obtain ⟨hu, hm, -, -⟩ := hL.weil (Sp K₀) P k (Out.baseOver (Sp K₀))
  have hinj0 := SympBasis.injective_of_pairing (fun a b c => Out.WeilIs P.A P.L (k : ℤ) a b c) k hu
    (fun a a' b c c' => hm a a' b c c') pt hpt (unitOn ze) hzu hw

  have hlin : ∀ c : Fin (2 * P.g) → ZMod k,
      Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val) = h ≫ ∏ i, pt i ^ (c i).val := by
    intro c
    rw [← SympBasis.comp_linComb]
    unfold Out.linComb
    rw [List.prod_ofFn]
  have htors : ∀ c : Fin (2 * P.g) → ZMod k,
      (Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val)) ^ k = 1 := by
    intro c
    rw [hlin, ← MonObj.comp_pow, ← Finset.prod_pow,
      Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hpt i, one_pow]]
    exact MonObj.comp_one _
  let Φ : (Fin (2 * P.g) → ZMod k) → {y : Over.mk x ⟶ P.A // y ^ k = 1} := fun c => ⟨_, htors c⟩
  have hΦ : Function.Injective Φ := by
    intro c c' hcc
    have h1 : Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val) =
        Out.linComb (fun i => h ≫ pt i) (fun i => (c' i).val) := congrArg Subtype.val hcc
    rw [hlin, hlin] at h1
    exact hinj0 (hpre _ _ h1)

  have hkK : ((k : ℕ) : K) ≠ 0 := by
    have hc : ((k : ℕ) : K) = (Spec.preimage x).hom (k : K₀) := by simp
    rw [hc]
    exact (map_ne_zero_iff _ (Spec.preimage x).hom.injective).2 hk
  have hcard := (hL.mulN (Sp K₀) P k (Nat.one_le_iff_ne_zero.2 hk0)).2.2.2.2 K x hkK
  have : Finite {y : Over.mk x ⟶ P.A // y ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hbij : Function.Bijective Φ := hΦ.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin])
  obtain ⟨c, hc⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨c, congrArg Subtype.val hc,
    fun c' hc' => hbij.1 (Subtype.ext (hc'.trans (congrArg Subtype.val hc).symm))⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsoDifferBySimilitude
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} in
theorem _root_.GlobalTheory.tateIso_ev_eq_iff (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ D.ModN n (a - b) := by
  have key : I.ev n (a - b) * I.ev n b = I.ev n a := by rw [← I.add, sub_add_cancel]
  rw [show D.ModN n (a - b) ↔ ∃ c, a - b = n • c from Iff.rfl, ← I.ker n hn, ← key]
  exact mul_eq_right


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} in
theorem _root_.GlobalTheory.tateIso_ev_pow (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a : D.La) :
    I.ev n a ^ n = 1 :=
  (I.onto n hn _).mpr ⟨a, rfl⟩

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} in
private lemma exists_linearMap_ev_eq_of_tateIso (I I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D.La, ∀ a, I.ev n (f a) = I'.ev n a := by
  classical
  haveI := D.proj
  let N : Submodule (𝓞 E) D.La := LinearMap.range ((n : 𝓞 E) • LinearMap.id)
  have hN : ∀ x, x ∈ N ↔ D.ModN n x := by
    intro x
    show (∃ y, (n : 𝓞 E) • y = x) ↔ ∃ y, x = n • y
    simp only [Nat.cast_smul_eq_nsmul]
    constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨y, hy.symm⟩
  have hrel : ∀ x y, I.ev n x = I.ev n y ↔ x - y ∈ N := fun x y =>
    (_root_.GlobalTheory.tateIso_ev_eq_iff I hn x y).trans (hN _).symm
  have hs : ∀ a, ∃ b, I.ev n b = I'.ev n a :=
    fun a => (I.onto n hn _).mp (_root_.GlobalTheory.tateIso_ev_pow I' hn a)
  choose s hs using hs
  let g : D.La →ₗ[𝓞 E] D.La ⧸ N :=
    { toFun := fun a => N.mkQ (s a)
      map_add' := fun a b => by
        rw [← map_add (f := _), Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrel,
          I.add, hs, hs, hs, I'.add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply,
          Submodule.Quotient.eq, ← hrel, I.lin, hs, hs, I'.lin] }
  obtain ⟨f, hf⟩ := Module.projective_lifting_property N.mkQ g (Submodule.mkQ_surjective N)
  refine ⟨f, fun a => ?_⟩
  have h1 : N.mkQ (f a) = N.mkQ (s a) := LinearMap.congr_fun hf a
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrel] at h1
  rw [h1, hs]


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.tateIso_differ_by_similitude :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e, ∃ g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n := by
  intro E _ _ _ H D k _ Q _ act e he I I'
  have hf : ∀ n, ∃ f : D.La →ₗ[𝓞 E] D.La, 0 < n → ∀ a, I.ev n (f a) = I'.ev n a := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨f, hf⟩ := exists_linearMap_ev_eq_of_tateIso I I' hn
      exact ⟨f, fun _ => hf⟩
  choose f hf using hf
  have hk : ∀ n, ∃ ν : ℤ, 0 < n → I'.ζ n = I.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      have hprim : IsPrimitiveRoot ((I.ζ n : kˣ) : k) n :=
        IsPrimitiveRoot.coe_units_iff.mpr (I.ζ_prim n hn)
      have hpow : ((I'.ζ n : kˣ) : k) ^ n = 1 := by
        rw [← Units.val_pow_eq_pow_val, (I'.ζ_prim n hn).pow_eq_one, Units.val_one]
      obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hpow
      refine ⟨i, fun _ => ?_⟩
      ext
      rw [zpow_natCast, Units.val_pow_eq_pow_val, hi]
  choose ν hν using hk
  refine ⟨⟨f, ν, ?_, ?_, ?_⟩, fun n hn => ⟨fun a => (hf n hn a).symm, hν n hn⟩⟩
  · intro n m hn hm a
    rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I hn, ← I.tower n m hn hm, hf (n * m) (Nat.mul_pos hn hm),
      hf n hn, I'.tower n m hn hm]
  · intro n hn
    obtain ⟨g, hg⟩ := exists_linearMap_ev_eq_of_tateIso I' I hn
    refine ⟨g, fun a => ⟨?_, ?_⟩⟩
    · rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I' hn, hg, hf n hn]
    · rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I hn, hf n hn, hg]
  · intro n hn a b
    have h1 := I.isom n hn (f n a) (f n b)
    have h2 := I'.isom n hn a b
    rw [hf n hn, hf n hn] at h1
    have hc := he n _ _ _ _ hn (_root_.GlobalTheory.tateIso_ev_pow I' hn a)
      (_root_.GlobalTheory.tateIso_ev_pow I' hn b) h1 h2
    rw [hν n hn, ← zpow_mul] at hc
    rw [← (I.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, hc, mul_inv_cancel]

end GlobalTheory
end

