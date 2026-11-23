module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfTameDescent
section
open scoped TensorProduct

namespace GlobalTheory

namespace TameFlat

open TensorProduct

theorem flat_of_retraction {A B R : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup R] [Module A R] (e : B →ₗ[A] A) (he : e 1 = 1)
    [Module.Flat B (B ⊗[A] R)] : Module.Flat A R := by
  classical
  rw [Module.Flat.iff_rTensor_injective']
  intro I

  have hmem : ∀ z ∈ I.map (algebraMap A B), ∀ c : B, e (c * z) ∈ I := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro c
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      exact I.mul_mem_right _ ha
    | zero => intro c; simp
    | add x y _ _ hx hy => intro c; rw [mul_add, map_add (f := _)]; exact I.add_mem (hx c) (hy c)
    | smul d x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx (c * d)
  set J : Ideal B := I.map (algebraMap A B)

  let eJ : J →ₗ[A] I := LinearMap.codRestrict (I.restrictScalars A)
    (e ∘ₗ J.subtype.restrictScalars A) (fun z => by simpa using hmem z z.2 1)
  have heJ : eJ ∘ₗ Algebra.idealMap B I = LinearMap.id := by
    ext i
    change e (algebraMap A B (i : A)) = (i : A)
    rw [Algebra.algebraMap_eq_smul_one, map_smul, he, smul_eq_mul, mul_one]

  let Φ : I ⊗[A] R →ₗ[A] J ⊗[B] (B ⊗[A] R) :=
    (AlgebraTensorModule.cancelBaseChange A B B J R).symm.toLinearMap.restrictScalars A ∘ₗ
      TensorProduct.map (Algebra.idealMap B I) LinearMap.id
  let Ψ : J ⊗[B] (B ⊗[A] R) →ₗ[A] I ⊗[A] R :=
    TensorProduct.map eJ LinearMap.id ∘ₗ
      (AlgebraTensorModule.cancelBaseChange A B B J R).toLinearMap.restrictScalars A
  have hΨΦ : ∀ x, Ψ (Φ x) = x := by
    intro x
    have : Ψ ∘ₗ Φ = LinearMap.id := by
      apply TensorProduct.ext'
      intro i r
      simp only [Ψ, Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [← LinearMap.comp_apply eJ, heJ, LinearMap.id_apply]
    exact congrArg (fun f => f x) this
  have hinc : Function.Injective (LinearMap.rTensor (B ⊗[A] R) J.subtype) :=
    Module.Flat.iff_rTensor_injective'.mp inferInstance J

  have hkey : ∀ x, TensorProduct.lid B (B ⊗[A] R) (LinearMap.rTensor (B ⊗[A] R) J.subtype (Φ x)) =
      (1 : B) ⊗ₜ[A] TensorProduct.lid A R (LinearMap.rTensor R I.subtype x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul i r =>
      simp only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
        AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.rTensor_tmul,
        Submodule.subtype_apply, TensorProduct.lid_tmul]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      change algebraMap A B (i : A) ⊗ₜ[A] r = _
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, TensorProduct.tmul_add]
  intro x y hxy
  have h1 : Φ x = Φ y := by
    apply hinc
    apply (TensorProduct.lid B (B ⊗[A] R)).injective
    rw [hkey, hkey, hxy]
  rw [← hΨΦ x, ← hΨΦ y, h1]

theorem exists_retraction {Γ A B : Type} [Group Γ] [Finite Γ] [CommRing A] [CommRing B]
    [MulSemiringAction Γ B] [Algebra A B] [SMulCommClass Γ A B] [Algebra.IsInvariant A B Γ]
    (hinj : Function.Injective (algebraMap A B)) (b : B) (hb : ∑ᶠ g : Γ, g • b = 1) :
    ∃ e : B →ₗ[A] A, e 1 = 1 := by
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  rw [finsum_eq_sum_of_fintype] at hb
  have hfix : ∀ x : B, ∃ a : A, algebraMap A B a = ∑ g : Γ, g • (b * x) := by
    intro x
    apply Algebra.IsInvariant.isInvariant (G := Γ)
    intro h
    rw [Finset.smul_sum]
    simp_rw [← mul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => g • (b * x))
  choose f hf using hfix
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply hinj
    rw [map_add (f := _), hf, hf, hf, ← Finset.sum_add_distrib]
    simp_rw [mul_add, smul_add]
  · intro a x
    apply hinj
    rw [RingHom.id_apply, smul_eq_mul, map_mul, hf, hf, ← Algebra.smul_def, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_smul_comm, smul_comm]
  · show f 1 = 1
    apply hinj
    rw [hf, mul_one, map_one, hb]

end TameFlat

theorem flat_of_tame_descent :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R]
      [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R]
      [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C]
      [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ]
      [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) →
      Function.Injective (algebraMap R C) →
      (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) →
      Algebra.IsPushout A B R C → Module.Flat B C → (∃ b : B, ∑ᶠ g : Γ, g • b = 1) →
      Module.Flat A R := by
  intro Γ _ _ A B R C
  intros
  rename_i hAB _ _ hpo hflat htr
  obtain ⟨b, hb⟩ := htr
  obtain ⟨e, he⟩ := TameFlat.exists_retraction (Γ := Γ) (A := A) hAB b hb
  have : Module.Flat B (B ⊗[A] R) := Module.Flat.of_linearEquiv hpo.out.equiv
  exact TameFlat.flat_of_retraction e he

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
private lemma comap_algebraMap_fractionRing_specializes (O F : Type) [CommRing O] [IsDomain O] [Field F]
    [Algebra O F] [IsFractionRing O F] (x : PrimeSpectrum F) (y : PrimeSpectrum O) :
    PrimeSpectrum.comap (algebraMap O F) x ⤳ y := by
  rw [← PrimeSpectrum.le_iff_specializes]
  intro a ha
  have h0 : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [PrimeSpectrum.comap_asIdeal, h0, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O F)] at ha
  rw [Ideal.mem_bot.mp ha]
  exact zero_mem _


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.genericPart_dense_proOpen : ∀ (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F] (X U : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (jQ : U ⟶ pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))), Flat s → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s → IsOpenImmersion jQ → Dense (Set.range jQ) → IsLocallyNoetherian X ∧ CompactSpace X ∧ X.IsSeparated ∧ IsPreimmersion (jQ ≫ pullback.fst _ _) ∧ Flat (jQ ≫ pullback.fst _ _) ∧ IsDominant (jQ ≫ pullback.fst _ _) ∧ QuasiCompact (jQ ≫ pullback.fst _ _) := by
  intro O F _ _ _ _ _ X U s jQ hflat hproj hopen hdense
  obtain ⟨N, i, hi, hsi⟩ := hproj
  have := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N
  have hprop : IsProper s := by rw [← hsi]; infer_instance
  have hnO : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hnF : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hcF : CompactSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hcO : CompactSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hsepO : IsSeparated (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O).toSpecΓ := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hpre : IsPreimmersion (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have hflg : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat F (nonZeroDivisors O)
  have hnP : IsLocallyNoetherian (pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))
  have hcP : CompactSpace ↥(pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))
  have : IsNoetherian (pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := jQ.isOpenEmbedding.isInducing.noetherianSpace
  have hdomj : IsDominant jQ := ⟨hdense⟩
  have hdomf : IsDominant (pullback.fst s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) := by
    constructor
    intro x
    obtain ⟨p⟩ : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
    have hp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F) p ⤳ s x := comap_algebraMap_fractionRing_specializes O F p (s x)
    obtain ⟨x', hx', hsx'⟩ := Flat.generalizingMap s hp
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) x' p hsx'
    exact closure_mono (show {x'} ⊆ Set.range _ from Set.singleton_subset_iff.mpr ⟨z, hz⟩)
      (specializes_iff_mem_closure.mp hx')
  refine ⟨LocallyOfFiniteType.isLocallyNoetherian s, QuasiCompact.compactSpace_of_compactSpace s,
    ?_, inferInstance, inferInstance, inferInstance, inferInstance⟩
  constructor
  rw [← terminal.comp_from s]
  infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HermFormSwapOfIsHermitian
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LatticeHom

theorem exists_le_mul_of_homogeneous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (q q' : E → ℝ) (hq : Continuous q) (hq' : Continuous q') (hpos : ∀ z, z ≠ 0 → 0 < q z)
    (hs : ∀ (t : ℝ) z, q (t • z) = t ^ 2 * q z) (hs' : ∀ (t : ℝ) z, q' (t • z) = t ^ 2 * q' z) :
    ∃ C : ℝ, ∀ z, q' z ≤ C * q z := by
  have hS : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  have hcont : ContinuousOn (fun z => q' z / q z) (Metric.sphere (0 : E) 1) := by
    refine hq'.continuousOn.div hq.continuousOn ?_
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
    exact (hpos z hz0).ne'
  obtain ⟨C, hC⟩ := hS.bddAbove_image hcont
  refine ⟨C, fun z => ?_⟩
  have h0 : ∀ f : E → ℝ, (∀ (t : ℝ) z, f (t • z) = t ^ 2 * f z) → f 0 = 0 := by
    intro f hf
    simpa using hf 0 0
  by_cases hz : z = 0
  · rw [hz, h0 q hs, h0 q' hs', mul_zero]
  · have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hwS : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr0.ne']
    have hzw : z = ‖z‖ • (‖z‖⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
    have hw0 : ‖z‖⁻¹ • z ≠ 0 := by
      intro h
      rw [h] at hwS
      simp at hwS
    have hwpos := hpos _ hw0
    have hCw : q' (‖z‖⁻¹ • z) / q (‖z‖⁻¹ • z) ≤ C := hC (Set.mem_image_of_mem _ hwS)
    rw [div_le_iff₀ hwpos] at hCw
    rw [hzw, hs, hs']
    calc ‖z‖ ^ 2 * q' (‖z‖⁻¹ • z) ≤ ‖z‖ ^ 2 * (C * q (‖z‖⁻¹ • z)) :=
          mul_le_mul_of_nonneg_left hCw (sq_nonneg _)
      _ = C * (‖z‖ ^ 2 * q (‖z‖⁻¹ • z)) := by ring

theorem hermForm_swap_of_isHermitian {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = (starRingEnd ℂ) (hermForm Hm z w) := by
  unfold hermForm
  change _ = star _
  simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h.apply j i]
  ring

theorem hermForm_add_add {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (z + w) (z + w) = hermForm Hm z z + hermForm Hm z w + hermForm Hm w z + hermForm Hm w w := by
  unfold hermForm
  simp only [star_add, mulVec_add, add_dotProduct, dotProduct_add]
  ring

theorem re_hermForm_real_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z : Fin g → ℂ) :
    (hermForm Hm (t • z) (t • z)).re = t ^ 2 * (hermForm Hm z z).re := by
  unfold hermForm
  have hst : star (t • z) = t • star z := by rw [star_smul, star_trivial]
  rw [hst, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul, Complex.smul_re]
  ring

theorem continuous_re_hermForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun z : Fin g → ℂ => (hermForm Hm z z).re := by
  unfold hermForm
  simp only [dotProduct, mulVec, Pi.star_apply]
  fun_prop

theorem exists_hermForm_pull {g g' : ℕ} {Hm : Matrix (Fin g') (Fin g') ℂ} (h : Hm.IsHermitian)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) :
    ∃ K : Matrix (Fin g) (Fin g) ℂ, K.IsHermitian ∧ ∀ z w, hermForm K z w = hermForm Hm (F z) (F w) := by
  set M := LinearMap.toMatrix' F
  have hF : ∀ z, F z = M *ᵥ z := fun z => by rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  refine ⟨Mᵀ * Hm * Mᵀᴴ, isHermitian_mul_mul_conjTranspose _ h, fun z w => ?_⟩
  unfold hermForm
  rw [hF, hF, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec z Mᵀ, vecMul_transpose, ← star_vecMul,
    vecMul_transpose]

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}

theorem semicharacter_add (u : HolUnif A L g) (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) (l m : u.Λ) :
    χ (l + m) = χ l * χ m * cexp (Real.pi * I * (hermForm Hm l m).im) := by
  obtain ⟨i, hi⟩ := GlobalTheory.SymmetricSemicharacter.exists_chart u GlobalTheory.SymmetricSemicharacter.valueRules hL 0
  have hfr := h.2.2.2
  have hl : ⊤ ≤ (u.ex (0 + (l : Fin g → ℂ))).left ⁻¹ᵁ L.U i := by
    rw [GlobalTheory.SectionTheta.ex_add_lattice]; exact hi
  have hex : u.ex ((l : Fin g → ℂ) + m) = u.ex 0 := by
    simpa using GlobalTheory.SectionTheta.ex_add_lattice u 0 (l + m)
  have hX : u.fr i ((l : Fin g → ℂ) + m) ≠ 0 := u.fr_ne i _ (by rw [hex]; exact hi)
  have hz : ∀ x, hermForm Hm 0 x = 0 := fun x => by simp [hermForm]
  have e1 : u.fr i 0 = χ (l + m) * cexp (Real.pi * hermForm Hm 0 ((l + m : u.Λ) : Fin g → ℂ) +
      Real.pi / 2 * hermForm Hm ((l + m : u.Λ) : Fin g → ℂ) ((l + m : u.Λ) : Fin g → ℂ)) *
      u.fr i (0 + ((l + m : u.Λ) : Fin g → ℂ)) := hfr (l + m) i 0 hi
  have e2 : u.fr i 0 = χ l * cexp (Real.pi * hermForm Hm 0 l + Real.pi / 2 * hermForm Hm l l) *
      u.fr i (0 + (l : Fin g → ℂ)) := hfr l i 0 hi
  have e3 : u.fr i (0 + (l : Fin g → ℂ)) = χ m * cexp (Real.pi * hermForm Hm (0 + (l : Fin g → ℂ)) m +
      Real.pi / 2 * hermForm Hm m m) * u.fr i (0 + (l : Fin g → ℂ) + m) := hfr m i (0 + l) hl
  simp only [hz, zero_add, mul_zero, Submodule.coe_add] at e1 e2 e3
  rw [e3] at e2
  rw [e2] at e1
  have hb : hermForm Hm (m : Fin g → ℂ) l = (starRingEnd ℂ) (hermForm Hm l m) :=
    hermForm_swap_of_isHermitian h.1 l m
  have hsc := Complex.sub_conj (hermForm Hm l m)
  have hexp : cexp (Real.pi / 2 * hermForm Hm l l) * cexp (Real.pi * hermForm Hm l m + Real.pi / 2 * hermForm Hm m m) =
      cexp (Real.pi / 2 * hermForm Hm ((l : Fin g → ℂ) + m) ((l : Fin g → ℂ) + m)) *
        cexp (Real.pi * I * (hermForm Hm l m).im) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hermForm_add_add, hb]
    congr 1
    push_cast at hsc ⊢
    linear_combination (Real.pi / 2 : ℂ) * hsc
  have hC := Complex.exp_ne_zero (Real.pi / 2 * hermForm Hm ((l : Fin g → ℂ) + m) ((l : Fin g → ℂ) + m))
  have key : (χ (l + m) - χ l * χ m * cexp (Real.pi * I * (hermForm Hm l m).im)) *
      (cexp (Real.pi / 2 * hermForm Hm ((l : Fin g → ℂ) + m) ((l : Fin g → ℂ) + m)) *
        u.fr i ((l : Fin g → ℂ) + m)) = 0 := by
    linear_combination -e1 + (χ l * χ m * u.fr i ((l : Fin g → ℂ) + m)) * hexp
  rcases mul_eq_zero.1 key with h1 | h1
  · exact sub_eq_zero.1 h1
  · exact absurd h1 (mul_ne_zero hC hX)

private theorem conj_cexp_pi_mul_I_mul_real (t : ℝ) :
    (starRingEnd ℂ) (cexp (Real.pi * I * t)) = cexp (-(Real.pi * I * t)) := by
  rw [← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  ring

theorem exists_complementary_theta
    (hth : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ H₀ : Matrix (Fin g) (Fin g) ℂ, (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) → ∃ ρ : ℝ, ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, ρ * (z ⬝ᵥ H₀.mulVec (star z)).re ≤ (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, χ (l + m) = χ l * χ m * cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)) → ∀ z₀, ∃ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ θ z₀ ≠ 0 ∧ ∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z)
    (u : HolUnif A L g) (u' : HolUnif A' L' g') (hL : L.IsLB) (hL' : L'.IsLB)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ' : u'.Λ → ℂ}
    (h : u.IsAH Hm χ) (h' : u'.IsAH Hm' χ') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u'.Λ) (N : ℕ) :
    ∃ d : ℕ, ∀ z₀, ∃ G : (Fin g → ℂ) → ℂ, G z₀ ≠ 0 ∧
      ∀ θ, u'.IsThetaFn Hm' χ' N θ → u.IsThetaFn Hm χ d (fun z => θ (F z) * G z) := by
  obtain ⟨K, hK, hKF⟩ := exists_hermForm_pull h'.1 F
  obtain ⟨Fl, hFl⟩ : ∃ Fl : u.Λ → u'.Λ, ∀ l, ((Fl l : u'.Λ) : Fin g' → ℂ) = F l :=
    ⟨fun l => ⟨F l, hF l l.2⟩, fun _ => rfl⟩
  have hFl_add : ∀ l m, Fl (l + m) = Fl l + Fl m := fun l m => by
    apply Subtype.ext
    rw [Submodule.coe_add, hFl, hFl, hFl, Submodule.coe_add, map_add (f := _)]
  obtain ⟨ρ, hρ⟩ := hth g u.Λ u.discrete u.full Hm h.2.1
  obtain ⟨C, hC⟩ := exists_le_mul_of_homogeneous (fun z => (hermForm Hm z z).re) (fun z => (hermForm K z z).re)
    (continuous_re_hermForm Hm) (continuous_re_hermForm K) h.2.1 (re_hermForm_real_smul Hm)
    (re_hermForm_real_smul K)
  obtain ⟨d, hd⟩ := exists_nat_ge (ρ + N * C)
  refine ⟨d, fun z₀ => ?_⟩
  obtain ⟨Hg, hHg⟩ : ∃ Hg : Matrix (Fin g) (Fin g) ℂ, Hg = (d : ℂ) • Hm - (N : ℂ) • K := ⟨_, rfl⟩
  obtain ⟨χg, hχg⟩ : ∃ f : u.Λ → ℂ, ∀ l, f l = χ l ^ d * (starRingEnd ℂ) (χ' (Fl l)) ^ N := ⟨_, fun _ => rfl⟩
  have hHg_form : ∀ z w, hermForm Hg z w = d * hermForm Hm z w - N * hermForm K z w := by
    intro z w
    simp [hHg, hermForm, sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul]
  have hHgH : Hg.IsHermitian := by
    rw [hHg, IsHermitian, conjTranspose_sub, conjTranspose_smul, conjTranspose_smul, h.1.eq, hK.eq]
    simp
  have hbound : ∀ z : Fin g → ℂ, ρ * (hermForm Hm z z).re ≤ (hermForm Hg z z).re := by
    intro z
    have hre : (hermForm Hg z z).re = d * (hermForm Hm z z).re - N * (hermForm K z z).re := by
      rw [hHg_form]; simp
    rw [hre]
    have h1 := hC z
    have h2 : 0 ≤ (hermForm Hm z z).re := by
      by_cases hz : z = 0
      · simp [hz, hermForm]
      · exact (h.2.1 z hz).le
    nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hd) h2]
  have hnorm : ∀ l, ‖χg l‖ = 1 := by
    intro l
    rw [hχg, norm_mul, norm_pow, norm_pow, h.2.2.1, Complex.norm_conj, h'.2.2.1, one_pow, one_pow, _root_.one_mul]
  have hsemi : ∀ l m : u.Λ, χg (l + m) = χg l * χg m *
      cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hg.mulVec (star (m : Fin g → ℂ))).im) := by
    intro l m
    change χg (l + m) = χg l * χg m * cexp (Real.pi * I * (hermForm Hg l m).im)
    have s1 := semicharacter_add u hL h l m
    have s2 := semicharacter_add u' hL' h' (Fl l) (Fl m)
    rw [hFl, hFl, ← hKF] at s2
    rw [hχg, hχg, hχg, hFl_add, s1, s2, hHg_form, map_mul, map_mul, conj_cexp_pi_mul_I_mul_real]
    have him : ((d : ℂ) * hermForm Hm l m - N * hermForm K l m).im =
        d * (hermForm Hm l m).im - N * (hermForm K l m).im := by simp
    rw [him]
    have he : cexp (Real.pi * I * (hermForm Hm l m).im) ^ d * cexp (-(Real.pi * I * (hermForm K l m).im)) ^ N =
        cexp (Real.pi * I * ((d * (hermForm Hm l m).im - N * (hermForm K l m).im : ℝ) : ℂ)) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    linear_combination (χ l ^ d * χ m ^ d * (starRingEnd ℂ) (χ' (Fl l)) ^ N * (starRingEnd ℂ) (χ' (Fl m)) ^ N) * he
  obtain ⟨G, hGd, hG0, hGt⟩ := hρ Hg χg hHgH hbound hnorm hsemi z₀
  refine ⟨G, hG0, fun θ hθ => ⟨?_, fun l z => ?_⟩⟩
  · exact (hθ.1.comp (LinearMap.toContinuousLinearMap F).differentiable).mul hGd
  · have t1 := hθ.2 (Fl l) (F z)
    rw [hFl, ← hKF, ← hKF] at t1
    have t2 : G (z + l) = χg l * cexp (Real.pi * hermForm Hg z l + Real.pi / 2 * hermForm Hg l l) * G z := hGt l z
    have hψ : χ' (Fl l) * (starRingEnd ℂ) (χ' (Fl l)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h'.2.2.1]; simp
    have hψN : (χ' (Fl l) * (starRingEnd ℂ) (χ' (Fl l))) ^ N = 1 := by rw [hψ, one_pow]
    have hexp : cexp (Real.pi * (d * hermForm Hm z l - N * hermForm K z l) +
        Real.pi / 2 * (d * hermForm Hm l l - N * hermForm K l l)) *
        cexp (Real.pi * hermForm K z l + Real.pi / 2 * hermForm K l l) ^ N =
        cexp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) ^ d := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      ring
    show θ (F (z + l)) * G (z + l) = _ * (θ (F z) * G z)
    rw [map_add (f := _), t1, t2, hHg_form, hHg_form, hχg]
    linear_combination (χ l ^ d * θ (F z) * G z * (cexp (Real.pi * (d * hermForm Hm z l - N * hermForm K z l) +
        Real.pi / 2 * (d * hermForm Hm l l - N * hermForm K l l)) *
        cexp (Real.pi * hermForm K z l + Real.pi / 2 * hermForm K l l) ^ N)) * hψN +
      (χ l ^ d * θ (F z) * G z) * hexp

end GlobalTheory.LatticeHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliRepOfBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

def objRestrictBase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {B : Type} [CommRing B] {b : Base l B} (j : KA l →+* B) {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (hρ : j (baseKA l).ρ = b.ρ) (hζ : j (baseKA l).ζ = b.ζ) : Obj D l (baseKA l) (s ≫ spMap j) where
  t := o.t
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta := o.eta
  eta_add := o.eta_add
  eta_ker := o.eta_ker
  etaA := o.etaA
  etaA_add := o.etaA_add
  etaA_ker := o.etaA_ker
  geom := by
    intro k _ _ x β hx
    have h1 : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := by
      simp [spMap]
    have h2 : β = (Spec.preimage (x ≫ s)).hom.comp j := by
      have h3 : spMap β = spMap ((Spec.preimage (x ≫ s)).hom.comp j) := by
        rw [← hx, ← Category.assoc]
        conv_lhs => rw [h1]
        simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)
    have h := o.geom k x _ h1
    rw [← hρ, ← hζ] at h
    subst h2
    exact h

theorem moduli_rep_of_base :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f) := by
  intro _ E _ _ _ H D l Xo B _ b j S s o hS hρ hζ
  obtain ⟨f, ⟨hf, ⟨m⟩⟩, hu⟩ := Xo.rep S (s ≫ spMap j) hS (objRestrictBase j o hρ hζ)
  refine ⟨f, ⟨hf, ⟨⟨m.toSABMap, m.eta, m.etaA⟩⟩⟩, ?_⟩
  rintro g ⟨hg, ⟨m'⟩⟩
  exact hu g ⟨hg, ⟨⟨m'.toSABMap, m'.eta, m'.etaA⟩⟩⟩

end GlobalTheory
end
end

