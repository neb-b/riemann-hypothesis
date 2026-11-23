module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsResidueEqZeroIff
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.ResidueBoxVolume


open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
theorem _root_.GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    (∃ y : v.adicCompletionIntegers F, x = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = 0) ↔ Valued.v x < 1 := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hy
    exact lt_of_le_of_ne ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).1 y.2) hy
  · intro hx
    refine ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 hx.le⟩, rfl, ?_⟩
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hx.ne

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
theorem _root_.GlobalTheory.ResidueBoxVolume.isOpen_val_lt_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen {x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | Valued.v x < 1} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Valued.mem_nhds]
  refine ⟨1, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hy' : y = (y - x) + x := by ring
  rw [hy']
  exact Valuation.map_add_lt _ (by simpa using hy) hx

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
private theorem mem_residue_box_singleton_iff (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))
    (s : ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F)) (x : V) :
    (∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({s} : Set _)) ↔
    ∀ i, ∃ y : v.adicCompletionIntegers F, e x i = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = s i := by
  simp only [Set.mem_singleton_iff, funext_iff]
  constructor
  · rintro ⟨y, h1, h2⟩ i
    exact ⟨y i, h1 i, h2 i⟩
  · intro h
    choose y hy1 hy2 using h
    exact ⟨y, hy1, hy2⟩

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
private theorem exists_residue_eq_iff_exists_residue_sub_eq_zero {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (c : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) (t : v.adicCompletionIntegers F)
    (ht : IsLocalRing.residue (v.adicCompletionIntegers F) t = c) :
    (∃ y : v.adicCompletionIntegers F, a = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = c) ↔
    ∃ y : v.adicCompletionIntegers F, a - t = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = 0 := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    exact ⟨y - t, rfl, by rw [map_sub, hy, ht, sub_self]⟩
  · rintro ⟨y, hy, hy0⟩
    refine ⟨y + t, ?_, by rw [map_add (f := _), hy0, ht, zero_add]⟩
    show a = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) + (t : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    rw [← hy]
    ring

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
private theorem exists_residueBox_eq_preimage_add_lemma_2 (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))
    (s : ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :
    ∃ w : V, {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({s} : Set _)} =
      (fun x => x + w) ⁻¹' {x | ∃ y : ι → v.adicCompletionIntegers F,
        (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} := by
  choose t ht using fun i => IsLocalRing.residue_surjective (s i)
  refine ⟨-e.symm (fun i => (t i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)), ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_residue_box_singleton_iff, Pi.zero_apply,
    map_add, map_neg, map_sub, ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply,
    Pi.neg_apply, Pi.sub_apply, ← sub_eq_add_neg]
  exact forall_congr' fun i => exists_residue_eq_iff_exists_residue_sub_eq_zero v _ _ _ (ht i)

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
private theorem measurableSet_residue_box_zero (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) :
    MeasurableSet {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} := by
  have h : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} =
      ⋂ i, (fun x => e x i) ⁻¹' {a : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | Valued.v a < 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, mem_residue_box_singleton_iff,
      Pi.zero_apply, _root_.GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff]
  rw [h]
  exact (isOpen_iInter_of_finite fun i =>
    (_root_.GlobalTheory.ResidueBoxVolume.isOpen_val_lt_one v).preimage ((continuous_apply i).comp e.continuous)).measurableSet

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
private theorem measure_residueBox_lemma (μ : Measure V) [μ.IsAddHaarMeasure]
    (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))
    (S : Set (ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F))) :
    μ {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ S} =
    S.ncard * μ {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} := by
  classical
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    _root_.GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hS : S.Finite := S.toFinite
  have hunion : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ S} =
      ⋃ s ∈ hS.toFinset, {x | ∃ y : ι → v.adicCompletionIntegers F,
        (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({s} : Set _)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_singleton_iff,
      exists_prop]
    constructor
    · rintro ⟨y, h1, h2⟩
      exact ⟨_, h2, y, h1, rfl⟩
    · rintro ⟨s, hs, y, h1, rfl⟩
      exact ⟨y, h1, hs⟩
  rw [hunion, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl fun s _ => ?_, Finset.sum_const, nsmul_eq_mul,
      Set.ncard_eq_toFinset_card S hS]
    obtain ⟨w, hw⟩ := exists_residueBox_eq_preimage_add_lemma_2 e s
    rw [hw, measure_preimage_add_right]
  · intro s _ s' _ hss'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨y, h1, h2⟩ ⟨y', h1', h2'⟩
    apply hss'
    have hyy : y = y' := funext fun i => Subtype.ext ((h1 i).symm.trans (h1' i))
    subst hyy
    rw [Set.mem_singleton_iff] at h2 h2'
    rw [← h2, ← h2']
  · intro s _
    obtain ⟨w, hw⟩ := exists_residueBox_eq_preimage_add_lemma_2 e s
    rw [hw]
    exact (measurableSet_residue_box_zero e).preimage (continuous_add_const w).measurable


open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
theorem _root_.GlobalTheory.ResidueBoxVolume.measureReal_residueBox (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι] (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) (S : Set (ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F))) :
    μ.real {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧ (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ S} * (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) ^ Fintype.card ι = (S.ncard : ℝ) * μ.real {x | ∀ i, e x i ∈ v.adicCompletionIntegers F} := by
  have hB : {x | ∀ i, e x i ∈ v.adicCompletionIntegers F} =
      {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ Set.univ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, and_true]
    constructor
    · intro h
      exact ⟨fun i => ⟨e x i, h i⟩, fun i => rfl⟩
    · rintro ⟨y, hy⟩ i
      rw [hy i]
      exact (y i).2
  rw [hB, measureReal_def, measureReal_def, measure_residueBox_lemma μ e Set.univ, measure_residueBox_lemma μ e S,
    Set.ncard_univ, Nat.card_fun, Nat.card_eq_fintype_card (α := ι), ENNReal.toReal_mul,
    ENNReal.toReal_mul]
  simp only [Nat.cast_pow, ENNReal.toReal_natCast, ENNReal.toReal_pow]
  ring

end GlobalTheory.ResidueBoxVolume
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntertwinerZeroOfCharacterTwist
section
open Formalism.MainNotions.N

namespace GlobalTheory

theorem _root_.GlobalTheory.commute_on_ker_of_commute_on_ker_inter :
    ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ₀ : Γ →* GL (Fin n) k) (η₀ η : Γ →* ℤˣ), (∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((η g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → (∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = (((η * η₀) g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → ∀ Y : Matrix (Fin n) (Fin n) k, (∀ g, η₀ g = 1 → η g = 1 → ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ∀ g, η₀ g = 1 → ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro Γ k _ _ _ n ρ₀ η₀ η hη hηη₀ Y hY g hg
  obtain ⟨Y₁, Y₂, rfl, h₁, h₂⟩ :=
    _root_.GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel Γ k n ρ₀ ρ₀ η₀.ker 1 η Y
      (fun g hg h1 => by simpa using hY g (MonoidHom.mem_ker.mp hg) h1)
  obtain ⟨A, B, hAB, hA, hB⟩ :=
    _root_.GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel Γ k n ρ₀ ρ₀ ⊤ η η₀ Y₂
      (fun g _ h1 => by simpa using h₂ g (MonoidHom.mem_ker.mpr h1))
  have hA0 : A = 0 := hη A (fun g => hA g (Subgroup.mem_top g))
  have hB0 : B = 0 := hηη₀ B (fun g => hB g (Subgroup.mem_top g))
  have hY₂ : Y₂ = 0 := by rw [hAB, hA0, hB0, add_zero]
  subst hY₂
  simpa using h₁ g (MonoidHom.mem_ker.mpr hg)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldIffNoResidualRoot
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.QuadFieldCriterion
open Polynomial IsLocalRing

theorem exists_root_of_residual {O : Type*} [CommRing O] [IsLocalRing O]
    [HenselianRing O (maximalIdeal O)] (t n : O) (hd : IsUnit (t ^ 2 - 4 * n))
    (r : ResidueField O) (hr : r ^ 2 - residue O t * r + residue O n = 0) :
    ∃ s : O, s ^ 2 - t * s + n = 0 := by
  obtain ⟨r₀, rfl⟩ := residue_surjective r
  have hmon : (X ^ 2 - C t * X + C n : O[X]).Monic := by monicity!
  have h0 : r₀ ^ 2 - t * r₀ + n ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff]; simpa using hr
  obtain ⟨s, hs, -⟩ := HenselianRing.is_henselian (I := maximalIdeal O) _ hmon r₀
    (by simpa using h0) (by
      have h1 : IsUnit (residue O (t ^ 2 - 4 * n)) := hd.map _
      have h2 : residue O (t ^ 2 - 4 * n) = (residue O (2 * r₀ - t)) ^ 2 := by
        simp only [map_sub, map_pow, map_mul, map_ofNat]
        linear_combination (-4) * hr
      rw [h2, isUnit_pow_iff two_ne_zero] at h1
      have h3 : eval r₀ (derivative (X ^ 2 - C t * X + C n : O[X])) = 2 * r₀ - t := by
        simp; norm_num
      rw [h3]
      exact h1)
  exact ⟨s, by simpa using hs⟩

theorem exists_root_of_fraction {O K : Type*} [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    [Field K] [Algebra O K] [IsFractionRing O K] (t n : O) (x : K)
    (hx : x ^ 2 - algebraMap O K t * x + algebraMap O K n = 0) :
    ∃ s : O, s ^ 2 - t * s + n = 0 := by
  have hmon : (X ^ 2 - C t * X + C n : O[X]).Monic := by monicity!
  have hi : IsIntegral O x := ⟨_, hmon, by simpa using hx⟩
  obtain ⟨s, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  refine ⟨s, IsFractionRing.injective O K ?_⟩
  simpa using hx

theorem isField_iff_no_root {K A : Type*} [Field K] [CommRing A] [Algebra K A] (w : A) (t n : K)
    (hw : w ^ 2 - algebraMap K A t * w + algebraMap K A n = 0)
    (hspan : ∀ z : A, ∃ a b : K, z = algebraMap K A a + algebraMap K A b * w)
    (hind : ∀ a b : K, algebraMap K A a + algebraMap K A b * w = 0 → a = 0 ∧ b = 0) :
    IsField A ↔ ¬ ∃ x : K, x ^ 2 - t * x + n = 0 := by
  constructor
  · rintro hF ⟨x, hx⟩
    letI := hF.toField
    have hx' : algebraMap K A x ^ 2 - algebraMap K A t * algebraMap K A x + algebraMap K A n = 0 := by
      simpa using congrArg (algebraMap K A) hx
    have hprod : (algebraMap K A (-x) + algebraMap K A 1 * w) *
        (algebraMap K A (x - t) + algebraMap K A 1 * w) = 0 := by
      simp only [map_neg, map_sub, map_one]
      linear_combination hw - hx'
    rcases mul_eq_zero.mp hprod with h | h
    · exact one_ne_zero (hind _ _ h).2
    · exact one_ne_zero (hind _ _ h).2
  · intro hno
    refine ⟨⟨1, 0, fun h => one_ne_zero (hind 1 0 (by simpa using h)).1⟩, mul_comm, ?_⟩
    intro z hz
    obtain ⟨a, b, rfl⟩ := hspan z
    have hN : a ^ 2 + t * a * b + n * b ^ 2 ≠ 0 := by
      intro hN
      by_cases hb : b = 0
      · subst hb
        have : a = 0 := by simpa using hN
        subst this
        simp at hz
      · exact hno ⟨-a / b, by field_simp; linear_combination hN⟩
    refine ⟨algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2)⁻¹ *
      (algebraMap K A a + algebraMap K A b * (algebraMap K A t - w)), ?_⟩
    have h1 : algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2)⁻¹ *
        algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hN, map_one]
    rw [← h1]
    simp only [map_add (f := _), map_mul, map_pow]
    linear_combination (- algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2)⁻¹ *
      algebraMap K A b ^ 2) * hw

theorem isField_iff_no_residual_root : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (A : Type) [CommRing A] [Algebra (Fv F v) A] (w : A) (t n : v.adicCompletionIntegers F), IsUnit (t ^ 2 - 4 * n) → w ^ 2 - algebraMap (Fv F v) A t * w + algebraMap (Fv F v) A n = 0 → (∀ z : A, ∃ a b : Fv F v, z = algebraMap (Fv F v) A a + algebraMap (Fv F v) A b * w) → (∀ a b : Fv F v, algebraMap (Fv F v) A a + algebraMap (Fv F v) A b * w = 0 → a = 0 ∧ b = 0) → (IsField A ↔ ¬ ∃ r : IsLocalRing.ResidueField (v.adicCompletionIntegers F), r ^ 2 - IsLocalRing.residue (v.adicCompletionIntegers F) t * r + IsLocalRing.residue (v.adicCompletionIntegers F) n = 0) := by
  intro F _ _ v A _ _ w t n hd hw hspan hind
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  rw [isField_iff_no_root w _ _ hw hspan hind]
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := exists_root_of_fraction (K := Fv F v) t n x hx
    exact ⟨residue _ s, by simpa using congrArg (residue _) hs⟩
  · rintro ⟨r, hr⟩
    obtain ⟨s, hs⟩ := exists_root_of_residual t n hd r hr
    exact ⟨(s : Fv F v), by
      simpa using congrArg (algebraMap (v.adicCompletionIntegers F) (Fv F v)) hs⟩

end GlobalTheory.QuadFieldCriterion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotIsFieldAdicCompletionTensorOfSplit
section
open scoped TensorProduct
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.SplitPlace

open scoped TensorProduct in
open NumberField IsDedekindDomain Polynomial in
private lemma isMaximal_and_algebraMap_mem_iff_of_mem_primesOver (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : Ideal (𝓞 E))
    (h : P ∈ v.asIdeal.primesOver (𝓞 E)) :
    P.IsMaximal ∧ ∀ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a ∈ P ↔ a ∈ v.asIdeal := by
  obtain ⟨hp, ho⟩ := h
  haveI := hp; haveI := ho; haveI := v.isMaximal
  refine ⟨Ideal.IsMaximal.of_liesOver_isMaximal P v.asIdeal, fun a => ?_⟩
  rw [Ideal.over_def P v.asIdeal, Ideal.under_def, Ideal.mem_comap]

open scoped TensorProduct in
open NumberField IsDedekindDomain Polynomial in
private lemma exists_root_quadratic_of_isUnit_of_mem_maximalIdeal (R : Type) [CommRing R]
    [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (b c : R)
    (hb : IsUnit b) (hc : c ∈ IsLocalRing.maximalIdeal R) : ∃ β : R, β ^ 2 + b * β + c = 0 := by
  have hmon : (X ^ 2 + C b * X + C c : R[X]).Monic := by monicity!
  obtain ⟨β, hβ, -⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal R)
    (X ^ 2 + C b * X + C c) hmon 0 (by simpa using hc) (by simpa using hb.map _)
  exact ⟨β, by simpa using hβ⟩


open scoped TensorProduct in
open NumberField IsDedekindDomain Polynomial in
theorem _root_.GlobalTheory.SplitPlace.not_isField_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F),
    (v.asIdeal.primesOver (𝓞 E)).ncard = 2 → ¬ IsField (v.adicCompletion F ⊗[F] E) := by
  intro F E _ _ _ _ _ hrank v hsplit hfield
  obtain ⟨P, Q, hPQ, hset⟩ := Set.ncard_eq_two.mp hsplit
  obtain ⟨hPmax, hPmem⟩ := isMaximal_and_algebraMap_mem_iff_of_mem_primesOver F E v P
    (by rw [hset]; exact Set.mem_insert _ _)
  obtain ⟨hQmax, hQmem⟩ := isMaximal_and_algebraMap_mem_iff_of_mem_primesOver F E v Q
    (by rw [hset]; exact Set.mem_insert_of_mem _ rfl)
  obtain ⟨α, hαP, hαQ⟩ := SetLike.not_le_iff_exists.mp
    (fun h => hPQ (hPmax.eq_of_le hQmax.ne_top h))
  have hαF : (α : E) ∉ (algebraMap F E).range := by
    rintro ⟨a, ha⟩
    have hint : IsIntegral ℤ a := by
      have h1 : IsIntegral ℤ (algebraMap F E a) := ha ▸ RingOfIntegers.isIntegral_coe α
      exact (isIntegral_algHom_iff ((Algebra.ofId F E).restrictScalars ℤ)
        (algebraMap F E).injective).mp h1
    have hα : algebraMap (𝓞 F) (𝓞 E) ⟨a, hint⟩ = α := RingOfIntegers.ext (by rw [← ha]; rfl)
    have hav : (⟨a, hint⟩ : 𝓞 F) ∈ v.asIdeal := (hPmem _).mp (hα ▸ hαP)
    exact hαQ (hα ▸ (hQmem _).mpr hav)
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ hrank
  have hint : IsIntegral (𝓞 F) α := Algebra.IsIntegral.isIntegral α
  have hdeg : (minpoly (𝓞 F) α).natDegree = 2 := by
    have hE : minpoly (𝓞 F) (α : E) = minpoly (𝓞 F) α :=
      minpoly.algHom_eq (IsScalarTower.toAlgHom (𝓞 F) (𝓞 E) E) Subtype.val_injective α
    have hF : minpoly F (α : E) = (minpoly (𝓞 F) α).map (algebraMap (𝓞 F) F) := by
      rw [← hE]
      exact minpoly.isIntegrallyClosed_eq_field_fractions' F (hint.map (IsScalarTower.toAlgHom (𝓞 F) (𝓞 E) E))
    have hle : (minpoly F (α : E)).natDegree ≤ 2 := hrank ▸ minpoly.natDegree_le (α : E)
    have hne1 : (minpoly F (α : E)).natDegree ≠ 1 := fun h => hαF (minpoly.natDegree_eq_one_iff.mp h)
    have hpos : 0 < (minpoly F (α : E)).natDegree :=
      minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral _)
    rw [hF, (minpoly.monic hint).natDegree_map] at hle hne1 hpos
    omega
  set b := (minpoly (𝓞 F) α).coeff 1 with hb
  set c := (minpoly (𝓞 F) α).coeff 0 with hc
  have hα2 : α ^ 2 + algebraMap (𝓞 F) (𝓞 E) b * α + algebraMap (𝓞 F) (𝓞 E) c = 0 := by
    have h := minpoly.aeval (𝓞 F) α
    have h2 : (minpoly (𝓞 F) α).coeff 2 = 1 := by
      rw [← hdeg]; exact (minpoly.monic hint).coeff_natDegree
    rw [aeval_eq_sum_range, hdeg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      h2] at h
    simp only [Algebra.smul_def, map_one, one_mul, pow_zero, pow_one, mul_one] at h
    linear_combination h
  have hcv : c ∈ v.asIdeal := by
    rw [← hPmem]
    have hce : algebraMap (𝓞 F) (𝓞 E) c = -(α ^ 2 + algebraMap (𝓞 F) (𝓞 E) b * α) := by
      linear_combination hα2
    rw [hce]
    exact P.neg_mem (P.add_mem (P.pow_mem_of_mem hαP 2 two_pos) (P.mul_mem_left _ hαP))
  have hbv : b ∉ v.asIdeal := by
    intro hbv
    have hsq : α ^ 2 = -(algebraMap (𝓞 F) (𝓞 E) b * α + algebraMap (𝓞 F) (𝓞 E) c) := by
      linear_combination hα2
    have hmem : α ^ 2 ∈ Q := by
      rw [hsq]
      exact Q.neg_mem (Q.add_mem (Q.mul_mem_right _ ((hQmem b).mpr hbv)) ((hQmem c).mpr hcv))
    exact hαQ (hQmax.isPrime.mem_of_pow_mem 2 hmem)
  haveI := _root_.GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  obtain ⟨β, hβ⟩ := exists_root_quadratic_of_isUnit_of_mem_maximalIdeal
    (v.adicCompletionIntegers F) (algebraMap (𝓞 F) _ b) (algebraMap (𝓞 F) _ c)
    ((_root_.GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v b).mpr hbv)
    (by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, _root_.GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff]
      exact not_not.mpr hcv)
  have hβF : (β : v.adicCompletion F) ^ 2 + algebraMap F (v.adicCompletion F) (b : F) * β
      + algebraMap F (v.adicCompletion F) (c : F) = 0 := by
    have h := congrArg (v.adicCompletionIntegers F).subtype hβ
    rw [map_add (f := _), map_add (f := _), map_mul, map_pow, map_zero] at h
    exact h
  have hαE : (α : E) ^ 2 + algebraMap F E (b : F) * α + algebraMap F E (c : F) = 0 := by
    have h := congrArg (algebraMap (𝓞 E) E) hα2
    rw [map_add (f := _), map_add (f := _), map_mul, map_pow, map_zero] at h
    exact h
  set x : v.adicCompletion F ⊗[F] E :=
    Algebra.TensorProduct.includeLeft (S := F) (B := E) (β : v.adicCompletion F) with hx
  set y : v.adicCompletion F ⊗[F] E :=
    Algebra.TensorProduct.includeRight (A := v.adicCompletion F) (α : E) with hy
  have hxeq : x ^ 2 + algebraMap F _ (b : F) * x + algebraMap F _ (c : F) = 0 := by
    have h := congrArg (Algebra.TensorProduct.includeLeft (R := F) (S := F) (B := E)) hβF
    rw [map_add (f := _), map_add (f := _), map_mul, map_pow, AlgHom.commutes, AlgHom.commutes, map_zero] at h
    exact h
  have hyeq : y ^ 2 + algebraMap F _ (b : F) * y + algebraMap F _ (c : F) = 0 := by
    have h := congrArg (Algebra.TensorProduct.includeRight (R := F) (A := v.adicCompletion F)) hαE
    rw [map_add (f := _), map_add (f := _), map_mul, map_pow, AlgHom.commutes, AlgHom.commutes, map_zero] at h
    exact h
  have hprod : (x - y) * (x + y + algebraMap F _ (b : F)) = 0 := by
    linear_combination hxeq - hyeq
  haveI := hfield.isDomain
  obtain ⟨z, hz⟩ : ∃ z : v.adicCompletion F,
      y = Algebra.TensorProduct.includeLeft (S := F) (B := E) z := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact ⟨β, (sub_eq_zero.mp h).symm⟩
    · refine ⟨-(β : v.adicCompletion F) - algebraMap F _ (b : F), ?_⟩
      rw [map_sub, map_neg, AlgHom.commutes, ← hx]
      linear_combination h
  obtain ⟨ℓ, hℓ1, hℓα⟩ : ∃ ℓ : E →ₗ[F] F, ℓ 1 = 0 ∧ ℓ α = 1 := by
    have hnot : (α : E) ∉ Submodule.span F {(1 : E)} := by
      rw [Submodule.mem_span_singleton]
      rintro ⟨a, ha⟩
      exact hαF ⟨a, by rw [Algebra.algebraMap_eq_smul_one]; exact ha⟩
    obtain ⟨ℓ, hℓ, hℓα⟩ :=
      LinearMap.exists_extend_of_notMem (0 : Submodule.span F {(1 : E)} →ₗ[F] F) hnot 1
    refine ⟨ℓ, ?_, hℓα⟩
    have h := LinearMap.congr_fun hℓ ⟨1, Submodule.mem_span_singleton_self 1⟩
    simpa using h
  have key := congrArg ((TensorProduct.rid F (v.adicCompletion F)).toLinearMap ∘ₗ
    LinearMap.lTensor (v.adicCompletion F) ℓ) hz
  simp [hy, hℓ1, hℓα, Algebra.TensorProduct.includeLeft_apply] at key

end GlobalTheory.SplitPlace
end

