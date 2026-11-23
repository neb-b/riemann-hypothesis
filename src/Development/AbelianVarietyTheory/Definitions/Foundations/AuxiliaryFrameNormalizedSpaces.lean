module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSingleSingle
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace Pre

variable (B : Pre)

theorem level_split_E : ∀ p ∈ B.host.levelPrimes, (placesOver B.host.E p).ncard = Module.finrank ℚ B.host.E := fun p hp =>
  (GlobalTheory.HostSplit.split_of_one_mod B.R B.host p (B.level_cond p hp).1 (B.level_cond p hp).2).1

theorem g_split : ∀ k, (placesOver B.host.E (B.host.g k)).ncard = Module.finrank ℚ B.host.E := fun k => B.level_split_E _ (B.host.g_level k)

theorem pde_split :
    (Ideal.primesOver (Ideal.span {(B.host.pde : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E ∧
    (Ideal.primesOver (Ideal.span {(B.host.pde' : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E := by
  constructor
  · rw [← GlobalTheory.HostSplit.ncard_placesOver _ B.host.pde_prime]
    exact B.level_split_E _ B.host.pde_level.1
  · rw [← GlobalTheory.HostSplit.ncard_placesOver _ B.host.pde'_prime]
    exact B.level_split_E _ B.host.pde_level.2

end Pre

section Spaces

open DiagSp

variable (R : Ranks) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)

def spacesNorm : Spaces R F E :=
  { spacesStd R cm T hT pz hpz (fun _ => false) with
    z := Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz
    z_anis := by
      refine ne_of_eq_of_ne (diag_single_single _ (fun _ => false) _ _ pz pz) ?_
      rw [if_pos rfl]
      simp only [sgn, Bool.false_eq_true, if_false, mul_one, hpz]
      exact_mod_cast hT.ne_zero
    z_orth := fun x => diag_ext_single _ _ (fun _ => false) x _ pz le_rfl }

theorem spacesNorm_Y_sig (j : ℕ) (τ : E →+* ℂ) : ((spacesNorm R cm T hT pz hpz).Y j).sig τ = sigYD R j := spY_sig R j τ

theorem spacesNorm_z_norm : ((spacesNorm R cm T hT pz hpz).X R.m).hT (spacesNorm R cm T hT pz hpz).z
    (spacesNorm R cm T hT pz hpz).z = (T : E) := by
  refine (diag_single_single (R.N R.m) (fun _ => false)
    (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) _ pz pz).trans ?_
  rw [if_pos rfl]
  simp only [sgn, Bool.false_eq_true, if_false, mul_one, hpz]

end Spaces

theorem exists_finset_capitulation (E : Type) [Field E] [NumberField E] (τ : E →+* ℂ) :
    ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K],
      (∀ z ∈ S, z ∈ K) → (∀ x, τ x ∈ K) → ∀ 𝔞 : Ideal (𝓞 E), ∃ β : K,
        Submodule.span (𝓞 K) {β} = Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} := by
  classical
  have hpos : 0 < Fintype.card (ClassGroup (𝓞 E)) := Fintype.card_pos
  choose rep γ hrep hγ hpow using exists_rep_pow_classNumber E
  choose α hα using fun c : ClassGroup (𝓞 E) =>
    IsAlgClosed.exists_pow_nat_eq (τ (γ c : E)) hpos
  have hαint : ∀ c, IsIntegral ℤ (α c) := fun c =>
    IsIntegral.of_pow hpos (by rw [hα c]; exact (RingOfIntegers.isIntegral_coe (γ c)).map τ.toIntAlgHom)
  refine ⟨Finset.univ.image α, ?_, ?_⟩
  · intro z hz
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hz
    exact ((hαint c).tower_top (A := ℚ)).isAlgebraic
  intro K _ hS hτ 𝔞
  have : NumberField K := {}
  let f : E →+* K := τ.codRestrict K hτ
  have hset : {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} = {x : K | ∃ a ∈ 𝔞, x = f (a : E)} := by
    ext x
    constructor
    · rintro ⟨a, ha, e⟩
      exact ⟨a, ha, Subtype.ext e⟩
    · rintro ⟨a, ha, e⟩
      exact ⟨a, ha, congrArg Subtype.val e⟩
  rw [hset, span_image_eq_coeSubmodule_map f 𝔞]
  by_cases h0 : 𝔞 = ⊥
  · refine ⟨0, ?_⟩
    rw [h0, Ideal.map_bot, IsLocalization.coeSubmodule_bot, Submodule.span_singleton_eq_bot.mpr rfl]
  set φ := RingOfIntegers.mapRingHom f
  set c := ClassGroup.mk0 (⟨𝔞, mem_nonZeroDivisors_of_ne_zero h0⟩ : (Ideal (𝓞 E))⁰) with hc
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp (hrep c).symm
  have haK : α c ∈ K := hS _ (Finset.mem_image_of_mem _ (Finset.mem_univ c))
  have haint : IsIntegral ℤ (⟨α c, haK⟩ : K) :=
    (isIntegral_algHom_iff (K.val : K →+* ℂ).toIntAlgHom Subtype.val_injective).mp (hαint c)
  let aO : 𝓞 K := ⟨⟨α c, haK⟩, haint⟩
  have hφγ : φ (γ c) = aO ^ Fintype.card (ClassGroup (𝓞 E)) := by
    apply RingOfIntegers.ext
    apply Subtype.ext
    simp only [φ, RingOfIntegers.mapRingHom_apply, map_pow]
    exact (hα c).symm
  have hrepmap : Ideal.map φ (rep c : Ideal (𝓞 E)) = Ideal.span {aO} := by
    apply pow_left_injective hpos.ne'
    simp only
    rw [← Ideal.map_pow, hpow c, Ideal.map_span, Set.image_singleton, hφγ, Ideal.span_singleton_pow]
  have hmap := congrArg (fun I => IsLocalization.coeSubmodule K (Ideal.map φ I)) hxy
  simp only [Ideal.map_mul, hrepmap, Ideal.map_span, Set.image_singleton,
    IsLocalization.coeSubmodule_mul, IsLocalization.coeSubmodule_span_singleton] at hmap
  have hu : algebraMap (𝓞 K) K (φ x) ≠ 0 := by
    show f (x : E) ≠ 0
    rw [map_ne_zero]
    exact fun h => hx (RingOfIntegers.ext (by simpa using h))
  refine ⟨(algebraMap (𝓞 K) K (φ x))⁻¹ * (algebraMap (𝓞 K) K (φ y) * algebraMap (𝓞 K) K aO), ?_⟩
  have hone : Submodule.span (𝓞 K) {(algebraMap (𝓞 K) K (φ x))⁻¹} *
      Submodule.span (𝓞 K) {algebraMap (𝓞 K) K (φ x)} = 1 := by
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ hu,
      Submodule.one_eq_span]
  rw [← one_mul (IsLocalization.coeSubmodule K (Ideal.map φ 𝔞)), ← hone, mul_assoc, hmap,
    Submodule.span_mul_span, Set.singleton_mul_singleton, Submodule.span_mul_span,
    Set.singleton_mul_singleton]

end GlobalTheory.Mem

end
