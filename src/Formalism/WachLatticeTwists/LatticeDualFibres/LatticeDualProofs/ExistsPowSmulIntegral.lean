module

public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice

@[expose] public section

universe u

open Formalism.NG (KO)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

section SlopeTestRemainingChoices

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem exists_pow_smul_integral {ϖ : O} (hϖ : Irreducible ϖ) (k : FractionRing O) :
    ∃ (n : ℕ) (a : O), (ϖ ^ n) • k = algebraMap O (FractionRing O) a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨n, a * ((w⁻¹ : Oˣ) : O), ?_⟩
  have hne : algebraMap O (FractionRing O) ((w : O) * ϖ ^ n) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hb0
  rw [Algebra.smul_def, ← mul_div_assoc, div_eq_iff hne, ← map_mul, ← map_mul]
  congr 1
  have : ((w⁻¹ : Oˣ) : O) * (w : O) = 1 := by simp
  calc ϖ ^ n * a = ϖ ^ n * a * (((w⁻¹ : Oˣ) : O) * (w : O)) := by rw [this, mul_one]
    _ = a * ((w⁻¹ : Oˣ) : O) * ((w : O) * ϖ ^ n) := by ring

theorem exists_pow_smul_mem {V : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] {T : Submodule O V}
    (hT : Submodule.span (FractionRing O) (T : Set V) = ⊤) {ϖ : O} (hϖ : Irreducible ϖ) (x : V) :
    ∃ n : ℕ, (ϖ ^ n) • x ∈ T := by
  have hx : x ∈ Submodule.span (FractionRing O) (T : Set V) := by rw [hT]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact T.smul_mem _ hn
    · rw [pow_add, mul_smul]; exact T.smul_mem _ hm
  | smul k x _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, a, ha⟩ := exists_pow_smul_integral hϖ k
    refine ⟨m + n, ?_⟩
    have : (ϖ ^ (m + n)) • k • x = a • (ϖ ^ n) • x := by
      rw [pow_add, mul_comm, mul_smul, ← smul_assoc (ϖ ^ m) k x, ha, algebraMap_smul,
        smul_comm]
    rw [this]; exact T.smul_mem _ hn

end SlopeTestRemainingChoices

end Formalism.RepresentationBoundsCohomology.LOC
