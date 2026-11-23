module

public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.UnitaryNorms.ArtGCut
section
noncomputable section

open NumberField

namespace Formalism.L2.Host

theorem sqSign_eq_jacobi {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hq4 : q % 4 = 3) (hp2 : p ≠ 2)
    (v : (ZMod q)ˣ) (hv : (v : ZMod q) = (p : ZMod q)) :
    ((sqSign v : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p := by
  haveI := Fact.mk hq
  haveI := Fact.mk hp
  have hpq : p ≠ q := by
    rintro rfl
    have h0 : (v : ZMod p) = 0 := by
      rw [hv]
      exact ZMod.natCast_self p
    exact v.ne_zero h0
  have hq2 : q ≠ 2 := by
    rintro rfl
    norm_num at hq4
  have hp0 : ((p : ℤ) : ZMod q) ≠ 0 := by
    rw [Int.cast_natCast, ← hv]
    exact v.ne_zero
  have hq0 : ((q : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 hd)
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have key : legendreSym p (-(q : ℤ)) = legendreSym q p := by
    rw [show (-(q : ℤ)) = -1 * q by ring, legendreSym.mul, legendreSym.at_neg_one hp2,
      ZMod.χ₄_eq_neg_one_pow hpodd]
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hp4 with h4 | h4
    · have hp2' : (p / 2) % 2 = 0 := by omega
      rw [legendreSym.quadratic_reciprocity_one_mod_four h4 hq2,
        (Nat.even_iff.2 hp2').neg_one_pow, one_mul]
    · have hp2' : (p / 2) % 2 = 1 := by omega
      rw [legendreSym.quadratic_reciprocity_three_mod_four h4 hq4,
        (Nat.odd_iff.2 hp2').neg_one_pow, neg_one_mul]
  rw [← jacobiSym.legendreSym.to_jacobiSym, key]
  unfold sqSign
  split_ifs with h
  · rw [Units.val_one, eq_comm, legendreSym.eq_one_iff q hp0, Int.cast_natCast, ← hv]
    exact h
  · rw [Units.val_neg, Units.val_one, eq_comm, legendreSym.eq_neg_one_iff q, Int.cast_natCast, ← hv]
    exact h

end Formalism.L2.Host
end
end

-- bundled from Formalism.LocalToGlobal.UnitaryNorms.IotaABijective
section
noncomputable section

namespace Formalism.L2.Host

theorem iota_mem (ι : Qb →+* ℂ) (x : Qb) : ι x ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  exact ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).algHom ι.toRatAlgHom

def iotaA (ι : Qb →+* ℂ) : Qb →+* algebraicClosure ℚ ℂ := ι.codRestrict (algebraicClosure ℚ ℂ) (iota_mem ι)

theorem iotaA_bijective (ι : Qb →+* ℂ) : Function.Bijective (iotaA ι) := by
  refine ⟨(iotaA ι).injective, fun y => ?_⟩
  have hy : IsIntegral ℚ (y : ℂ) := (mem_algebraicClosure_iff.1 y.2).isIntegral
  have hy' : IsIntegral ℚ y := IntermediateField.isIntegral_iff.2 hy
  have hr : y ∈ (iotaA ι).range := by
    refine Polynomial.Splits.mem_range_of_isRoot (IsAlgClosed.splits ((minpoly ℚ y).map (algebraMap ℚ Qb)))
      (Polynomial.map_ne_zero (f := algebraMap ℚ Qb) (minpoly.ne_zero hy')) ?_
    rw [Polynomial.map_map]
    have e : (iotaA ι).comp (algebraMap ℚ Qb) = algebraMap ℚ (algebraicClosure ℚ ℂ) :=
      Subsingleton.elim _ _
    rw [e, Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ y
  exact RingHom.mem_range.1 hr

def algC (ι : Qb →+* ℂ) : Qb ≃+* algebraicClosure ℚ ℂ := RingEquiv.ofBijective (iotaA ι) (iotaA_bijective ι)

@[simp] theorem algC_coe (ι : Qb →+* ℂ) (x : Qb) : ((algC ι x : algebraicClosure ℚ ℂ) : ℂ) = ι x := rfl

end Formalism.L2.Host
end
end

-- bundled from Formalism.LocalToGlobal.UnitaryNorms.Lemmas
section
noncomputable section

open IntermediateField NumberField

namespace Formalism.L2.Host

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem sqQ_eq {m : ℤ} {w : Qb} (hw : w ^ 2 = (m : Qb)) : sqQ m = ℚ⟮w⟯ := by
  apply le_antisymm
  · show adjoin ℚ (sqrts m) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    have hz' : z ^ 2 = w ^ 2 := by
      rw [hw]
      exact hz
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz' with rfl | rfl
    · exact IntermediateField.mem_adjoin_simple_self ℚ z
    · exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ w)
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ (sqrts m) hw

theorem pow_add_inv_pow_mem {w : Qb} (hw : w ≠ 0) (k : ℕ) : w ^ k + w⁻¹ ^ k ∈ ℚ⟮w + w⁻¹⟯ := by
  have key : ∀ n : ℕ, w ^ n + w⁻¹ ^ n ∈ ℚ⟮w + w⁻¹⟯ ∧ w ^ (n + 1) + w⁻¹ ^ (n + 1) ∈ ℚ⟮w + w⁻¹⟯ := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [pow_zero]
        exact add_mem (one_mem _) (one_mem _)
      · simp only [zero_add, pow_one]
        exact IntermediateField.mem_adjoin_simple_self ℚ _
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h1 : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
      have e : w ^ (n + 1 + 1) + w⁻¹ ^ (n + 1 + 1) =
          (w + w⁻¹) * (w ^ (n + 1) + w⁻¹ ^ (n + 1)) - (w ^ n + w⁻¹ ^ n) := by
        linear_combination (-(w ^ n + w⁻¹ ^ n)) * h1
      rw [e]
      exact sub_mem (mul_mem (IntermediateField.mem_adjoin_simple_self ℚ _) ih.2) ih.1
  exact (key k).1

theorem cycQplus_eq {N : ℕ} [NeZero N] {w : Qb} (hw : IsPrimitiveRoot w N) :
    cycQplus N = ℚ⟮w + w⁻¹⟯ := by
  have hw0 : w ≠ 0 := hw.ne_zero (NeZero.ne N)
  apply le_antisymm
  · show adjoin ℚ ((fun z => z + z⁻¹) '' mus N) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, -, rfl⟩ := hw.eq_pow_of_pow_eq_one hz
    show w ^ i + (w ^ i)⁻¹ ∈ ℚ⟮w + w⁻¹⟯
    rw [← inv_pow]
    exact pow_add_inv_pow_mem hw0 i
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ ((fun z : Qb => z + z⁻¹) '' mus N) ⟨w, hw.pow_eq_one, rfl⟩

theorem cycQ_eq {N : ℕ} [NeZero N] {w : Qb} (hw : IsPrimitiveRoot w N) : cycQ N = ℚ⟮w⟯ := by
  apply le_antisymm
  · show adjoin ℚ (mus N) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    obtain ⟨i, -, rfl⟩ := hw.eq_pow_of_pow_eq_one hz
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ w) i
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ (mus N) hw.pow_eq_one

theorem adjoin_pair_eq_sup (x y : Qb) : adjoin ℚ {x, y} = ℚ⟮x⟯ ⊔ ℚ⟮y⟯ := by
  rw [Set.insert_eq]
  exact IntermediateField.gc.l_sup

section Layer

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem map_a_sq (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    φ a ^ 2 = ((-(q : ℤ) : ℤ) : Qb) := by
  rw [← map_pow, h.2.1]
  simp

theorem map_b_sq (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    φ b ^ 2 = ((-(d : ℤ) : ℤ) : Qb) := by
  rw [← map_pow, h.2.2.1]
  simp

theorem map_zeta (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    IsPrimitiveRoot (φ ζ) (2 ^ (e + 2)) := h.1.map_of_injective (f := φ) (RingHom.injective φ.toRingHom)

private theorem adjoin_union_eq_sup {E : Type*} [Field E] [Algebra ℚ E] (S T : Set E) :
    adjoin ℚ (S ∪ T) = adjoin ℚ S ⊔ adjoin ℚ T :=
  IntermediateField.gc.l_sup

theorem map_hostE (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    (hostE ζ a b).map φ = EQ e q d := by
  rw [show hostE ζ a b = adjoin ℚ ({a, b} ∪ {ζ + ζ⁻¹}) from (adjoin_union_eq_sup _ _).symm,
    IntermediateField.adjoin_map, Set.image_union, Set.image_insert_eq, Set.image_singleton, Set.image_singleton,
    map_add, map_inv₀, adjoin_union_eq_sup, adjoin_pair_eq_sup]
  show _ = sqQ (-(q : ℤ)) ⊔ sqQ (-(d : ℤ)) ⊔ cycQplus (2 ^ (e + 2))
  rw [sqQ_eq (map_a_sq h φ), sqQ_eq (map_b_sq h φ), cycQplus_eq (map_zeta h φ)]

theorem exists_layer_emb (f : hostE ζ a b →ₐ[ℚ] Qb) :
    ∃ φ : L →ₐ[ℚ] Qb, ∀ x : hostE ζ a b, φ (x : L) = f x := by
  letI : Algebra (hostE ζ a b) Qb := f.toRingHom.toAlgebra
  haveI : FiniteDimensional (hostE ζ a b) L := FiniteDimensional.right ℚ (hostE ζ a b) L
  haveI : Algebra.IsAlgebraic (hostE ζ a b) L := Algebra.IsAlgebraic.of_finite (hostE ζ a b) L
  let ψ : L →ₐ[hostE ζ a b] Qb := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨ψ.toRingHom.toRatAlgHom, fun x => ψ.commutes x⟩

theorem range_hostE (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) :
    f.fieldRange = EQ e q d := by
  obtain ⟨φ, hφ⟩ := exists_layer_emb f
  rw [← map_hostE h φ]
  ext y
  simp only [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, hφ x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (hφ ⟨x, hx⟩).symm⟩

theorem mem_EQ (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) (x : hostE ζ a b) :
    f x ∈ EQ e q d := by
  rw [← range_hostE h f]
  exact AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩

def jOf (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) : hostE ζ a b ≃ₐ[ℚ] EQ e q d :=
  AlgEquiv.ofBijective (f.codRestrict (EQ e q d).toSubalgebra (mem_EQ h f))
    ⟨fun x y hxy => f.toRingHom.injective (congrArg Subtype.val hxy), fun y => by
      have hy : (y : Qb) ∈ f.fieldRange := by rw [range_hostE h f]; exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

end Layer

end Formalism.L2.Host
end
end

