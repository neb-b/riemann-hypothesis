module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.EquivOfRange
section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

private theorem act_root {K : Type} [Field K] {N : ℕ} [NeZero N] {ζ x : K} (hζ : IsPrimitiveRoot ζ N)
    (σ : K →+* K) {a : ℕ} (hσ : σ ζ = ζ ^ a) (hx : x ^ N = 1) : σ x = x ^ a := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, hσ, pow_right_comm]

private theorem exists_pow {N : ℕ} [NeZero N] {ζ : CyclotomicField N ℚ} (hζ : IsPrimitiveRoot ζ N)
    (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) : ∃ a : ℕ, τ ζ = ζ ^ a := by
  obtain ⟨i, -, h⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  exact ⟨i, h.symm⟩

private theorem mem_fix {E K : Type} [Field E] [Field K] [Algebra ℚ E] [Algebra ℚ K] (j : E →ₐ[ℚ] K)
    (τ : K ≃ₐ[ℚ] K) : τ ∈ j.fieldRange.fixingSubgroup ↔ ∀ x : E, τ (j x) = j x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x => h _ ⟨x, rfl⟩, fun h _ ⟨x, hx⟩ => hx ▸ h x⟩

private theorem ker_congr (A : AbF) {a b : ℕ} (h : a ≡ b [MOD A.m]) (hb : A.ker b) : A.ker a := by
  obtain ⟨u, hu, e⟩ := hb
  exact ⟨u, hu, e.trans ((ZMod.natCast_eq_natCast_iff _ _ _).2 h).symm⟩

private theorem exists_res {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] [Normal ℚ K]
    (f : K →ₐ[ℚ] L) (σ : L ≃ₐ[ℚ] L) : ∃ τ : K ≃ₐ[ℚ] K, ∀ x : K, σ (f x) = f (τ x) := by
  letI : Algebra K L := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact ⟨σ.restrictNormal K, fun x => (σ.restrictNormal_commutes K x).symm⟩

private theorem equiv_of_range {F L L' Ω : Type} [Field F] [Field L] [Field L'] [Field Ω] [Algebra F L]
    [Algebra F L'] [Algebra F Ω] (g : L →ₐ[F] Ω) (g' : L' →ₐ[F] Ω) (e : g.fieldRange = g'.fieldRange) :
    Nonempty (L ≃+* L') :=
  ⟨((g.equivFieldRange.trans (IntermediateField.equivOfEq e)).trans g'.equivFieldRange.symm).toRingEquiv⟩

private theorem equiv_of_fix {L L' Ω : Type} [Field L] [Field L'] [Field Ω] [Algebra ℚ L] [Algebra ℚ L']
    [Algebra ℚ Ω] [IsGalois ℚ Ω] (g : L →ₐ[ℚ] Ω) (g' : L' →ₐ[ℚ] Ω)
    (h : ∀ σ : Ω ≃ₐ[ℚ] Ω, (∀ x, σ (g x) = g x) ↔ ∀ x, σ (g' x) = g' x) : Nonempty (L ≃+* L') := by
  have e : g.fieldRange = g'.fieldRange := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup g.fieldRange,
      ← InfiniteGalois.fixedField_fixingSubgroup g'.fieldRange]
    congr 1
    ext σ
    rw [mem_fix, mem_fix, h]
  exact equiv_of_range g g' e

theorem UpperTheory.V.Win.abiso :
    ∀ (A : AbF) (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'],
      IsAbField A L → IsAbField A L' → Nonempty (L ≃+* L') := by
  intro A L L' _ _ _ _ hL hL'
  obtain ⟨N, hN, i, ζ, hm, hζ, H0⟩ := hL
  obtain ⟨N', hN', j, ζ', hm', hζ', H⟩ := hL'
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  haveI : IsCyclotomicExtension {N'} ℚ (CyclotomicField N' ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isAbelianGalois {N} ℚ _
  haveI : IsAbelianGalois ℚ (CyclotomicField N' ℚ) := IsCyclotomicExtension.isAbelianGalois {N'} ℚ _
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := by
    first
      | exact @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _
      | convert @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _
  let f : CyclotomicField N ℚ →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let f' : CyclotomicField N' ℚ →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine equiv_of_fix (f.comp i) (f'.comp j) fun σ => ?_
  obtain ⟨τ, hσ⟩ := exists_res f σ
  obtain ⟨τ', hσ'⟩ := exists_res f' σ
  obtain ⟨a, hτ⟩ := exists_pow hζ τ
  obtain ⟨b, hb⟩ := exists_pow hζ' τ'
  obtain ⟨k, hk⟩ := id hm
  obtain ⟨k', hk'⟩ := id hm'
  have hω : IsPrimitiveRoot (f (ζ ^ k)) A.m :=
    (hζ.pow (NeZero.pos N) (by rw [hk, mul_comm])).map_of_injective f.injective
  have hω' : IsPrimitiveRoot (f' (ζ' ^ k')) A.m :=
    (hζ'.pow (NeZero.pos N') (by rw [hk', mul_comm])).map_of_injective f'.injective
  have h1 : σ (f (ζ ^ k)) = f (ζ ^ k) ^ a := by
    rw [hσ, map_pow τ, hτ, pow_right_comm, map_pow f]
  have h2 : σ (f' (ζ' ^ k')) = f' (ζ' ^ k') ^ b := by
    rw [hσ', map_pow τ', hb, pow_right_comm, map_pow f']
  have h3 : σ (f (ζ ^ k)) = f (ζ ^ k) ^ b :=
    act_root hω' (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) h2 hω.pow_eq_one
  have hab : a ≡ b [MOD A.m] := by
    have := ((hω.isOfFinOrder A.pos.ne').pow_eq_pow_iff_modEq).1 (h1.symm.trans h3)
    rwa [← hω.eq_orderOf] at this
  have h4 : A.ker a ↔ A.ker b := ⟨ker_congr A hab.symm, ker_congr A hab⟩
  have e1 : (∀ x, σ ((f.comp i) x) = (f.comp i) x) ↔ ∀ x, τ (i x) = i x := by
    refine forall_congr' fun x => ?_
    show σ (f (i x)) = f (i x) ↔ _
    rw [hσ]
    exact f.injective.eq_iff
  have e2 : (∀ x, σ ((f'.comp j) x) = (f'.comp j) x) ↔ ∀ x, τ' (j x) = j x := by
    refine forall_congr' fun x => ?_
    show σ (f' (j x)) = f' (j x) ↔ _
    rw [hσ']
    exact f'.injective.eq_iff
  rw [e1, e2, H0 τ a hτ, H τ' b hb, h4]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Final
section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.final :
    ∀ Ct eps C : ℝ, 0 < eps → ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x ≥ x0, x ^ Ct * ptBound C eps x ≤ Real.exp (x ^ (4 * eps / 5)) := by
  intro Ct eps C heps
  have hba : 0 < 4 * eps / 5 - 3 * eps / 4 := by linarith
  have hb : 0 < 4 * eps / 5 := by linarith
  have E1 := ((isLittleO_log_rpow_atTop hb).const_mul_left (|Ct| + |C|)).bound
    (by norm_num : (0:ℝ) < 1 / 4)
  have E2 := (tendsto_rpow_atTop hba).eventually_ge_atTop (4 * |C|)
  have E3 := (tendsto_rpow_atTop hb).eventually_ge_atTop (4 * (Real.log 3 + |C|))
  have E4 := Filter.eventually_ge_atTop (2:ℝ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (E1.and (E2.and (E3.and E4)))
  refine ⟨max N 2, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hN x (le_trans (le_max_left _ _) hx)
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hxa : 0 ≤ x ^ (3 * eps / 4) := Real.rpow_nonneg hx0.le _
  have hxb : 0 ≤ x ^ (4 * eps / 5) := Real.rpow_nonneg hx0.le _
  have hsplit : x ^ (4 * eps / 5) = x ^ (3 * eps / 4) * x ^ (4 * eps / 5 - 3 * eps / 4) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (add_nonneg (abs_nonneg Ct) (abs_nonneg C)) hlog),
    abs_of_nonneg hxb] at h1
  have hC2 : |C| * x ^ (3 * eps / 4) ≤ 1 / 4 * x ^ (4 * eps / 5) := by
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left h2 hxa]
  have hS : Real.log 3 + (|Ct| + |C|) * Real.log x + |C| + |C| * x ^ (3 * eps / 4)
      ≤ x ^ (4 * eps / 5) := by linarith
  have hp1 : C * (1 + Real.log x)
      ≤ Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4)) := by
    have q1 : C * (1 + Real.log x) ≤ |C| * (1 + Real.log x) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
    have q2 : 0 ≤ |C| * x ^ (3 * eps / 4) := mul_nonneg (abs_nonneg C) hxa
    linarith [Real.add_one_le_exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))]
  have hp2 : Real.exp (C * x ^ (3 * eps / 4))
      ≤ Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4)) := by
    apply Real.exp_le_exp.mpr
    have q1 : C * x ^ (3 * eps / 4) ≤ |C| * x ^ (3 * eps / 4) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hxa
    have q2 : 0 ≤ |C| * (1 + Real.log x) := mul_nonneg (abs_nonneg C) (by linarith)
    linarith
  have hpt : ptBound C eps x
      ≤ 3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4)) := by
    show C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (3 * eps / 4)) ≤ _
    linarith
  have hxc : x ^ Ct ≤ Real.exp (|Ct| * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    have q := mul_le_mul_of_nonneg_right (le_abs_self Ct) hlog
    linarith
  calc x ^ Ct * ptBound C eps x
      ≤ x ^ Ct * (3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))) :=
        mul_le_mul_of_nonneg_left hpt (Real.rpow_nonneg hx0.le _)
    _ ≤ Real.exp (|Ct| * Real.log x)
          * (3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))) :=
        mul_le_mul_of_nonneg_right hxc (by positivity)
    _ = Real.exp (|Ct| * Real.log x + Real.log 3
          + (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))) := by
        rw [Real.exp_add (|Ct| * Real.log x + Real.log 3), Real.exp_add (|Ct| * Real.log x),
          Real.exp_log (by norm_num : (0:ℝ) < 3)]
        ring
    _ ≤ Real.exp (x ^ (4 * eps / 5)) := Real.exp_le_exp.mpr (by linarith)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Imports
section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.disc :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N → Nonempty (L →ₐ[ℚ] CyclotomicField N ℚ) →
      Real.log ((discr L).natAbs : ℝ) ≤ (Module.finrank ℚ L : ℝ) * Real.log (N : ℝ) := by
  intro L _ _ N hN hφ
  obtain ⟨φ⟩ := hφ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  letI : Algebra L (CyclotomicField N ℚ) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ L (CyclotomicField N ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  have key := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow L (𝓞 L)
    (CyclotomicField N ℚ) (𝓞 (CyclotomicField N ℚ))
  have hdC := IsCyclotomicExtension.Rat.natAbs_discr N (CyclotomicField N ℚ)
  have hfin : Module.finrank ℚ (CyclotomicField N ℚ) = N.totient :=
    IsCyclotomicExtension.finrank (CyclotomicField N ℚ) (Polynomial.cyclotomic.irreducible_rat hN)
  have htow := Module.finrank_mul_finrank ℚ L (CyclotomicField N ℚ)
  have hm : 0 < Module.finrank L (CyclotomicField N ℚ) := Module.finrank_pos
  have hne := NumberField.discr_ne_zero (CyclotomicField N ℚ)
  have hdL := NumberField.discr_ne_zero L
  have h1 : (discr L).natAbs ^ Module.finrank L (CyclotomicField N ℚ)
      ≤ (discr (CyclotomicField N ℚ)).natAbs := by
    rw [key]
    have h0 : Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 (CyclotomicField N ℚ))) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at key
      exact hne (Int.natAbs_eq_zero.mp key)
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h0)
  have h2 : (discr (CyclotomicField N ℚ)).natAbs
      ≤ (N ^ Module.finrank ℚ L) ^ Module.finrank L (CyclotomicField N ℚ) := by
    rw [hdC, ← pow_mul, htow, hfin]
    exact Nat.div_le_self _ _
  have h3 : (discr L).natAbs ≤ N ^ Module.finrank ℚ L :=
    (Nat.pow_le_pow_iff_left hm.ne').mp (h1.trans h2)
  have hd0 : 0 < (discr L).natAbs := Int.natAbs_pos.mpr hdL
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast hd0)
  exact_mod_cast h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Kexp
section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.kexp :
    ∀ (CK eps c0 x : ℝ) (e n n0 D : ℕ), 0 < CK → 0 < eps → 0 ≤ c0 → 1 ≤ x → (e : ℝ) ≤ x ^ (eps / (2 * CK)) → n ≤ n0 →
      Real.log (2 * (D : ℝ)) ≤ c0 * x ^ (eps / 4) →
        kBound CK e n D ≤ Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4)) := by
  intro CK eps c0 x e n n0 D hCK heps hc0 hx he hn hD
  have hx0 : 0 < x := by linarith
  have hn' : (n : ℝ) ≤ n0 := by exact_mod_cast hn
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn00 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
  have hy : 0 ≤ x ^ (eps / (2 * CK)) := Real.rpow_nonneg hx0.le _
  have h1 : 2 * (e : ℝ) * n ≤ (2 * (n0 : ℝ)) * x ^ (eps / (2 * CK)) := by
    have := mul_le_mul he hn' hn0 hy
    nlinarith
  have h2 : (2 * (e : ℝ) * n) ^ CK ≤ (2 * (n0 : ℝ)) ^ CK * x ^ (eps / 2) := by
    calc (2 * (e : ℝ) * n) ^ CK ≤ ((2 * (n0 : ℝ)) * x ^ (eps / (2 * CK))) ^ CK :=
          Real.rpow_le_rpow (by positivity) h1 hCK.le
      _ = (2 * (n0 : ℝ)) ^ CK * x ^ (eps / 2) := by
          rw [Real.mul_rpow (by positivity) hy, ← Real.rpow_mul hx0.le]
          congr 2
          field_simp
  have h3 : x ^ (3 * eps / 4) = x ^ (eps / 2) * x ^ (eps / 4) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  unfold kBound
  apply Real.exp_le_exp.mpr
  have ha : 0 ≤ (2 * (e : ℝ) * n) ^ CK := Real.rpow_nonneg (by positivity) _
  have hb : 0 ≤ c0 * x ^ (eps / 4) := mul_nonneg hc0 (Real.rpow_nonneg hx0.le _)
  calc (2 * (e : ℝ) * n) ^ CK * Real.log (2 * (D : ℝ))
      ≤ (2 * (e : ℝ) * n) ^ CK * (c0 * x ^ (eps / 4)) := mul_le_mul_of_nonneg_left hD ha
    _ ≤ ((2 * (n0 : ℝ)) ^ CK * x ^ (eps / 2)) * (c0 * x ^ (eps / 4)) := mul_le_mul_of_nonneg_right h2 hb
    _ = (2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4) := by rw [h3]; ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Kmono
section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.kmono :
    ∀ C C' : ℝ, C ≤ C' → LemmaK C → LemmaK C' := by
  intro C C' hCC hK
  unfold LemmaK at hK ⊢
  intro l _ L Ω _ _ _ _ _ D hL hMu e he
  obtain ⟨hf, hb⟩ := hK l L Ω D hL hMu e he
  refine ⟨hf, hb.trans ?_⟩
  unfold kBound
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right
  · apply Real.rpow_le_rpow_of_exponent_le _ hCC
    have hn : 0 < Module.finrank ℚ L := Module.finrank_pos
    have h1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    have h2 : (1 : ℝ) ≤ (Module.finrank ℚ L : ℝ) := by exact_mod_cast hn
    nlinarith
  · rcases Nat.eq_zero_or_pos (discr L).natAbs with h0 | h0
    · rw [h0]
      simp
    · apply Real.log_nonneg
      have : (1 : ℝ) ≤ ((discr L).natAbs : ℝ) := by exact_mod_cast h0
      linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layerex
section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win
open Polynomial

private theorem winlx_up {K : Type} [Field K] {l m : ℕ} (hl : l.Prime) {b : K}
    (h : IsPrimitiveRoot (b ^ l) (l ^ (m + 1))) : IsPrimitiveRoot b (l ^ (m + 2)) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h1 : ¬ b ^ (l ^ (m + 1)) = 1 := by
    intro e
    have : (b ^ l) ^ (l ^ m) = 1 := by rw [← pow_mul, ← pow_succ']; exact e
    exact h.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hl.ne_zero)
      (Nat.pow_lt_pow_right hl.one_lt (Nat.lt_succ_self m)) this
  have h2 : b ^ (l ^ (m + 1 + 1)) = 1 := by
    rw [pow_succ' l (m + 1), pow_mul]; exact h.pow_eq_one
  have h3 := orderOf_eq_prime_pow h1 h2
  have := IsPrimitiveRoot.orderOf b
  rwa [h3] at this

private theorem winlx_max (K : Type) [Field K] [NumberField K] {l k : ℕ} (hl : l.Prime)
    (h : ∃ z : K, IsPrimitiveRoot z (l ^ (k + 1))) :
    ∃ m, k ≤ m ∧ (∃ z : K, IsPrimitiveRoot z (l ^ (m + 1))) ∧
      ¬ ∃ z : K, IsPrimitiveRoot z (l ^ (m + 2)) := by
  by_contra hc
  push Not at hc
  have key : ∀ n, ∃ z : K, IsPrimitiveRoot z (l ^ (k + n + 1)) := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih => exact hc (k + n) (by omega) ih
  obtain ⟨z, hz⟩ := key (Module.finrank ℚ K)
  have hpos : 0 < Nat.lcm (l ^ (k + Module.finrank ℚ K + 1)) (l ^ (k + Module.finrank ℚ K + 1)) := by
    rw [Nat.lcm_self]; exact pow_pos hl.pos _
  have h1 := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) hz hz (Polynomial.cyclotomic.irreducible_rat hpos)
  rw [Nat.lcm_self, Nat.totient_prime_pow_succ hl] at h1
  have h2 : k + Module.finrank ℚ K < l ^ (k + Module.finrank ℚ K) := Nat.lt_pow_self hl.one_lt
  have h3 : 1 ≤ l - 1 := by have := hl.two_le; omega
  have h4 := Nat.mul_le_mul_left (l ^ (k + Module.finrank ℚ K)) h3
  omega

private theorem winlx_step (K : Type) [Field K] [NumberField K] {l m : ℕ} (hl : l.Prime)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (m + 1))) (hn : ¬ ∃ z : K, IsPrimitiveRoot z (l ^ (m + 2))) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K'),
      IsCyclotomicExtension {l ^ (m + 2)} K K' ∧ Module.finrank K K' = l := by
  have hirr : Irreducible (X ^ l - C z : K[X]) :=
    X_pow_sub_C_irreducible_of_prime hl (fun b hb => hn ⟨b, winlx_up hl (hb ▸ hz)⟩)
  haveI : Fact (Irreducible (X ^ l - C z : K[X])) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite K (AdjoinRoot (X ^ l - C z : K[X])) := pb.finite
  haveI : NeZero (l ^ (m + 2)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hr : IsPrimitiveRoot (AdjoinRoot.root (X ^ l - C z : K[X])) (l ^ (m + 2)) := by
    apply winlx_up hl
    rw [root_X_pow_sub_C_pow]
    exact hz.map_of_injective (AdjoinRoot.of (X ^ l - C z : K[X])).injective
  refine ⟨AdjoinRoot (X ^ l - C z : K[X]), inferInstance, NumberField.of_module_finite K _, inferInstance, ?_, ?_⟩
  · rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨_, hr⟩, fun x => ?_⟩
    have : x ∈ Algebra.adjoin K {AdjoinRoot.root (X ^ l - C z : K[X])} := by
      rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
    refine Algebra.adjoin_mono ?_ this
    rintro _ rfl
    exact hr.pow_eq_one
  · rw [pb.finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C _]

theorem UpperTheory.V.Win.layerex :
    ∀ (l j : ℕ), l.Prime → ∀ (L : Type) [Field L] [NumberField L], HasMuQ l L →
      ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L'), IsLayer l j L L' := by
  intro l j hl L _ _ hq
  have hz : ∃ z : L, IsPrimitiveRoot z l := by
    obtain ⟨ζ, hζ⟩ := hq
    by_cases h2 : l = 2
    · subst h2
      rw [if_pos rfl] at hζ
      exact ⟨ζ ^ 2, hζ.pow (by norm_num) (by norm_num)⟩
    · rw [if_neg h2] at hζ
      exact ⟨ζ, hζ⟩
  have key : ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L'),
      (∃ k : ℕ, IsCyclotomicExtension {l ^ (k + 1)} L L') ∧ Module.finrank L L' = l ^ j := by
    induction j with
    | zero =>
      refine ⟨L, inferInstance, inferInstance, inferInstance, ⟨0, ?_⟩, by simp⟩
      haveI : NeZero (l ^ (0 + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
      rw [IsCyclotomicExtension.iff_singleton]
      exact ⟨by simpa using hz, fun x => Subalgebra.algebraMap_mem _ x⟩
    | succ j ih =>
      obtain ⟨K, _, _, _, ⟨k, hk⟩, hd⟩ := ih
      obtain ⟨m, hkm, ⟨z, hz⟩, hn⟩ := winlx_max K (k := k) hl
        (hk.exists_isPrimitiveRoot (Set.mem_singleton _) (pow_ne_zero _ hl.ne_zero))
      obtain ⟨K', _, _, _, hc, hd'⟩ := winlx_step K hl hz hn
      letI : Algebra L K' := ((algebraMap K K').comp (algebraMap L K)).toAlgebra
      haveI : IsScalarTower L K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      refine ⟨K', inferInstance, inferInstance, inferInstance, ⟨m + 1, ?_⟩, ?_⟩
      · haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
        have h1 := IsCyclotomicExtension.trans {l ^ (k + 1)} {l ^ (m + 2)} L K K' (algebraMap K K').injective
        rw [Set.union_comm] at h1
        exact (IsCyclotomicExtension.iff_union_of_dvd L K'
          ⟨l ^ (m + 2), Set.mem_singleton _, pow_ne_zero _ hl.ne_zero, pow_dvd_pow _ (by omega)⟩).2 h1
      · rw [← Module.finrank_mul_finrank L K K', hd, hd', pow_succ]
  obtain ⟨L', _, _, _, ⟨k, hk⟩, hd⟩ := key
  exact ⟨L', inferInstance, inferInstance, inferInstance, ⟨k + 1, hk⟩, hd⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layeriso
section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

private theorem nonempty_ringEquiv_of_isCyclotomic_finrank_eq (l j k k' : ℕ) (hl : l.Prime) (hk : k ≤ k') (L₀ L₀' L₁ L₁' : Type)
    [Field L₀] [Field L₀'] [Field L₁] [Field L₁'] [Algebra L₀ L₁] [Algebra L₀' L₁']
    (e : L₀ ≃+* L₀') (h₁ : IsCyclotomicExtension {l ^ k} L₀ L₁)
    (h₁' : IsCyclotomicExtension {l ^ k'} L₀' L₁')
    (d₁ : Module.finrank L₀ L₁ = l ^ j) (d₁' : Module.finrank L₀' L₁' = l ^ j) :
    Nonempty (L₁ ≃+* L₁') := by
  haveI : NeZero (l ^ k') := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta (l ^ k') L₀' L₁' ^ (l ^ (k' - k))) (l ^ k) :=
    (IsCyclotomicExtension.zeta_spec (l ^ k') L₀' L₁').pow (pow_pos hl.pos _)
      (by rw [← pow_add, Nat.sub_add_cancel hk])
  letI : Algebra L₀ L₀' := e.toRingHom.toAlgebra
  letI : Algebra L₀ L₁' := ((algebraMap L₀' L₁').comp e.toRingHom).toAlgebra
  haveI : IsScalarTower L₀ L₀' L₁' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h1 : Module.finrank L₀ L₀' = 1 := by
    rw [← (AlgEquiv.ofRingEquiv (R := L₀) (A₁ := L₀) (A₂ := L₀') (f := e)
      (fun _ => rfl)).toLinearEquiv.finrank_eq, Module.finrank_self]
  have h2 : Module.finrank L₀ L₁' = l ^ j := by
    rw [← Module.finrank_mul_finrank L₀ L₀' L₁', h1, one_mul, d₁']
  haveI : FiniteDimensional L₀ L₁' :=
    Module.finite_of_finrank_pos (by rw [h2]; exact pow_pos hl.pos _)
  haveI : Algebra.IsIntegral L₀ L₁' := Algebra.IsIntegral.of_finite L₀ L₁'
  haveI := hζ.intermediateField_adjoin_isCyclotomicExtension L₀
  let φ := IsCyclotomicExtension.algEquiv {l ^ k} L₀ L₁
    (IntermediateField.adjoin L₀ {IsCyclotomicExtension.zeta (l ^ k') L₀' L₁' ^ (l ^ (k' - k))})
  have htop : IntermediateField.adjoin L₀
      {IsCyclotomicExtension.zeta (l ^ k') L₀' L₁' ^ (l ^ (k' - k))} = ⊤ :=
    IntermediateField.eq_of_le_of_finrank_eq le_top
      (by rw [IntermediateField.finrank_top', ← φ.toLinearEquiv.finrank_eq, d₁, h2])
  exact ⟨φ.toRingEquiv.trans ((IntermediateField.equivOfEq htop).toRingEquiv.trans
    IntermediateField.topEquiv.toRingEquiv)⟩

theorem UpperTheory.V.Win.layeriso :
    ∀ (l j : ℕ), l.Prime → ∀ (L₀ L₀' L₁ L₁' : Type) [Field L₀] [NumberField L₀] [Field L₀'] [NumberField L₀']
      [Field L₁] [NumberField L₁] [Field L₁'] [NumberField L₁'] [Algebra L₀ L₁] [Algebra L₀' L₁'],
        Nonempty (L₀ ≃+* L₀') → IsLayer l j L₀ L₁ → IsLayer l j L₀' L₁' → Nonempty (L₁ ≃+* L₁') := by
  intro l j hl L₀ L₀' L₁ L₁' _ _ _ _ _ _ _ _ _ _ ⟨e⟩ ⟨⟨k, hk⟩, d⟩ ⟨⟨k', hk'⟩, d'⟩
  rcases le_total k k' with h | h
  · exact nonempty_ringEquiv_of_isCyclotomic_finrank_eq l j k k' hl h L₀ L₀' L₁ L₁' e hk hk' d d'
  · obtain ⟨f⟩ := nonempty_ringEquiv_of_isCyclotomic_finrank_eq l j k' k hl h L₀' L₀ L₁' L₁ e.symm hk' hk d' d
    exact ⟨f.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Rootdeg
section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.rootdeg :
    ∀ (L : Type) [Field L] [NumberField L] (l k : ℕ), l.Prime → (∃ ζ : L, IsPrimitiveRoot ζ (l ^ k)) →
      l ^ k ≤ 2 * Module.finrank ℚ L := by
  intro L _ _ l k hl ⟨ζ, hζ⟩
  have hpos : 0 < l ^ k := pow_pos hl.pos k
  have ht : (l ^ k).totient ≤ Module.finrank ℚ L := by
    have h1 := hζ.lcm_totient_le_finrank (K := ℚ) hζ
      (by rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat hpos)
    rwa [Nat.lcm_self] at h1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, Nat.totient_one] at ht ⊢
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.totient_prime_pow hl hk, Nat.add_sub_cancel] at ht
    have h2 : l ≤ 2 * (l - 1) := by
      have := hl.two_le
      omega
    calc l ^ (m + 1) = l ^ m * l := pow_succ l m
      _ ≤ l ^ m * (2 * (l - 1)) := Nat.mul_le_mul_left _ h2
      _ = 2 * (l ^ m * (l - 1)) := by ring
      _ ≤ 2 * Module.finrank ℚ L := Nat.mul_le_mul_left _ ht
end

