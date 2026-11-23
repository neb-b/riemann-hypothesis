module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgClosureOfTower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.CardFiberReductionEqTotient
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem fib_card {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq H]
    (f : G →* H) (hf : Function.Surjective f) (z : H) :
    Fintype.card G = Fintype.card H * (Finset.univ.filter (fun y => f y = z)).card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  have hc : ∀ b ∈ (Finset.univ : Finset H),
      (Finset.univ.filter (fun a => f a = b)).card = (Finset.univ.filter (fun y => f y = z)).card :=
    fun b _ => MonoidHom.card_fiber_eq_of_mem_range f (hf b) (hf z)
  rw [Finset.card_univ, Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  exact h

theorem UpperTheory.card_fiber_reduction_eq_totient :
    ∀ (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N], ¬ l ∣ N → ∀ z : (ZMod (l ^ (m + n)))ˣ, (Finset.univ.filter (fun y => redTop l n m N y = z)).card = Nat.totient (N * N) := by
  intro l _ n m N _ hN z
  have hl : l.Prime := Fact.out
  have hdvd : l ^ (m + n) ∣ topM l n m (N * N) := Dvd.intro _ rfl
  haveI : NeZero (l ^ (m + n)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (topM l n m (N * N)) :=
    ⟨mul_ne_zero (pow_ne_zero _ hl.ne_zero) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
  have key := fib_card (ZMod.unitsMap hdvd) (ZMod.unitsMap_surjective hdvd) z
  have hred : ∀ y, redTop l n m N y = ZMod.unitsMap hdvd y := fun y => rfl
  simp only [hred]
  rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient] at key
  have hcop : (l ^ (m + n)).Coprime (N * N) := by
    have h1 : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hl).2 hN
    exact Nat.Coprime.pow_left _ (Nat.Coprime.mul_right h1 h1)
  have htot : (topM l n m (N * N)).totient = (l ^ (m + n)).totient * (N * N).totient :=
    Nat.totient_mul hcop
  rw [htot] at key
  have hpos : 0 < (l ^ (m + n)).totient := Nat.totient_pos.2 (pow_pos hl.pos _)
  exact (Nat.eq_of_mul_eq_mul_left hpos key).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.CongruenceActionInvariant
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.congruence_action_invariant :
    ∀ (l : ℕ) [Fact l.Prime] (L m : ℕ), 1 ≤ m → m ≤ L → ∀ (z : (ZMod (l ^ L))ˣ) (t : SL(2, ZMod (l ^ L)) → (ZMod (l ^ L))ˣ → GL (Fin 2) (ZMod (l ^ L))), (∀ h u i, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0 = h i 0) → (∀ h u i, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1 = (u : ZMod (l ^ L)) * h i 1) → ∀ (V : Type) [AddCommMonoid V] (f : GL (Fin 2) (ZMod (l ^ L)) → V), ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ L)) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ L))ˣ => (a : ZMod (l ^ L)).val ≡ 1 [MOD l ^ m]), f (t h (a * z)) = ∑ γ ∈ ((unitSet l L).filter fun γ : GL (Fin 2) (ZMod (l ^ L)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m)) = (((z : ZMod (l ^ L)).val : ℕ) : ZMod (l ^ m))), f γ := by
  intro l _ L m _ hmL z t ht0 ht1 V _ f
  have hd : l ^ m ∣ l ^ L := pow_dvd_pow l hmL
  set φ := ZMod.castHom hd (ZMod (l ^ m)) with hφ
  have hcast : ∀ x : ZMod (l ^ L), ((x.val : ℕ) : ZMod (l ^ m)) = φ x := by
    intro x
    rw [ZMod.natCast_val, hφ, ZMod.castHom_apply]
  have hmod : ∀ a : (ZMod (l ^ L))ˣ, (a : ZMod (l ^ L)).val ≡ 1 [MOD l ^ m] ↔ φ a = 1 := by
    intro a
    rw [← ZMod.natCast_eq_natCast_iff, hcast, Nat.cast_one]
  have hdet : ∀ h u, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det
      = (u : ZMod (l ^ L)) := by
    intro h u
    have h1 : (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det = 1 := h.prop
    rw [Matrix.det_fin_two] at h1 ⊢
    rw [ht0, ht0, ht1, ht1]
    linear_combination (u : ZMod (l ^ L)) * h1
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun p _ => t p.1 (p.2 * z))
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, ht0, hcast, hdet]
    refine ⟨hp.1, ?_⟩
    rw [Units.val_mul, map_mul, (hmod _).mp hp.2, one_mul]
  · intro p _ q _ hpq
    have hu : p.2 * z = q.2 * z := by
      apply Units.ext
      rw [← hdet p.1, ← hdet q.1, hpq]
    have ha : p.2 = q.2 := mul_right_cancel hu
    have hh : p.1 = q.1 := by
      ext i j
      fin_cases j
      · have := congrArg (fun g : GL (Fin 2) (ZMod (l ^ L)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0) hpq
        simpa [ht0] using this
      · have := congrArg (fun g : GL (Fin 2) (ZMod (l ^ L)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1) hpq
        simp only [ht1] at this
        rw [hu] at this
        exact (Units.mul_right_inj _).mp this
    exact Prod.ext hh ha
  · intro γ hγ
    simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, hcast] at hγ
    set g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L)) := (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) with hg
    set u : (ZMod (l ^ L))ˣ := Matrix.GeneralLinearGroup.det γ with hu
    have hug : (u : ZMod (l ^ L)) = g.det := rfl
    set M : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L)) :=
      !![g 0 0, (↑u⁻¹ : ZMod (l ^ L)) * g 0 1; g 1 0, (↑u⁻¹ : ZMod (l ^ L)) * g 1 1] with hM
    have hMdet : M.det = 1 := by
      rw [hM, Matrix.det_fin_two_of]
      have h2 : (↑u⁻¹ : ZMod (l ^ L)) * g.det = 1 := by
        rw [← hug, Units.inv_mul]
      rw [Matrix.det_fin_two] at h2
      linear_combination h2
    refine ⟨(⟨M, hMdet⟩, u * z⁻¹), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hγ.1⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hmod, Units.val_mul, map_mul, hug, hγ.2, ← map_mul, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, map_one]
    · apply Units.ext
      have hz : u * z⁻¹ * z = u := by group
      have e0 : ∀ i, ((t ⟨M, hMdet⟩ (u * z⁻¹ * z) : GL (Fin 2) (ZMod (l ^ L))) :
          Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0 = g i 0 := by
        intro i
        refine (ht0 _ _ i).trans ?_
        fin_cases i <;> rfl
      have e1 : ∀ i, ((t ⟨M, hMdet⟩ (u * z⁻¹ * z) : GL (Fin 2) (ZMod (l ^ L))) :
          Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1 = g i 1 := by
        intro i
        refine (ht1 _ _ i).trans ?_
        rw [hz]
        fin_cases i
        · change (u : ZMod (l ^ L)) * ((↑u⁻¹ : ZMod (l ^ L)) * g 0 1) = g 0 1
          rw [← mul_assoc, Units.mul_inv, one_mul]
        · change (u : ZMod (l ^ L)) * ((↑u⁻¹ : ZMod (l ^ L)) * g 1 1) = g 1 1
          rw [← mul_assoc, Units.mul_inv, one_mul]
      ext i j
      fin_cases j
      · exact e0 i
      · exact e1 i
  · intro p _
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.InZlClosedAddMulAndCyclotomicGaloisStable
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.inZl_closed_add_mul_and_cyclotomic_galois_stable :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (l n : ℕ) [Fact l.Prime], (∀ k : ℕ, InZl ε l n (k : Ω)) ∧ (∀ F G : Ω, InZl ε l n F → InZl ε l n G → InZl ε l n (F + G)) ∧ (∀ F G : Ω, InZl ε l n F → InZl ε l n G → InZl ε l n (F * G)) ∧ ∀ (s : Ω ≃ₐ[ℚ] Ω) (k : ℕ), s (zt ε l n) = zt ε l n ^ k → ∀ F : Ω, InZl ε l n F → InZl ε l n (s F) := by
  intro Ω _ _ ε l n hl
  have hp : l.Prime := hl.out
  have hmul : ∀ D E : ℕ, ¬ l ∣ D → ¬ l ∣ E → ¬ l ∣ D * E := fun D E hD hE h =>
    ((Nat.Prime.dvd_mul hp).1 h).elim hD hE
  refine ⟨fun k => ⟨1, hp.not_dvd_one, ?_⟩, ?_, ?_, ?_⟩
  · rw [Nat.cast_one, one_mul]
    exact natCast_mem _ k
  · rintro F G ⟨D, hD, hF⟩ ⟨E, hE, hG⟩
    refine ⟨D * E, hmul D E hD hE, ?_⟩
    have h : ((D * E : ℕ) : Ω) * (F + G) = (E : Ω) * ((D : Ω) * F) + (D : Ω) * ((E : Ω) * G) := by
      push_cast; ring
    rw [h]
    exact add_mem (mul_mem (natCast_mem _ E) hF) (mul_mem (natCast_mem _ D) hG)
  · rintro F G ⟨D, hD, hF⟩ ⟨E, hE, hG⟩
    refine ⟨D * E, hmul D E hD hE, ?_⟩
    have h : ((D * E : ℕ) : Ω) * (F * G) = ((D : Ω) * F) * ((E : Ω) * G) := by
      push_cast; ring
    rw [h]
    exact mul_mem hF hG
  · rintro s k hs F ⟨D, hD, hF⟩
    refine ⟨D, hD, ?_⟩
    have key : ∀ y ∈ Subring.closure ({zt ε l n} : Set Ω), s y ∈ Subring.closure ({zt ε l n} : Set Ω) := by
      intro y hy
      have hle : Subring.closure ({zt ε l n} : Set Ω) ≤
          (Subring.closure ({zt ε l n} : Set Ω)).comap (s : Ω →+* Ω) := by
        rw [Subring.closure_le, Set.singleton_subset_iff]
        show s (zt ε l n) ∈ Subring.closure ({zt ε l n} : Set Ω)
        rw [hs]
        exact pow_mem (Subring.subset_closure (Set.mem_singleton _)) k
      exact hle hy
    have h := key _ hF
    rwa [map_mul, map_natCast] at h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.IsPrimitiveRootEOmAndPowCompatible
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.isPrimitiveRoot_eOm_and_pow_compatible :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N], (∀ L : ℕ, IsPrimitiveRoot (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (N * l ^ L)) ∧ (∀ L : ℕ, eOm ε (1 / ((N * l ^ L : ℕ) : ℚ)) ^ N = zt ε l L) ∧ (∀ m n : ℕ, eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) ^ (l ^ n) = eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) := by
  intro Ω _ _ _ ε l hl N _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hN0 : N ≠ 0 := NeZero.ne N
  have hl1 : (l : ℚ) ≠ 0 := by exact_mod_cast hl0
  have hN1 : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  refine ⟨fun L => GlobalTheory.K4.isPrimitiveRoot_eOm ε (mul_ne_zero hN0 (pow_ne_zero L hl0)), fun L => ?_, fun m n => ?_⟩
  · rw [← GlobalTheory.UlCusp.eOm_nsmul]
    have h : (N : ℚ) * (1 / ((N * l ^ L : ℕ) : ℚ)) = 1 / (l : ℚ) ^ L := by
      push_cast; field_simp
    rw [h]; rfl
  · rw [← GlobalTheory.UlCusp.eOm_nsmul]
    have h : ((l ^ n : ℕ) : ℚ) * (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) = 1 / ((N : ℚ) * (l : ℚ) ^ m) := by
      push_cast; rw [pow_add]; field_simp
    rw [h]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.NormalModularTowerTopAlgebraModel
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.normal_modularTowerTop_algebraModel :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ), M ≠ 0 → @Normal (topF X M) (topL X M) _ _ (algMdl X _ _) := by
  intro Ω _ _ _ ε X M hM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hζ := isPrimitiveRoot_eOm ε hM
  have hS : fixMu Ω M = (IntermediateField.adjoin ℚ {eOm ε (1 / (M : ℚ))}).fixingSubgroup := by
    unfold fixMu
    congr 1
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      haveI : NeZero M := ⟨hM⟩
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
      exact pow_mem (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)) i
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin ℚ _ hζ.pow_eq_one
  have h := GlobalTheory.K4.LevNormal.normal Ω ε X (CongruenceSubgroup.Gamma M) M _ (Nat.pos_of_ne_zero hM) hζ le_rfl
  rw [← hS] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.RepMApplyZtEqPowRedTop
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.repM_apply_zt_eq_pow_redTop :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N] (y : (ZMod (topM l n m (N * N)))ˣ), (repM (topM l n m (N * N)) y : Ω ≃ₐ[ℚ] Ω) (zt ε l (m + n)) = zt ε l (m + n) ^ ((redTop l n m N y : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n))).val := by
  intro Ω _ _ _ ε l hl n m N _ y
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl0 : l ^ (m + n) ≠ 0 := pow_ne_zero _ hl.out.ne_zero
  haveI : NeZero (l ^ (m + n)) := ⟨hl0⟩
  have h1 : zt ε l (m + n) ^ (l ^ (m + n)) = 1 := by
    have h := (isPrimitiveRoot_eOm ε hl0).pow_eq_one
    rw [Nat.cast_pow] at h
    exact h
  have hd : l ^ (m + n) ∣ topM l n m (N * N) := Dvd.intro _ rfl
  have h2 : zt ε l (m + n) ^ topM l n m (N * N) = 1 := by
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_mul, h1, one_pow]
  rw [repM_apply _ y h2]
  have e : ((redTop l n m N y : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n))) =
      (((y : ZMod (topM l n m (N * N))).val : ℕ) : ZMod (l ^ (m + n))) := by
    show ZMod.castHom hd (ZMod (l ^ (m + n))) (y : ZMod (topM l n m (N * N))) = _
    rw [ZMod.castHom_apply, ZMod.natCast_val]
  rw [e, ZMod.val_natCast, ← pow_eq_pow_mod _ h1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.RingHomApplySmoothedEisensteinCoeff
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem UpperTheory.ring_hom_eisenstein_coeff {K : Type} [Field K] [CharZero K] (s : K →+* K) (j M : ℕ) (ζ : K) (a₁ a₂ b₂ : ℤ)
    (h : s (ζ ^ a₂) = ζ ^ b₂) (n : ℕ) : s (eisF j M ζ a₁ a₂ n) = eisF j M ζ a₁ b₂ n := by
  have hz : ∀ k : ℤ, s (ζ ^ (a₂ * k)) = ζ ^ (b₂ * k) := by
    intro k
    rw [zpow_mul, zpow_mul, map_zpow₀, h]
  have hz' : ∀ k : ℤ, s (ζ ^ (-(a₂ * k))) = ζ ^ (-(b₂ * k)) := by
    intro k
    rw [zpow_neg, zpow_neg, map_inv₀, hz]
  unfold eisF const0 coefPos
  split_ifs
  · simp only [map_div₀, map_mul, map_add (f := _), map_sub, map_one, map_ofNat, h]
  · simp only [map_ratCast]
  · simp only [map_neg, map_ratCast]
  · set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_sub]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    · split_ifs
      · rw [map_mul, map_pow, map_div₀, map_natCast, map_natCast, hz]
      · exact map_zero s
    · split_ifs
      · rw [map_mul, map_pow, map_neg, map_div₀, map_natCast, map_natCast, hz']
      · exact map_zero s

theorem UpperTheory.ringHom_apply_smoothedEisensteinCoeff :
    ∀ {K : Type} [Field K] [CharZero K] (s : K →+* K) (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ b₂ : ℤ), ζ ≠ 0 → s (ζ ^ a₂) = ζ ^ b₂ → ∀ n : ℕ, s (smF c j M ζ a₁ a₂ n) = smF c j M ζ a₁ b₂ n := by
  intro K _ _ s c j M ζ a₁ a₂ b₂ _ h n
  have hc : s (ζ ^ (c * a₂)) = ζ ^ (c * b₂) := by
    rw [mul_comm c a₂, mul_comm c b₂, zpow_mul, zpow_mul, map_zpow₀, h]
  unfold smF
  rw [map_sub, map_mul, map_mul, UpperTheory.ring_hom_eisenstein_coeff s j M ζ a₁ a₂ b₂ h n,
    UpperTheory.ring_hom_eisenstein_coeff s j M ζ (c * a₁) (c * a₂) (c * b₂) hc n]
  simp only [map_pow, map_zpow₀, map_intCast]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCoeffShiftSecondIndex
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem zpow_cg {K : Type} [Field K] {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1) {x y : ℤ}
    (h : x ≡ y [ZMOD M]) : ζ ^ x = ζ ^ y := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  obtain ⟨k, hk⟩ := h.dvd
  have : y = x + (M : ℤ) * k := by linarith
  rw [this, zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

private theorem eisF_shift {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (a₁ a₂ e : ℤ) (hM : 0 < M)
    (hζ : ζ ^ M = 1) (n : ℕ) :
    eisF j M ζ a₁ (a₂ + e * a₁) n = ζ ^ (e * (n : ℤ)) * eisF j M ζ a₁ a₂ n := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  unfold eisF
  split_ifs with hn
  · subst hn
    simp only [Nat.cast_zero, mul_zero, zpow_zero, one_mul]
    unfold const0
    by_cases hd : (M : ℤ) ∣ a₁
    · have : ζ ^ (a₂ + e * a₁) = ζ ^ a₂ :=
        zpow_cg hM hζ (Int.ModEq.symm ((Int.modEq_iff_dvd).2 (by simpa using hd.mul_left e)))
      rw [this]
    · simp only [if_neg hd]
  · unfold coefPos
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hnd : (n : ℤ) = ((n / d : ℕ) : ℤ) * d := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
    rw [mul_sub]
    congr 1
    · split_ifs with h
      · have : ζ ^ ((a₂ + e * a₁) * d) = ζ ^ (e * (n : ℤ)) * ζ ^ (a₂ * d) := by
          rw [← zpow_add₀ h0]
          apply zpow_cg hM hζ
          have h2 := ((h.symm.mul_left e).add_left a₂).mul_right (d : ℤ)
          refine h2.trans ?_
          rw [show (a₂ + e * ((n / d : ℕ) : ℤ)) * d = e * (((n / d : ℕ) : ℤ) * d) + a₂ * d by ring, ← hnd]
        rw [this]; ring
      · rw [mul_zero]
    · split_ifs with h
      · have : ζ ^ (-((a₂ + e * a₁) * d)) = ζ ^ (e * (n : ℤ)) * ζ ^ (-(a₂ * d)) := by
          rw [← zpow_add₀ h0]
          apply zpow_cg hM hζ
          have h2 := (((h.symm.mul_left e).add_left a₂).mul_right (d : ℤ)).neg
          refine h2.trans ?_
          rw [show -((a₂ + e * -((n / d : ℕ) : ℤ)) * d) = e * (((n / d : ℕ) : ℤ) * d) + -(a₂ * d) by ring, ← hnd]
        rw [this]; ring
      · rw [mul_zero]

theorem UpperTheory.smoothedEisensteinCoeff_shift_second_index :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ e : ℤ), 0 < M → ζ ^ M = 1 → ∀ n : ℕ, smF c j M ζ a₁ (a₂ + e * a₁) n = ζ ^ (e * (n : ℤ)) * smF c j M ζ a₁ a₂ n := by
  intro K _ _ c j M ζ a₁ a₂ e hM hζ n
  unfold smF
  rw [show c * (a₂ + e * a₁) = c * a₂ + e * (c * a₁) by ring, eisF_shift j M ζ a₁ a₂ e hM hζ,
    eisF_shift j M ζ (c * a₁) (c * a₂) e hM hζ]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCongrOfModEq
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem zpow_congr_mod {K : Type} [Field K] {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1) {a b : ℤ}
    (h : a ≡ b [ZMOD M]) : ζ ^ a = ζ ^ b := by
  obtain ⟨k, hk⟩ := h.dvd
  have hz : ζ ^ (M : ℤ) = 1 := by
    rw [zpow_natCast, hζ]
  have hb : b = a + M * k := by
    omega
  rw [hb, zpow_add₀ (by rintro rfl; simp [zero_pow hM.ne'] at hζ), zpow_mul, hz, one_zpow, mul_one]

private theorem eisF_congr_mod {K : Type} [Field K] [CharZero K] (j : ℕ) {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1)
    {a₁ b₁ a₂ b₂ : ℤ} (h₁ : a₁ ≡ b₁ [ZMOD M]) (h₂ : a₂ ≡ b₂ [ZMOD M]) (n : ℕ) :
    eisF j M ζ a₁ a₂ n = eisF j M ζ b₁ b₂ n := by
  unfold eisF
  split_ifs
  · unfold const0 frc
    have hd : ((M : ℤ) ∣ a₁ ↔ (M : ℤ) ∣ b₁) := by
      rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, h₁]
    rw [zpow_congr_mod hM hζ h₂, show a₁ % (M : ℤ) = b₁ % M from h₁]
    simp only [hd]
  · unfold coefPos
    refine Finset.sum_congr rfl fun d _ => ?_
    have hc : ∀ x : ℤ, (x ≡ a₁ [ZMOD M] ↔ x ≡ b₁ [ZMOD M]) :=
      fun x => ⟨fun h => h.trans h₁, fun h => h.trans h₁.symm⟩
    simp only [hc, zpow_congr_mod hM hζ (h₂.mul_right (d : ℤ)),
      zpow_congr_mod hM hζ (h₂.mul_right (d : ℤ)).neg]

theorem UpperTheory.smoothedEisenstein_congr_of_modEq :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K), 0 < M → ζ ^ M = 1 → ∀ {a₁ b₁ a₂ b₂ : ℤ}, a₁ ≡ b₁ [ZMOD M] → a₂ ≡ b₂ [ZMOD M] → smF c j M ζ a₁ a₂ = smF c j M ζ b₁ b₂ := by
  intro K _ _ c j M ζ hM hζ a₁ b₁ a₂ b₂ h₁ h₂
  funext n
  unfold smF
  rw [eisF_congr_mod j hM hζ h₁ h₂, eisF_congr_mod j hM hζ (h₁.mul_left c) (h₂.mul_left c)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinRootPow
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem UpperTheory.eisenstein_coeff_root_pow {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (β n : ℕ) :
    eisF j M (ζ ^ β) a₁ a₂ n = eisF j M ζ a₁ ((β : ℤ) * a₂) n := by
  have hz : ∀ t : ℤ, (ζ ^ β) ^ t = ζ ^ ((β : ℤ) * t) := fun t => by
    rw [zpow_mul, zpow_natCast]
  unfold eisF const0 coefPos
  simp only [hz, mul_neg, mul_assoc]

theorem UpperTheory.smoothedEisenstein_root_pow :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (β : ℕ), ζ ≠ 0 → smF c j M (ζ ^ β) a₁ a₂ = smF c j M ζ a₁ ((β : ℤ) * a₂) := by
  intro K _ _ c j M ζ a₁ a₂ β _
  funext n
  unfold smF
  rw [UpperTheory.eisenstein_coeff_root_pow, UpperTheory.eisenstein_coeff_root_pow, mul_left_comm (β : ℤ) c a₂]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.TwistedEisensteinPieceTrivialCharacterEq
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.twistedEisensteinPiece_trivialCharacter_eq :
    ∀ {K : Type} [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (N L m w : ℕ) (c d : ℤ) (v v' : ℤ × ℤ) (ζ : K) (z₀ : ZMod (l ^ m)), 1 ≤ m → m ≤ L → ∀ r : ℕ, pieceT N l L m (w + 2) (1 : DirichletCharacter K (l ^ m)) c d v v' ζ ((unitSet l L).filter fun γ : GL (Fin 2) (ZMod (l ^ L)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m)) = z₀) r = -((l : K) ^ ((L : ℤ) * ((w : ℤ) - 2))) * ∑ γ ∈ ((unitSet l L).filter fun γ : GL (Fin 2) (ZMod (l ^ L)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m)) = z₀), cmul (smF c (w + 1) (N * l ^ L) ζ (rowT N l L γ 0 v).1 (rowT N l L γ 0 v).2) (smF d 1 (N * l ^ L) ζ (rowT N l L γ 1 v').1 (rowT N l L γ 1 v').2) r := by
  intro K _ _ l _ N L m w c d v v' ζ z₀ _ hmL r
  unfold pieceT
  have hd : l ^ m ∣ l ^ L := pow_dvd_pow l hmL
  have hexp : ((L : ℤ) * (((w + 2 : ℕ) : ℤ) - 4)) = (L : ℤ) * ((w : ℤ) - 2) := by
    push_cast
    ring
  have hk : w + 2 - 1 = w + 1 := by omega
  rw [hexp, hk]
  congr 1
  apply Finset.sum_congr rfl
  intro γ _
  have hu : IsUnit ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m))) := by
    rw [ZMod.natCast_val]
    have hdet : IsUnit (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit
    exact hdet.map (ZMod.castHom hd (ZMod (l ^ m)))
  rw [MulChar.one_apply hu, one_mul]
end

