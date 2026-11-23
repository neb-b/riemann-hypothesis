module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.CmulSmFInvariantOfCongruentMulTPow
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem en_cg {M : ℕ} {g g' : SL(2, ℤ)}
    (h : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g' =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g) (i j : Fin 2) :
    en g' i j ≡ en g i j [ZMOD M] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  have := congrArg (fun A : SL(2, ZMod M) => (A : Matrix (Fin 2) (Fin 2) (ZMod M)) i j) h
  exact this

private theorem entries_mul_T_pow (g : SL(2, ℤ)) (b : ℕ) (i : Fin 2) :
    en (g * ModularGroup.T ^ b) i 0 = en g i 0 ∧
      en (g * ModularGroup.T ^ b) i 1 = en g i 1 + (b : ℤ) * en g i 0 := by
  have h := ModularGroup.coe_T_zpow (b : ℤ)
  rw [zpow_natCast] at h
  unfold en
  rw [Matrix.SpecialLinearGroup.coe_mul, h]
  constructor
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

private theorem cmul_phase {K : Type} [Field K] [CharZero K] (ζ : K) (h0 : ζ ≠ 0) (e : ℤ) (f g f' g' : ℕ → K)
    (hf : ∀ n : ℕ, f' n = ζ ^ (e * (n : ℤ)) * f n) (hg : ∀ n : ℕ, g' n = ζ ^ (e * (n : ℤ)) * g n) (n : ℕ) :
    cmul f' g' n = ζ ^ (e * (n : ℤ)) * cmul f g n := by
  unfold cmul
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [hf, hg, Nat.cast_sub hi', show e * (n : ℤ) = e * (i : ℤ) + e * ((n : ℤ) - (i : ℤ)) by ring,
    zpow_add₀ h0]
  ring

theorem UpperTheory.cmul_smF_invariant_of_congruent_mul_T_pow :
    ∀ {K : Type} [Field K] [CharZero K] (ζ : K) (l L N : ℕ) (x : ZMod N) (c d w M : ℕ) [NeZero M], 0 < N → 0 < l → ζ ^ (N * l ^ L) = 1 → N * l ^ L ∣ M → ∀ (b : ℕ) (g g' : SL(2, ℤ)), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g' = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (g * ModularGroup.T ^ b) → ∀ i : ℕ, cmul (smF (c : ℤ) (w + 1) (N * l ^ L) ζ (en g' 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g' 0 1)) (smF (d : ℤ) 1 (N * l ^ L) ζ (en g' 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g' 1 0) ((N : ℤ) * en g' 1 1)) (l ^ L * i) = cmul (smF (c : ℤ) (w + 1) (N * l ^ L) ζ (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1)) (smF (d : ℤ) 1 (N * l ^ L) ζ (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1)) (l ^ L * i) := by
  intro K _ _ ζ l L N x c d w M _ hN hl hζ hM b g g' h i
  have hpos : 0 < N * l ^ L := Nat.mul_pos hN (pow_pos hl L)
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hζ
    exact zero_ne_one hζ
  have hc : ∀ i j, en g' i j ≡ en (g * ModularGroup.T ^ b) i j [ZMOD (N * l ^ L : ℕ)] := fun i j =>
    (en_cg h i j).of_dvd (Int.natCast_dvd_natCast.mpr hM)
  have h00 := hc 0 0
  have h01 := hc 0 1
  have h10 := hc 1 0
  have h11 := hc 1 1
  rw [(entries_mul_T_pow g b _).1] at h00 h10
  rw [(entries_mul_T_pow g b _).2] at h01 h11
  have e1 : smF (c : ℤ) (w + 1) (N * l ^ L) ζ
      (en g' 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g' 0 1) =
      smF (c : ℤ) (w + 1) (N * l ^ L) ζ
      (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1 +
        ((N : ℤ) * b) * (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L))) := by
    refine UpperTheory.smoothedEisenstein_congr_of_modEq _ _ _ ζ hpos hζ (h00.mul_right _) ((h01.mul_left _).trans ?_)
    refine Int.modEq_iff_dvd.2 ⟨b * en g 0 0 * (x.val : ℤ) * (topT l L N : ℤ), ?_⟩
    push_cast
    ring
  have e2 : smF (d : ℤ) 1 (N * l ^ L) ζ
      (en g' 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g' 1 0) ((N : ℤ) * en g' 1 1) =
      smF (d : ℤ) 1 (N * l ^ L) ζ
      (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1 +
        ((N : ℤ) * b) * (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0)) := by
    refine UpperTheory.smoothedEisenstein_congr_of_modEq _ _ _ ζ hpos hζ (((h00.mul_right _).mul_right _).add h10) ((h11.mul_left _).trans ?_)
    refine Int.modEq_iff_dvd.2 ⟨b * en g 0 0 * (topT l L N : ℤ), ?_⟩
    push_cast
    ring
  rw [e1, e2, cmul_phase ζ h0 ((N : ℤ) * b) _ _ _ _
    (UpperTheory.smoothedEisensteinCoeff_shift_second_index _ _ _ ζ _ _ _ hpos hζ) (UpperTheory.smoothedEisensteinCoeff_shift_second_index _ _ _ ζ _ _ _ hpos hζ)]
  have : ζ ^ ((N : ℤ) * b * ((l ^ L * i : ℕ) : ℤ)) = 1 := by
    rw [show (N : ℤ) * b * ((l ^ L * i : ℕ) : ℤ) = ((N * l ^ L * (b * i) : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_mul, hζ, one_pow]
  rw [this, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.Gamma0DiamondActionEq
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.gamma0_diamond_action_eq :
    ∀ {K : Type} [Field K] [CharZero K] (ζ : K) (l : ℕ) [Fact l.Prime] (L N : ℕ) [NeZero N] (x : ZMod N) (c d w : ℕ) (a : ℤ) (s : K →+* K) (u : ZMod (l ^ L)), ¬ l ∣ N → ζ ^ (N * l ^ L) = 1 → s (ζ ^ N) = (ζ ^ N) ^ u.val → ∀ g ∈ CongruenceSubgroup.Gamma0 N, ((en g 0 0 : ℤ) : ZMod N) = (a : ZMod N) → ∀ h : GL (Fin 2) (ZMod (l ^ L)), (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 0 0 = ((en g 0 0 : ℤ) : ZMod (l ^ L)) → (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 0 1 = u * (((N : ℤ) * en g 0 1 : ℤ) : ZMod (l ^ L)) → (N : ZMod (l ^ L)) * (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 1 0 = ((en g 1 0 : ℤ) : ZMod (l ^ L)) → (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 1 1 = u * ((en g 1 1 : ℤ) : ZMod (l ^ L)) → ∀ r : ℕ, s (cmul (smF (c : ℤ) (w + 1) (N * l ^ L) ζ (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1)) (smF (d : ℤ) 1 (N * l ^ L) ζ (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1)) r) = cmul (smF (c : ℤ) (w + 1) (N * l ^ L) ζ (rowT N l L h 0 ((x.val : ℤ) * a * (topT l L N : ℤ), 0)).1 (rowT N l L h 0 ((x.val : ℤ) * a * (topT l L N : ℤ), 0)).2) (smF (d : ℤ) 1 (N * l ^ L) ζ (rowT N l L h 1 (a * (topT l L N : ℤ), 0)).1 (rowT N l L h 1 (a * (topT l L N : ℤ), 0)).2) r := by
  intro K _ _ ζ l hl L N _ x c d w a s u hlN hζ hs g hg ha h h00 h01 h10 h11 r
  have hP : 0 < l ^ L := pow_pos hl.out.pos L
  haveI : NeZero (l ^ L) := ⟨hP.ne'⟩
  have hM : 0 < N * l ^ L := Nat.mul_pos (NeZero.pos N) hP
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  have hz : ∀ k : ℤ, s (ζ ^ ((N : ℤ) * k)) = ζ ^ ((N : ℤ) * (u.val * k)) := by
    intro k
    rw [zpow_mul, map_zpow₀, zpow_natCast, hs, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  have ea : (N : ℤ) ∣ a - en g 0 0 := ((ZMod.intCast_eq_intCast_iff _ _ _).1 ha).dvd
  have eg : (N : ℤ) ∣ en g 1 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact CongruenceSubgroup.Gamma0_mem.1 hg
  have key : ∀ p q : ℤ, ((p : ℤ) : ZMod (l ^ L)) = (q : ZMod (l ^ L)) → (l : ℤ) ^ L ∣ q - p := by
    intro p q hpq
    have := ((ZMod.intCast_eq_intCast_iff _ _ _).1 hpq).dvd
    simpa using this
  have e00 := key (en g 0 0) ((h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 0 0).val
    (by rw [Int.cast_natCast, ZMod.natCast_zmod_val, h00])
  have e01 := key (u.val * ((N : ℤ) * en g 0 1)) ((h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 0 1).val
    (by rw [Int.cast_natCast, ZMod.natCast_zmod_val, h01, Int.cast_mul (u.val : ℤ), Int.cast_natCast, ZMod.natCast_zmod_val])
  have e11 := key (u.val * (en g 1 1)) ((h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 1 1).val
    (by rw [Int.cast_natCast, ZMod.natCast_zmod_val, h11, Int.cast_mul (u.val : ℤ), Int.cast_natCast, ZMod.natCast_zmod_val])
  have e10 := key (en g 1 0) ((N : ℤ) * ((h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 1 0).val)
    (by rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, h10])
  have hcop : IsCoprime (N : ℤ) ((l : ℤ) ^ L) :=
    (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hlN).symm).pow_right
  have e10' : (N : ℤ) * (l : ℤ) ^ L ∣ (N : ℤ) * ((h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 1 0).val - en g 1 0 :=
    hcop.mul_dvd (dvd_sub (dvd_mul_right _ _) eg) e10
  obtain ⟨k, hk⟩ := ea
  obtain ⟨k00, hk00⟩ := e00
  obtain ⟨k01, hk01⟩ := e01
  obtain ⟨k11, hk11⟩ := e11
  obtain ⟨k10, hk10⟩ := e10'
  have c1 : en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L) ≡
      (rowT N l L h 0 ((x.val : ℤ) * a * (topT l L N : ℤ), 0)).1 [ZMOD (N * l ^ L : ℕ)] := by
    refine Int.modEq_iff_dvd.2 ⟨k00 + (x.val : ℤ) * (topT l L N : ℤ) * k, ?_⟩
    simp only [rowT, Nat.cast_mul, Nat.cast_pow]
    linear_combination (N : ℤ) * hk00 + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L * hk
  have c2 : (N : ℤ) * (u.val * ((N : ℤ) * en g 0 1)) ≡
      (rowT N l L h 0 ((x.val : ℤ) * a * (topT l L N : ℤ), 0)).2 [ZMOD (N * l ^ L : ℕ)] := by
    refine Int.modEq_iff_dvd.2 ⟨k01, ?_⟩
    simp only [rowT, Nat.cast_mul, Nat.cast_pow]
    linear_combination (N : ℤ) * hk01
  have c3 : en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0 ≡
      (rowT N l L h 1 (a * (topT l L N : ℤ), 0)).1 [ZMOD (N * l ^ L : ℕ)] := by
    refine Int.modEq_iff_dvd.2 ⟨k10 + (topT l L N : ℤ) * k, ?_⟩
    simp only [rowT, Nat.cast_mul, Nat.cast_pow]
    linear_combination hk10 + (topT l L N : ℤ) * (l : ℤ) ^ L * hk
  have c4 : (N : ℤ) * (u.val * (en g 1 1)) ≡
      (rowT N l L h 1 (a * (topT l L N : ℤ), 0)).2 [ZMOD (N * l ^ L : ℕ)] := by
    refine Int.modEq_iff_dvd.2 ⟨k11, ?_⟩
    simp only [rowT, Nat.cast_mul, Nat.cast_pow]
    linear_combination (N : ℤ) * hk11
  rw [← UpperTheory.smoothedEisenstein_congr_of_modEq (c : ℤ) (w + 1) (N * l ^ L) ζ hM hζ c1 c2, ← UpperTheory.smoothedEisenstein_congr_of_modEq (d : ℤ) 1 (N * l ^ L) ζ hM hζ c3 c4]
  unfold cmul
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz1 : s (ζ ^ ((N : ℤ) ^ 2 * en g 0 1)) = ζ ^ ((N : ℤ) * (u.val * ((N : ℤ) * en g 0 1))) := by
    rw [← hz, sq, mul_assoc]
  rw [map_mul, UpperTheory.ringHom_apply_smoothedEisensteinCoeff s _ _ _ ζ _ _ _ h0 hz1, UpperTheory.ringHom_apply_smoothedEisensteinCoeff s _ _ _ ζ _ _ _ h0 (hz _)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.PieceTDetFiberEqPieceTRootPow
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem siegel_function_root_power_eq {K : Type} [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (N m j : ℕ) (c a : ℤ) (ζ : K) (β : ℕ)
    (hN : 0 < N) (hζ : ζ ^ (N * l ^ m) = 1) (y : ZMod (l ^ m)) :
    smF c j (N * l ^ m) (ζ ^ β) a ((N : ℤ) * (y.val : ℤ) + (l : ℤ) ^ m * 0) =
      smF c j (N * l ^ m) ζ a ((N : ℤ) * (((y * (β : ZMod (l ^ m))).val : ℕ) : ℤ) + (l : ℤ) ^ m * 0) := by
  have hl : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  haveI : NeZero (l ^ m) := ⟨hl.ne'⟩
  have hM : 0 < N * l ^ m := Nat.mul_pos hN hl
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  rw [UpperTheory.smoothedEisenstein_root_pow c j _ ζ a _ β hζ0]
  refine UpperTheory.smoothedEisenstein_congr_of_modEq c j _ ζ hM hζ (Int.ModEq.refl _) ?_
  have h1 : ((β : ℤ) * (y.val : ℤ)) ≡ (((y * (β : ZMod (l ^ m))).val : ℕ) : ℤ) [ZMOD ((l ^ m : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    simp [mul_comm]
  have h2 := Int.ModEq.mul_left' (c := (N : ℤ)) h1
  simp only [mul_zero, add_zero]
  rw [Nat.cast_mul N, mul_left_comm]
  exact h2

theorem UpperTheory.pieceT_det_fiber_eq_pieceT_root_pow :
    ∀ {K : Type} [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (N m k : ℕ) (c d xt t : ℤ) (ζ : K) (β : ℕ) (z₀ : ZMod (l ^ m)), 0 < N → 1 ≤ m → ζ ^ (N * l ^ m) = 1 → IsUnit z₀ → (β : ZMod (l ^ m)) = z₀ → ∀ r : ℕ, pieceT N l m m k (1 : DirichletCharacter K (l ^ m)) c d (xt, 0) (t, 0) ζ ((unitSet l m).filter fun γ : GL (Fin 2) (ZMod (l ^ m)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det.val : ℕ) : ZMod (l ^ m)) = z₀) r = pieceT N l m m k (1 : DirichletCharacter K (l ^ m)) c d (xt, 0) (t, 0) (ζ ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1) r := by
  intro K _ _ l _ N m k c d xt t ζ β z₀ hN hm hζ hz hβ r
  have hl : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  haveI : NeZero (l ^ m) := ⟨hl.ne'⟩
  have hdet : (!![1, 0; 0, z₀] : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = z₀ := by
    simp [Matrix.det_fin_two]
  obtain ⟨D, hD⟩ : ∃ D : GL (Fin 2) (ZMod (l ^ m)), (D : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) = !![1, 0; 0, z₀] :=
    ⟨Matrix.GeneralLinearGroup.mk'' _ (by rw [hdet]; exact hz), rfl⟩
  have e0 : ∀ (γ : GL (Fin 2) (ZMod (l ^ m))) (i : Fin 2),
      ((γ * D : GL (Fin 2) (ZMod (l ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) i 0 =
        (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) i 0 := by
    intro γ i
    rw [Units.val_mul, hD]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e1 : ∀ (γ : GL (Fin 2) (ZMod (l ^ m))) (i : Fin 2),
      ((γ * D : GL (Fin 2) (ZMod (l ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) i 1 =
        (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) i 1 * (β : ZMod (l ^ m)) := by
    intro γ i
    rw [Units.val_mul, hD, hβ]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have ed : ∀ (γ : GL (Fin 2) (ZMod (l ^ m))),
      ((γ * D : GL (Fin 2) (ZMod (l ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det =
        (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det * z₀ := by
    intro γ
    rw [Units.val_mul, Matrix.det_mul, hD, hdet]
  have eψ : ∀ (γ : GL (Fin 2) (ZMod (l ^ m))),
      (1 : DirichletCharacter K (l ^ m))
        (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det.val : ℕ) : ZMod (l ^ m)) = 1 := by
    intro γ
    rw [ZMod.natCast_zmod_val]
    exact MulChar.one_apply (Matrix.isUnits_det_units γ)
  unfold pieceT
  congr 1
  symm
  refine Finset.sum_equiv (Equiv.mulRight D) (fun γ => ?_) (fun γ _ => ?_)
  · simp only [Finset.mem_filter, unitSet, Finset.mem_univ, true_and, Equiv.coe_mulRight, e0, ed, ZMod.natCast_zmod_val]
    refine and_congr_right fun _ => ⟨fun h => by rw [h, one_mul], fun h => ?_⟩
    exact hz.mul_right_cancel (by rw [h, one_mul])
  · simp only [Equiv.coe_mulRight, eψ, rowT, e0, e1]
    rw [siegel_function_root_power_eq l N m _ c _ ζ β hN hζ, siegel_function_root_power_eq l N m _ d _ ζ β hN hζ]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.PieceTLevelRaiseEqVp
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.pieceT_level_raise_eq_vp :
    ∀ {K : Type} [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (N m k : ℕ) (c d : ℤ) (z₀ : ZMod (l ^ m)), 0 < N → ¬ l ∣ N → 1 ≤ m → 3 ≤ k → ¬ (l : ℤ) ∣ c → ¬ (l : ℤ) ∣ d → ∀ (n : ℕ) (ζ : K) (v v' u u' : ℤ × ℤ), IsPrimitiveRoot ζ (N * l ^ (m + n)) → (l : ℤ) ^ n * v.1 ≡ u.1 [ZMOD N] → (l : ℤ) ^ n * v.2 ≡ u.2 [ZMOD N] → (l : ℤ) ^ n * v'.1 ≡ u'.1 [ZMOD N] → (l : ℤ) ^ n * v'.2 ≡ u'.2 [ZMOD N] → ∀ r : ℕ, pieceT N l (m + n) m k (1 : DirichletCharacter K (l ^ m)) c d v v' ζ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀) r = vp (l ^ n) (pieceT N l m m k (1 : DirichletCharacter K (l ^ m)) c d u u' (ζ ^ (l ^ n)) ((unitSet l m).filter fun γ : GL (Fin 2) (ZMod (l ^ m)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det.val : ℕ) : ZMod (l ^ m)) = z₀)) r := by
  intro K _ _ l hl N m k c d z₀ hN hlN hm hk hc hd n
  have cop : IsCoprime (l : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hlN)
  induction n with
  | zero =>
    intro ζ v v' u u' hζ h1 h2 h3 h4 r
    simp only [pow_zero, one_mul, pow_one, Nat.add_zero] at *
    have hv : ∀ f : ℕ → K, vp 1 f r = f r := fun f => by simp [vp]
    rw [hv]
    unfold pieceT
    congr 1
    refine Finset.sum_congr rfl fun γ _ => ?_
    congr 1
    have M0 : 0 < N * l ^ m := Nat.mul_pos hN (pow_pos hl.out.pos _)
    have key : ∀ (a : ℤ) {s t : ℤ}, s ≡ t [ZMOD N] → a + (l : ℤ) ^ m * s ≡ a + (l : ℤ) ^ m * t [ZMOD ((N * l ^ m : ℕ) : ℤ)] := by
      intro a s t h
      refine Int.ModEq.add_left _ ?_
      have := h.mul_left' (c := (l : ℤ) ^ m)
      push_cast
      rwa [mul_comm (N : ℤ)]
    congr 1
    · exact UpperTheory.smoothedEisenstein_congr_of_modEq _ _ _ _ M0 hζ.pow_eq_one (key _ h1) (key _ h2)
    · exact UpperTheory.smoothedEisenstein_congr_of_modEq _ _ _ _ M0 hζ.pow_eq_one (key _ h3) (key _ h4)
  | succ n ih =>
    intro ζ v v' u u' hζ h1 h2 h3 h4 r
    have hX := _root_.GlobalTheory.KummerEisensteinGalois.pieceT_unitSet_level_succ l N (m + n) m k K (1 : DirichletCharacter K (l ^ m)) c d ((l : ℤ) * v.1, (l : ℤ) * v.2) ((l : ℤ) * v'.1, (l : ℤ) * v'.2) v v' ζ
      ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀)
      hζ hN hlN hm (Nat.le_add_right m n) hk hc hd rfl rfl rfl rfl (fun γ hγ => by
        simpa [unitSet] using (Finset.mem_filter.1 hγ).1) r
    have hζ' : IsPrimitiveRoot (ζ ^ l) (N * l ^ (m + n)) :=
      hζ.pow (Nat.mul_pos hN (pow_pos hl.out.pos _)) (by rw [← Nat.add_assoc, pow_succ]; ring)
    have e : ∀ {s t : ℤ}, (l : ℤ) ^ (n + 1) * s ≡ t [ZMOD N] → (l : ℤ) ^ n * ((l : ℤ) * s) ≡ t [ZMOD N] := fun h => by
      rwa [pow_succ, mul_assoc] at h
    have hI := funext (ih (ζ ^ l) ((l : ℤ) * v.1, (l : ℤ) * v.2) ((l : ℤ) * v'.1, (l : ℤ) * v'.2) u u' hζ' (e h1) (e h2) (e h3) (e h4))
    rw [hI] at hX
    have hval : ∀ (j : ℕ) (hj : l ^ j ∣ l ^ (m + n)) (a : ZMod (l ^ (m + n + 1))),
        (((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (m + n))) (ZMod (l ^ (m + n))) a).val : ℕ) : ZMod (l ^ j)) = ((a.val : ℕ) : ZMod (l ^ j)) := by
      intro j hj a
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, ZMod.natCast_eq_natCast_iff]
      exact (Nat.mod_modEq _ _).of_dvd hj
    have hdv : ∀ a : ZMod (l ^ (m + n + 1)),
        l ∣ (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (m + n))) (ZMod (l ^ (m + n))) a).val ↔ l ∣ a.val := by
      intro a
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
      exact Nat.dvd_mod_iff (dvd_pow_self l (by omega))
    refine Eq.trans ?_ (hX.trans ?_)
    · congr 1
      ext γ
      simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have d1 : ((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (m + n))) (ZMod (l ^ (m + n)))) γ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))) = (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (m + n))) (ZMod (l ^ (m + n)))).mapMatrix (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n + 1)))) := rfl
      rw [d1, ← RingHom.map_det, hval m (pow_dvd_pow l (Nat.le_add_right m n))]
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hdv]
    · rw [← pow_mul, ← pow_succ']
      simp only [vp]
      by_cases h : l ∣ r
      · obtain ⟨r', rfl⟩ := h
        have : l ^ (n + 1) ∣ l * r' ↔ l ^ n ∣ r' := by rw [pow_succ', Nat.mul_dvd_mul_iff_left hl.out.pos]
        rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl.out.pos]
        simp only [this]
        rw [pow_succ' l n, Nat.mul_div_mul_left _ _ hl.out.pos]
      · rw [if_neg h, if_neg (fun h' => h ((dvd_pow_self l (Nat.succ_ne_zero n)).trans h'))]
end

