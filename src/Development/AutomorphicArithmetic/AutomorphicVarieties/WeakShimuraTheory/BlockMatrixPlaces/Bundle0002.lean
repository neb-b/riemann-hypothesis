module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.FlagVec
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem unit_add_mem {R : Type} [CommRing R] [IsLocalRing R] {a b : R} (ha : IsUnit a)
    (hb : b ∈ maximalIdeal R) : IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : a ∈ maximalIdeal R := by simpa using (maximalIdeal R).sub_mem h1 hb
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 ha

private theorem two_kill {R : Type} [CommRing R] [IsLocalRing R] {p q r s a b : R} (hp : IsUnit p) (hs : IsUnit s)
    (hq : q ∈ maximalIdeal R) (e1 : p * a + q * b = 0) (e2 : r * a + s * b = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨s', hs'⟩ := hs.exists_right_inv
  have hb : b = -(s' * r) * a := by linear_combination s' * e2 - b * hs'
  have hm : q * s' * r ∈ maximalIdeal R :=
    (maximalIdeal R).mul_mem_right _ ((maximalIdeal R).mul_mem_right _ hq)
  have hu : IsUnit (p + -(q * s' * r)) := unit_add_mem hp ((maximalIdeal R).neg_mem hm)
  have ha : a = 0 := (hu.mul_right_eq_zero).mp (by linear_combination e1 - q * hb)
  refine ⟨ha, ?_⟩
  rw [hb, ha]
  ring

private theorem cols {R : Type} [CommRing R] [IsLocalRing R] (X u U : M4 R) (hb : IsBlock X) (hs : Sep X)
    (e : X * u = u * U) (hU : IsUp U) (hc : ∀ i, U i i - X i i ∈ maximalIdeal R) :
    ∃ y, u 0 1 = y * u 0 0 ∧ u 2 1 = y * u 2 0 := by
  have h01 : IsUnit (X 0 0 - X 1 1) := hs.unit 0 1 (by decide)
  have h21 : IsUnit (X 2 2 - X 1 1) := hs.unit 2 1 (by decide)
  have p0 : IsUnit (X 0 0 - U 1 1) := by
    have := unit_add_mem h01 (neg_mem (hc 1))
    convert this using 1; ring
  have p2 : IsUnit (X 2 2 - U 1 1) := by
    have := unit_add_mem h21 (neg_mem (hc 1))
    convert this using 1; ring
  have pU : IsUnit (U 0 0 - U 1 1) := by
    have := unit_add_mem p0 (hc 0)
    convert this using 1; ring
  obtain ⟨w, hw⟩ := pU.exists_left_inv
  have z01 := hb 0 1 (by decide)
  have z03 := hb 0 3 (by decide)
  have z21 := hb 2 1 (by decide)
  have z23 := hb 2 3 (by decide)
  have y10 := hU 1 0 (by decide)
  have y20 := hU 2 0 (by decide)
  have y30 := hU 3 0 (by decide)
  have y21 := hU 2 1 (by decide)
  have y31 := hU 3 1 (by decide)
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_four, z01, z03, z21, z23, y10, y20, y30, y21, y31, zero_mul, mul_zero,
    add_zero] at e00 e01 e20 e21
  have := two_kill (a := u 0 1 - U 0 1 * w * u 0 0) (b := u 2 1 - U 0 1 * w * u 2 0) (r := X 2 0) p0 p2
    (hs.off 0 2 (by decide))
    (by linear_combination e01 - U 0 1 * w * e00 - U 0 1 * u 0 0 * hw)
    (by linear_combination e21 - U 0 1 * w * e20 - U 0 1 * u 2 0 * hw)
  exact ⟨U 0 1 * w, sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩

private theorem entries_one_three_zero_eq_zero_of_intertwine_up {R : Type} [CommRing R] [IsLocalRing R] (X u U : M4 R) (hb : IsBlock X)
    (hs : Sep X) (e : X * u = u * U) (hU : IsUp U) (hc : ∀ i, U i i - X i i ∈ maximalIdeal R) :
    u 1 0 = 0 ∧ u 3 0 = 0 := by
  have X10 : X 1 0 = 0 := hb 1 0 (by simp [lamW])
  have coord_mul_inv_coord_eq_one : X 1 2 = 0 := hb 1 2 (by simp [lamW])
  have X30 : X 3 0 = 0 := hb 3 0 (by simp [lamW])
  have X32 : X 3 2 = 0 := hb 3 2 (by simp [lamW])
  have U10 : U 1 0 = 0 := hU 1 0 (by decide)
  have U20 : U 2 0 = 0 := hU 2 0 (by decide)
  have U30 : U 3 0 = 0 := hU 3 0 (by decide)
  have r10 := congrFun (congrFun e 1) 0
  have r30 := congrFun (congrFun e 3) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_four, X10, coord_mul_inv_coord_eq_one, X30, X32, U10, U20, U30,
    zero_mul, mul_zero, add_zero, zero_add] at r10 r30
  have hc0 := hc 0
  have hp : IsUnit (X 1 1 - U 0 0) := by
    have e' : X 1 1 - U 0 0 = (X 1 1 - X 0 0) + -(U 0 0 - X 0 0) := by ring
    rw [e']
    exact unit_add_mem (hs.unit 1 0 (by simp [lamW])) ((maximalIdeal R).neg_mem hc0)
  have hs' : IsUnit (X 3 3 - U 0 0) := by
    have e' : X 3 3 - U 0 0 = (X 3 3 - X 0 0) + -(U 0 0 - X 0 0) := by ring
    rw [e']
    exact unit_add_mem (hs.unit 3 0 (by simp [lamW])) ((maximalIdeal R).neg_mem hc0)
  have hq : X 1 3 ∈ maximalIdeal R := hs.off 1 3 (by decide)
  exact two_kill (r := X 3 1) (a := u 1 0) (b := u 3 0) hp hs' hq
    (by linear_combination r10) (by linear_combination r30)

theorem UpperTheory.V.Ws.Bl.flagVec :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X u : M4 R), IsBlock X → Sep X → IsGSp 1 u → IsUp (adj u * X * u) → (∀ i, (adj u * X * u) i i - X i i ∈ maximalIdeal R) → uPlus u ≠ ⊥ := by
  intro R _ _ X u hb hs hg hup hc
  have hinv : adj u * u = 1 := by simpa [IsGSp] using hg
  have e : X * u = u * (adj u * X * u) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.mp hinv, Matrix.one_mul]
  obtain ⟨y, hy1, hy2⟩ := cols X u _ hb hs e hup hc
  obtain ⟨h10, h30⟩ := entries_one_three_zero_eq_zero_of_intertwine_up X u _ hb hs e hup hc
  have I10 := congrFun (congrFun hinv 1) 0
  have I11 := congrFun (congrFun hinv 1) 1
  have I00 := congrFun (congrFun hinv 0) 0
  have I31 := congrFun (congrFun hinv 3) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev] at I10 I11 I00 I31
  have iso : u 0 0 * u 3 1 = u 2 0 * u 1 1 := by
    linear_combination I31 - u 2 1 * h10 + u 0 1 * h30
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → R, w = ![0, u 1 1, 0, u 3 1] := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin 4 → R, φ = ![u 2 0, 0, -u 0 0, 0] := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y : M4 R, Y = Matrix.vecMulVec w φ := ⟨_, rfl⟩
  have hYm : Y ∈ uM R := by
    show Y ∈ hAB R ⊓ sp4 R
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · show ∀ i j, ¬ lamW i < lamW j → Y i j = 0
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [lamW, Matrix.vecMulVec_apply]
    · show adj Y = -Y
      ext i j
      fin_cases i <;> fin_cases j <;>
        (try simp [hYd, hw, hφ, adj_apply, sgn, Fin.rev, Matrix.vecMulVec_apply]) <;>
        first
          | linear_combination iso
          | linear_combination (-1 : R) * iso
  have hv : w = Matrix.mulVec u ![-y, 1, 0, 0] := by
    funext i
    fin_cases i <;> simp [hw, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      first
        | linear_combination (-1 : R) * hy1
        | linear_combination y * h10
        | linear_combination (-1 : R) * hy2
        | linear_combination y * h30
        | linear_combination hy1
        | linear_combination hy2
        | linear_combination (-y) * h10
        | linear_combination (-y) * h30
  have hA : Matrix.mulVec (adj u) w = ![-y, 1, 0, 0] := by
    rw [hv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hB0 : Matrix.vecMul φ u 0 = 0 := by
    simp [hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_four] <;> ring
  have hB1 : Matrix.vecMul φ u 1 = 0 := by
    simp [hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_four] <;>
      linear_combination u 2 0 * hy1 - u 0 0 * hy2
  have hN : adj u * Y * u = Matrix.vecMulVec ![-y, 1, 0, 0] (Matrix.vecMul φ u) := by
    rw [hYd, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hA]
  have hsup : IsSUp (adj u * Y * u) := by
    intro i j hji
    rw [hN, Matrix.vecMulVec_apply]
    fin_cases i <;> fin_cases j <;>
      first
        | (simp [hB0, hB1]; done)
        | (exfalso; simp at hji; done)
        | (exfalso; revert hji; decide)
  rw [Submodule.ne_bot_iff]
  refine ⟨⟨Y, hYm⟩, ?_, ?_⟩
  · exact hsup
  · intro hY0
    have hY : Y = 0 := congrArg Subtype.val hY0
    have f1 : u 1 1 * u 2 0 = 0 := by
      have h := congrFun (congrFun hY 1) 0
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f2 : u 1 1 * u 0 0 = 0 := by
      have h := congrFun (congrFun hY 1) 2
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero, -neg_eq_zero, -mul_neg] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f3 : u 3 1 * u 2 0 = 0 := by
      have h := congrFun (congrFun hY 3) 0
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f4 : u 3 1 * u 0 0 = 0 := by
      have h := congrFun (congrFun hY 3) 2
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero, -neg_eq_zero, -mul_neg] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have J : u 2 2 * u 1 1 - u 0 2 * u 3 1 = 1 := by
      linear_combination I11 - u 3 2 * hy1 + u 1 2 * hy2 - y * I10 + y * u 2 2 * h10 -
        y * u 0 2 * h30
    have z00 : u 0 0 = 0 := by linear_combination (-u 0 0) * J + u 2 2 * f2 - u 0 2 * f4
    have z20 : u 2 0 = 0 := by linear_combination (-u 2 0) * J + u 2 2 * f1 - u 0 2 * f3
    have h1 : (1 : R) = 0 := by
      linear_combination (-1 : R) * I00 + u 3 3 * z00 + u 2 3 * h10 - u 1 3 * z20 - u 0 3 * h30
    exact one_ne_zero h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.IsPrecompleteFinite
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem, mem_smul_top_pi] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact h i
  choose L hL using key
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have h := hL i n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.map_surjective I hπ y
  obtain ⟨w, rfl⟩ := AdicCompletion.of_surjective I (Fin r → R) z
  exact ⟨π w, (AdicCompletion.map_of I π w).symm⟩

private theorem lift_seq {A : Type} [CommRing A] [IsLocalRing A] {T : Type} [AddCommGroup T] [Module A T]
    [IsPrecomplete (maximalIdeal A) T] (x : ∀ n, T ⧸ lev A T n) (hx : ∀ n, redn A T n (x (n + 1)) = x n) :
    ∃ L : T, ∀ n, (lev A T n).mkQ L = x n := by
  choose f hf using fun n => (lev A T n).mkQ_surjective (x n)
  have h1 : ∀ n, f n - f (n + 1) ∈ lev A T n := fun n => by
    rw [← Submodule.Quotient.eq]
    have := hx n
    rw [← hf (n + 1), redn_mk, ← hf n] at this
    exact this.symm
  have h2 : ∀ m n, m ≤ n → f m - f n ∈ lev A T m := fun m n hmn => by
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h3 : lev A T n ≤ lev A T m := Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)
      simpa using (lev A T m).add_mem ih (h3 (h1 n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal A) f fun {m n} hmn => SModEq.sub_mem.2 (h2 m n hmn)
  exact ⟨L, fun n => Eq.trans (SModEq.def.1 (hL n).symm) (hf n)⟩

private theorem mem_of_lev {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {T : Type} [AddCommGroup T]
    [Module A T] [Module.Finite A T] (P : Submodule A T) (x : T)
    (hx : ∀ n, (lev A T n).mkQ x ∈ P.map (lev A T n).mkQ) : x ∈ P := by
  rw [← Submodule.Quotient.mk_eq_zero]
  refine IsHausdorff.haus' (I := maximalIdeal A) _ fun n => ?_
  obtain ⟨p, hp, e⟩ := hx n
  have e' : p - x ∈ lev A T n := (Submodule.Quotient.eq _).1 e
  have h1 : P.mkQ (p - x) ∈ (lev A T n).map P.mkQ := Submodule.mem_map_of_mem e'
  rw [Submodule.map_smul'', map_sub, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 hp, zero_sub,
    neg_mem_iff] at h1
  rw [SModEq.zero]
  exact Submodule.smul_mono le_rfl le_top h1

private theorem eq_of_lev {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {T : Type} [AddCommGroup T]
    [Module A T] [Module.Finite A T] (x y : T)
    (hx : ∀ n, (lev A T n).mkQ x = (lev A T n).mkQ y) : x = y := by
  rw [← sub_eq_zero, ← Submodule.mem_bot A]
  refine mem_of_lev ⊥ _ fun n => ?_
  rw [map_sub, hx n, sub_self]
  exact zero_mem _

theorem UpperTheory.V.Ws.Bl.limit :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), IsAdicComplete (maximalIdeal A) A → ∀ (z : ∀ n, Γ → T ⧸ lev A T n) (y : ∀ n, T ⧸ lev A T n), (∀ n, IsZn ρ c N H P n (z n) (y n)) → (∀ n g, redn A T n (z (n + 1) g) = z n g) → (∀ n, redn A T n (y (n + 1)) = y n) → Prim (z 1) →
          ∃ (z' : Γ → T) (y' : T), IsZT ρ c N H P z' y' ∧ z' ≠ 0 := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hA z y hZ hz hy hP
  haveI : IsPrecomplete (maximalIdeal A) T := isPrecomplete_finite _
  choose z' hz' using fun g => lift_seq (fun n => z n g) fun n => hz n g
  obtain ⟨y', hy'⟩ := lift_seq y hy
  refine ⟨z', y', ⟨fun n => ?_, fun g h => ?_, ?_, fun g hg => ?_, fun h hh => ?_⟩, ?_⟩
  · simp only [hz']
    exact (hZ n).lc
  · refine eq_of_lev (A := A) _ _ fun n => ?_
    rw [map_add (f := _), ← modRep_mk, hz', hz', hz']
    exact (hZ n).coc g h
  · refine eq_of_lev (A := A) _ _ fun n => ?_
    rw [hz', map_zero]
    exact (hZ n).cz
  · refine eq_of_lev (A := A) _ _ fun n => ?_
    rw [hz', map_zero]
    exact (hZ n).kill g hg
  · refine mem_of_lev P _ fun n => ?_
    rw [map_sub, map_sub, ← modRep_mk, hz', hy']
    exact (hZ n).loc h hh
  · rintro rfl
    obtain ⟨g, hg⟩ := hP
    apply hg
    rw [← hz' g 1, Pi.zero_apply, map_zero]
    exact zero_mem _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.NoCompl
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem blk_one {R : Type} [CommRing R] : IsBlock (1 : M4 R) := fun i j h =>
  Matrix.one_apply_ne fun e => h (by rw [e])

private theorem key {R : Type} [CommRing R] {X Z Y : M4 R} (hX : IsBlock X) (hZ : Z ∈ hAB R) (hY : Y ∈ hAB R)
    (h : IsBlock ((1 - Y) * ((1 + Z) * X) * (1 + Y))) : Z * X + X * Y - Y * X = 0 := by
  have hZX : Z * X ∈ hAB R := by
    have h0 := hAB_mul_mul blk_one hZ hX
    rwa [one_mul] at h0
  have hXY : X * Y ∈ hAB R := by
    have h0 := hAB_mul_mul hX hY blk_one
    rwa [mul_one] at h0
  have hYX : Y * X ∈ hAB R := by
    have h0 := hAB_mul_mul blk_one hY hX
    rwa [one_mul] at h0
  have hN : Z * X + X * Y - Y * X ∈ hAB R := (hAB R).sub_mem ((hAB R).add_mem hZX hXY) hYX
  have h1 : ∀ W : M4 R, Y * (Z * W) = 0 := by
    intro W
    rw [← mul_assoc, hAB_mul_hAB hY hZ, zero_mul]
  have h2 : Y * (X * Y) = 0 := by rw [← mul_assoc, hAB_mul_hAB hYX hY]
  have h3 : Z * (X * Y) = 0 := by rw [← mul_assoc, hAB_mul_hAB hZX hY]
  have e : (1 - Y) * ((1 + Z) * X) * (1 + Y) = X + (Z * X + X * Y - Y * X) := by
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, mul_assoc, h1, h2, h3, zero_mul, mul_zero]
    abel
  ext i j
  rw [Matrix.zero_apply]
  by_cases hij : lamW i = lamW j
  · exact hN i j (by rw [hij]; exact lt_irrefl _)
  · have hb := h i j hij
    rw [e, Matrix.add_apply, hX i j hij, zero_add] at hb
    exact hb

theorem UpperTheory.V.Ws.Bl.noCompl :
    ∀ (R Γ : Type) [CommRing R] [Group Γ] (r : Γ →* M4 R) (z : Γ → M4 R) (c : Γ) (Y : M4 R), IsUnit (2 : R) → (∀ g, IsBlock (r g)) → (∀ g, z g ∈ hAB R) → r c = eAB R → z c = 0 → Y ∈ hAB R →
          (∀ g, IsBlock ((1 - Y) * ((1 + z g) * r g) * (1 + Y))) → ∀ g, z g = 0 := by
  intro R Γ _ _ r z c Y h2u hrb hz hrc hzc hY hB g
  have hc := key (hrb c) (hz c) hY (hB c)
  rw [hzc, hrc, zero_mul, zero_add] at hc
  have hY0 : Y = 0 := by
    ext i j
    by_cases hij : lamW i < lamW j
    · have hd : (![-1, 1, -1, 1] : Fin 4 → R) i = 1 ∧ (![-1, 1, -1, 1] : Fin 4 → R) j = -1 := by
        fin_cases i <;> fin_cases j <;> simp [lamW] at hij ⊢
      have h2 : (2 : R) * Y i j = 0 := by
        have h0 := congrFun (congrFun hc i) j
        simp only [eAB, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply] at h0
        rw [hd.1, hd.2] at h0
        linear_combination h0
      exact h2u.mul_right_eq_zero.mp h2
    · exact hY i j hij
  have hg := key (hrb g) (hz g) hY (hB g)
  rw [hY0, mul_zero, zero_mul, sub_zero, add_zero] at hg
  calc z g = z g * (r g * r g⁻¹) := by rw [← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = 0 := by rw [← mul_assoc, hg, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.PlaceSet
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.placeSet :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (B : ValuationSubring Ω), (∀ p ∈ S, p.Prime) → l ∈ S → B.valuation (l : Ω) < 1 →
          ∃ (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (Av : S' → ValuationSubring Ω) (v0 : S'), ContainsAbove S' l ∧ (∀ v, IsPlaceOver (Av v) v.1) ∧ Av v0 = B ∧ ((l : ℕ) : 𝓞 ℚ) ∈ v0.1.asIdeal ∧
            ∀ K : Subgroup (G ℚ Ω), K.Normal → IsClosed (K : Set (G ℚ Ω)) → (∀ A, Raw.Away S A → Ine (F := ℚ) A ≤ K) → NS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ K := by
  intro Ω _ _ _ l hl S B hS hlS hB
  classical
  have hfin : Set.Finite {v : HeightOneSpectrum (𝓞 ℚ) | ∃ p ∈ S, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} := by
    have e : {v : HeightOneSpectrum (𝓞 ℚ) | ∃ p ∈ S, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} =
        ⋃ p ∈ (S : Set ℕ), {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 ℚ)}} := by
      ext v
      simp [Ideal.dvd_span_singleton]
    rw [e]
    refine S.finite_toSet.biUnion fun p hp => Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (hS p hp).ne_zero
  obtain ⟨h1, h2, h3, -⟩ := UpperTheory.V.Base.places ℚ Ω l B
  obtain ⟨w, hw⟩ := h1 fun h => (h2 h).2 hB
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := (h3 w hw).1 hB
  have hex : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ (v = w → A = B) := by
    intro v
    by_cases e : v = w
    · exact ⟨B, e ▸ hw, fun _ => rfl⟩
    · obtain ⟨A, hA⟩ := (exists_isPlaceOver Ω v : ∃ A : ValuationSubring Ω, IsPlaceOver A v)
      exact ⟨A, hA, fun h => absurd h e⟩
  choose f hf hf' using hex
  refine ⟨hfin.toFinset, fun v => f v.1, ⟨w, hfin.mem_toFinset.2 ⟨l, hlS, hlw⟩⟩,
    fun v hv => hfin.mem_toFinset.2 ⟨l, hlS, hv⟩, fun v => hf v.1, hf' w rfl, hlw, fun K hK hc hI => ?_⟩
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hc
  intro g hg
  simp only [Set.mem_iUnion] at hg
  obtain ⟨v, hv, A, hA, hg⟩ := hg
  refine hI A (fun p hp h => hv ?_) hg
  refine Finset.mem_coe.2 (hfin.mem_toFinset.2 ⟨p, hp, (hA ((p : ℕ) : 𝓞 ℚ)).1 ?_⟩)
  simpa using h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.PlusCard
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.plusCard :
    LocalFiniteness → LocalEulerChar → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (B : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (ρ : Representation (ZMod (l ^ r)) (Dec (F := ℚ) B) M), 0 < r → IsPlaceOver B v → ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ContAction ρ →
          ∀ P : Submodule (ZMod (l ^ r)) M, (∀ h, ∀ x ∈ P, ρ h x ∈ P) → (∃ s, Function.Bijective fun x => ρ s x - x) →
          ∃ L : Submodule (ZMod (l ^ r)) (H1 ρ), Nat.card P ≤ Nat.card L ∧ ∀ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) ∈ L → ∃ y, ∀ h, z.1 h - (ρ h y - y) ∈ P := by
  intro hFin hEul Ω _ _ _ l _ r M _ _ _ _ _ B v ρ hr hB hl hc P hP hs
  let ρP : Representation (ZMod (l ^ r)) (Dec (F := ℚ) B) P :=
    { toFun := fun h => (ρ h).restrict (fun x hx => hP h x hx)
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro a b
        ext x
        simp }
  have hρP : ∀ h (x : P), ((ρP h x : P) : M) = ρ h x := fun _ _ => rfl
  have hcP : ContAction ρP := by
    have h1 : Continuous fun p : Dec (F := ℚ) B × P => ρ p.1 (p.2 : M) :=
      hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact continuous_induced_rng.2 h1
  obtain ⟨hH0, hH1, hH2, -⟩ := hFin ℚ Ω l r P B ρP v hr hB hcP
  have hE := (hEul ℚ Ω l r P B ρP v hr hB hcP).1 hl
  have hdeg : 0 < locDeg v := by
    unfold locDeg
    exact Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hle : Nat.card P ≤ Nat.card (H1 ρP) := by
    rw [hE]
    have a0 : 0 < Nat.card (H0 ρP) := Nat.card_pos
    have a2 : 0 < Nat.card (H2 ρP) := Nat.card_pos
    calc Nat.card P ≤ Nat.card P ^ locDeg v := Nat.le_self_pow hdeg.ne' _
      _ ≤ Nat.card (H0 ρP) * Nat.card (H2 ρP) * Nat.card P ^ locDeg v :=
        Nat.le_mul_of_pos_left _ (Nat.mul_pos a0 a2)
  have hu : Continuous (P.subtype : P → M) := continuous_subtype_val
  have heq : ∀ (g : Dec (F := ℚ) B) (m : P), P.subtype (ρP g m) = ρ g (P.subtype m) := fun _ _ => rfl
  let φ := mapH1 ρP ρ P.subtype hu heq
  obtain ⟨s, hsb⟩ := hs
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    induction w using Submodule.Quotient.induction_on with
    | _ w =>
    rw [Submodule.Quotient.mk_eq_zero]
    have hw' : (φ (Submodule.Quotient.mk w)) = 0 := hw
    simp only [φ, mapH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.coe_subtype] at hw'
    rw [mem_coboundaries1] at hw'
    obtain ⟨m, hm⟩ := hw'
    have hm' : ∀ g, ((w.1 g : P) : M) = ρ g m - m := fun g => hm g
    have hmP : m ∈ P := by
      obtain ⟨q, hq⟩ : ∃ q : P, ρP s q - q = w.1 s := by
        have hinjP : Function.Injective fun q : P => ρP s q - q := by
          intro a b hab
          apply Subtype.ext
          apply hsb.1
          have := congrArg Subtype.val hab
          simpa [hρP] using this
        exact (Finite.injective_iff_surjective.1 hinjP) (w.1 s)
      have h1 : ρ s (q : M) - q = ρ s m - m := by
        have := congrArg Subtype.val hq
        simp only [AddSubgroupClass.coe_sub, hρP] at this
        rw [this, hm' s]
      have := hsb.1 h1
      rw [← this]
      exact q.2
    rw [Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    refine ⟨⟨m, hmP⟩, fun g => ?_⟩
    apply Subtype.ext
    rw [hm' g]
    rfl
  refine ⟨LinearMap.range φ, ?_, ?_⟩
  · calc Nat.card P ≤ Nat.card (H1 ρP) := hle
      _ = Nat.card (LinearMap.range φ) := Nat.card_congr (LinearEquiv.ofInjective φ hinj).toEquiv
  · intro z hz
    obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hz
    induction w using Submodule.Quotient.induction_on with
    | _ w =>
    simp only [φ, mapH1, Submodule.mapQ_apply] at hw
    rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hw
    obtain ⟨y, hy⟩ := hw
    refine ⟨-y, fun h => ?_⟩
    have h1 := hy h
    have h2 : ((cocycles1MapOfEquivariant ρP ρ P.subtype hu heq w : Z1 ρ) : _ → M) h = (w.1 h : M) := rfl
    simp only [Submodule.coe_sub, Pi.sub_apply, h2] at h1
    have h3 : z.1 h - (ρ h (-y) - -y) = (w.1 h : M) := by
      rw [map_neg]
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      abel
    rw [h3]
    exact (w.1 h).2
end

