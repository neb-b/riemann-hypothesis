module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.WMConjDiagonal

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.ContConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_sum {Γ A ι : Type} [TopologicalSpace Γ] [AddCommMonoid A] (s : Finset ι) (f : ι → Γ → A)
    (h : ∀ i, IsLocallyConstant (f i)) : IsLocallyConstant fun g => ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const (0 : A)
  | insert a s ha ih =>
    have e : (fun g => ∑ i ∈ insert a s, f i g) = f a + fun g => ∑ i ∈ s, f i g := by
      funext g
      simp [Finset.sum_insert ha]
    rw [e]
    exact (h a).add ih

theorem UpperTheory.V.Ws.Lab.contConj :
    ∀ (Γ R : Type) [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (r : Γ → M4 R) (p q : M4 R), (∀ i j, AdicCont I fun g => r g i j) →
      ∀ i j, AdicCont I fun g => (p * r g * q : M4 R) i j := by
  intro Γ R _ _ I r p q hr i j N
  have e : (fun g => (Ideal.Quotient.mk (I ^ N)) ((p * r g * q : M4 R) i j)) =
      fun g => ∑ k : Fin 4, ∑ m : Fin 4,
        (Ideal.Quotient.mk (I ^ N) (p i m) * Ideal.Quotient.mk (I ^ N) (r g m k)) * Ideal.Quotient.mk (I ^ N) (q k j) := by
    funext g
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, Finset.sum_mul, map_sum, map_mul]
  rw [e]
  refine lc_sum _ _ (fun k => ?_)
  refine lc_sum _ _ (fun m => ?_)
  exact (hr m k N).comp (fun x => (Ideal.Quotient.mk (I ^ N) (p i m) * x) * Ideal.Quotient.mk (I ^ N) (q k j))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.LowAdj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem low_mk {R : Type} [CommRing R] (x y z t : R) :
    IsLow (!![1, 0, 0, 0; x, 1, 0, 0; y + t * x, t, 1, 0; z, y, -x, 1] : M4 R) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  · intro i
    fin_cases i <;> simp
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢

private theorem low_adj {R : Type} [CommRing R] {m : M4 R} (h : IsLow m) : IsLow (adj m) := by
  refine ⟨sp_adj h.1, fun i => ?_, fun i j hij => ?_⟩
  · rw [adj_apply, h.2.1]
    fin_cases i <;> simp [sgn]
  · rw [adj_apply, h.2.2 _ _ (Fin.rev_lt_rev.2 hij), smul_zero]

private theorem up_of {R : Type} [CommRing R] {w : M4 R} (h : IsGSp 1 w) (h0 : IsUnit (w 0 0))
    (h1 : w 1 0 = 0) (h2 : w 2 0 = 0) (h3 : w 3 0 = 0) (h4 : w 2 1 = 0) : IsUp w := by
  have e := sp_adj_mul h
  have e1 := congrFun (congrFun e 1) 0
  have e2 := congrFun (congrFun e 2) 0
  simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four, h1, h2, h3] at e1 e2
  have a1 : w 3 2 = 0 := (h0.mul_left_eq_zero).1 e1
  have a2 : w 3 1 = 0 := (h0.mul_left_eq_zero).1 e2
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> assumption

theorem UpperTheory.V.Ws.Lab.luSp :
    ∀ (R : Type) [CommRing R] (u : M4 R), IsGSp 1 u → IsUnit (u 0 0) → IsUnit (u 0 0 * u 1 1 - u 0 1 * u 1 0) →
      ∃ n b : M4 R, IsLow n ∧ IsGSp 1 b ∧ IsUp b ∧ u = n * b := by
  intro R _ u hu h0 hD
  obtain ⟨ai, hai⟩ := h0.exists_right_inv
  obtain ⟨di, hdi⟩ := hD.exists_right_inv
  obtain ⟨x, hx⟩ : ∃ x : R, x = -(u 1 0 * ai) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : R, s = (u 2 1 * u 1 0 - u 2 0 * u 1 1) * di := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : R, t = (u 0 1 * u 2 0 - u 0 0 * u 2 1) * di := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : R, y = s - t * x := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : R, z = (-(y * u 1 0) + x * u 2 0 - u 3 0) * ai := ⟨_, rfl⟩
  have hm := low_mk x y z t
  refine ⟨_, _, low_adj hm, sp_mul hm.1 hu, ?_, ?_⟩
  · refine up_of (sp_mul hm.1 hu) ?_ ?_ ?_ ?_ ?_
    · simpa [Matrix.mul_apply, Fin.sum_univ_four] using h0
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination u 0 0 * hx + (-u 1 0) * hai
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination u 0 0 * hy + u 0 0 * hs + u 1 0 * ht + (-u 2 0) * hdi
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination u 0 0 * hz + (-(y * u 1 0) + x * u 2 0 - u 3 0) * hai
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination u 0 1 * hy + u 0 1 * hs + u 1 1 * ht + (-u 2 1) * hdi
  · rw [← Matrix.mul_assoc, sp_adj_mul hm.1, Matrix.one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.ParEig
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem two_by_two {R : Type} [CommRing R] [IsLocalRing R] {a b c e x y : R} (ha : IsUnit a) (he : IsUnit e)
    (hb : b ∈ maximalIdeal R) (h1 : a * x + b * y = 0) (h2 : c * x + e * y = 0) : x = 0 ∧ y = 0 := by
  obtain ⟨u, rfl⟩ := ha
  have hu : (↑u⁻¹ : R) * ↑u = 1 := Units.inv_mul u
  have hx : x = -(↑u⁻¹ * b * y) := by linear_combination (↑u⁻¹ : R) * h1 - x * hu
  have hy' : (e - c * ↑u⁻¹ * b) * y = 0 := by
    rw [hx] at h2
    linear_combination h2
  have hm : c * ↑u⁻¹ * b ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hb
  have hunit : IsUnit (e - c * ↑u⁻¹ * b) := by
    by_contra hn
    have h3 : e - c * ↑u⁻¹ * b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hn
    have h4 : e ∈ maximalIdeal R := by
      have := Ideal.add_mem _ h3 hm
      simpa using this
    exact ((IsLocalRing.mem_maximalIdeal _).1 h4) he
  have hy : y = 0 := hunit.mul_right_eq_zero.1 hy'
  refine ⟨?_, hy⟩
  rw [hx, hy]
  ring

private theorem mem_maxIdeal_of_mul_unit_mem {R : Type} [CommRing R] [IsLocalRing R] {z u : R} (hu : IsUnit u)
    (h : z * u ∈ maximalIdeal R) : z ∈ maximalIdeal R := by
  obtain ⟨w, rfl⟩ := hu
  have := Ideal.mul_mem_right (↑w⁻¹ : R) _ h
  simpa [mul_assoc] using this

theorem UpperTheory.V.Ws.Lab.parEig :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X v : M4 R) (d : Fin 4 → R), (∀ i j, i ≠ j → X i j ∈ maximalIdeal R) →
      (∀ i j, i ≠ j → IsUnit (X i i - X j j)) → Cg (maximalIdeal R) v 1 → X * v = v * Matrix.diagonal d → Par X → Par v := by
  intro R _ _ X v d hoff hdiag hv hXv hX
  have hunit : ∀ i, IsUnit (v i i) := fun i => unit_of_sub_mem isUnit_one (by simpa using hv i i)
  have hE : ∀ i j, ∑ k, X i k * v k j = v i j * d j := fun i j => by
    have := congrFun (congrFun hXv i) j
    rwa [Matrix.mul_apply, Matrix.mul_diagonal] at this
  have hd : ∀ j, X j j - d j ∈ maximalIdeal R := fun j => by
    apply mem_maxIdeal_of_mul_unit_mem (hunit j)
    have e := hE j j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at e
    have hs : (X j j - d j) * v j j = -∑ k ∈ Finset.univ.erase j, X j k * v k j := by
      linear_combination e
    rw [hs, Ideal.neg_mem_iff]
    exact Ideal.sum_mem _ fun k hk => Ideal.mul_mem_right _ _ (hoff j k (Finset.ne_of_mem_erase hk).symm)
  have z01 : X 0 1 = 0 := hX 0 1 (by simp [lamW])
  have z03 : X 0 3 = 0 := hX 0 3 (by simp [lamW])
  have z21 : X 2 1 = 0 := hX 2 1 (by simp [lamW])
  have z23 : X 2 3 = 0 := hX 2 3 (by simp [lamW])
  have key : ∀ j, (0 : Fin 4) ≠ j → (2 : Fin 4) ≠ j → v 0 j = 0 ∧ v 2 j = 0 := by
    intro j h0 h2
    have e0 := hE 0 j
    have e2 := hE 2 j
    rw [Fin.sum_univ_four] at e0 e2
    refine two_by_two (a := X 0 0 - d j) (b := X 0 2) (c := X 2 0) (e := X 2 2 - d j) ?_ ?_
      (hoff 0 2 (by decide)) ?_ ?_
    · refine unit_of_sub_mem (hdiag 0 j h0) ?_
      have : X 0 0 - d j - (X 0 0 - X j j) = X j j - d j := by ring
      rw [this]
      exact hd j
    · refine unit_of_sub_mem (hdiag 2 j h2) ?_
      have : X 2 2 - d j - (X 2 2 - X j j) = X j j - d j := by ring
      rw [this]
      exact hd j
    · linear_combination e0 - v 1 j * z01 - v 3 j * z03
    · linear_combination e2 - v 1 j * z21 - v 3 j * z23
  intro i j hij
  fin_cases i <;> fin_cases j <;> (try simp [lamW] at hij)
  all_goals first
    | exact (key 1 (by decide) (by decide)).1
    | exact (key 1 (by decide) (by decide)).2
    | exact (key 3 (by decide) (by decide)).1
    | exact (key 3 (by decide) (by decide)).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.ResFlag
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem resFlag_field {k : Type} [Field k] (u T : M4 k) (d : Fin 4 → k) (hu : IsGSp 1 u)
    (hT : IsUp T) (e : Matrix.diagonal d * u = u * T) (hd : ∀ i j, lamW i ≠ lamW j → d i - T j j ≠ 0) :
    u 1 0 = 0 ∧ u 3 0 = 0 ∧ (u 0 0 ≠ 0 ∨ u 2 0 ≠ 0) ∧
      (u 0 0 ≠ 0 → u 0 0 * u 1 1 - u 0 1 * u 1 0 ≠ 0 ∧ u 0 0 * u 2 1 - u 0 1 * u 2 0 = 0) := by
  have t10 : T 1 0 = 0 := hT _ _ (by decide)
  have t20 : T 2 0 = 0 := hT _ _ (by decide)
  have t30 : T 3 0 = 0 := hT _ _ (by decide)
  have t21 : T 2 1 = 0 := hT _ _ (by decide)
  have t31 : T 3 1 = 0 := hT _ _ (by decide)
  have c0 : ∀ i, (d i - T 0 0) * u i 0 = 0 := fun i => by
    have := congrFun (congrFun e i) 0
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_four, t10, t20, t30] at this
    linear_combination this
  have c1 : ∀ i, (d i - T 1 1) * u i 1 = u i 0 * T 0 1 := fun i => by
    have := congrFun (congrFun e i) 1
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_four, t21, t31] at this
    linear_combination this
  have h10 : u 1 0 = 0 := (mul_eq_zero.1 (c0 1)).resolve_left (hd _ _ (by decide))
  have h30 : u 3 0 = 0 := (mul_eq_zero.1 (c0 3)).resolve_left (hd _ _ (by decide))
  have s := sp_adj_mul hu
  have s00 := congrFun (congrFun s 0) 0
  have s10 := congrFun (congrFun s 1) 0
  have s11 := congrFun (congrFun s 1) 1
  have s31 := congrFun (congrFun s 3) 1
  rw [Matrix.mul_apply, Fin.sum_univ_four] at s00 s10 s11 s31
  rw [Matrix.one_apply_eq] at s00 s11
  rw [Matrix.one_apply_ne (by decide)] at s10 s31
  have a30 : adj u 3 0 = - u 3 0 := by simp [adj_apply, sgn, Fin.rev]
  have a31 : adj u 3 1 = - u 2 0 := by simp [adj_apply, sgn, Fin.rev]
  have a32 : adj u 3 2 = u 1 0 := by simp [adj_apply, sgn, Fin.rev]
  have a33 : adj u 3 3 = u 0 0 := by simp [adj_apply, sgn, Fin.rev]
  rw [a30, a31, a32, a33] at s31
  refine ⟨h10, h30, ?_, fun h00 => ?_⟩
  · by_contra hn
    push Not at hn
    rw [hn.1, hn.2, h10, h30] at s00
    simp at s00
  · have hA : d 0 - T 1 1 ≠ 0 := hd _ _ (by decide)
    have hB : d 2 - T 1 1 ≠ 0 := hd _ _ (by decide)
    have key : u 0 0 * u 2 1 - u 0 1 * u 2 0 = 0 := by
      apply mul_left_cancel₀ (mul_ne_zero hA hB)
      linear_combination (d 0 - T 1 1) * u 0 0 * c1 2 - (d 2 - T 1 1) * u 2 0 * c1 0
        + u 2 0 * T 0 1 * c0 0 - u 0 0 * T 0 1 * c0 2
    refine ⟨fun hn => ?_, key⟩
    rw [h10, mul_zero, sub_zero] at hn
    have h11 : u 1 1 = 0 := (mul_eq_zero.1 hn).resolve_left h00
    rw [h10, h30, h11] at s31
    have h31 : u 3 1 = 0 := by
      apply mul_left_cancel₀ h00
      linear_combination s31
    rw [h10, h30] at s10
    rw [h11, h31] at s11
    apply h00
    linear_combination u 0 1 * s10 - u 0 0 * s11 + adj u 1 2 * key

theorem UpperTheory.V.Ws.Lab.resFlag :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X u : M4 R) (d d' : Fin 4 → R), Cg (maximalIdeal R) X (Matrix.diagonal d) → IsGSp 1 u →
      IsUp (adj u * X * u) → (∀ i, (adj u * X * u : M4 R) i i - d' i ∈ maximalIdeal R) → (∀ i j, lamW i ≠ lamW j → IsUnit (d i - d' j)) →
      u 1 0 ∈ maximalIdeal R ∧ u 3 0 ∈ maximalIdeal R ∧ (IsUnit (u 0 0) ∨ IsUnit (u 2 0)) ∧
        (IsUnit (u 0 0) → IsUnit (u 0 0 * u 1 1 - u 0 1 * u 1 0) ∧ u 0 0 * u 2 1 - u 0 1 * u 2 0 ∈ maximalIdeal R) := by
  intro R _ _ X u d d' hX hu hUp hdi hsep
  have hX' : X.map (residue R) = Matrix.diagonal fun i => residue R (d i) := by
    ext i j
    have := (residue_eq_zero_iff _).2 (hX i j)
    rw [map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this]
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.diagonal_apply_ne _ e]
  have hu' : IsGSp 1 (u.map (residue R)) := by simpa using gsp_map (residue R) hu
  have e : X * u = u * (adj u * X * u) := by
    rw [← mul_assoc, ← mul_assoc, sp_mul_adj hu, one_mul]
  have e' := congrArg (fun M : M4 R => M.map (residue R)) e
  beta_reduce at e'
  rw [Matrix.map_mul, Matrix.map_mul (L := u), hX'] at e'
  have H := resFlag_field (u.map (residue R)) ((adj u * X * u).map (residue R)) _ hu'
    (fun i j h => by rw [Matrix.map_apply, hUp i j h, map_zero]) e' (fun i j h => by
      have h1 := (residue_eq_zero_iff _).2 (hdi j)
      rw [map_sub, sub_eq_zero] at h1
      rw [Matrix.map_apply, h1, ← map_sub]
      exact ((hsep i j h).map _).ne_zero)
  simp only [Matrix.map_apply, ← map_mul, ← map_sub, residue_eq_zero_iff, Ne] at H
  simpa only [notMem_maximalIdeal] using H
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.StarConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Lab

private theorem span_entry {K n Γ : Type} [Field K] [Fintype n] [DecidableEq n] (f : Γ → Matrix n n K) (a m : Matrix n n K)
    (h : a * m = 1) (hf : Submodule.span K (Set.range f) = ⊤) (i j : n) : ∃ g, (a * f g * m) i j ≠ 0 := by
  classical
  by_contra hall
  push_neg at hall
  let L : Matrix n n K →ₗ[K] K :=
    { toFun := fun X => (a * X * m) i j
      map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hle : Submodule.span K (Set.range f) ≤ LinearMap.ker L :=
    Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hall g)
  rw [hf] at hle
  have h0 := hle (Submodule.mem_top (x := m * Matrix.single i j (1 : K) * a))
  rw [LinearMap.mem_ker] at h0
  have e : L (m * Matrix.single i j (1 : K) * a) = Matrix.single i j (1 : K) i j := by
    change (a * (m * Matrix.single i j (1 : K) * a) * m) i j = _
    have : a * (m * Matrix.single i j (1 : K) * a) * m = (a * m) * Matrix.single i j (1 : K) * (a * m) := by
      simp only [Matrix.mul_assoc]
    rw [this, h, Matrix.one_mul, Matrix.mul_one]
  rw [e] at h0
  simp at h0

private theorem sub_mul_par {K : Type} [CommRing K] (X : M4 K) {Y : M4 K} (hY : Par Y) :
    (X * Y).submatrix ixB ixB = X.submatrix ixB ixB * Y.submatrix ixB ixB := by
  have h01 := hY 0 1 (by decide)
  have h03 := hY 0 3 (by decide)
  have h21 := hY 2 1 (by decide)
  have h23 := hY 2 3 (by decide)
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [ixB, h01, h03, h21, h23]

private theorem block_mul {K : Type} [CommRing K] {X Y : M4 K} (hX : IsBlock X) (hY : IsBlock Y) : IsBlock (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : lamW i = lamW k
  · rw [hY k j (by omega), mul_zero]
  · rw [hX i k hk, zero_mul]

private def pA (K : Type) [CommRing K] : M4 K := Matrix.diagonal fun i => (lamW i : K)

private theorem lam_cases (i : Fin 4) : lamW i = 0 ∨ lamW i = 1 := by revert i; decide

private theorem add_pA_mul_sub_mul_pA_apply {K : Type} [CommRing K] (X : M4 K) (i j : Fin 4) :
    (X + pA K * X - X * pA K) i j = X i j * (1 + (lamW i : K) - (lamW j : K)) := by
  simp [pA, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

private theorem par_of_isBlock {K : Type} [CommRing K] {X : M4 K} (hX : IsBlock X) : Par X :=
  fun i j h => hX i j h.ne'

private theorem block_part {K : Type} [CommRing K] {X : M4 K} (hX : Par X) : IsBlock (X + pA K * X - X * pA K) := by
  intro i j hij
  rw [add_pA_mul_sub_mul_pA_apply]
  rcases lam_cases i with hi | hi <;> rcases lam_cases j with hj | hj
  · exact absurd (hi.trans hj.symm) hij
  · simp [hi, hj]
  · rw [hX i j (by rw [hi, hj]; norm_num)]
    simp
  · exact absurd (hi.trans hj.symm) hij

private theorem split_of_block {K : Type} [CommRing K] {a m : M4 K} (h : a * m = 1) (h' : m * a = 1) (ha : Par a) (hm : Par m) :
    ∃ Y : M4 K, (∀ i j, ¬ lamW i < lamW j → Y i j = 0) ∧ ∀ X, IsBlock (a * X * m) → IsBlock ((1 - Y) * X * (1 + Y)) := by
  let Ba : M4 K := a + pA K * a - a * pA K
  let Bm : M4 K := m + pA K * m - m * pA K
  have hBa : IsBlock Ba := block_part ha
  have hBm : IsBlock Bm := block_part hm
  have hsum : m * Ba + Bm * a = 1 + 1 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Ba, Bm, add_pA_mul_sub_mul_pA_apply]
    rw [← Finset.sum_add_distrib]
    have hma : ∑ k, m i k * a k j = (1 : M4 K) i j := by
      rw [← Matrix.mul_apply, h']
    have : ∑ k, (m i k * (a k j * (1 + (lamW k : K) - (lamW j : K))) +
        m i k * (1 + (lamW i : K) - (lamW k : K)) * a k j) =
        (2 + (lamW i : K) - (lamW j : K)) * ∑ k, m i k * a k j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [this, hma]
    by_cases hij : i = j
    · subst hij
      simp
      ring
    · simp [Matrix.one_apply_ne hij]
  let Y : M4 K := m * Ba - 1
  have h1Y : 1 + Y = m * Ba := by simp [Y]
  have h2Y : 1 - Y = Bm * a := by
    calc 1 - Y = (1 + 1) - m * Ba := by simp only [Y]; abel
      _ = (m * Ba + Bm * a) - m * Ba := by rw [hsum]
      _ = Bm * a := by abel
  refine ⟨Y, ?_, ?_⟩
  · intro i j hij
    simp only [Y, Matrix.sub_apply]
    rcases lt_or_eq_of_le (not_lt.mp hij) with hlt | heq
    · rw [Par.mul hm (par_of_isBlock hBa) i j hlt, Matrix.one_apply_ne (by rintro rfl; exact lt_irrefl _ hlt)]
      simp
    · have : (m * Ba) i j = (m * a) i j := by
        simp only [Matrix.mul_apply, Ba, add_pA_mul_sub_mul_pA_apply]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rcases lt_trichotomy (lamW k) (lamW j) with hk | hk | hk
        · rw [hm i k (by rw [← heq]; exact hk)]
          simp
        · rw [hk]
          simp
        · rw [ha k j hk]
          simp
      rw [this, h']
      simp
  · intro X hX
    rw [h2Y, h1Y]
    have e : Bm * a * X * (m * Ba) = Bm * (a * X * m) * Ba := by
      simp only [Matrix.mul_assoc]
    rw [e]
    exact block_mul (block_mul hBm hX) hBa

end UpperTheory.V.Ws.Lab

open UpperTheory.V.Ws.Lab in
theorem UpperTheory.V.Ws.Lab.starConj :
    ∀ (K : Type) [Field K] (Γ : Type) [Group Γ] (r r' : Γ →* M4 K) (m : M4 K), IsGSp 1 m → (∀ g, r' g = adj m * r g * m) →
      ((∀ g, Par (r g)) → Par m) → Star r → StarE r' := by
  intro K _ Γ _ r r' m hm hr' hpar hstar
  have hma : adj m * m = 1 := sp_adj_mul hm
  have hmm : m * adj m = 1 := sp_mul_adj hm
  rcases hstar with hirr | hbe
  · obtain ⟨g1, hg1⟩ := span_entry (⇑r) (adj m) m hma hirr 0 2
    obtain ⟨g2, hg2⟩ := span_entry (⇑r) (adj m) m hma hirr 2 0
    obtain ⟨g3, hg3⟩ := span_entry (⇑r) (adj m) m hma hirr 1 2
    refine ⟨⟨g1, 0, 2, by decide, by rw [hr']; exact hg1⟩,
      ⟨g2, 2, 0, by decide, by rw [hr']; exact hg2⟩,
      Or.inl ⟨g3, 1, 2, by decide, by rw [hr']; exact hg3⟩⟩
  · obtain ⟨hpr, hspan, hno⟩ := hbe
    have hmPar : Par m := hpar hpr
    have hadjPar : Par (adj m) := Par.adj hmPar
    have hsub : ∀ g, (r' g).submatrix ixB ixB =
        (adj m).submatrix ixB ixB * (r g).submatrix ixB ixB * m.submatrix ixB ixB := by
      intro g
      rw [hr', sub_mul_par _ hmPar, sub_mul_par _ (hpr g)]
    have hi0 : (![1, 3] : Fin 2 → Fin 4) 0 = 1 := rfl
    have hi1 : (![1, 3] : Fin 2 → Fin 4) 1 = 3 := rfl
    have hinv2 : (adj m).submatrix ixB ixB * m.submatrix ixB ixB = 1 := by
      rw [← sub_mul_par _ hmPar, hma]
      ext p q
      fin_cases p <;> fin_cases q <;> simp [ixB, hi0, hi1, Matrix.one_apply]
    obtain ⟨g1, hg1⟩ := span_entry (fun g => (r g).submatrix ixB ixB) _ _ hinv2 hspan 0 1
    obtain ⟨g2, hg2⟩ := span_entry (fun g => (r g).submatrix ixB ixB) _ _ hinv2 hspan 1 0
    rw [← hsub] at hg1 hg2
    refine ⟨⟨g1, 1, 3, by decide, by simpa [ixB, hi0, hi1] using hg1⟩,
      ⟨g2, 3, 1, by decide, by simpa [ixB, hi0, hi1] using hg2⟩, ?_⟩
    by_contra hnot
    have key : ∀ i j : Fin 4, lamW i < lamW j → (wt i j = wBe ∨ wt i j = -wAl ∨ wt i j = -wTh) := by
      decide
    have hblock : ∀ g, IsBlock (adj m * r g * m) := by
      intro g i j hij
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · by_contra hne
        have hne' : r' g i j ≠ 0 := by rw [hr']; exact hne
        rcases key i j hlt with hw | hw | hw
        · exact hnot (Or.inl ⟨g, i, j, hw, hne'⟩)
        · exact hnot (Or.inr (Or.inl ⟨g, i, j, hw, hne'⟩))
        · exact hnot (Or.inr (Or.inr ⟨g, i, j, hw, hne'⟩))
      · exact Par.mul (Par.mul hadjPar (hpr g)) hmPar i j hgt
    obtain ⟨Y, hYs, hYb⟩ := split_of_block hma hmm hadjPar hmPar
    exact hno ⟨Y, hYs, fun g => hYb (r g) (hblock g)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.UpConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_mul {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k < i
  · rw [hX i k hk, zero_mul]
  · rw [hY k j (lt_of_lt_of_le h (not_lt.1 hk)), mul_zero]

private theorem up_mul_diag {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) :
    (X * Y : M4 R) i i = X i i * Y i i := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hX i k h, zero_mul]
    · rw [hY k i h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

private theorem up_adj {R : Type} [CommRing R] {X : M4 R} (hX : IsUp X) : IsUp (adj X) := by
  intro i j h
  rw [adj_apply, hX _ _ (Fin.rev_lt_rev.2 h), smul_zero]

theorem UpperTheory.V.Ws.Lab.upConj :
    ∀ (R : Type) [CommRing R] (b T : M4 R), IsGSp 1 b → IsUp b → IsUp T → IsUp (b * T * adj b) ∧ ∀ i, (b * T * adj b : M4 R) i i = T i i := by
  intro R _ b T hb hbu hT
  have hadj := up_adj hbu
  refine ⟨up_mul (up_mul hbu hT) hadj, fun i => ?_⟩
  have h1 : b i i * adj b i i = 1 := by
    have := congrFun (congrFun (sp_mul_adj hb) i) i
    rw [up_mul_diag hbu hadj] at this
    simpa using this
  rw [up_mul_diag (up_mul hbu hT) hadj, up_mul_diag hbu hT]
  linear_combination (T i i) * h1
end

