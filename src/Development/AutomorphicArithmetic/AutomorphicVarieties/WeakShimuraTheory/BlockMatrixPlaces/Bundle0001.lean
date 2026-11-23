module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.AdjointBlockSubmatrixEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

namespace UpperTheory.V.Ws.Bl

private def blockAdjointFin2 (R : Type) [CommRing R] : Matrix (Fin 2) (Fin 2) R →ₗ[R] Matrix (Fin 2) (Fin 2) R where
  toFun Y := Matrix.of fun a b => (sgn (ixB a) * sgn (ixB b)) • Y b.rev a.rev
  map_add' X Y := by ext a b; simp only [Matrix.of_apply, Matrix.add_apply, smul_add]
  map_smul' c X := by
    ext a b
    simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
    rw [smul_comm]

private theorem adjoint_block_submatrix_eq {R : Type} [CommRing R] (X : M4 R) :
    blockAdjointFin2 R (X.submatrix ixA ixA) = (adj X).submatrix ixB ixB := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

private theorem adjoint_block_surjective {R : Type} [CommRing R] : Function.Surjective (blockAdjointFin2 R) := by
  intro Y
  refine ⟨blockAdjointFin2 R Y, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockAdjointFin2, ixB, sgn]

end UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.spanB :
    ∀ (R Γ : Type) [CommRing R] [Group Γ] (r : Γ →* M4 R), BG r → Submodule.span R (Set.range fun g => (r g).submatrix ixA ixA) = ⊤ → Submodule.span R (Set.range fun g => (r g).submatrix ixB ixB) = ⊤ := by
  intro R Γ _ _ r hr hA
  have hadj : ∀ g, (adj (r g)).submatrix ixB ixB ∈ Submodule.span R (Set.range fun g => (r g).submatrix ixB ixB) := by
    intro g
    obtain ⟨ν, hν⟩ := hr.gsp g
    have hinv : r g * r g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [(grp R).2.2.2.2.2.2.1 ν _ _ hν hinv]
    have hs : (ν • r g⁻¹).submatrix ixB ixB = ν • (r g⁻¹).submatrix ixB ixB := rfl
    rw [hs]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹, rfl⟩)
  rw [eq_top_iff]
  calc (⊤ : Submodule R (Matrix (Fin 2) (Fin 2) R))
        = Submodule.map (blockAdjointFin2 R) ⊤ := by
          rw [Submodule.map_top, LinearMap.range_eq_top.mpr adjoint_block_surjective]
    _ = Submodule.map (blockAdjointFin2 R) (Submodule.span R (Set.range fun g => (r g).submatrix ixA ixA)) := by rw [hA]
    _ = Submodule.span R (blockAdjointFin2 R '' Set.range fun g => (r g).submatrix ixA ixA) := Submodule.map_span _ _
    _ ≤ _ := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      rw [adjoint_block_submatrix_eq]
      exact hadj g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.CardP
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.cardP :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (P : Submodule A T), (∀ (a : A) (x : T), a ≠ 0 → a • x ∈ P → x ∈ P) → P ≠ ⊥ →
          ∀ n, Finite (T ⧸ lev A T n) ∧ n ≤ Nat.card (P.map (lev A T n).mkQ) := by
  intro A _ _ _ _ T _ _ _ _ P hsat hP n
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hm : maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hL : ∀ (k : ℕ) (z : T), z ∈ lev A T k ↔ ∃ t, ϖ ^ k • t = z := by
    intro k z
    show z ∈ maximalIdeal A ^ k • (⊤ : Submodule A T) ↔ _
    rw [hm, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hfin : ∀ k, Finite (T ⧸ lev A T k) := by
    intro k
    have h1 : (maximalIdeal A).FG := IsNoetherian.noetherian _
    haveI : Finite (A ⧸ maximalIdeal A) := (inferInstance : Finite (ResidueField A))
    haveI := Ideal.finite_quotient_pow h1 k
    haveI : Finite (T ⧸ (⊤ : Submodule A T)) := inferInstance
    exact Submodule.finite_quotient_smul _ (Module.finite_def.mp inferInstance)
  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hx : ∃ x ∈ P, x ∉ lev A T 1 := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ k : ℕ, ∀ z ∈ P, z ∈ lev A T k := by
      intro k
      induction k with
      | zero =>
        intro z _
        exact (hL 0 z).mpr ⟨z, by simp⟩
      | succ k ih =>
        intro z hz
        obtain ⟨t, rfl⟩ := (hL 1 z).mp (hcon z hz)
        have htP : t ∈ P := hsat _ _ (pow_ne_zero 1 hϖ0) hz
        obtain ⟨s, rfl⟩ := (hL k t).mp (ih t htP)
        exact (hL (k + 1) _).mpr ⟨s, by rw [smul_smul, ← pow_add, add_comm 1 k]⟩
    have hmem : y ∈ (⨅ i : ℕ, maximalIdeal A ^ i • (⊤ : Submodule A T)) :=
      Submodule.mem_iInf _ |>.mpr (fun i => hall i y hyP)
    rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top] at hmem
    exact hy0 ((Submodule.mem_bot A).mp hmem)
  obtain ⟨x, hxP, hx1⟩ := hx
  refine ⟨hfin n, ?_⟩
  haveI := hfin n
  have key : ∀ i j : ℕ, i < j → j < n → ϖ ^ i • x - ϖ ^ j • x ∉ lev A T n := by
    intro i j hij hjn hmem
    obtain ⟨s, hs⟩ := (hL n _).mp hmem
    have e1 : ϖ ^ i • (ϖ ^ (n - i) • s) = ϖ ^ i • (x - ϖ ^ (j - i) • x) := by
      rw [smul_smul, ← pow_add, Nat.add_sub_cancel' (by omega), hs, smul_sub, smul_smul,
        ← pow_add, Nat.add_sub_cancel' hij.le]
    have e2 : ϖ ^ (n - i) • s = x - ϖ ^ (j - i) • x :=
      smul_right_injective T (pow_ne_zero i hϖ0) e1
    apply hx1
    rw [hL 1]
    refine ⟨ϖ ^ (n - i - 1) • s + ϖ ^ (j - i - 1) • x, ?_⟩
    rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add,
      Nat.add_sub_cancel' (by omega : 1 ≤ n - i), Nat.add_sub_cancel' (by omega : 1 ≤ j - i),
      e2, sub_add_cancel]
  let f : Fin n → P.map (lev A T n).mkQ := fun i =>
    ⟨(lev A T n).mkQ (ϖ ^ (i : ℕ) • x), Submodule.mem_map_of_mem (P.smul_mem _ hxP)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h' : (lev A T n).mkQ (ϖ ^ (i : ℕ) • x) = (lev A T n).mkQ (ϖ ^ (j : ℕ) • x) :=
      congrArg Subtype.val hij
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h'
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact absurd h' (key _ _ h j.2)
    · exact Fin.ext h
    · have h'' := (lev A T n).neg_mem h'
      rw [neg_sub] at h''
      exact absurd h'' (key _ _ h i.2)
  calc n = Nat.card (Fin n) := by simp
    _ ≤ _ := Nat.card_le_card_of_injective f hf
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.CcNeg
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem eq_diag_of_square_eq_one_of_near_sign {R : Type} [CommRing R] [IsLocalRing R] (s a b c d : R)
    (hs : s * s = 1) (h2 : IsUnit (2 : R)) (ha : a - s ∈ maximalIdeal R)
    (hd : d - s ∈ maximalIdeal R) (e1 : a * a + b * c = 1) (e2 : a * b + b * d = 0)
    (e3 : c * a + d * c = 0) (e4 : c * b + d * d = 1) : a = s ∧ b = 0 ∧ c = 0 ∧ d = s := by
  have hunit : ∀ u : R, u - 2 * s ∈ maximalIdeal R → IsUnit u := by
    intro u hu
    have h2s : IsUnit (2 * s) := h2.mul ⟨⟨s, s, hs, hs⟩, rfl⟩
    by_contra hnu
    have hum : u ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h2m : 2 * s ∈ maximalIdeal R := by
      have := (maximalIdeal R).sub_mem hum hu
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).mp h2m h2s
  have hsum : IsUnit (a + d) := hunit _ (by
    have e : a + d - 2 * s = (a - s) + (d - s) := by ring
    rw [e]
    exact (maximalIdeal R).add_mem ha hd)
  have hb : b = 0 := (hsum.mul_left_eq_zero).mp (by linear_combination e2)
  have hc : c = 0 := (hsum.mul_left_eq_zero).mp (by linear_combination e3)
  subst hb hc
  have hpa : IsUnit (a + s) := hunit _ (by
    have e : a + s - 2 * s = a - s := by ring
    rw [e]
    exact ha)
  have hpd : IsUnit (d + s) := hunit _ (by
    have e : d + s - 2 * s = d - s := by ring
    rw [e]
    exact hd)
  refine ⟨?_, rfl, rfl, ?_⟩
  · have h : (a - s) * (a + s) = 0 := by linear_combination e1 - hs
    exact sub_eq_zero.mp ((hpa.mul_left_eq_zero).mp h)
  · have h : (d - s) * (d + s) = 0 := by linear_combination e4 - hs
    exact sub_eq_zero.mp ((hpd.mul_left_eq_zero).mp h)

theorem UpperTheory.V.Ws.Bl.ccNeg :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : M4 R), IsUnit (2 : R) → IsBlock X → X * X = 1 → (∀ i j, X i j - eAB R i j ∈ maximalIdeal R) → X = eAB R := by
  intro R _ _ X h2 hB hX hm
  have sq : ∀ i j, ∑ k, X i k * X k j = (1 : M4 R) i j := fun i j => by
    rw [← Matrix.mul_apply, hX]
  have hm' : ∀ i, X i i - ![-1, 1, -1, 1] i ∈ maximalIdeal R := fun i => by
    simpa [eAB] using hm i i
  have z01 : X 0 1 = 0 := hB 0 1 (by simp [lamW])
  have z03 : X 0 3 = 0 := hB 0 3 (by simp [lamW])
  have z10 : X 1 0 = 0 := hB 1 0 (by simp [lamW])
  have z12 : X 1 2 = 0 := hB 1 2 (by simp [lamW])
  have z21 : X 2 1 = 0 := hB 2 1 (by simp [lamW])
  have z23 : X 2 3 = 0 := hB 2 3 (by simp [lamW])
  have z30 : X 3 0 = 0 := hB 3 0 (by simp [lamW])
  have z32 : X 3 2 = 0 := hB 3 2 (by simp [lamW])
  have q : ∀ i j, (∑ k, X i k * X k j) = X i 0 * X 0 j + X i 1 * X 1 j + X i 2 * X 2 j + X i 3 * X 3 j :=
    fun i j => Fin.sum_univ_four _
  obtain ⟨a0, b0, c0, d0⟩ := eq_diag_of_square_eq_one_of_near_sign (-1) (X 0 0) (X 0 2) (X 2 0) (X 2 2) (by ring) h2
    (by simpa using hm' 0) (by simpa using hm' 2)
    (by have h := sq 0 0; rw [q] at h; simp [z01, z03, z10, z30] at h; linear_combination h)
    (by have h := sq 0 2; rw [q] at h; simp [z01, z03, z12, z32] at h; linear_combination h)
    (by have h := sq 2 0; rw [q] at h; simp [z21, z23, z10, z30] at h; linear_combination h)
    (by have h := sq 2 2; rw [q] at h; simp [z21, z23, z12, z32] at h; linear_combination h)
  obtain ⟨a1, b1, c1, d1⟩ := eq_diag_of_square_eq_one_of_near_sign 1 (X 1 1) (X 1 3) (X 3 1) (X 3 3) (by ring) h2
    (by simpa using hm' 1) (by simpa using hm' 3)
    (by have h := sq 1 1; rw [q] at h; simp [z10, z12, z01, z21] at h; linear_combination h)
    (by have h := sq 1 3; rw [q] at h; simp [z10, z12, z03, z23] at h; linear_combination h)
    (by have h := sq 3 1; rw [q] at h; simp [z30, z32, z01, z21] at h; linear_combination h)
    (by have h := sq 3 3; rw [q] at h; simp [z30, z32, z03, z23] at h; linear_combination h)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eAB, z01, z03, z10, z12, z21, z23, z30, z32, a0, b0, c0, d0, a1, b1, c1, d1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.DivStep
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem mem_lev_iff {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {T : Type} [AddCommGroup T]
    [Module A T] {t : A} (ht : Irreducible t) (n : ℕ) (x : T) : x ∈ lev A T n ↔ ∃ w, t ^ n • w = x := by
  have hm : maximalIdeal A = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht
  show x ∈ maximalIdeal A ^ n • (⊤ : Submodule A T) ↔ _
  rw [hm, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

private theorem mem_of_bij {A : Type} [CommRing A] {T : Type} [AddCommGroup T] [Module A T] [Module.Finite A T]
    (f : T →ₗ[A] T) (hf : Function.Surjective f) (Q : Submodule A T) (hQ : Q ≤ Q.comap f) {y : T} (hy : f y ∈ Q) :
    y ∈ Q := by
  let g := Q.mapQ Q f hQ
  have hs : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨w, rfl⟩ := hf x
    exact ⟨Q.mkQ w, by simp [g]⟩
  have hi := OrzechProperty.injective_of_surjective_endomorphism g hs
  have h0 : g (Q.mkQ y) = g 0 := by
    simp only [g, Submodule.mkQ_apply, Submodule.mapQ_apply, map_zero]
    exact (Submodule.Quotient.mk_eq_zero Q).2 hy
  have h1 := hi h0
  simpa using h1

theorem UpperTheory.V.Ws.Bl.divStep :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), Lat ρ H P → ∀ t : A, Irreducible t → ∀ n, ∀ z ∈ Zn ρ c N H P (n + 1), ¬ Prim z →
          ∃ z' ∈ Zn ρ c N H P n, ∀ g x, (lev A T n).mkQ x = z' g → (lev A T (n + 1)).mkQ (t • x) = z g := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hL t ht n z hz hnp
  obtain ⟨y, hzy⟩ := hz
  have ht0 : t ≠ 0 := ht.ne_zero
  have hinjt : Function.Injective (fun x : T => t • x) := smul_right_injective T ht0
  have hlev := fun k x => mem_lev_iff (T := T) ht k x
  have hφ : lev A T n ≤ (lev A T (n + 1)).comap (t • LinearMap.id) := by
    intro x hx
    obtain ⟨w, rfl⟩ := (hlev n x).1 hx
    rw [Submodule.mem_comap]
    refine (hlev (n + 1) _).2 ⟨w, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, pow_succ', mul_smul]
  let φ := (lev A T n).mapQ (lev A T (n + 1)) (t • LinearMap.id) hφ
  have hφmk : ∀ x, φ ((lev A T n).mkQ x) = (lev A T (n + 1)).mkQ (t • x) := fun x => rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    rw [hφmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ha
    obtain ⟨w, hw⟩ := (hlev (n + 1) _).1 ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine (hlev n x).2 ⟨w, hinjt ?_⟩
    simp only
    rw [← hw, pow_succ', mul_smul]
  have hφP : ∀ a, φ a ∈ Submodule.map (lev A T (n + 1)).mkQ P →
      a ∈ Submodule.map (lev A T n).mkQ P := by
    intro a ha
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    obtain ⟨q, hq, hqe⟩ := Submodule.mem_map.1 ha
    rw [hφmk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hqe
    obtain ⟨v, hv⟩ := (hlev (n + 1) _).1 hqe
    have hq' : t • (x + t ^ n • v) ∈ P := by
      have e : t • (x + t ^ n • v) = q := by
        rw [smul_add, ← mul_smul, ← pow_succ', hv]
        abel
      rw [e]
      exact hq
    have hxP := hL.sat t _ ht0 hq'
    refine Submodule.mem_map.2 ⟨x + t ^ n • v, hxP, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact (hlev n _).2 ⟨v, by abel⟩
  have hφρ : ∀ g a, φ (modRep ρ n g a) = modRep ρ (n + 1) g (φ a) := by
    intro g a
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    rw [modRep_mk, hφmk, hφmk, modRep_mk, LinearMap.map_smul (ρ g) t x]
  have hz1 : ∀ g, z g ∈ Submodule.map (lev A T (n + 1)).mkQ (lev A T 1) := by
    intro g
    by_contra hc
    exact hnp ⟨g, hc⟩
  have hrange : ∀ g, ∃ a, φ a = z g := by
    intro g
    obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 (hz1 g)
    obtain ⟨w, rfl⟩ := (hlev 1 u).1 hu
    refine ⟨(lev A T n).mkQ w, ?_⟩
    rw [hφmk, ← hue, pow_one]
  choose z' hz' using hrange
  obtain ⟨s, hsH, hsb⟩ := hL.fr
  obtain ⟨y0, rfl⟩ := (lev A T (n + 1)).mkQ_surjective y
  have hle1 : lev A T (n + 1) ≤ lev A T 1 :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
  have hy0 : y0 ∈ P ⊔ lev A T 1 := by
    let f : T →ₗ[A] T := ρ s - LinearMap.id
    have hfs : Function.Surjective f := hsb.2
    apply mem_of_bij f hfs
    · intro x hx
      rw [Submodule.mem_comap]
      show ρ s x - x ∈ _
      apply Submodule.sub_mem _ _ hx
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
      refine Submodule.mem_sup.2 ⟨ρ s p, hL.stab s hsH p hp, ρ s q, ?_, (map_add _ _ _).symm⟩
      obtain ⟨w, rfl⟩ := (hlev 1 q).1 hq
      exact (hlev 1 _).2 ⟨ρ s w, (map_smul _ _ _).symm⟩
    · show ρ s y0 - y0 ∈ _
      have hloc : z s - (modRep ρ (n + 1) s ((lev A T (n + 1)).mkQ y0) - (lev A T (n + 1)).mkQ y0)
          ∈ Submodule.map (lev A T (n + 1)).mkQ P := hzy.loc s hsH
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hloc
      obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 (hz1 s)
      rw [modRep_mk, ← hue, ← map_sub, ← map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq] at hpe
      have e : ρ s y0 - y0 = ((p - (u - (ρ s y0 - y0))) + u) - p := by abel
      rw [e]
      apply Submodule.sub_mem _ _ (Submodule.mem_sup_left hp)
      apply Submodule.add_mem _ (Submodule.mem_sup_right (hle1 hpe)) (Submodule.mem_sup_right hu)
  obtain ⟨p0, hp0, q0, hq0, hpq⟩ := Submodule.mem_sup.1 hy0
  obtain ⟨w0, rfl⟩ := (hlev 1 q0).1 hq0
  subst hpq
  have hcomp : ⇑φ ∘ z' = z := funext hz'
  refine ⟨z', ⟨(lev A T n).mkQ w0, ?_⟩, ?_⟩
  · refine ⟨IsLocallyConstant.desc z' φ (by rw [hcomp]; exact hzy.lc) hφinj, ?_, ?_, ?_, ?_⟩
    · intro g h
      show z' (g * h) = z' g + modRep ρ n g (z' h)
      apply hφinj
      rw [hz', map_add (f := _), hφρ, hz', hz']
      exact hzy.coc g h
    · apply hφinj
      rw [hz', map_zero]
      exact hzy.cz
    · intro g hg
      apply hφinj
      rw [hz', map_zero]
      exact hzy.kill g hg
    · intro h hh
      show z' h - (modRep ρ n h ((lev A T n).mkQ w0) - (lev A T n).mkQ w0)
        ∈ Submodule.map (lev A T n).mkQ P
      apply hφP
      rw [map_sub, map_sub, hφρ, hz', hφmk]
      have hloc : z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))
          - (lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0)) ∈ Submodule.map (lev A T (n + 1)).mkQ P :=
        hzy.loc h hh
      have e : z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (t • w0)) - (lev A T (n + 1)).mkQ (t • w0))
          = (z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))
            - (lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))) + (lev A T (n + 1)).mkQ (ρ h p0 - p0) := by
        simp only [pow_one, map_add (f := _), map_sub, modRep_mk]
        abel
      rw [e]
      exact Submodule.add_mem _ hloc
        (Submodule.mem_map_of_mem (Submodule.sub_mem _ (hL.stab h hh p0 hp0) hp0))
  · intro g x hx
    rw [← hφmk, hx, hz']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.GwIneq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem card_one_of {R N : Type} [Ring R] [AddCommGroup N] [Module R N] (P : Submodule R N)
    (h : ∀ x ∈ P, x = 0) : Nat.card P = 1 := by
  haveI : Subsingleton P := ⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩

theorem UpperTheory.V.Ws.Bl.gwIneq :
    GlobalFiniteness → GreenbergWiles → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), 0 < r → l ≠ 2 → ContainsAbove S l → ContAction ρ →
          ∀ c : G ℚ Ω, IsCC c → (∀ m, ρ (toGS Ω _ c) m = -m) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
          ∀ (v0 : S) (s : G ℚ Ω), s ∈ Dec (F := ℚ) (Av v0) → cycZ ℚ Ω l s = 1 → (Function.Bijective fun x => ρ (toGS Ω _ s) x - x) →
          ∀ L : LocCond ρ (locFam S Av), (∀ v, v ≠ v0 → Nat.card (H0 (ρ.comp (locFam S Av v))) ≤ Nat.card (L v)) →
          Nat.card (L v0) ≤ Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := by
  intro hGF hGW Ω _ _ _ l _ r M _ _ _ _ _ S ρ hr hl2 hS hρ c hc hcneg Av hAv v0 s hsD hsz hsbij L hL
  have hcop : Nat.Coprime 2 (l ^ r) :=
    Nat.Coprime.pow_right r ((Nat.coprime_primes Nat.prime_two (Fact.out)).mpr (Ne.symm hl2))
  have hinv : ∀ m : M, m = -m → m = 0 := by
    intro m hm
    set u := ZMod.unitOfCoprime 2 hcop
    have hu : (u : ZMod (l ^ r)) = 2 := by simp [u]
    have h2 : (2 : ZMod (l ^ r)) • m = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hm]
      exact add_neg_cancel m
    calc m = ((u⁻¹ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) • ((u : ZMod (l ^ r)) • m) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = 0 := by rw [hu, h2, smul_zero]
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := r) hS
  have hcc : ∀ w : InfinitePlace ℚ, w.IsReal → IsCCAt w c := by
    intro w _
    obtain ⟨j, hj⟩ := hc
    exact ⟨j, hj, Subsingleton.elim _ _⟩
  have key := hGW ℚ Ω l r M S ρ hr hl2 hS hρ μ hμ Av hAv (fun _ => c) hcc L
  have hμs : μ (toGS Ω _ s) = 1 := by
    have h := congrArg (fun f => f s) hμ
    simp only [MonoidHom.comp_apply] at h
    rw [h]
    simp [cycMod, hsz]
  have htw : Nat.card (H0 (twDual μ ρ)) = 1 := by
    refine card_one_of _ (fun φ hφ => ?_)
    have hfix := (mem_riemannRochSpace_iff_regularAt_everywhere _ φ).mp hφ (toGS Ω _ s)
    change (φ : Module.Dual (ZMod (l ^ r)) M) = 0
    apply LinearMap.ext
    intro m
    obtain ⟨x, rfl⟩ := hsbij.2 m
    have hx : φ (ρ (toGS Ω _ s) x) = φ x := by
      have h := congrArg (fun ψ : TDual (ZMod (l ^ r)) M => ψ (ρ (toGS Ω _ s) x)) hfix
      simp only [twDual_apply, hμs, Units.val_one, one_mul] at h
      rw [← h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hsub : (φ : Module.Dual (ZMod (l ^ r)) M) (ρ (toGS Ω _ s) x - x) =
        (φ : Module.Dual (ZMod (l ^ r)) M) (ρ (toGS Ω _ s) x) - (φ : Module.Dual (ZMod (l ^ r)) M) x :=
      LinearMap.map_sub _ _ _
    show φ (ρ (toGS Ω _ s) x - x) = 0
    exact hsub.trans (by erw [hx]; exact sub_self _)
  have harch : archH0Card S ρ (fun _ => c) = 1 := by
    have h0 : InfinitePlace.nrComplexPlaces ℚ = 0 := by simp
    unfold archH0Card
    rw [h0, pow_zero, mul_one]
    refine Finset.prod_eq_one (fun w _ => ?_)
    haveI : Subsingleton {m : M // ρ (toGS Ω _ c) m = m} :=
      ⟨fun a b => Subtype.ext (by
        have ha := hinv a.1 (by rw [← hcneg a.1, a.2])
        have hb := hinv b.1 (by rw [← hcneg b.1, b.2])
        rw [ha, hb])⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨⟨0, map_zero _⟩⟩⟩
  have hv0 : Nat.card (H0 (ρ.comp (locFam S Av v0))) = 1 := by
    refine card_one_of _ (fun m hm => ?_)
    have hfix := (mem_riemannRochSpace_iff_regularAt_everywhere _ m).mp hm ⟨s, hsD⟩
    have hfix' : ρ (toGS Ω _ s) m = m := hfix
    apply hsbij.1
    show ρ (toGS Ω _ s) m - m = ρ (toGS Ω _ s) 0 - 0
    rw [hfix', sub_self, map_zero, sub_self]
  classical
  rw [htw, harch, mul_one, mul_one] at key
  obtain ⟨-, hH1, -, -⟩ := hGF ℚ Ω l r M S ρ hr hS hρ
  have hSelpos : 0 < Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := Nat.card_pos
  have hH0pos : ∀ v, 0 < Nat.card (H0 (ρ.comp (locFam S Av v))) := fun v => Nat.card_pos
  have hP := Finset.mul_prod_erase Finset.univ (fun v => Nat.card (H0 (ρ.comp (locFam S Av v)))) (Finset.mem_univ v0)
  have hQ := Finset.mul_prod_erase Finset.univ (fun v => Nat.card (L v)) (Finset.mem_univ v0)
  simp only at hP hQ
  rw [hv0, one_mul] at hP
  set P' := ∏ v ∈ Finset.univ.erase v0, Nat.card (H0 (ρ.comp (locFam S Av v)))
  set Q' := ∏ v ∈ Finset.univ.erase v0, Nat.card (L v)
  have hP'pos : 0 < P' := Finset.prod_pos (fun v _ => hH0pos v)
  have hPQ : P' ≤ Q' := Finset.prod_le_prod₀ (fun v _ => Nat.zero_le _)
    (fun v hv => hL v (Finset.ne_of_mem_erase hv))
  rw [← hP, ← hQ] at key
  set a := Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L)
  set b := Nat.card (Sel (twDual μ ρ) (locFam S Av) _ (perpCond μ ρ (locFam S Av) _ L))
  set h0 := Nat.card (H0 ρ)
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · rw [hb, zero_mul, zero_mul] at key
      exact absurd key (Nat.mul_pos hSelpos hP'pos).ne'
    · exact hb
  have hh0 : 0 < h0 := Nat.card_pos
  have h1 : Nat.card (L v0) * Q' ≤ a * P' := by
    rw [key]
    calc Nat.card (L v0) * Q' ≤ (b * h0) * (Nat.card (L v0) * Q') :=
          Nat.le_mul_of_pos_left _ (Nat.mul_pos hbpos hh0)
      _ = _ := rfl
  have h2 : Nat.card (L v0) * P' ≤ a * P' :=
    le_trans (Nat.mul_le_mul_left _ hPQ) h1
  exact Nat.le_of_mul_le_mul_right h2 hP'pos
end

