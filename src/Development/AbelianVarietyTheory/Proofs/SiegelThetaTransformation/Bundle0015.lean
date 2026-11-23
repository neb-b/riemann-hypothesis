module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsNearlyPrimitive
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.NearPrim

theorem exists_reduce (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, ∀ x : E, ∃ y : E, IsIntegral ℤ y ∧ ‖canonicalEmbedding E (x - y)‖ ≤ C := by
  classical
  let b := integralBasis E
  refine ⟨∑ i, ‖canonicalEmbedding E (b i)‖, fun x => ⟨∑ i, ⌊b.repr x i⌋ • b i, ?_, ?_⟩⟩
  · refine IsIntegral.sum _ fun i _ => IsIntegral.zsmul ?_ _
    simp only [b, integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  · have h : x - ∑ i, ⌊b.repr x i⌋ • b i = ∑ i, (Int.fract (b.repr x i) : ℚ) • b i := by
      conv_lhs => rw [← b.sum_repr x]
      rw [b.sum_repr x]
      nth_rewrite 1 [← b.sum_repr x]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.fract, sub_smul, Int.cast_smul_eq_zsmul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_rat_smul, norm_smul]
    have h0 := Int.fract_nonneg (b.repr x i)
    have h1 := (Int.fract_lt_one (b.repr x i)).le
    have : ‖(Int.fract (b.repr x i) : ℚ)‖ ≤ 1 := by
      rw [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast h0)]
      exact_mod_cast h1
    exact mul_le_of_le_one_left (norm_nonneg _) this

theorem exists_approx (E : Type) [Field E] [NumberField E] :
    ∃ M : ℕ, ∀ x : E, ∃ (m : ℕ) (y : E), 0 < m ∧ m ≤ M ∧ IsIntegral ℤ y ∧
      ‖canonicalEmbedding E (m * x - y)‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer
  | exact _root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer
  | (apply _root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer <;> assumption)
  | (intros; apply _root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer ..)

theorem exists_min {E : Type} [Field E] [NumberField E] (S : Set E) (d : ℤ) (hd : d ≠ 0)
    (hS : ∀ x ∈ S, IsIntegral ℤ ((d : E) * x)) (h1 : (1 : E) ∈ S) :
    ∃ α ∈ S, ‖canonicalEmbedding E α‖ ≤ 1 ∧
      ∀ x ∈ S, ‖canonicalEmbedding E α‖ ≤ ‖canonicalEmbedding E x‖ := by
  have hfin : {x ∈ S | ‖canonicalEmbedding E x‖ ≤ 1}.Finite := by
    refine Set.Finite.of_finite_image (f := fun x => (d : E) * x)
      ((Embeddings.finite_of_norm_le E ℂ |(d : ℝ)|).subset ?_) ?_
    · rintro _ ⟨x, ⟨hx, hx1⟩, rfl⟩
      refine ⟨hS x hx, fun φ => ?_⟩
      have := (canonicalEmbedding.norm_le_iff x 1).1 hx1 φ
      rw [map_mul, norm_mul, map_intCast, Complex.norm_intCast]
      exact mul_le_of_le_one_right (abs_nonneg _) this
    · intro x _ y _ h
      exact mul_left_cancel₀ (Int.cast_ne_zero.2 hd) h
  have hone : ‖canonicalEmbedding E 1‖ ≤ 1 := (canonicalEmbedding.norm_le_iff 1 1).2 (by simp)
  obtain ⟨α, hα, hmin⟩ := Set.exists_min_image _ (fun x => ‖canonicalEmbedding E x‖) hfin
    ⟨1, h1, hone⟩
  refine ⟨α, hα.1, hα.2, fun x hx => ?_⟩
  by_cases h : ‖canonicalEmbedding E x‖ ≤ 1
  · exact hmin x ⟨hx, h⟩
  · exact hα.2.trans (not_le.1 h).le

theorem exists_den {E : Type} [Field E] [NumberField E] {k : ℕ} {m : Type} [Fintype m]
    (W : Matrix (Fin k) m E) (hW : LinearIndependent E (fun i => W i)) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ s : Fin k → E, (∀ j, IsIntegral ℤ ((s ᵥ* W) j)) →
      ∀ i, IsIntegral ℤ ((d : E) * s i) := by
  classical
  have hinj : LinearMap.ker (W.vecMulLinear) = ⊥ :=
    LinearMap.ker_eq_bot.2 (Matrix.vecMul_injective_iff.2 hW)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (Finset.univ.image fun p : m × Fin k => g (Pi.single p.1 1) p.2)
  refine ⟨d, hd, fun s hs i => ?_⟩
  have h1 : g (s ᵥ* W) = s := by simpa using LinearMap.congr_fun hg s
  have h2 : s ᵥ* W = ∑ j, (s ᵥ* W) j • (Pi.single j 1 : m → E) := pi_eq_sum_univ' _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h1, h2, map_sum, Finset.sum_apply, Finset.mul_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
  refine (hs j).mul ?_
  have := hint _ (Finset.mem_image.2 ⟨(j, i), Finset.mem_univ _, rfl⟩)
  simpa [zsmul_eq_mul] using this

theorem exists_rows {E : Type} [Field E] [NumberField E] {k : ℕ} (L : AddSubgroup (Fin k → E))
    (hO : ∀ s : Fin k → E, (∀ i, IsIntegral ℤ (s i)) → s ∈ L) (d : ℤ) (hd : d ≠ 0)
    (hL : ∀ s ∈ L, ∀ i, IsIntegral ℤ ((d : E) * s i)) (C : ℝ)
    (hC : ∀ x : E, ∃ y : E, IsIntegral ℤ y ∧ ‖canonicalEmbedding E (x - y)‖ ≤ C) (i : Fin k) :
    ∃ a ∈ L, (∀ j, i < j → a j = 0) ∧ a i ≠ 0 ∧ (∀ j, ‖canonicalEmbedding E (a j)‖ ≤ max 1 C) ∧
      ∀ s ∈ L, (∀ j, i < j → s j = 0) → s i ≠ 0 →
        ‖canonicalEmbedding E (a i)‖ ≤ ‖canonicalEmbedding E (s i)‖ := by
  classical
  obtain ⟨α, ⟨hα0, a, haL, ha0, rfl⟩, hα1, hmin⟩ := exists_min
    {x : E | x ≠ 0 ∧ ∃ s ∈ L, (∀ j, i < j → s j = 0) ∧ s i = x} d hd
    (by rintro _ ⟨-, s, hs, -, rfl⟩; exact hL s hs i)
    ⟨one_ne_zero, Pi.single i 1, hO _ (fun j => by
      by_cases h : j = i
      · subst h; simpa using isIntegral_one
      · simpa [h] using isIntegral_zero), fun j hj => by simp [hj.ne'], by simp⟩
  choose y hy hyC using hC
  refine ⟨a - fun j => if j < i then y (a j) else 0, L.sub_mem haL (hO _ fun j => ?_),
    fun j hj => ?_, ?_, fun j => ?_, fun s hs hs0 hsi => ?_⟩
  · split_ifs
    · exact hy _
    · exact isIntegral_zero
  · simp [ha0 j hj, not_lt.2 hj.le]
  · simpa using hα0
  · rcases lt_trichotomy j i with h | rfl | h
    · simp only [Pi.sub_apply, if_pos h]
      exact (hyC _).trans (le_max_right _ _)
    · simp only [Pi.sub_apply, lt_irrefl, if_false, sub_zero]
      exact hα1.trans (le_max_left _ _)
    · simp [ha0 j h, not_lt.2 h.le]
  · simp only [Pi.sub_apply, lt_irrefl, if_false, sub_zero]
    exact hmin _ ⟨hsi, s, hs, hs0, rfl⟩

theorem integral_coord {E : Type} [Field E] [NumberField E] {k : ℕ}
    (L : AddSubgroup (Fin k → E))
    (hsm : ∀ y : E, IsIntegral ℤ y → ∀ s ∈ L, y • s ∈ L) (M : ℕ)
    (hM : ∀ x : E, ∃ (m : ℕ) (y : E), 0 < m ∧ m ≤ M ∧ IsIntegral ℤ y ∧
      ‖canonicalEmbedding E (m * x - y)‖ < 1)
    (a : Matrix (Fin k) (Fin k) E) (haL : ∀ i, a i ∈ L) (ha0 : ∀ i j, i < j → a i j = 0)
    (hai : ∀ i, a i i ≠ 0)
    (hmin : ∀ i, ∀ s ∈ L, (∀ j, i < j → s j = 0) → s i ≠ 0 →
        ‖canonicalEmbedding E (a i i)‖ ≤ ‖canonicalEmbedding E (s i)‖) (p : ℕ) (hp : p ≤ k) :
    ∀ t : Fin k → E, (∀ j : Fin k, p ≤ j → t j = 0) → t ᵥ* a ∈ L →
      ∀ i, IsIntegral ℤ (((M.factorial ^ p : ℕ) : E) * t i) := by
  classical
  induction p with
  | zero =>
    intro t ht _ i
    rw [ht i (Nat.zero_le _), mul_zero]
    exact isIntegral_zero
  | succ p ih =>
    intro t ht hL i
    let q : Fin k := ⟨p, hp⟩
    obtain ⟨m, y, hm0, hmM, hy, hlt⟩ := hM (t q)
    set t' : Fin k → E := (m : E) • t - y • Pi.single q 1 with ht'
    have ht'L : t' ᵥ* a ∈ L := by
      rw [ht', sub_vecMul, smul_vecMul, smul_vecMul, single_one_vecMul]
      exact L.sub_mem (hsm _ (isIntegral_natCast m) _ hL) (hsm _ hy _ (haL q))
    have hz : ∀ j, q < j → t' j = 0 := fun j hj => by
      simp [ht', hj.ne', ht j hj]
    have hq : t' q = m * t q - y := by simp [ht']
    have hs : ∀ j, q ≤ j → (t' ᵥ* a) j = t' j * a j j := by
      intro j hj
      rw [vecMul, dotProduct]
      refine Finset.sum_eq_single j (fun l _ hl => ?_) (by simp)
      rcases lt_or_gt_of_ne hl with h | h
      · rw [ha0 l j h, mul_zero]
      · rw [hz l (hj.trans_lt h), zero_mul]
    have hq0 : t' q = 0 := by
      by_contra hne
      have h1 := hmin q _ ht'L (fun j hj => by rw [hs j hj.le, hz j hj, zero_mul])
        (by rw [hs q le_rfl]; exact mul_ne_zero hne (hai q))
      rw [hs q le_rfl, map_mul, hq] at h1
      have h2 : 0 < ‖canonicalEmbedding E (a q q)‖ := by
        rw [norm_pos_iff]
        exact fun h => hai q (canonicalEmbedding_injective E (h.trans (map_zero _).symm))
      have h3 := norm_mul_le (canonicalEmbedding E (m * t q - y)) (canonicalEmbedding E (a q q))
      nlinarith
    have h := ih (by omega) t' (fun j hj => by
      rcases (show q ≤ j from hj).eq_or_lt with rfl | h
      · exact hq0
      · exact hz j h) ht'L i
    obtain ⟨e, he⟩ := Nat.dvd_factorial hm0 hmM
    have hint : IsIntegral ℤ ((Pi.single q 1 : Fin k → E) i) := by
      by_cases h : i = q
      · subst h; simpa using isIntegral_one
      · simpa [h] using isIntegral_zero
    have : ((M.factorial ^ (p + 1) : ℕ) : E) * t i =
        (e : E) * (((M.factorial ^ p : ℕ) : E) * t' i +
          ((M.factorial ^ p : ℕ) : E) * (y * (Pi.single q 1 : Fin k → E) i)) := by
      rw [pow_succ, Nat.cast_mul]
      nth_rewrite 2 [he]
      simp only [ht', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
      ring
    rw [this]
    exact (isIntegral_natCast e).mul (h.add ((isIntegral_natCast _).mul (hy.mul hint)))

end GlobalTheory.SW.NearPrim

namespace GlobalTheory.SW


open NearPrim in
theorem exists_nearly_primitive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : ℕ), ∃ (c : ℕ) (C : ℝ), 0 < c ∧ ∀ (m : Type) [Fintype m] (W : Matrix (Fin k) m E), IntM W → LinearIndependent E (fun i => W i) → ∃ a : Matrix (Fin k) (Fin k) E, a.det ≠ 0 ∧ (∀ (τ : E →+* ℂ) i j, ‖τ (a i j)‖ ≤ C) ∧ IntM (a * W) ∧ ∀ t : Fin k → E, (∀ j, IsIntegral ℤ ((t ᵥ* (a * W)) j)) → ∀ i, IsIntegral ℤ ((c : E) * t i) := by
  intro E _ _ _ k
  obtain ⟨C, hC⟩ := exists_reduce E
  obtain ⟨M, hM⟩ := exists_approx E
  refine ⟨M.factorial ^ k, max 1 C, pow_pos M.factorial_pos _, fun m _ W hW hind => ?_⟩
  obtain ⟨d, hd, hden⟩ := exists_den W hind
  let L : AddSubgroup (Fin k → E) :=
    { carrier := {s | ∀ j, IsIntegral ℤ ((s ᵥ* W) j)}
      add_mem' := fun {s t} hs ht j => by rw [add_vecMul]; exact (hs j).add (ht j)
      zero_mem' := fun j => by rw [zero_vecMul]; exact isIntegral_zero
      neg_mem' := fun {s} hs j => by rw [neg_vecMul]; exact (hs j).neg }
  have hO : ∀ s : Fin k → E, (∀ i, IsIntegral ℤ (s i)) → s ∈ L := fun s hs j =>
    IsIntegral.sum (s := Finset.univ) (fun i => s i * W i j) fun i _ => (hs i).mul (hW i j)
  have hsm : ∀ y : E, IsIntegral ℤ y → ∀ s ∈ L, y • s ∈ L := fun y hy s hs j => by
    rw [smul_vecMul]; exact hy.mul (hs j)
  choose a haL ha0 hai haC hmin using exists_rows L hO d hd hden C hC
  refine ⟨Matrix.of a, ?_, fun τ i j => (canonicalEmbedding.norm_le_iff _ _).1 (haC i j) τ,
    fun i j => haL i j, fun t ht => ?_⟩
  · rw [Matrix.det_of_lowerTriangular (Matrix.of a) (fun i j h => ha0 i j h)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hai i
  · refine integral_coord L hsm M hM (Matrix.of a) haL ha0 hai hmin k le_rfl t
      (fun j hj => absurd j.2 (not_lt.2 hj)) fun j => ?_
    rw [vecMul_vecMul]
    exact ht j

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitaryExt
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.RowExt

theorem exists_right_inv {E : Type} [Field E] [NumberField E] {κ ι : Type} [Fintype κ] [Fintype ι]
    [DecidableEq κ] (c : E) (W : Matrix κ ι E) (hW : IntM W)
    (hli : LinearIndependent E (fun i => W i))
    (hprim : ∀ t : κ → E, (∀ j, IsIntegral ℤ ((t ᵥ* W) j)) → ∀ i, IsIntegral ℤ (c * t i)) :
    ∃ X : Matrix ι κ E, IntM X ∧ W * X = c • (1 : Matrix κ κ E) := by
  classical
  have hinj : LinearMap.ker W.vecMulLinear = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Matrix.vecMul_injective_iff.mpr hli
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hg' : ∀ t, g (t ᵥ* W) = t := fun t => LinearMap.congr_fun hg t
  let j : (ι → 𝓞 E) →ₗ[𝓞 E] (ι → E) := (Algebra.linearMap (𝓞 E) E).compLeft ι
  let q : (ι → E) →ₗ[E] (ι → E) := LinearMap.id - W.vecMulLinear ∘ₗ g
  let φ : (ι → 𝓞 E) →ₗ[𝓞 E] (ι → E) := (q.restrictScalars (𝓞 E)) ∘ₗ j
  haveI : Module.Finite (𝓞 E) (LinearMap.range φ) := inferInstance
  haveI : Module.FinitePresentation (𝓞 E) (LinearMap.range φ) :=
    Module.finitePresentation_of_finite _ _
  haveI : Module.Flat (𝓞 E) (LinearMap.range φ) := inferInstance
  haveI : Module.Projective (𝓞 E) (LinearMap.range φ) :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property φ.rangeRestrict LinearMap.id
    φ.surjective_rangeRestrict
  let r : (ι → 𝓞 E) →ₗ[𝓞 E] (ι → 𝓞 E) := LinearMap.id - s ∘ₗ φ.rangeRestrict
  have hr : ∀ m, φ (r m) = 0 := by
    intro m
    have := congrArg Subtype.val (LinearMap.congr_fun hs (φ.rangeRestrict m))
    simp only [r, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
    rw [sub_eq_zero]
    exact this.symm
  have hr' : ∀ m, g (j (r m)) ᵥ* W = j (r m) := by
    intro m
    have : j (r m) - g (j (r m)) ᵥ* W = 0 := hr m
    exact (sub_eq_zero.mp this).symm
  let h : (ι → 𝓞 E) →ₗ[𝓞 E] (κ → E) := (g.restrictScalars (𝓞 E)) ∘ₗ j ∘ₗ r
  refine ⟨Matrix.of fun a k => c * h (Pi.single a 1) k, ?_, ?_⟩
  · intro a k
    refine hprim _ (fun b => ?_) k
    show IsIntegral ℤ ((g (j (r _)) ᵥ* W) b)
    rw [hr']
    exact RingOfIntegers.isIntegral_coe _
  · ext i k
    let w : ι → 𝓞 E := fun a => ⟨W i a, hW i a⟩
    have hjw : j w = Pi.single i 1 ᵥ* W := by
      rw [Matrix.single_one_vecMul]; rfl
    have hφw : φ.rangeRestrict w = 0 := by
      apply Subtype.ext
      show j w - g (j w) ᵥ* W = 0
      rw [hjw, hg', sub_self]
    have hw : h w = Pi.single i 1 := by
      show g (j (w - s (φ.rangeRestrict w))) = _
      rw [hφw, map_zero, sub_zero, hjw, hg']
    have hw2 : w = ∑ a, w a • Pi.single a 1 := pi_eq_sum_univ' w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw2, map_sum] at hw
    have := congrFun hw k
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply] at this
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : (1 : Matrix κ κ E) i k = (Pi.single i 1 : κ → E) k := by
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [h1, ← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, mul_left_comm]
    rfl

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {α β γ : Type}

theorem ccT_eq (A : Matrix α β E) : ccT A = Aᴴ := rfl

omit [NumberField E] [IsCMField E] in
theorem intM_mul [Fintype β] {A : Matrix α β E} {B : Matrix β γ E} (hA : IntM A) (hB : IntM B) :
    IntM (A * B) := fun a c => by
  rw [Matrix.mul_apply]
  exact IsIntegral.sum _ fun b _ => (hA a b).mul (hB b c)

theorem intM_conj {A : Matrix α β E} (hA : IntM A) : IntM Aᴴ := fun a b =>
  (hA b a).map ((IsCMField.complexConj E).toAlgHom.restrictScalars ℤ)

omit [NumberField E] [IsCMField E] in
theorem intM_nat {A : Matrix α β E} (n : ℕ) (hA : IntM A) : IntM ((n : E) • A) := fun a b =>
  (isIntegral_natCast n).mul (hA a b)

omit [NumberField E] [IsCMField E] in
theorem intM_J [DecidableEq α] : IntM (Matrix.J α E) := by
  rintro (a | a) (b | b) <;> by_cases h : a = b <;>
    simp [Matrix.J, Matrix.one_apply, h, isIntegral_zero, isIntegral_one, isIntegral_one.neg]

theorem J_conj [DecidableEq α] : (Matrix.J α E)ᴴ = -Matrix.J α E := by
  simp [Matrix.J, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]

end

theorem exists_unitary_ext :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N c : ℕ), 0 < c → ∃ c' : ℕ, 0 < c' ∧
      ∀ W : Matrix (Fin N) (Fin N ⊕ Fin N) E, IntM W → LinearIndependent E (fun i => W i) →
        W * Matrix.J (Fin N) E * ccT W = 0 →
        (∀ t : Fin N → E, (∀ j, IsIntegral ℤ ((t ᵥ* W) j)) → ∀ i, IsIntegral ℤ ((c : E) * t i)) →
        ∃ γ ∈ UU E N, Den c' γ ∧ ∀ a, γ (Sum.inr a) = W a := by
  intro E _ _ _ N c hc
  refine ⟨2 * c * c, by positivity, fun W hW hli hiso hprim => ?_⟩
  obtain ⟨X, hX, hWX⟩ := exists_right_inv (c : E) W hW hli hprim
  rw [ccT_eq] at hiso
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  set J := Matrix.J (Fin N) E with hJ
  have hJJ : J * J = -1 := Matrix.J_squared _ _
  have hJc : Jᴴ = -J := J_conj
  have hJi : IntM J := intM_J
  obtain ⟨V₀, hV₀⟩ : ∃ V₀ : Matrix (Fin N) (Fin N ⊕ Fin N) E, V₀ = (c : E)⁻¹ • (Xᴴ * J) := ⟨_, rfl⟩
  have hcV : (c : E) • V₀ = Xᴴ * J := by rw [hV₀, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hVi : IntM ((c : E) • V₀) := hcV ▸ intM_mul (intM_conj hX) hJi
  have h1 : V₀ * J * Wᴴ = -1 := by
    rw [hV₀, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc Xᴴ, hJJ, Matrix.mul_neg,
      Matrix.mul_one, Matrix.neg_mul, ← Matrix.conjTranspose_mul, hWX]
    simp [smul_smul, hc0]
  have skew : ∀ A B : Matrix (Fin N) (Fin N ⊕ Fin N) E, (A * J * Bᴴ)ᴴ = -(B * J * Aᴴ) := by
    intro A B
    simp [Matrix.conjTranspose_mul, hJc, Matrix.mul_assoc]
  have h2 : W * J * V₀ᴴ = 1 := by
    have := skew V₀ W
    rw [h1] at this
    simpa using this.symm
  obtain ⟨S, hS⟩ : ∃ S, S = V₀ * J * V₀ᴴ := ⟨_, rfl⟩
  have hSc : Sᴴ = -S := hS ▸ skew V₀ V₀
  obtain ⟨T, hT⟩ : ∃ T, T = (-(2 : E)⁻¹) • S := ⟨_, rfl⟩
  have hTc : Tᴴ = -T := by
    rw [hT, Matrix.conjTranspose_smul, hSc]; simp
  obtain ⟨V, hV⟩ : ∃ V, V = V₀ + T * W := ⟨_, rfl⟩
  have k2 : W * J * Vᴴ = 1 := by
    rw [hV, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.mul_add, h2,
      ← Matrix.mul_assoc, hiso, Matrix.zero_mul, add_zero]
  have k1 : V * J * Wᴴ = -1 := by
    have := skew W V
    rw [k2] at this
    rw [← neg_neg (V * J * Wᴴ), ← this]; simp
  have k0 : V * J * Vᴴ = 0 := by
    have e : V * J * V₀ᴴ = S + T := by
      rw [hV, Matrix.add_mul, Matrix.add_mul, ← hS, Matrix.mul_assoc T, Matrix.mul_assoc T, h2,
        Matrix.mul_one]
    conv_lhs => rw [show Vᴴ = V₀ᴴ + Wᴴ * Tᴴ by
      rw [hV, Matrix.conjTranspose_add, Matrix.conjTranspose_mul]]
    rw [Matrix.mul_add, e, ← Matrix.mul_assoc, k1, hTc, hT]
    simp only [Matrix.neg_mul, Matrix.one_mul, neg_neg]
    rw [add_assoc, ← add_smul, show (-(2 : E)⁻¹ + -(2 : E)⁻¹) = -1 by norm_num]
    simp
  have key : Matrix.fromRows V W * J * (Matrix.fromRows V W)ᴴ = J := by
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols, k0, k1, k2, hiso]
    rfl
  refine ⟨Matrix.fromRows V W, ?_, ?_, fun a => rfl⟩
  · generalize Matrix.fromRows V W = g at key
    show gᴴ * J * g = J
    have e1 : g * (J * gᴴ * -J) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, key, Matrix.mul_neg, hJJ, neg_neg]
    have e2 := mul_eq_one_comm.mp e1
    have e3 : J * (J * gᴴ * -J * g) = J := by rw [e2, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ] at e3
    simpa using e3
  · have hVV : ((2 * c * c : ℕ) : E) • V = ((2 * c : ℕ) : E) • ((c : E) • V₀) -
        ((c : E) • V₀) * J * ((c : E) • V₀)ᴴ * W := by
      rw [hV, hT, hS]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
        star_natCast, sub_eq_add_neg, ← neg_smul]
      congr 2
      · push_cast; ring
      · push_cast; field_simp
    have i1 := intM_nat (2 * c) hVi
    have i2 := intM_mul (intM_mul (intM_mul hVi hJi) (intM_conj hVi)) hW
    rintro (a | a) b
    · show IsIntegral ℤ ((((2 * c * c : ℕ) : E) • V) a b)
      rw [hVV]
      exact (i1 a b).sub (i2 a b)
    · exact intM_nat (2 * c * c) hW a b

end GlobalTheory.SW.RowExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PosSemidefSubSmulOne
section
open Matrix Complex Unitary
open scoped ComplexOrder

namespace GlobalTheory.PosSemidefShiftByScalar

theorem posSemidef_sub_smul_one {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ δ' : ℝ, δ' ≤ δ → (A - (δ' : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  have hH := hA.isHermitian
  obtain ⟨δ, hδ, hle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ hH.eigenvalues i := by
    rcases isEmpty_or_nonempty n with h | h
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, -, hi0⟩ :=
        Finset.exists_min_image Finset.univ hH.eigenvalues Finset.univ_nonempty
      exact ⟨_, hA.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ i)⟩
  refine ⟨δ, hδ, fun δ' hδ' => ?_⟩
  have e : A - (δ' : ℂ) • (1 : Matrix n n ℂ) = conjStarAlgAut ℂ _ hH.eigenvectorUnitary
      (diagonal (fun i => ((hH.eigenvalues i - δ' : ℝ) : ℂ))) := by
    have d : diagonal (fun i => ((hH.eigenvalues i - δ' : ℝ) : ℂ)) =
        diagonal (RCLike.ofReal ∘ hH.eigenvalues) - (δ' : ℂ) • (1 : Matrix n n ℂ) := by
      ext i j; by_cases h : i = j <;> simp [diagonal, one_apply, h]
    conv_lhs => rw [hH.spectral_theorem]
    rw [d, map_sub, map_smul, map_one]
  rw [e, conjStarAlgAut_apply, isUnit_coe.posSemidef_star_right_conjugate_iff]
  exact PosSemidef.diagonal fun i =>
    Complex.zero_le_real.2 (sub_nonneg.2 (hδ'.trans (hle i)))

theorem exists_pos_mem_HnGe {N : ℕ} {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    {Z : GlobalTheory.SW.CM Ψ N N} (hZ : Z ∈ GlobalTheory.SW.Hn Ψ N) :
    ∃ δ : ℝ, (0 : ℝ) < δ ∧ Z ∈ GlobalTheory.SW.HnGe Ψ N δ := by
  choose d hd h using fun τ : Ψ => posSemidef_sub_smul_one (hZ τ)
  rcases isEmpty_or_nonempty Ψ with hΨ | hΨ
  · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
  · obtain ⟨τ0, -, hτ0⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
    exact ⟨d τ0, hd τ0, fun τ => h τ _ (hτ0 τ (Finset.mem_univ τ))⟩

theorem main : ∀ {N : ℕ} {E : Type} [inst : Field E] (Ψ : Finset (E →+* ℂ)) {Z : GlobalTheory.SW.CM Ψ N N},
    Z ∈ GlobalTheory.SW.Hn Ψ N → ∃ (δ : ℝ), (0 : ℝ) < δ ∧ Z ∈ GlobalTheory.SW.HnGe Ψ N δ :=
  fun Ψ _ hZ => exists_pos_mem_HnGe Ψ hZ

end GlobalTheory.PosSemidefShiftByScalar
end

