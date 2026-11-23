module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNatMulQuadraticLt
section
open Matrix

namespace GlobalTheory

theorem exists_nat_mul_quadratic_lt (N : ℕ) (hN : 1 ≤ N) (a b q c : ℚ) (hq : q < 0) :
    ∃ k : ℕ, a + ((N : ℚ) * k) * b + ((N : ℚ) * k) ^ 2 * q < c := by
  set B : ℚ := (|b| + |a - c| + 1) / (-q) with hB
  have hq' : 0 < -q := by linarith
  have hBpos : 0 < B := div_pos (by positivity) hq'
  obtain ⟨k, hk⟩ := exists_nat_gt B
  refine ⟨k, ?_⟩
  have hk1 : (1 : ℚ) ≤ k := by
    have : (0 : ℚ) < k := lt_trans hBpos hk
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at this)
  have hN1 : (1 : ℚ) ≤ N := by exact_mod_cast hN
  set m : ℚ := (N : ℚ) * k with hm
  have hm1 : 1 ≤ m := by nlinarith
  have hmk : (k : ℚ) ≤ m := by nlinarith
  have hmB : B < m := lt_of_lt_of_le hk hmk
  have h1 : |b| + |a - c| + 1 < m * (-q) := by
    rw [hB, div_lt_iff₀ hq'] at hmB; linarith
  have h2 : m * (|b| + |a - c| + 1) < m * (m * (-q)) := mul_lt_mul_of_pos_left h1 (by linarith)
  have h3 : m * b ≤ m * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) (by linarith)
  have h4 : a - c ≤ |a - c| := le_abs_self _
  have h5 : 0 ≤ (m - 1) * (|a - c| + 1) := mul_nonneg (by linarith) (by positivity)
  nlinarith

private theorem trace_mul_vecMulVec {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℚ) (u w : n → ℚ) : (T * vecMulVec u w).trace = w ⬝ᵥ T.mulVec u := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem trace_transvection_conj {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℚ) (x y : n → ℚ) (t : ℚ) :
    ((1 + t • vecMulVec x y)ᵀ * T * (1 + t • vecMulVec x y)).trace =
      T.trace + t * (x ⬝ᵥ T.mulVec y + y ⬝ᵥ T.mulVec x) +
        t ^ 2 * ((y ⬝ᵥ y) * (x ⬝ᵥ T.mulVec x)) := by
  have hP : (1 + t • vecMulVec x y)ᵀ = 1 + t • vecMulVec y x := by
    rw [transpose_add, transpose_one, transpose_smul, transpose_vecMulVec]
  rw [hP]
  have e : (1 + t • vecMulVec y x) * T * (1 + t • vecMulVec x y) =
      T + t • (T * vecMulVec x y) + t • (vecMulVec y x * T) + (t * t) • (vecMulVec y x * T * vecMulVec x y) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul]
    abel
  rw [e, trace_add, trace_add, trace_add, trace_smul, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, Matrix.trace_mul_comm (vecMulVec y x) T]
  simp only [trace_mul_vecMulVec]
  rw [← Matrix.mulVec_mulVec]
  have hv : ∀ w : n → ℚ, vecMulVec y x *ᵥ w = (x ⬝ᵥ w) • y := by
    intro w
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hv, dotProduct_smul, smul_eq_mul]
  ring

theorem exists_congruence_trace_lt :
    ∀ (g N : ℕ), 2 ≤ g → 1 ≤ N → ∀ T : Matrix (Fin g) (Fin g) ℚ, T.IsSymm →
      (∃ v : Fin g → ℚ, v ⬝ᵥ T.mulVec v < 0) →
      ∀ c : ℚ, ∃ U : Matrix (Fin g) (Fin g) ℤ, U.det = 1 ∧
        (∀ i j, (N : ℤ) ∣ U i j - (1 : Matrix (Fin g) (Fin g) ℤ) i j) ∧
        ((U.map (Int.cast : ℤ → ℚ)).transpose * T * U.map (Int.cast : ℤ → ℚ)).trace < c := by
  intro g N hg hN T _ hv c
  obtain ⟨v, hv⟩ := hv
  set D : ℕ := ∏ i, (v i).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun i _ => (v i).den_pos
  have hden : ∀ i, (v i).den ∣ D := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  set xz : Fin g → ℤ := fun i => ((D / (v i).den : ℕ) : ℤ) * (v i).num with hxz
  have hx : ∀ i, ((xz i : ℤ) : ℚ) = (D : ℚ) * v i := by
    intro i
    have hne : ((v i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (v i).den_nz
    simp only [hxz]
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div (hden i) hne, ← Rat.mul_den_eq_num (v i)]
    field_simp
  set x : Fin g → ℚ := fun i => (xz i : ℚ) with hxdef
  have hxv : x = (D : ℚ) • v := funext fun i => by simp [hxdef, hx]
  have hxT : x ⬝ᵥ T *ᵥ x < 0 := by
    rw [hxv, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    have : (0 : ℚ) < D := by exact_mod_cast hDpos
    exact mul_neg_of_pos_of_neg (by positivity) hv
  obtain ⟨i0, hi0⟩ : ∃ i0, xz i0 ≠ 0 := by
    by_contra h
    push Not at h
    have : x = 0 := funext fun i => by simp [hxdef, h i]
    rw [this] at hxT
    simp at hxT
  obtain ⟨i1, hi1⟩ := Fintype.exists_ne_of_one_lt_card (by simp; omega) i0
  set yz : Fin g → ℤ := Pi.single i0 (xz i1) - Pi.single i1 (xz i0) with hyz
  have hyx : yz ⬝ᵥ xz = 0 := by
    rw [hyz, sub_dotProduct, single_dotProduct, single_dotProduct]; ring
  set y : Fin g → ℚ := fun j => (yz j : ℚ) with hydef
  have hy1 : y i1 = -(xz i0 : ℚ) := by
    simp [hydef, hyz, Pi.single_apply, hi1]
  have hyy : 0 < y ⬝ᵥ y := by
    have hle : y i1 * y i1 ≤ y ⬝ᵥ y :=
      Finset.single_le_sum (f := fun j => y j * y j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ i1)
    have hpos : 0 < y i1 * y i1 := by
      rw [hy1]
      have : (xz i0 : ℚ) ≠ 0 := by exact_mod_cast hi0
      exact mul_self_pos.mpr (neg_ne_zero.mpr this)
    linarith
  have hq : (y ⬝ᵥ y) * (x ⬝ᵥ T *ᵥ x) < 0 := mul_neg_of_pos_of_neg hyy hxT
  obtain ⟨k, hk⟩ := exists_nat_mul_quadratic_lt N hN T.trace (x ⬝ᵥ T.mulVec y + y ⬝ᵥ T.mulVec x)
    ((y ⬝ᵥ y) * (x ⬝ᵥ T.mulVec x)) c hq
  refine ⟨1 + ((N : ℤ) * k) • vecMulVec xz yz, ?_, ?_, ?_⟩
  · rw [← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
      hyx, smul_zero, add_zero]
  · intro i j
    refine ⟨k * (xz i * yz j), ?_⟩
    simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    ring
  · have hmap : (1 + ((N : ℤ) * k) • vecMulVec xz yz).map (Int.cast : ℤ → ℚ) =
        1 + ((N : ℚ) * k) • vecMulVec x y := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
        Matrix.one_apply, hxdef, hydef]
      split_ifs <;> push_cast <;> ring
    rw [hmap, trace_transvection_conj]
    exact hk

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrimeDimensionLEOneAvoiding
section
open Polynomial
namespace GlobalTheory.LineThrough

theorem exists_common_nonroot (d : ℕ) (S : Set (MvPolynomial (Fin d) ℂ)) (hS : S.Countable)
    (h0 : (0 : MvPolynomial (Fin d) ℂ) ∉ S) :
    ∃ c : Fin d → ℂ, ∀ f ∈ S, MvPolynomial.eval c f ≠ 0 := by
  have hd : Dense (⋂ f ∈ S, {c : Fin d → ℂ | MvPolynomial.eval c f ≠ 0}) := by
    refine dense_biInter_of_isOpen (fun f _ => ?_) hS (fun f hf => ?_)
    · exact isOpen_ne_fun (MvPolynomial.continuous_eval f) continuous_const
    · rw [Metric.dense_iff]
      intro x r hr
      by_contra hne
      apply h0
      have : f = 0 := by
        refine MvPolynomial.funext_set (fun i => Metric.ball (x i) r)
          (fun i => (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)) |> infinite_of_mem_nhds (x i)) ?_
        intro y hy
        by_contra hy0
        apply hne
        refine ⟨y, ?_, by simpa using hy0⟩
        rw [ball_pi _ hr]
        exact hy
      exact this ▸ hf
  obtain ⟨c, hc⟩ := hd.nonempty
  exact ⟨c, fun f hf => by simpa using Set.mem_iInter₂.1 hc f hf⟩

noncomputable def lineMap {d : ℕ} (a c : Fin d → ℂ) : MvPolynomial (Fin d) ℂ →ₐ[ℂ] ℂ[X] :=
  MvPolynomial.aeval fun i => C (a i) + C (c i - a i) * X

theorem eval_zero_lineMap {d : ℕ} (a c : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    (lineMap a c f).eval 0 = MvPolynomial.eval a f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [lineMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, eval_mul, hp]; simp [lineMap]

theorem eval_one_lineMap {d : ℕ} (a c : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    (lineMap a c f).eval 1 = MvPolynomial.eval c f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [lineMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, eval_mul, hp]; simp [lineMap]

theorem lineMap_self {d : ℕ} (a : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    lineMap a a f = C (MvPolynomial.eval a f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [lineMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, hp]; simp [lineMap]

theorem lineMap_surjective {d : ℕ} {a c : Fin d → ℂ} (h : c ≠ a) :
    Function.Surjective (lineMap a c) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have hi' : c i - a i ≠ 0 := sub_ne_zero.2 hi
  have hX : (X : ℂ[X]) ∈ (lineMap a c).range := by
    refine ⟨MvPolynomial.C (c i - a i)⁻¹ * (MvPolynomial.X i - MvPolynomial.C (a i)), ?_⟩
    simp only [lineMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_sub,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [add_sub_cancel_left, ← mul_assoc, ← C_sub, ← C_mul, inv_mul_cancel₀ hi', C_1, one_mul]
  rw [← AlgHom.range_eq_top, eq_top_iff, ← Polynomial.adjoin_X]
  exact Algebra.adjoin_le (by simpa using hX)

theorem isMaximal_of_ker_lineMap_lt {d : ℕ} (a c : Fin d → ℂ)
    (P : Ideal (MvPolynomial (Fin d) ℂ)) [hP : P.IsPrime] (h : RingHom.ker (lineMap a c) < P) :
    P.IsMaximal := by
  by_cases hc : c = a
  · subst hc
    have hk : RingHom.ker (lineMap c c) = RingHom.ker (MvPolynomial.eval c) := by
      ext f
      simp [RingHom.mem_ker, lineMap_self]
    have hm : (RingHom.ker (MvPolynomial.eval c)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun z => ⟨MvPolynomial.C z, by simp⟩)
    rw [hk] at h
    exact absurd (hm.1.2 P h) hP.ne_top
  · have hs := lineMap_surjective hc
    have hp : (P.map (lineMap a c)).IsPrime := Ideal.map_isPrime_of_surjective hs h.le
    have hcm : (P.map (lineMap a c)).comap (lineMap a c) = P := by
      rw [Ideal.comap_map_of_surjective _ hs, sup_eq_left]
      exact h.le
    have hne : P.map (lineMap a c) ≠ ⊥ := by
      intro hb
      rw [hb] at hcm
      exact h.ne hcm
    have hm : (P.map (lineMap a c)).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hne hp
    rw [← hcm]
    exact Ideal.comap_isMaximal_of_surjective _ hs

theorem exists_prime_dimensionLEOne_avoiding
    (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E] [Algebra.FiniteType ℂ E]
    (e : E →ₐ[ℂ] ℂ) (T : Set E) (hT : T.Countable) (h0 : (0 : E) ∉ T) :
    ∃ Q : Ideal E, Q.IsPrime ∧ Q ≤ RingHom.ker e ∧ (∀ r ∈ T, r ∉ Q) ∧
      Ring.DimensionLEOne (E ⧸ Q) := by
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ E
  letI : Algebra (MvPolynomial (Fin d) ℂ) E := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) E := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) E :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hn : ∀ r : T, ∃ n : MvPolynomial (Fin d) ℂ, n ≠ 0 ∧
      algebraMap _ E n ∈ Ideal.span {(r : E)} := by
    intro r
    have hr : (r : E) ≠ 0 := fun h => h0 (h ▸ r.2)
    have := Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℂ) hr
      (Ideal.mem_span_singleton_self (r : E)) (Algebra.IsIntegral.isIntegral _)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨n, hn0, hn⟩
  choose n hn0 hn using hn
  haveI : Countable T := hT.to_subtype
  obtain ⟨c, hc⟩ := exists_common_nonroot d (Set.range n) (Set.countable_range n)
    (by rintro ⟨r, hr⟩; exact hn0 r hr)
  let a : Fin d → ℂ := fun i => e (g (MvPolynomial.X i))
  have hea : ∀ f, e (g f) = MvPolynomial.eval a f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r =>
      have : g (MvPolynomial.C r) = algebraMap ℂ E r := g.commutes r
      simp [this]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, a]
  haveI hpp : (RingHom.ker (lineMap a c)).IsPrime := RingHom.ker_isPrime _
  haveI hM : (RingHom.ker e).IsPrime := RingHom.ker_isPrime _
  have hle : RingHom.ker (lineMap a c) ≤ (RingHom.ker e).under (MvPolynomial (Fin d) ℂ) := by
    intro f hf
    change e (g f) = 0
    rw [hea, ← eval_zero_lineMap a c, RingHom.mem_ker.1 hf, eval_zero]
  obtain ⟨Q, hQ, hQp, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := RingHom.ker (lineMap a c)) (RingHom.ker e) hle
  have hQc : Q.comap (algebraMap (MvPolynomial (Fin d) ℂ) E) = RingHom.ker (lineMap a c) :=
    hQo.over.symm
  refine ⟨Q, hQp, hQ, fun r hr hrQ => ?_, ⟨fun {P} hP0 hP => ?_⟩⟩
  · have h1 : n ⟨r, hr⟩ ∈ RingHom.ker (lineMap a c) := by
      rw [← hQc]
      exact (Ideal.span_singleton_le_iff_mem _).2 hrQ (hn ⟨r, hr⟩)
    apply hc _ ⟨⟨r, hr⟩, rfl⟩
    rw [← eval_one_lineMap a c, RingHom.mem_ker.1 h1, eval_zero]
  · have hs : Function.Surjective (Ideal.Quotient.mk Q) := Ideal.Quotient.mk_surjective
    have hlt : Q < P.comap (Ideal.Quotient.mk Q) := by
      refine lt_of_le_of_ne (fun x hx => ?_) (fun h => hP0 ?_)
      · simp [Ideal.Quotient.eq_zero_iff_mem.2 hx]
      · rw [← Ideal.map_comap_of_surjective _ hs P, ← h, Ideal.map_quotient_self]
    have hlt' := Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin d) ℂ) hlt
    change Q.comap (algebraMap (MvPolynomial (Fin d) ℂ) E) < _ at hlt'
    rw [hQc] at hlt'
    have hm := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := MvPolynomial (Fin d) ℂ) _
      (isMaximal_of_ker_lineMap_lt a c _ hlt')
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hs hm with h | h
    · rw [Ideal.map_comap_of_surjective _ hs] at h
      exact absurd h hP.ne_top
    · rwa [Ideal.map_comap_of_surjective _ hs] at h

end GlobalTheory.LineThrough
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRepresentativesModSimilitudeTranspose
section
namespace GlobalTheory

theorem natAbs_det_of_transpose_mul_self (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ)
    (h : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    al.det.natAbs = m ^ 2 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one] at h1
  have h2 := congrArg Int.natAbs h1
  simp only [Int.natAbs_mul, Fintype.card_fin, mul_one, Int.natAbs_pow, Int.natAbs_natCast] at h2
  have h3 : al.det.natAbs ^ 2 = (m ^ 2) ^ 2 := by rw [sq, h2]; ring
  exact Nat.pow_left_injective (by norm_num) h3

theorem card_quotient_range_mulVecLin {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (hA : A.det ≠ 0) :
    Nat.card ((ι → ℤ) ⧸ LinearMap.range (Matrix.toLin' A)) = A.det.natAbs := by
  have hinj : Function.Injective (Matrix.toLin' A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hA (by simpa using hv)
  rw [← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _ hinj)]
  congr 1
  rw [← LinearMap.det_toLin' A]
  congr 1

theorem exists_representatives_mod_similitude_transpose :
    ∀ (g m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ), 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ k n : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, ∀ k' n' : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, (∀ I I', I ≠ I' → ¬ ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k' I' c + ∑ r, al r c • d r ∧ n' I c = n' I' c + ∑ r, al r c • e r) → ∃ σ : Equiv.Perm (Fin 4 → Fin (m ^ g)), ∀ I, ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k (σ I) c + ∑ r, al r c • d r ∧ n' I c = n (σ I) c + ∑ r, al r c • e r := by
  intro g m al hm h
  classical
  have hdet := natAbs_det_of_transpose_mul_self m al h
  have hne : al.transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    intro h0
    rw [h0] at hdet
    have : 0 < m ^ 2 := by positivity
    simp at hdet
    omega
  set L := LinearMap.range (Matrix.toLin' al.transpose) with hL
  have hQ : Nat.card ((Fin 4 → ℤ) ⧸ L) = m ^ 2 := by
    rw [hL, card_quotient_range_mulVecLin _ hne, Matrix.det_transpose, hdet]
  haveI : Finite ((Fin 4 → ℤ) ⧸ L) := Nat.finite_of_card_ne_zero (by rw [hQ]; positivity)
  let cl : (Fin 4 → Fin g → ℤ) → Fin g → ((Fin 4 → ℤ) ⧸ L) :=
    fun x j => Submodule.Quotient.mk (fun c => x c j)
  have hsurj : Function.Surjective cl := by
    intro q
    choose f hf using fun j => Submodule.Quotient.mk_surjective L (q j)
    exact ⟨fun c j => f j c, funext hf⟩
  have hrel : ∀ x y, cl x = cl y → ∃ d : Fin 4 → Fin g → ℤ,
      ∀ c, x c = y c + ∑ r, al r c • d r := by
    intro x y hxy
    have : ∀ j, ∃ v : Fin 4 → ℤ, Matrix.toLin' al.transpose v
        = (fun c => x c j) - (fun c => y c j) := fun j =>
      (Submodule.Quotient.eq L).1 (congrFun hxy j)
    choose v hv using this
    refine ⟨fun r j => v j r, fun c => ?_⟩
    funext j
    have := congrFun (hv j) c
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Pi.sub_apply] at this
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]; ring
  have hcard : Nat.card (Fin 4 → Fin (m ^ g)) =
      Nat.card ((Fin g → ((Fin 4 → ℤ) ⧸ L)) × (Fin g → ((Fin 4 → ℤ) ⧸ L))) := by
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, hQ]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    ring
  obtain ⟨β⟩ := Finite.card_eq.1 hcard
  choose s hs using hsurj
  refine ⟨fun I => s (β I).1, fun I => s (β I).2, fun k' n' hkn => ?_⟩
  let f : (Fin 4 → Fin (m ^ g)) → (Fin 4 → Fin (m ^ g)) :=
    fun I => β.symm (cl (k' I), cl (n' I))
  have hf : Function.Injective f := by
    intro I I' hI
    by_contra hne'
    have h1 := β.symm.injective hI
    obtain ⟨d, hd⟩ := hrel _ _ (congrArg Prod.fst h1)
    obtain ⟨e, he⟩ := hrel _ _ (congrArg Prod.snd h1)
    exact hkn I I' hne' ⟨d, e, fun c => ⟨hd c, he c⟩⟩
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun I => ?_⟩
  obtain ⟨d, hd⟩ := hrel (k' I) (s (β (f I)).1) (by rw [hs]; simp [f])
  obtain ⟨e, he⟩ := hrel (n' I) (s (β (f I)).2) (by rw [hs]; simp [f])
  exact ⟨d, e, fun c => ⟨hd c, he c⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FinitePreimageOfIsPullbackOfFiniteBase
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.KeyFin

theorem finite_preimage_of_isPullback_of_finite_base :
    ∀ (X X' S S' : Scheme.{0}) (h : X ⟶ S) (h' : X' ⟶ S') (φ : X' ⟶ X) (f : S' ⟶ S) (Z : Set X),
      LocallyOfFiniteType h → QuasiCompact h → IsPullback φ h' h f → Finite S' → IsClosed Z →
      Z.Finite → (φ ⁻¹' Z).Finite := by
  intro X X' S S' h h' φ f Z _ _ H _ hZ hfin
  let I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩
  have hr : Set.range I.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hf : Finite I.subscheme := by
    have : Finite (Set.range I.subschemeι) := by rw [hr]; exact hfin.to_subtype
    exact Finite.of_injective_finite_range I.subschemeι.isClosedEmbedding.injective
  have hq : LocallyQuasiFinite (I.subschemeι ≫ h) :=
    .of_finite_preimage_singleton _ fun _ => Set.toFinite _
  have P := (IsPullback.of_hasPullback I.subschemeι φ).paste_vert H
  have h1 : LocallyQuasiFinite (pullback.snd I.subschemeι φ ≫ h') :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) P hq
  have h2 : QuasiCompact (pullback.snd I.subschemeι φ ≫ h') :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) P inferInstance
  have h3 : (Set.univ : Set ↑(pullback I.subschemeι φ)).Finite := by
    have := (Set.toFinite (Set.univ : Set S')).preimage'
      (f := (pullback.snd I.subschemeι φ ≫ h')) fun _ _ =>
        (pullback.snd I.subschemeι φ ≫ h').finite_preimage_singleton _
    simpa using this
  rw [← hr, ← Scheme.Pullback.range_snd, ← Set.image_univ]
  exact h3.image _

end GlobalTheory.KeyFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MkTensorLe
section
namespace GlobalTheory.EmbC

open Cardinal TensorProduct

theorem mk_tensor_le (R A B : Type) [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (hA : #A ≤ 𝔠) (hB : #B ≤ 𝔠) : #(A ⊗[R] B) ≤ 𝔠 := by
  have h1 : Function.Surjective (fun l : List (A × B) => (l.map (fun p => p.1 ⊗ₜ[R] p.2)).sum) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨[], by simp⟩
    | tmul a b => exact ⟨[(a, b)], by simp⟩
    | add x y hx hy =>
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨m, rfl⟩ := hy
      exact ⟨l ++ m, by simp⟩
  refine (Cardinal.mk_le_of_surjective h1).trans ((Cardinal.mk_list_le_max _).trans ?_)
  refine max_le Cardinal.aleph0_le_continuum ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  calc #A * #B ≤ 𝔠 * 𝔠 := mul_le_mul' hA hB
    _ = 𝔠 := Cardinal.continuum_mul_self

theorem exists_emb (R A B : Type) [CommRing R] [IsDomain R] [Field A] [Field B] [CharZero A]
    [Algebra R A] [Algebra R B] (hA : #A = 𝔠) (hB : #B = 𝔠)
    (ha : Function.Injective (algebraMap R A)) (hb : Function.Injective (algebraMap R B)) :
    ∃ (σ : A →+* ℂ) (σ' : B →+* ℂ), σ.comp (algebraMap R A) = σ'.comp (algebraMap R B) := by
  haveI : Nontrivial (A ⊗[R] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain R A B ha hb
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A ⊗[R] B)
  letI : Field ((A ⊗[R] B) ⧸ m) := Ideal.Quotient.field m
  let L := (A ⊗[R] B) ⧸ m
  let Ω := AlgebraicClosure L
  let p : (A ⊗[R] B) →+* Ω := (algebraMap L Ω).comp (Ideal.Quotient.mk m)
  let i : A →+* Ω := p.comp (Algebra.TensorProduct.includeLeftRingHom)
  let j : B →+* Ω := p.comp (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
  haveI : CharZero Ω := charZero_of_injective_ringHom i.injective
  have hL : #L ≤ 𝔠 :=
    (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans (mk_tensor_le R A B hA.le hB.le)
  have hΩ : #Ω = 𝔠 := by
    apply le_antisymm
    · exact (Algebra.IsAlgebraic.cardinalMk_le_max L Ω).trans (max_le hL Cardinal.aleph0_le_continuum)
    · rw [← hA]; exact Cardinal.mk_le_of_injective i.injective
  obtain ⟨e⟩ : Nonempty (Ω ≃+* ℂ) :=
    IsAlgClosed.ringEquiv_of_equiv_of_charZero (by rw [hΩ]; exact Cardinal.aleph0_lt_continuum)
      (Cardinal.eq.mp (by rw [hΩ, Cardinal.mk_complex]))
  refine ⟨e.toRingHom.comp i, e.toRingHom.comp j, ?_⟩
  ext r
  have : (algebraMap R A r) ⊗ₜ[R] (1 : B) = (1 : A) ⊗ₜ[R] (algebraMap R B r) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  show e (p ((algebraMap R A r) ⊗ₜ[R] (1 : B))) = e (p ((1 : A) ⊗ₜ[R] (algebraMap R B r)))
  rw [this]

theorem exists_comp_eq (R : Type) [CommRing R] [IsDomain R] (f f' : R →+* ℂ)
    (hf : Function.Injective f) (hf' : Function.Injective f') :
    ∃ σ σ' : ℂ →+* ℂ, σ.comp f = σ'.comp f' :=
  @exists_emb R ℂ ℂ _ _ _ _ _ f.toAlgebra f'.toAlgebra Cardinal.mk_complex Cardinal.mk_complex hf hf'

end GlobalTheory.EmbC
end

