module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsForallAbvSubLt
section
open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad.Approx


open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
theorem _root_.GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt {F : Type*} [Field F] {ι : Type*} [Finite ι]
    {v : ι → AbsoluteValue F ℝ} (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) (z : ι → F) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : F, ∀ i, v i (z i - x) < ε := by
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨x, hx⟩ := (AbsoluteValue.denseRange_algebraMap_pi h hv).exists_dist_lt
    (fun i ↦ WithAbs.toAbs (v i) (z i)) hε
  refine ⟨x, fun i ↦ ?_⟩
  have hi := (dist_pi_lt_iff hε).1 hx i
  rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs] at hi
  convert hi using 2
  rfl

variable {F : Type} [Field F] [NumberField F]

noncomputable def abv (T : Finset (HeightOneSpectrum (𝓞 F))) :
    T ⊕ (F →+* ℝ) → AbsoluteValue F ℝ
  | Sum.inl v => NumberField.HeightOneSpectrum.adicAbv F v.1
  | Sum.inr σ => (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1

open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.LocalQuad.Approx.abv_inl (T : Finset (HeightOneSpectrum (𝓞 F))) (v : T) (x : F) :
    _root_.GlobalTheory.LocalQuad.Approx.abv T (Sum.inl v) x = ‖algebraMap F (v.1.adicCompletion F) x‖ :=
  (FinitePlace.norm_embedding v.1 x).symm

open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.LocalQuad.Approx.abv_isNontrivial (T : Finset (HeightOneSpectrum (𝓞 F)))
    (i : T ⊕ (F →+* ℝ)) : (_root_.GlobalTheory.LocalQuad.Approx.abv T i).IsNontrivial := by
  rcases i with v | σ
  · obtain ⟨r, hrv, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.1.ne_bot
    refine ⟨algebraMap (𝓞 F) F r, (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hr0, ?_⟩
    change NumberField.HeightOneSpectrum.adicAbv F v.1 _ ≠ 1
    rw [← FinitePlace.norm_embedding]
    exact ((FinitePlace.norm_lt_one_iff_mem F v.1 r).2 hrv).ne
  · exact (InfinitePlace.mk (Complex.ofRealHom.comp σ)).isNontrivial

open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
variable {F : Type} [Field F] [NumberField F] in
private theorem not_isEquiv_adicAbv_real_place (v : HeightOneSpectrum (𝓞 F)) (σ : F →+* ℝ) :
    ¬(NumberField.HeightOneSpectrum.adicAbv F v).IsEquiv
      (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1 := by
  intro hE
  have h2 := (hE.le_one_iff (x := (2 : F))).1
    (by simpa using NumberField.HeightOneSpectrum.adicAbv_natCast_le_one F v 2)
  change InfinitePlace.mk (Complex.ofRealHom.comp σ) 2 ≤ 1 at h2
  rw [InfinitePlace.apply] at h2
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  simp only [RingHom.comp_apply, hσ2] at h2
  norm_num at h2

open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.LocalQuad.Approx.abv_pairwise (T : Finset (HeightOneSpectrum (𝓞 F))) :
    Pairwise fun i j ↦ ¬(_root_.GlobalTheory.LocalQuad.Approx.abv T i).IsEquiv
      (_root_.GlobalTheory.LocalQuad.Approx.abv T j) := by
  rintro (v | σ) (w | τ) hne hE
  · have hvw : v.1 ≠ w.1 := fun h ↦ hne (congrArg Sum.inl (Subtype.ext h))
    have hle : ¬v.1.asIdeal ≤ w.1.asIdeal := fun hle ↦
      hvw (HeightOneSpectrum.ext (v.1.isMaximal.eq_of_le w.1.isPrime.ne_top hle))
    obtain ⟨r, hrv, hrw⟩ := Set.not_subset.1 hle
    have h1 := hE.lt_one_iff (x := algebraMap (𝓞 F) F r)
    change NumberField.HeightOneSpectrum.adicAbv F v.1 _ < 1 ↔
      NumberField.HeightOneSpectrum.adicAbv F w.1 _ < 1 at h1
    rw [← FinitePlace.norm_embedding, ← FinitePlace.norm_embedding,
      FinitePlace.norm_lt_one_iff_mem, FinitePlace.norm_lt_one_iff_mem] at h1
    exact hrw (h1.1 hrv)
  · exact not_isEquiv_adicAbv_real_place v.1 τ hE
  · exact not_isEquiv_adicAbv_real_place w.1 σ hE.symm
  · have hmk := (InfinitePlace.eq_iff_isEquiv (w := InfinitePlace.mk (Complex.ofRealHom.comp σ))
      (v := InfinitePlace.mk (Complex.ofRealHom.comp τ))).2 hE
    rw [InfinitePlace.mk_eq_iff] at hmk
    have key : Complex.ofRealHom.comp σ = Complex.ofRealHom.comp τ := by
      rcases hmk with h | h
      · exact h
      · rw [← h]
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
    apply hne
    congr 1
    ext x
    simpa using congrArg (fun φ : F →+* ℂ ↦ φ x) key

end GlobalTheory.LocalQuad.Approx


open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.LocalQuad.denseRange_finite_real (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    DenseRange (fun x : F =>
      ((fun v : T => algebraMap F (v.1.adicCompletion F) x, fun σ : F →+* ℝ => σ x) :
        ((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ))) := by
  classical
  rw [Metric.denseRange_iff]
  rintro ⟨a, b⟩ r hr
  have hr2 : 0 < r / 2 := half_pos hr
  choose y hy using fun v : T ↦
    (HeightOneSpectrum.denseRange_algebraMap (K := F) v.1).exists_dist_lt (a v) hr2
  choose q hq using fun σ : F →+* ℝ ↦ exists_rat_btwn (show b σ - r / 2 < b σ + r / 2 by linarith)
  let z : T ⊕ (F →+* ℝ) → F := fun i ↦ match i with
    | Sum.inl v => y v
    | Sum.inr σ => (q σ : F)
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt
    (_root_.GlobalTheory.LocalQuad.Approx.abv_isNontrivial T)
    (_root_.GlobalTheory.LocalQuad.Approx.abv_pairwise T) z hr2
  refine ⟨x, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · rw [dist_pi_lt_iff hr]
    intro v
    have hxv := hx (Sum.inl v)
    rw [_root_.GlobalTheory.LocalQuad.Approx.abv_inl, map_sub, ← dist_eq_norm] at hxv
    calc dist (a v) (algebraMap F (v.1.adicCompletion F) x)
        ≤ dist (a v) (algebraMap F (v.1.adicCompletion F) (y v)) +
          dist (algebraMap F (v.1.adicCompletion F) (y v)) (algebraMap F (v.1.adicCompletion F) x) :=
          dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add (hy v) hxv
      _ = r := add_halves r
  · rw [dist_pi_lt_iff hr]
    intro σ
    have hxσ := hx (Sum.inr σ)
    change InfinitePlace.mk (Complex.ofRealHom.comp σ) ((q σ : F) - x) < r / 2 at hxσ
    rw [InfinitePlace.apply] at hxσ
    simp only [RingHom.comp_apply, map_sub, map_ratCast, Complex.ofRealHom_eq_coe] at hxσ
    rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hxσ
    rw [Real.dist_eq]
    have hqσ := hq σ
    rw [abs_lt] at hxσ ⊢
    constructor <;> linarith [hxσ.1, hxσ.2, hqσ.1, hqσ.2]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNonzeroIsotropic
section
universe u_1

namespace GlobalTheory.NonzeroIsotropic

open MvPolynomial

theorem quadForm_totalDegree_le {k : Type u_1} [Field k] (a : Fin 3 → Fin 3 → k) :
    (∑ i : Fin 3, ∑ j : Fin 3, C (a i j) * X i * X j : MvPolynomial (Fin 3) k).totalDegree ≤ 2 := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  calc (C (a i j) * X i * X j : MvPolynomial (Fin 3) k).totalDegree
      ≤ (C (a i j) * X i : MvPolynomial (Fin 3) k).totalDegree + (X j : MvPolynomial (Fin 3) k).totalDegree :=
        totalDegree_mul _ _
    _ ≤ ((C (a i j) : MvPolynomial (Fin 3) k).totalDegree + (X i : MvPolynomial (Fin 3) k).totalDegree)
          + (X j : MvPolynomial (Fin 3) k).totalDegree := by gcongr; exact totalDegree_mul _ _
    _ = 2 := by simp [totalDegree_C, totalDegree_X]

theorem exists_nonzero_isotropic :
    ∀ {k : Type u_1} [inst : Field k] [Finite k] (a : Fin (3 : ℕ) → Fin (3 : ℕ) → k),
      ∃ (x : Fin (3 : ℕ) → k), x ≠ (0 : Fin (3 : ℕ) → k) ∧
        ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), a i j * x i * x j = (0 : k) := by
  intro k _ _ a
  classical
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hp⟩ := CharP.exists k
  haveI := hp
  have hpp : p.Prime := by
    rcases CharP.char_is_prime_or_zero k p with h | h
    · exact h
    · subst h
      haveI : CharZero k := CharP.charP_to_charZero k
      exact absurd (Finite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective) (by
        intro h; exact not_finite ℕ)
  set f : MvPolynomial (Fin 3) k := ∑ i : Fin 3, ∑ j : Fin 3, C (a i j) * X i * X j with hf
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    have : f.totalDegree ≤ 2 := quadForm_totalDegree_le a
    simp only [Fintype.card_fin]; omega
  have hdvd := char_dvd_card_solutions p hdeg
  have heval : ∀ x : Fin 3 → k, eval x f = ∑ i : Fin 3, ∑ j : Fin 3, a i j * x i * x j := by
    intro x; simp [hf]
  let z : { x : Fin 3 → k // eval x f = 0 } := ⟨0, by rw [heval]; simp⟩
  have hcard : 1 < Fintype.card { x : Fin 3 → k // eval x f = 0 } := by
    have hpos : 0 < Fintype.card { x : Fin 3 → k // eval x f = 0 } := Fintype.card_pos_iff.mpr ⟨z⟩
    have := Nat.le_of_dvd hpos hdvd
    have := hpp.two_le
    omega
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card hcard z
  refine ⟨y.1, fun h => hy (Subtype.ext h), ?_⟩
  rw [← heval]; exact y.2

end GlobalTheory.NonzeroIsotropic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNsmulMem
section
open NumberField

namespace GlobalTheory.IntegralMultipleOfVectors

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ (e : ℕ) (b : RingOfIntegers E), 0 < e ∧ (e : E) * a = algebraMap (RingOfIntegers E) E b := by
  have h : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hi⟩ := h.exists_integral_multiple
  have hi' : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rcases Int.natAbs_eq y with h1 | h1
    · have : (y.natAbs : E) * a = y • a := by
        conv_rhs => rw [h1]
        simp
      rw [this]; exact hi
    · have : (y.natAbs : E) * a = -(y • a) := by
        conv_rhs => rw [h1]
        simp
      rw [this]; exact hi.neg
  exact ⟨y.natAbs, ⟨_, hi'⟩, Int.natAbs_pos.mpr hy, rfl⟩

theorem exists_nsmul_mem {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, he, hy⟩ := hy
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx e
    · rw [mul_smul]; exact nsmul_mem hy d
  | smul a x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, b, he, hb⟩ := exists_nat_mul_integral a
    refine ⟨e * d, Nat.mul_pos he hd, ?_⟩
    have : (e * d) • a • x = b • d • x := by
      rw [← algebraMap_smul E b, ← hb]
      ext i
      simp
      ring
    rw [this]
    exact L.smul_mem b hx

theorem exists_nsmul_mulVec_mem {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, d • M.mulVec v ∈ L := by
  classical
  obtain ⟨s, hs⟩ := hfg
  choose f hf hmem using fun v => exists_nsmul_mem L hL (M.mulVec v)
  refine ⟨∏ v ∈ s, f v, Finset.prod_pos fun v _ => hf v, fun v hv => ?_⟩
  have hv' : v ∈ Submodule.span (RingOfIntegers E) (s : Set (Fin n → E)) := by
    rw [hs]; exact hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul s f (Finset.mem_coe.mp hx), mul_smul]
    exact nsmul_mem (hmem x) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, smul_add]
    exact L.add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul E a, Matrix.mulVec_smul, algebraMap_smul, smul_comm]
    exact L.smul_mem a hx

end GlobalTheory.IntegralMultipleOfVectors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNsmulMulVecMem
section
namespace GlobalTheory.IntegralMultipleClearDenominators

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ K : ℕ, 0 < K ∧ IsIntegral ℤ ((K : E) * c) := by
  have h : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := h.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h1 | h1
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h1]
      exact (Int.cast_natCast _).symm
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h1]
      rw [Int.cast_neg, neg_neg]
      exact (Int.cast_natCast _).symm
    rw [this, neg_mul]; exact hint.neg

theorem exists_nsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (↑L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hxa b
    · rw [mul_smul]; exact nsmul_mem hyb a
  | smul c x _ hx =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨K, hK, hint⟩ := exists_nat_mul_integral c
    refine ⟨K * a, Nat.mul_pos hK ha, ?_⟩
    have h := L.smul_mem (⟨(K : E) * c, hint⟩ : RingOfIntegers E) hxa
    convert h using 1
    ext i
    change _ = ((K : E) * c) * (a • x i)
    simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring

theorem exists_nsmul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ L, N • Matrix.mulVec M v ∈ L := by
  obtain ⟨s, hs⟩ := hfg
  choose f hf0 hf using exists_nsmul_mem L hL
  refine ⟨∏ x ∈ s, f (M.mulVec x), Finset.prod_pos fun x _ => hf0 _, ?_⟩
  intro v hv
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => f (M.mulVec x)) (Finset.mem_coe.1 hx)
    rw [hk, mul_comm, mul_smul]
    exact nsmul_mem (hf _) k
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, smul_add]
    exact L.add_mem hx hy
  | smul c x _ hx =>
    rw [Matrix.mulVec_smul, smul_comm]
    exact L.smul_mem c hx

end GlobalTheory.IntegralMultipleClearDenominators
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPosMulNormSqLe
section
namespace GlobalTheory.IntegralPointNormSquareBound

theorem exists_pos_mul_norm_sq_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (h : ∀ v : V, v ≠ 0 → 0 < om v (J v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V, c * ‖v‖ ^ 2 ≤ om v (J v) := by
  have hcont : Continuous fun v : V => om v (J v) := by
    let B : V →ₗ[ℝ] V →L[ℝ] ℝ :=
      (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] V →L[ℝ] ℝ).toLinearMap ∘ₗ om
    have h1 : Continuous B := B.continuous_of_finiteDimensional
    have h2 : Continuous J := J.continuous_of_finiteDimensional
    exact h1.clm_apply h2
  have hcomp : IsCompact (Metric.sphere (0 : V) 1) := by
    haveI : ProperSpace V := FiniteDimensional.proper_real V
    exact isCompact_sphere 0 1
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Metric.sphere (0 : V) 1, c ≤ om u (J u) := by
    rcases (Metric.sphere (0 : V) 1).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun u hu => by rw [he] at hu; exact hu.elim⟩
    · obtain ⟨x, hx, hmin⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
      refine ⟨om x (J x), h x ?_, fun u hu => hmin hu⟩
      rintro rfl
      simp at hx
  refine ⟨c, hc, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv
    simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
      simp [norm_smul, hn.ne']
    have h3 := hle _ hu
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h3
    have h4 : ‖v‖⁻¹ * (‖v‖⁻¹ * om v (J v)) * ‖v‖ ^ 2 = om v (J v) := by
      field_simp
    calc c * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ * (‖v‖⁻¹ * om v (J v)) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = om v (J v) := h4

end GlobalTheory.IntegralPointNormSquareBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatBilinForm
section
namespace GlobalTheory.RationalValueRealScalar

theorem map_rat_smul_real {U : Type} [AddCommGroup U] [Module ℝ U] {V : Type} [AddCommGroup V]
    [Module ℚ V] (p : V →+ U) (c : ℚ) (x : V) : p (c • x) = (c : ℝ) • p x := by
  have h1 : (c.den : ℤ) • (c • x) = c.num • x := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    rw [Int.cast_natCast, mul_comm, Rat.mul_den_eq_num]
  have h2 : (c.den : ℝ) • p (c • x) = (c.num : ℝ) • p x := by
    rw [← Int.cast_natCast, Int.cast_smul_eq_zsmul ℝ, Int.cast_smul_eq_zsmul ℝ, ← map_zsmul, ← map_zsmul, h1]
  have hd : (c.den : ℝ) ≠ 0 := by positivity
  calc p (c • x) = ((c.den : ℝ)⁻¹ * c.den) • p (c • x) := by rw [inv_mul_cancel₀ hd, one_smul]
    _ = (c.den : ℝ)⁻¹ • ((c.den : ℝ) • p (c • x)) := by rw [smul_smul]
    _ = (c.den : ℝ)⁻¹ • ((c.num : ℝ) • p x) := by rw [h2]
    _ = (c : ℝ) • p x := by rw [smul_smul, Rat.cast_def, inv_mul_eq_div]

theorem exists_rat_value {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] (p : V →+ U) (L : AddSubgroup V)
    (hL : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = (k : ℝ)) (u v : V) :
    ∃ q : ℚ, (q : ℝ) = -(om (p u) (p v)) := by
  obtain ⟨N, hN, hNu⟩ := hL u
  obtain ⟨M, hM, hMv⟩ := hL v
  obtain ⟨k, hk⟩ := hint _ hNu _ hMv
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hk
  refine ⟨-(k / (N * M) : ℚ), ?_⟩
  have hNM : (N : ℝ) * M ≠ 0 := by positivity
  push_cast
  rw [neg_inj, div_eq_iff hNM, ← hk]
  ring

theorem exists_rat_bilinForm {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] [Module ℚ V] (p : V →+ U) (L : AddSubgroup V)
    (hL : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = (k : ℝ)) :
    ∃ B : LinearMap.BilinForm ℚ V, ∀ u v : V, ((B u v : ℚ) : ℝ) = -(om (p u) (p v)) := by
  choose q hq using exists_rat_value om p L hL hint
  refine ⟨LinearMap.mk₂ ℚ q ?_ ?_ ?_ ?_, fun u v => hq u v⟩
  · intro u1 u2 v
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_add, hq, hq, hq, map_add (f := _), LinearMap.map_add (f := _), LinearMap.add_apply]
    ring
  · intro c u v
    apply Rat.cast_injective (α := ℝ)
    rw [smul_eq_mul, Rat.cast_mul, hq, hq, map_rat_smul_real, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro u v1 v2
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_add, hq, hq, hq, map_add (f := _), LinearMap.map_add (f := _)]
    ring
  · intro c u v
    apply Rat.cast_injective (α := ℝ)
    rw [smul_eq_mul, Rat.cast_mul, hq, hq, map_rat_smul_real, LinearMap.map_smul, smul_eq_mul]
    ring

end GlobalTheory.RationalValueRealScalar
end

