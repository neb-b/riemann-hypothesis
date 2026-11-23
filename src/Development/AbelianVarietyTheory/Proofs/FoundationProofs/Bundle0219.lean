module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimes
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.SelectIdem

section Ring

variable {R : Type*} [CommRing R]

def LocDvd (P : Ideal R) (n x : R) : Prop := ∃ s, s ∉ P ∧ n ∣ s * x

theorem dvd_of_locDvd {n x : R} (h : ∀ P : Ideal R, P.IsMaximal → LocDvd P n x) : n ∣ x := by
  by_contra hx
  let I : Ideal R := Submodule.comap (LinearMap.toSpanSingleton R R x) (Ideal.span {n})
  have hI : ∀ s, s ∈ I ↔ n ∣ s * x := fun s => by
    simp [I, Ideal.mem_span_singleton]
  have hne : I ≠ ⊤ := fun h1 => hx (by
    have : (1 : R) ∈ I := h1 ▸ Submodule.mem_top
    simpa using (hI 1).1 this)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨s, hs, hd⟩ := h P hP
  exact hs (hIP ((hI s).2 hd))

theorem LocDvd.comb {P : Ideal R} (hP : P.IsPrime) {n x y z : R} (a b : R)
    (hx : LocDvd P n x) (hy : LocDvd P n y) (hz : z = a * x + b * y) : LocDvd P n z := by
  obtain ⟨s, hs, hs'⟩ := hx
  obtain ⟨t, ht, ht'⟩ := hy
  refine ⟨s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
  have : s * t * z = (t * a) * (s * x) + (s * b) * (t * y) := by rw [hz]; ring
  rw [this]
  exact dvd_add (hs'.mul_left _) (ht'.mul_left _)

theorem LocDvd.of_dvd {P : Ideal R} {n m x : R} (h : n ∣ m) (hx : LocDvd P m x) :
    LocDvd P n x := by
  obtain ⟨s, hs, hs'⟩ := hx
  exact ⟨s, hs, h.trans hs'⟩

theorem LocDvd.of_not_mem {P : Ideal R} {n : R} (h : n ∉ P) (x : R) : LocDvd P n x :=
  ⟨n, h, dvd_mul_right _ _⟩

theorem exists_loc [IsDedekindDomain R] {n : R} (hn : n ≠ 0) (T : Ideal R → Prop) :
    ∃ ε : R, ∀ P : Ideal R, P.IsMaximal → LocDvd P n (ε - if T P then 1 else 0) := by
  have hn' : Ideal.span {n} ≠ (⊥ : Ideal R) := by simpa using hn
  let S : Finset (Ideal R) := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {n})).toFinset
  have hS : ∀ P : Ideal R, P ∈ S ↔ P.IsPrime ∧ n ∈ P := fun P => by
    simp only [S, Multiset.mem_toFinset]
    rw [Ideal.mem_normalizedFactors_iff hn', Ideal.span_singleton_le_iff_mem]
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun P => P) (fun _ => 1)
    (fun P hP => by
      obtain ⟨h1, h2⟩ := (hS P).1 hP
      refine Ideal.prime_of_isPrime ?_ h1
      rintro rfl
      exact hn (by simpa using h2))
    (fun _ _ _ _ h => h) (fun P => if T P.1 then 1 else 0)
  have hb' : ∀ P : Ideal R, P.IsPrime → n ∈ P → b - (if T P then 1 else 0) ∈ P := fun P h1 h2 => by
    simpa using hb P ((hS P).2 ⟨h1, h2⟩)
  have hrad : (1 - b) * b ∈ (Ideal.span {n}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨h1, h2⟩
    have h3 := hb' P h2 ((Ideal.span_singleton_le_iff_mem _).1 h1)
    by_cases hT : T P
    · rw [if_pos hT] at h3
      have : (1 - b) * b = (-b) * (b - 1) := by ring
      rw [this]; exact P.mul_mem_left _ h3
    · rw [if_neg hT, sub_zero] at h3
      exact P.mul_mem_left _ h3
  obtain ⟨k, hk⟩ := hrad
  rw [Ideal.mem_span_singleton, mul_pow] at hk
  have hc : IsCoprime (1 - b) b := ⟨1, 1, by ring⟩
  obtain ⟨u, v, huv⟩ := hc.pow (m := k) (n := k)
  refine ⟨v * b ^ k, fun P hP => ?_⟩
  by_cases hnP : n ∈ P
  · have h3 := hb' P hP.isPrime hnP
    by_cases hT : T P
    · rw [if_pos hT] at h3 ⊢
      refine ⟨b ^ k, fun h => ?_, ?_⟩
      · have h4 := hP.isPrime.mem_of_pow_mem k h
        have : (1 : R) ∈ P := by simpa using P.sub_mem h4 h3
        exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
      · have : b ^ k * (v * b ^ k - 1) = (-u) * ((1 - b) ^ k * b ^ k) := by
          linear_combination b ^ k * huv
        rw [this]; exact hk.mul_left _
    · rw [if_neg hT, sub_zero] at h3 ⊢
      refine ⟨(1 - b) ^ k, fun h => ?_, ?_⟩
      · have h4 := hP.isPrime.mem_of_pow_mem k h
        have : (1 : R) ∈ P := by simpa using P.add_mem h4 h3
        exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
      · have : (1 - b) ^ k * (v * b ^ k) = v * ((1 - b) ^ k * b ^ k) := by ring
        rw [this]; exact hk.mul_left _
  · exact LocDvd.of_not_mem hnP _

theorem exists_select [IsDedekindDomain R] [CharZero R] {G : Type*} [Group G]
    [MulSemiringAction G R] (c : G) (hc : c * c = 1) :
    ∃ e : ℕ → R, (∀ N m : ℕ, 0 < N → 0 < m → (N : R) ∣ e (N * m) - e N) ∧
      (∀ N : ℕ, 0 < N → (N : R) ∣ e N * e N - e N ∧ (N : R) ∣ e N * (c • e N)) ∧
      ∀ N : ℕ, 0 < N →
        ((∀ P : Ideal R, P.IsMaximal → (N : R) ∈ P → c • P = P) → (N : R) ∣ e N + c • e N) ∧
        ((∀ P : Ideal R, P.IsMaximal → (N : R) ∈ P → c • P ≠ P) →
          (N : R) ∣ 1 - (e N + c • e N)) := by
  let T : Ideal R → Prop := fun P => WellOrderingRel P (c • P)
  have hcc : ∀ P : Ideal R, c • c • P = P := fun P => by rw [smul_smul, hc, one_smul]
  have hT1 : ∀ P, T P → ¬ T (c • P) := fun P h1 h2 => by
    simp only [T, hcc] at h1 h2
    exact asymm h1 h2
  have hT2 : ∀ P, c • P ≠ P → ¬ T P → T (c • P) := fun P h1 h2 => by
    simp only [T, hcc] at h2 ⊢
    rcases trichotomous_of WellOrderingRel P (c • P) with h | h | h
    · exact (h2 h).elim
    · exact (h1 h.symm).elim
    · exact h
  have hT3 : ∀ P, c • P = P → ¬ T P := fun P h1 h2 => hT1 P h2 (h1.symm ▸ h2)
  have hex : ∀ N : ℕ, ∃ ε : R, 0 < N →
      ∀ P : Ideal R, P.IsMaximal → LocDvd P (N : R) (ε - if T P then 1 else 0) := fun N => by
    by_cases hN : 0 < N
    · obtain ⟨ε, h⟩ := exists_loc (n := (N : R)) (by exact_mod_cast hN.ne') T
      exact ⟨ε, fun _ => h⟩
    · exact ⟨0, fun h => (hN h).elim⟩
  choose e he using hex
  have he' : ∀ N : ℕ, 0 < N → ∀ P : Ideal R, P.IsMaximal →
      LocDvd P (N : R) (c • e N - if T (c • P) then 1 else 0) := fun N hN P hP => by
    have hP' : (c • P).IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (MulSemiringAction.toRingHom G R c)
        (MulAction.surjective c) hP with h | h
      · exact absurd h (Ideal.IsPrime.smul (H := hP.isPrime) c).ne_top
      · exact h
    obtain ⟨s, hs, t, ht⟩ := he N hN _ hP'
    refine ⟨c • s, fun h => hs ?_, c • t, ?_⟩
    · have := Ideal.smul_mem_pointwise_smul c _ _ h
      rwa [smul_smul, hc, one_smul] at this
    · have h := congrArg (MulSemiringAction.toRingHom G R c) ht
      simp only [map_mul, map_sub, map_natCast, MulSemiringAction.toRingHom_apply] at h
      rw [← h]
      split_ifs <;> simp
  refine ⟨e, fun N m hN hm => ?_, fun N hN => ⟨?_, ?_⟩, fun N hN => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine dvd_of_locDvd fun P hP => ?_
    exact LocDvd.comb hP.isPrime 1 (-1)
      ((he (N * m) (Nat.mul_pos hN hm) P hP).of_dvd (by push_cast; exact dvd_mul_right _ _))
      (he N hN P hP) (by ring)
  · refine dvd_of_locDvd fun P hP => ?_
    have h := he N hN P hP
    by_cases hT : T P
    · rw [if_pos hT] at h
      exact LocDvd.comb hP.isPrime (e N) 0 h h (by ring)
    · rw [if_neg hT] at h
      exact LocDvd.comb hP.isPrime (e N - 1) 0 h h (by ring)
  · refine dvd_of_locDvd fun P hP => ?_
    have h := he N hN P hP
    have h' := he' N hN P hP
    by_cases hT : T P
    · rw [if_neg (hT1 P hT)] at h'
      exact LocDvd.comb hP.isPrime (e N) 0 h' h' (by ring)
    · rw [if_neg hT] at h
      exact LocDvd.comb hP.isPrime (c • e N) 0 h h (by ring)
  · refine dvd_of_locDvd fun P hP => ?_
    by_cases hNP : (N : R) ∈ P
    · have h1 := he N hN P hP
      have h2 := he' N hN P hP
      have h3 := h P hP hNP
      rw [h3] at h2
      rw [if_neg (hT3 P h3)] at h1 h2
      exact LocDvd.comb hP.isPrime 1 1 h1 h2 (by ring)
    · exact LocDvd.of_not_mem hNP _
  · refine dvd_of_locDvd fun P hP => ?_
    by_cases hNP : (N : R) ∈ P
    · have h1 := he N hN P hP
      have h2 := he' N hN P hP
      have h3 := h P hP hNP
      by_cases hT : T P
      · rw [if_pos hT] at h1
        rw [if_neg (hT1 P hT)] at h2
        exact LocDvd.comb hP.isPrime (-1) (-1) h1 h2 (by ring)
      · rw [if_neg hT] at h1
        rw [if_pos (hT2 P h3 hT)] at h2
        exact LocDvd.comb hP.isPrime (-1) (-1) h1 h2 (by ring)
    · exact LocDvd.of_not_mem hNP _

end Ring

theorem smul_eq_of_abelian {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]
    (hcomm : ∀ σ τ : E ≃ₐ[ℚ] E, σ * τ = τ * σ) (c : E ≃ₐ[ℚ] E) {q : ℕ} (hq : q.Prime)
    (P Q : Ideal (𝓞 E)) (hP : P.IsPrime) (hQ : Q.IsPrime) (hqP : (q : 𝓞 E) ∈ P)
    (hqQ : (q : 𝓞 E) ∈ Q) (h : c • P = P) : c • Q = Q := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible
  have key : ∀ P : Ideal (𝓞 E), P.IsPrime → (q : 𝓞 E) ∈ P → P.LiesOver (Ideal.span {(q : ℤ)}) :=
    fun P hP h => ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
      simpa using h)⟩
  haveI := key P hP hqP
  haveI := key Q hQ hqQ
  obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(q : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  rw [smul_smul, hcomm, ← smul_smul, h]

theorem exists_select_idem : ∀ (D : D7), ∃ e : ℕ → 𝓞 D.host.E, (∀ N m : ℕ, 0 < N → 0 < m → (N : 𝓞 D.host.E) ∣ e (N * m) - e N) ∧ (∀ N : ℕ, 0 < N → (N : 𝓞 D.host.E) ∣ e N * e N - e N ∧ (N : 𝓞 D.host.E) ∣ e N * (D.host.conj • e N)) ∧ ∀ q k : ℕ, q.Prime → (InertQ D q → ((q ^ k : ℕ) : 𝓞 D.host.E) ∣ e (q ^ k) + D.host.conj • e (q ^ k)) ∧ (¬ InertQ D q → ((q ^ k : ℕ) : 𝓞 D.host.E) ∣ 1 - (e (q ^ k) + D.host.conj • e (q ^ k))) := by
  intro D
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hcomm : ∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, σ * τ = τ * σ := fun σ τ =>
    D.host.galE_injective (by
      rw [D.host.galE_mul,
        D.host.galE_mul, mul_comm])
  have hc : D.host.conj * D.host.conj = 1 := by
    obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    refine AlgEquiv.ext fun x => φ.injective ?_
    have h1 := D.host.conjE_apply φ
    exact (h1 _).trans ((congrArg _ (h1 x)).trans (Complex.conj_conj _))
  obtain ⟨e, h1, h2, h3⟩ := exists_select (R := 𝓞 D.host.E) D.host.conj hc
  refine ⟨e, h1, h2, fun q k hq => ?_⟩
  have hq' : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ((q ^ k : ℕ) : 𝓞 D.host.E) ∈ P →
      (q : 𝓞 D.host.E) ∈ P := fun P hP h =>
    hP.isPrime.mem_of_pow_mem k (by simpa using h)
  obtain ⟨h4, h5⟩ := h3 (q ^ k) (pow_pos hq.pos k)
  refine ⟨fun hI => h4 fun P hP h => hI P hP.isPrime ?_ (hq' P hP h), fun hI => h5 fun P hP h hfix => hI ?_⟩
  · rintro rfl
    have := hq' _ hP h
    rw [Ideal.mem_bot] at this
    exact hq.ne_zero (by exact_mod_cast this)
  · intro Q hQ _ hqQ
    exact smul_eq_of_abelian hcomm _ hq P Q hP.isPrime hQ (hq' P hP h) hqQ hfix

end GlobalTheory.SelectIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDeterminantIdealHermitianLatticeBasis
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem exists_detIdeal_abstract {R K V ι : Type} [CommRing R] [CommRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (B : V → V →ₗ[K] K) (hB : ∀ (s : ℕ) (y x : V), B ((s : K) • y) x = (s : K) * B y x)
    (Y : Set V) (b₀ : ι → V)
    (hY : ∀ x ∈ Y, ∀ y ∈ Y, B y x ∈ (algebraMap R K).range)
    (h0 : ∀ i, ∃ s : ℕ, 0 < s ∧ (s : K) • b₀ i ∈ Y) :
    ∃ I : Submodule R K, (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : K) * x ∈ (algebraMap R K).range) ∧
      ∀ (p : ℕ) (b : ι → V), (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) • b i ∈ Y) →
        (∀ y ∈ Y, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : ι → R,
          (s : K) • y = ∑ i, algebraMap R K (c i) • b i) →
        (∃ s : ℕ, Nat.Coprime s p ∧ (s : K) * (Matrix.of fun i j => B (b₀ i) (b j)).det ∈ I) ∧
        ∀ x ∈ I, ∃ (s : ℕ) (c : R), Nat.Coprime s p ∧
          (s : K) * x = algebraMap R K c * (Matrix.of fun i j => B (b₀ i) (b j)).det := by
  have hcol : ∀ (s : ι → ℕ) (y : ι → V),
      (Matrix.of fun i j => B (b₀ i) ((s j : K) • y j)).det =
        ((∏ j, s j : ℕ) : K) * (Matrix.of fun i j => B (b₀ i) (y j)).det := by
    intro s y
    rw [Nat.cast_prod, ← Matrix.det_mul_row]
    congr 1
    ext i j
    simp
  refine ⟨Submodule.span R {d | ∃ y : ι → V, (∀ j, y j ∈ Y) ∧
    d = (Matrix.of fun i j => B (b₀ i) (y j)).det}, ?_, ?_⟩
  · choose s hs hsY using h0
    refine ⟨∏ i, s i, Finset.prod_pos fun i _ => hs i, ?_⟩
    intro x hx
    induction hx using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨y, hy, rfl⟩ := hd
      choose c hc using fun i j => hY (y j) (hy j) _ (hsY i)
      refine ⟨(Matrix.of c).det, ?_⟩
      rw [RingHom.map_det, Nat.cast_prod, ← Matrix.det_mul_column]
      congr 1
      ext i j
      simp [hc, hB]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, mul_left_comm]
      exact mul_mem ⟨a, rfl⟩ hx
  · intro p b h1 h2
    constructor
    · choose s hs hsY using h1
      refine ⟨∏ i, s i, Nat.Coprime.prod_left fun i _ => hs i, ?_⟩
      rw [← hcol]
      exact Submodule.subset_span ⟨_, hsY, rfl⟩
    · intro x hx
      induction hx using Submodule.span_induction with
      | mem d hd =>
        obtain ⟨y, hy, rfl⟩ := hd
        choose s hs c hc using fun j => h2 (y j) (hy j)
        refine ⟨∏ i, s i, (Matrix.of c).det, Nat.Coprime.prod_left fun i _ => hs i, ?_⟩
        rw [← hcol, RingHom.map_det, mul_comm, ← Matrix.det_transpose (RingHom.mapMatrix _ _),
          ← Matrix.det_mul]
        congr 1
        ext i j
        simp [hc, Matrix.mul_apply, mul_comm]
      | zero => exact ⟨1, 0, by simp, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, c, hs, hc⟩ := hx
        obtain ⟨t, d, ht, hd⟩ := hy
        refine ⟨s * t, t * c + s * d, Nat.Coprime.mul_left hs ht, ?_⟩
        simp only [Nat.cast_mul, map_add (f := _), map_mul, map_natCast]
        linear_combination (t : K) * hc + (s : K) * hd
      | smul a x _ hx =>
        obtain ⟨s, c, hs, hc⟩ := hx
        refine ⟨s, a * c, hs, ?_⟩
        rw [Algebra.smul_def, map_mul]
        linear_combination (algebraMap R K a) * hc

noncomputable def detIdealForm (D : D7) {N N' : ℕ} (y : Matrix (Fin N') (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.K] D.host.K where
  toFun x := hYY D x y
  map_add' x x' := by
    simp only [hYY, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)]
  map_smul' c x := by
    simp only [hYY, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, RingHom.id_apply]

theorem exists_detIdeal : ∀ (D : D7) (N N' r : ℕ) (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (b₀ : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ x ∈ Y, ∀ y ∈ Y, hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → (∀ i, ∃ s : ℕ, 0 < s ∧ (s : D.host.E) • b₀ i ∈ Y) → ∃ I : Submodule (𝓞 D.host.K) D.host.K, (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : D.host.K) * x ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) ∧ ∀ (p : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p Y b → (∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.K) * (Matrix.of fun i j => hYY D (b j) (b₀ i)).det ∈ I) ∧ ∀ x ∈ I, ∃ (s : ℕ) (c : 𝓞 D.host.K), Nat.Coprime s p ∧ (s : D.host.K) * x = (c : D.host.K) * (Matrix.of fun i j => hYY D (b j) (b₀ i)).det := by
  intro D N N' r Y b₀ hY h0
  have hsm : ∀ (s : ℕ) (y : Matrix (Fin N') (Fin N) D.host.E),
      (s : D.host.K) • y = (s : D.host.E) • y := by
    intro s y
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨I, hI1, hI2⟩ := exists_detIdeal_abstract (R := 𝓞 D.host.K) (K := D.host.K)
    (detIdealForm D) (by
      intro s y x
      change hYY D x _ = _ * hYY D x y
      rw [hsm, ← smul_eq_mul, hYY, hYY, ← map_smul, Nat.cast_smul_eq_nsmul D.host.K, nsmul_eq_mul]
      congr 1
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, Finset.mul_sum, mul_left_comm])
    (Y : Set (Matrix (Fin N') (Fin N) D.host.E)) b₀ hY (by simpa only [hsm, SetLike.mem_coe] using h0)
  refine ⟨I, hI1, fun p b hb => hI2 p b ?_ ?_⟩
  · simpa only [hsm, SetLike.mem_coe] using hb.2.1
  · intro y hy
    obtain ⟨s, hs, c, hc⟩ := hb.2.2 y hy
    exact ⟨s, hs, c, by rw [hsm, hc]; rfl⟩

end GlobalTheory.NormSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDvdMulInvolutionAddOne
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NegOneNorm

theorem exists_dvd_mul_involution_add_one {R : Type} [CommRing R] [IsDedekindDomain R] (s : R →+* R)
    (hs : ∀ x, s (s x) = x) (n : R) (hn : n ≠ 0) (hsn : s n = n)
    (hfin : ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P))
    (hne : ∀ P : Ideal R, P.IsMaximal → ∃ x, s x - x ∉ P)
    (h2 : ∀ P : Ideal R, P.IsMaximal → (∀ x ∈ P, s x ∈ P) → (2 : R) ∉ P) :
    ∃ l : R, n ∣ l * s l + 1 := by
  have hn' : Ideal.span {n} ≠ (⊥ : Ideal R) := by simpa using hn
  let S : Finset (Ideal R) := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {n})).toFinset
  have hS : ∀ P : Ideal R, P ∈ S ↔ P.IsPrime ∧ n ∈ P := fun P => by
    simp only [S, Multiset.mem_toFinset]
    rw [Ideal.mem_normalizedFactors_iff hn', Ideal.span_singleton_le_iff_mem]
  have hbot : ∀ P ∈ S, P ≠ ⊥ := fun P hP => by
    rintro rfl
    exact hn (by simpa using ((hS _).1 hP).2)
  have hpr : ∀ P ∈ S, Prime P := fun P hP => Ideal.prime_of_isPrime (hbot P hP) ((hS P).1 hP).1
  have hrad : ∏ P ∈ S, P ≤ (Ideal.span {n}).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro P ⟨h1, h3⟩
    exact Ideal.prod_le_inf.trans
      (Finset.inf_le (f := fun P => P) ((hS P).2 ⟨h3, (Ideal.span_singleton_le_iff_mem _).1 h1⟩))
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hcc : ∀ P : Ideal R, (P.comap s).comap s = P := fun P => by
    ext x; simp [Ideal.mem_comap, hs]
  have hz : ∀ P : Ideal R, ∃ z : R, P ∈ S → P.comap s = P → z * s z + 1 ∈ P ^ N := fun P => by
    by_cases h : P ∈ S ∧ P.comap s = P
    · obtain ⟨hP, hfix⟩ := h
      haveI hM : P.IsMaximal := ((hS P).1 hP).1.isMaximal (hbot P hP)
      haveI := hfin P hM
      have hsP : ∀ x ∈ P, s x ∈ P := fun x hx => by rwa [← hfix] at hx
      have : ∀ k : ℕ, ∃ z : R, k = 0 ∨ z * s z + 1 ∈ P ^ k := fun k => by
        induction k with
        | zero => exact ⟨0, Or.inl rfl⟩
        | succ k ih =>
          obtain ⟨z0, hz0⟩ := ih
          obtain ⟨z, hz, -⟩ := GlobalTheory.NormResidue.exists_mul_involution_add_one_mem_pow R s hs P hsP
            (hne P hM) (h2 P hM hsP) k z0 hz0
          exact ⟨z, Or.inr hz⟩
      obtain ⟨z, hz⟩ := this (N + 1)
      exact ⟨z, fun _ _ => Ideal.pow_le_pow_right (Nat.le_succ N) (hz.resolve_left (Nat.succ_ne_zero N))⟩
    · exact ⟨0, fun h1 h3 => (h ⟨h1, h3⟩).elim⟩
  choose z hz using hz
  let a : Ideal R → R := fun P =>
    if P.comap s = P then z P else if WellOrderingRel P (P.comap s) then 1 else -1
  have ha : ∀ P ∈ S, a P * s (a (P.comap s)) + 1 ∈ P ^ N := fun P hP => by
    by_cases hfix : P.comap s = P
    · simp only [a, hfix, if_true]
      exact hz P hP hfix
    · have hfix' : ¬ P = P.comap s := fun h => hfix h.symm
      simp only [a, hcc, if_neg hfix, if_neg hfix']
      rcases trichotomous_of WellOrderingRel P (P.comap s) with h | h | h
      · rw [if_pos h, if_neg (asymm h)]; simp
      · exact (hfix' h).elim
      · rw [if_pos h, if_neg (asymm h)]; simp
  obtain ⟨l, hl⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun P => P) (fun _ => N)
    hpr (fun _ _ _ _ h => h) (fun P => a P.1)
  have hmem : ∀ P ∈ S, l * s l + 1 ∈ P ^ N := fun P hP => by
    obtain ⟨h1, h3⟩ := (hS P).1 hP
    have hP' : P.comap s ∈ S := (hS _).2 ⟨Ideal.comap_isPrime s P, by rwa [Ideal.mem_comap, hsn]⟩
    have e1 : l - a P ∈ P ^ N := hl P hP
    have e2 : s (l - a (P.comap s)) ∈ P ^ N := Ideal.le_comap_pow s N (hl _ hP')
    have : l * s l + 1 = s l * (l - a P) + a P * s (l - a (P.comap s)) + (a P * s (a (P.comap s)) + 1) := by
      rw [map_sub]; ring
    rw [this]
    exact add_mem (add_mem (Ideal.mul_mem_left _ _ e1) (Ideal.mul_mem_left _ _ e2)) (ha P hP)
  refine ⟨l, Ideal.mem_span_singleton.1 (hN ?_)⟩
  rw [← Finset.prod_pow, ← IsDedekindDomain.inf_pow_eq_prod_of_prime S (fun P => P) (fun _ => N) hpr
    (fun _ _ _ _ h => h), Submodule.mem_finsetInf]
  exact hmem

theorem exists_norm_eq_neg_one : ∀ (D : D7) (m : ℕ), 0 < m → ∃ l b : 𝓞 D.host.E, (l : D.host.E) * D.host.conj (l : D.host.E) = -1 + (m : D.host.E) * (b : D.host.E) := by
  intro D m hm
  have hc : ∀ x, D.host.conj (D.host.conj x) = x := by
    obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    refine fun x => φ.injective ?_
    have h1 := D.host.conjE_apply φ
    exact (h1 _).trans ((congrArg _ (h1 x)).trans (Complex.conj_conj _))
  let s : 𝓞 D.host.E →+* 𝓞 D.host.E := (Formalism.L2.Pj.barE D).toRingHom
  have hs : ∀ x, ((s x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := Formalism.L2.Pj.barE_eq_conj D
  obtain ⟨l, b, hb⟩ := exists_dvd_mul_involution_add_one s
    (fun x => RingOfIntegers.ext (by rw [hs, hs, hc])) (m : 𝓞 D.host.E) (by exact_mod_cast hm.ne')
    (map_natCast s m)
    (fun P hP => Ideal.finiteQuotientOfFreeOfNeBot P
      (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)))
    (fun P hP => by
      obtain ⟨θ, hθ⟩ := Formalism.L2.Pj.cmUnram_conj D P hP
      exact ⟨θ, fun h => hθ (by
        have h' := P.neg_mem h
        rw [neg_sub] at h'
        exact h')⟩)
    (fun P hP hsP h2 => by
      have hw : s (Formalism.L2.Pj.w0E D) = 1 - Formalism.L2.Pj.w0E D := Formalism.L2.Pj.conj_w0E D
      have hsq := Formalism.L2.Pj.w0E_sq D
      obtain ⟨k, hk⟩ : ∃ k, Formalism.L2.Pj.mE D = 2 * k := by
        have h1 := D.host.hyp.2.2.2.1
        have h3 := Formalism.L2.Pj.mE_spec D
        exact ⟨Formalism.L2.Pj.mE D / 2, by omega⟩
      rw [hk] at hsq
      push_cast at hsq
      set w := Formalism.L2.Pj.w0E D
      have hm : w * (1 - w) ∈ P := by
        have : w * (1 - w) = k * 2 := by linear_combination -hsq
        rw [this]; exact P.mul_mem_left _ h2
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      rcases hP.isPrime.mem_or_mem hm with h | h
      · have h' := hsP _ h
        rw [hw] at h'
        simpa using P.add_mem h h'
      · have h' := hsP _ h
        rw [map_sub, map_one, hw] at h'
        simpa using P.add_mem h h')
  refine ⟨l, b, ?_⟩
  have := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hb
  simp only [map_add (f := _), map_mul, map_one, map_natCast] at this
  rw [← hs]
  linear_combination this

end GlobalTheory.NegOneNorm
end

