module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfNear
section
namespace UpperTheory.Reformulated.B.S7

theorem eq_one_of_near {l : ℕ} [Fact l.Prime] {u : PadicAlgCl l} {m : ℕ} (hm : ¬ l ∣ m) (hu : u ^ m = 1)
    (h : ‖u - 1‖ < 1) : u = 1 := by
  by_contra hne
  have hu1 : ‖u‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (u - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le h.le le_rfl)
  have hpow : ∀ i : ℕ, ‖u ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : u ^ (i + 1) - 1 = (u ^ i - 1) * u + (u - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h)
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hu1).trans_lt ih
  have hsum : ∀ n : ℕ, ‖(∑ i ∈ Finset.range n, u ^ i) - (n : PadicAlgCl l)‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : PadicAlgCl l)
          = ((∑ i ∈ Finset.range n, u ^ i) - (n : PadicAlgCl l)) + (u ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (hpow n))
  have h0 : (∑ i ∈ Finset.range m, u ^ i) = 0 := by
    have := geom_sum_mul u m
    rw [hu, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hlt := hsum m
  rw [h0, zero_sub, norm_neg] at hlt
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := by simp
  rw [e, norm_algebraMap'] at hlt
  exact hm (Padic.norm_natCast_lt_one_iff.mp hlt)

end UpperTheory.Reformulated.B.S7
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfPowNear
section
theorem UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near :
    ∀ (z : ℂ),
    (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have step : ∀ n : ℕ, (3 / 2 : ℝ) * ‖z ^ n - 1‖ ≤ ‖z ^ (n * 2) - 1‖ := by
    intro n
    have e : z ^ (n * 2) - 1 = (z ^ n + 1) * (z ^ n - 1) := by ring
    have h1 : ‖(2 : ℂ)‖ ≤ ‖z ^ n + 1‖ + ‖z ^ n - 1‖ := by
      have e2 : (2 : ℂ) = (z ^ n + 1) - (z ^ n - 1) := by ring
      calc ‖(2 : ℂ)‖ = ‖(z ^ n + 1) - (z ^ n - 1)‖ := congrArg _ e2
        _ ≤ _ := norm_sub_le _ _
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have h3 := h n
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have grow : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have s := step (2 ^ k)
      rw [pow_succ, pow_succ]
      linarith
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ hpos] at hk
  have g := grow k
  have h4 := h (2 ^ k)
  linarith
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqZeroOfAevalEqZero
section
noncomputable def UpperTheory.Reformulated.B.G8.kry :
    {R : Type} → [CommRing R] → {n : ℕ} → Matrix (Fin n) (Fin n) R → (Fin n → R) → Matrix (Fin n) (Fin n) R :=
    fun {R : Type} [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦ (g ^ (↑j : ℕ)).mulVec v i

open Polynomial in
private theorem UpperTheory.Reformulated.B.G8.eq_zero_of_aeval_eq_zero {K : Type} [Field K] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : g.charpoly.Separable) (p : K[X])
    (hp : p.degree < n) (h0 : aeval g p = 0) : p = 0 := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hp
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let L := AlgebraicClosure K
  let f : K →+* L := algebraMap K L
  let G : Matrix (Fin n) (Fin n) L := g.map f
  have hG : G.charpoly.Separable := by
    rw [Matrix.charpoly_map]
    exact hg.map
  have hG0 : aeval G (p.map f) = 0 := by
    have h1 := congrArg (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId K L)) h0
    rw [map_zero, ← aeval_algHom_apply] at h1
    rw [aeval_map_algebraMap]
    exact h1
  have hcard : G.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hG), ← (IsAlgClosed.splits G.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hz : p.map f = 0 := by
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero G.charpoly.roots.toFinset ?_ ?_
    · rw [hcard, degree_map]
      exact hp
    · intro x hx
      have hx' : x ∈ spectrum L G :=
        Matrix.mem_spectrum_of_isRoot_charpoly (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx))
      have h2 := spectrum.subset_polynomial_aeval G (p.map f) ⟨x, hx', rfl⟩
      rw [hG0, spectrum.zero_eq] at h2
      exact h2
  exact (Polynomial.map_eq_zero_iff f.injective).mp hz

open Polynomial in
private theorem UpperTheory.Reformulated.B.G8.exists_kry_field {K : Type} [Field K] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : g.charpoly.Separable) :
    ∃ v : Fin n → K, (UpperTheory.Reformulated.B.G8.kry g v).det ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X]
    (Module.AEval K (Fin n → K) g)
  obtain ⟨v, rfl⟩ := (Module.AEval.of K (Fin n → K) g).surjective x
  refine ⟨v, fun hdet => ?_⟩
  obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : K[X] := ∑ j : Fin n, C (c j) * X ^ (j : ℕ)
  have hdeg : p.degree < n := degree_sum_fin_lt c
  have hv : aeval g p • v = 0 := by
    rw [← hc0]
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [p, map_sum, map_mul, aeval_C, map_pow, aeval_X, Finset.sum_smul, Finset.sum_apply,
      ← Algebra.smul_def, smul_assoc, Pi.smul_apply, smul_eq_mul, Matrix.smul_eq_mulVec]
    simp only [UpperTheory.Reformulated.B.G8.kry, Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hker : p ∈ Module.annihilator K[X] (Module.AEval K (Fin n → K) g) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Module.AEval.of_aeval_smul,
      hv, map_zero]
  have hp0 : aeval g p = 0 := by
    refine Matrix.ext_iff_mulVec.mpr fun w => ?_
    have h1 := Module.mem_annihilator.mp hker (Module.AEval.of K (Fin n → K) g w)
    rw [← Module.AEval.of_aeval_smul, map_eq_zero_iff _ (LinearEquiv.injective _)] at h1
    rw [Matrix.zero_mulVec]
    exact h1
  have hp : p = 0 := UpperTheory.Reformulated.B.G8.eq_zero_of_aeval_eq_zero g hg p hdeg hp0
  apply hc
  ext j
  have h1 := congrArg (fun q => q.coeff j) hp
  simpa [p, finsetSum_coeff, coeff_X_pow, Fin.val_inj] using h1

private theorem UpperTheory.Reformulated.B.G8.kry_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S)
    (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    f (UpperTheory.Reformulated.B.G8.kry g v).det = (UpperTheory.Reformulated.B.G8.kry (g.map f) (f ∘ v)).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [UpperTheory.Reformulated.B.G8.kry, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec, Matrix.map_pow]

theorem UpperTheory.Reformulated.B.G8.exists_kry :
    ∀ {R : Type} [inst : CommRing R] [Finite (MaximalSpectrum R)] {n : ℕ} (g : Matrix (Fin n) (Fin n) R),
      g.charpoly.Separable → ∃ (v : Fin n → R), IsUnit (UpperTheory.Reformulated.B.G8.kry g v).det := by
  intro R _ _ n g hg
  have h1 : ∀ m : MaximalSpectrum R, ∃ w : Fin n → R ⧸ m.asIdeal,
      (UpperTheory.Reformulated.B.G8.kry (g.map (Ideal.Quotient.mk m.asIdeal)) w).det ≠ 0 := by
    intro m
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    refine UpperTheory.Reformulated.B.G8.exists_kry_field _ ?_
    rw [Matrix.charpoly_map]
    exact hg.map
  choose w hw using h1
  have hco : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum R => m.asIdeal) := by
    intro a b hab
    exact Ideal.isCoprime_iff_sup_eq.mpr
      (a.isMaximal.coprime_of_ne b.isMaximal fun h => hab (MaximalSpectrum.ext h))
  choose v hv using fun i : Fin n => Ideal.pi_quotient_surjective hco fun m => w m i
  refine ⟨v, ?_⟩
  by_contra hu
  obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  apply hw ⟨M, hM⟩
  have h2 : w ⟨M, hM⟩ = Ideal.Quotient.mk M ∘ v := funext fun i => (hv i ⟨M, hM⟩).symm
  rw [h2, ← UpperTheory.Reformulated.B.G8.kry_map]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvDecomp
section
theorem UpperTheory.Reformulated.B.Qf39.ev_decomp :
    ∀ {O σ : Type} [inst : CommRing O] [inst_1 : Fintype σ]
    (f : MvPowerSeries σ O),
    ∃ (h : σ → MvPowerSeries σ O),
      f =
          (MvPowerSeries.C : O → MvPowerSeries σ O) ((MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) f) +
            ∑ i : σ, MvPowerSeries.X i * h i ∧
        ∀ (i : σ),
          (MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) (h i) =
            (MvPowerSeries.coeff fun₀ | i => (1 : ℕ) : MvPowerSeries σ O → O) f := by
  intro O σ _ _ f
  classical
  have key : ∀ m : σ →₀ ℕ, ∃ o : Option σ,
      (m ≠ 0 → ∃ j, o = some j) ∧ ∀ j, o = some j → m j ≠ 0 := by
    intro m
    by_cases hm : m = 0
    · exact ⟨none, fun h => (h hm).elim, fun j hj => by cases hj⟩
    · obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 hm
      refine ⟨some j, fun _ => ⟨j, rfl⟩, fun k hk => ?_⟩
      cases hk
      simpa using hj
  choose c hc₁ hc₂ using key
  let h : σ → MvPowerSeries σ O := fun i m =>
    if c (m + Finsupp.single i 1) = some i then
      MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0
  have hh : ∀ i m, MvPowerSeries.coeff m (h i) =
      if c (m + Finsupp.single i 1) = some i then
        MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0 := fun _ _ => rfl
  have hX : ∀ i m, MvPowerSeries.coeff m (MvPowerSeries.X i * h i) =
      if c m = some i then MvPowerSeries.coeff m f else 0 := by
    intro i m
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
    by_cases hle : Finsupp.single i 1 ≤ m
    · rw [if_pos hle, hh, tsub_add_cancel_of_le hle]
    · rw [if_neg hle, if_neg]
      intro hi
      exact hle (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (hc₂ m i hi)))
  refine ⟨h, ?_, fun i => ?_⟩
  · ext m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, MvPowerSeries.coeff_C]
    simp only [hX]
    by_cases hm : m = 0
    · subst hm
      have : ∀ i, ¬ c 0 = some i := fun i hi => hc₂ 0 i hi rfl
      simp [this]
    · obtain ⟨j, hj⟩ := hc₁ m hm
      simp [hm, hj]
  · have hne : (Finsupp.single i 1 : σ →₀ ℕ) ≠ 0 := by simp
    obtain ⟨j, hj⟩ := hc₁ _ hne
    have hji : j = i := by
      by_contra hji
      exact hc₂ _ j hj (Finsupp.single_eq_of_ne hji)
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh, zero_add, if_pos (hji ▸ hj)]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalDet
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi25.UG :
    ℕ → Type :=
    fun (N : ℕ) ↦ ↥(Matrix.unitaryGroup (Fin N) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qi25.ent :
    {N : ℕ} → UpperTheory.Reformulated.B.Qi25.UG N → Fin N × Fin N → ℂ :=
    fun {N : ℕ} (g : UpperTheory.Reformulated.B.Qi25.UG N) (ij : Fin N × Fin N) ↦ (↑g : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2

noncomputable def UpperTheory.Reformulated.B.Qi25.IsPD :
    {N : ℕ} → (UpperTheory.Reformulated.B.Qi25.UG N → ℂ) → Prop :=
    fun {N : ℕ} (f : UpperTheory.Reformulated.B.Qi25.UG N → ℂ) ↦
      ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ),
        ∀ (g : UpperTheory.Reformulated.B.Qi25.UG N),
          f g * (↑g : Matrix (Fin N) (Fin N) ℂ).det ^ k =
            (MvPolynomial.eval (UpperTheory.Reformulated.B.Qi25.ent g) : MvPolynomial (Fin N × Fin N) ℂ → ℂ) P

private theorem UpperTheory.Reformulated.B.Qi25.eval_det {N : ℕ} (g : UpperTheory.Reformulated.B.Qi25.UG N) :
    MvPolynomial.eval (UpperTheory.Reformulated.B.Qi25.ent g)
        (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det =
      (↑g : Matrix (Fin N) (Fin N) ℂ).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [UpperTheory.Reformulated.B.Qi25.ent]

theorem UpperTheory.Reformulated.B.Qi25.sum.{u_1} :
    ∀ {N : ℕ} {ι : Type u_1} (s : Finset ι) {F : ι → UpperTheory.Reformulated.B.Qi25.UG N → ℂ},
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi25.IsPD (F i)) → UpperTheory.Reformulated.B.Qi25.IsPD fun (g : UpperTheory.Reformulated.B.Qi25.UG N) ↦ ∑ i ∈ s, F i g := by
  intro N ι s F
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, 0, fun g ↦ by simp⟩
  | insert a s ha ih =>
    intro h
    obtain ⟨k, P, hP⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨l, Q, hQ⟩ := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    refine ⟨k + l,
      P * (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det ^ l
        + Q * (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det ^ k,
      fun g ↦ ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, UpperTheory.Reformulated.B.Qi25.eval_det, ← hP g, ← hQ g]
    simp only [Finset.sum_insert ha]
    ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalFg
section
theorem UpperTheory.Reformulated.B.Qn15.eval_fg :
    ∀ {R : Type} [inst : CommRing R] [inst_1 : Algebra R ℂ] {σ : Type} {M₀ : Submodule R ℂ},
    M₀.FG →
      ∀ (P : MvPolynomial σ ℂ),
        ∃ (M : Submodule R ℂ),
          M.FG ∧ ∀ (v : σ → ℂ), (∀ (i : σ), v i ∈ M₀) → (MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) P ∈ M := by
  intro R _ _ σ M₀ h₀ P
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Submodule.span R {a}, Submodule.fg_span_singleton a, fun v _ => ?_⟩
    rw [MvPolynomial.eval_C]
    exact Submodule.mem_span_singleton_self a
  | add p q hp hq =>
    obtain ⟨M, hM, hp⟩ := hp
    obtain ⟨N, hN, hq⟩ := hq
    refine ⟨M ⊔ N, hM.sup hN, fun v hv => ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hp v hv) (hq v hv)
  | mul_X p i hp =>
    obtain ⟨M, hM, hp⟩ := hp
    refine ⟨M * M₀, hM.mul h₀, fun v hv => ?_⟩
    rw [map_mul, MvPolynomial.eval_X]
    exact Submodule.mul_mem_mul (hp v hv) (hv i)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalProd
section
namespace UpperTheory.Reformulated.B.Gr23

open Polynomial

private theorem eval_prod (m : Multiset ℂ) (u : ℂ) :
    ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod.eval u
      = (m.map (fun x : ℂ ↦ u + x)).prod := by
  rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun x _ ↦ ?_
  simp

private theorem eq_of_prod_eq {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (fun x : ℂ ↦ u + x)).prod = (m'.map (fun x : ℂ ↦ u + x)).prod) :
    m = m' := by
  have hp : ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod
      = ((m'.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod := by
    refine Polynomial.funext fun u ↦ ?_
    rw [eval_prod, eval_prod, h u]
  have hr := congrArg Polynomial.roots hp
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

theorem abs {M : Type*} [AddCommGroup M] [Module ℂ M] {V : Submodule ℂ M} (hV : V ≠ ⊥)
    (T : ℂ → Module.End ℂ M) {a : ℕ} {m m' : Multiset ℂ}
    (h : m.card = a ∧ ∀ (u : ℂ), ∀ φ ∈ V,
      (T u) φ = (Multiset.map (fun (x : ℂ) ↦ u + x) m).prod • φ)
    (h' : m'.card = a ∧ ∀ (u : ℂ), ∀ φ ∈ V,
      (T u) φ = (Multiset.map (fun (x : ℂ) ↦ u + x) m').prod • φ) :
    m = m' := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  refine eq_of_prod_eq fun u ↦ ?_
  exact smul_left_injective ℂ hφ0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))

end UpperTheory.Reformulated.B.Gr23
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalSmulOfIsHomogeneous
section
theorem UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous :
    ∀ {σ : Type} [Fintype σ] {h : MvPolynomial σ ℂ} {d : ℕ},
      h.IsHomogeneous d →
        ∀ (t : ℂ) (v : σ → ℂ),
          (MvPolynomial.eval (t • v) : MvPolynomial σ ℂ → ℂ) h = t ^ d * (MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) h := by
  intro σ _ h d hh t v
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have h1 := hh (MvPolynomial.mem_support_iff.mp hm)
    rw [← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalSmulOfIsHomogeneousAlt
section
theorem UpperTheory.Reformulated.B.Ydc1.eval_smul_of_isHomogeneous.{u_1} :
    ∀ {τ : Type u_1} {φ : MvPolynomial τ ℂ} {n : ℕ},
      φ.IsHomogeneous n →
        ∀ (c : ℂ) (w : τ → ℂ),
          (MvPolynomial.eval (c • w) : MvPolynomial τ ℂ → ℂ) φ = c ^ n * (MvPolynomial.eval w : MvPolynomial τ ℂ → ℂ) φ := by
  intro τ φ n hφ c w
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hφ (MvPolynomial.mem_support_iff.mp hd)
    rw [← h, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvaluationMap
section
noncomputable def UpperTheory.Reformulated.B.EvaluationMap.coeffSpan :
    {K W : Type} →
      [inst : Group K] →
        [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module ℂ W] → Representation ℂ K W → Submodule ℂ (K → ℂ) :=
    fun {K W : Type} [Group K] [AddCommGroup W] [_root_.Module ℂ W] (ρ : Representation ℂ K W) ↦
      Submodule.span ℂ
        {f : K → ℂ | ∃ (ℓ : Module.Dual ℂ W) (w : W), f = fun (k : K) ↦ (ℓ : W → ℂ) (((ρ : K → W →ₗ[ℂ] W) k : W → W) w)}

namespace UpperTheory.Reformulated.B.EvaluationMap.Helpers

private noncomputable def Φ {K W : Type} [Group K] [AddCommGroup W] [_root_.Module ℂ W]
    (ρ : Representation ℂ K W) : Module.Dual ℂ (W →ₗ[ℂ] W) →ₗ[ℂ] (K → ℂ) where
  toFun φ := fun k => φ (ρ k)
  map_add' φ ψ := by funext k; simp
  map_smul' c φ := by funext k; simp

private noncomputable def evw {W : Type} [AddCommGroup W] [_root_.Module ℂ W]
    (ℓ : Module.Dual ℂ W) (w : W) : Module.Dual ℂ (W →ₗ[ℂ] W) where
  toFun A := ℓ (A w)
  map_add' A B := by simp
  map_smul' c A := by simp

end UpperTheory.Reformulated.B.EvaluationMap.Helpers

open UpperTheory.Reformulated.B.EvaluationMap.Helpers in
theorem UpperTheory.Reformulated.B.EvaluationMap.main :
    ∀ {K W : Type} [inst : Group K] [inst_1 : AddCommGroup W] [inst_2 : _root_.Module ℂ W] [FiniteDimensional ℂ W]
      (ρ : Representation ℂ K W), FiniteDimensional ℂ ↥(UpperTheory.Reformulated.B.EvaluationMap.coeffSpan ρ) := by
  intro K W _ _ _ _ ρ
  have hle : UpperTheory.Reformulated.B.EvaluationMap.coeffSpan ρ ≤ LinearMap.range (Φ ρ) := by
    unfold UpperTheory.Reformulated.B.EvaluationMap.coeffSpan
    rw [Submodule.span_le]
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨evw ℓ w, rfl⟩
  exact Submodule.finiteDimensional_of_le hle
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsBoundPolyMulExp
section
theorem UpperTheory.Reformulated.B.Rc4.exists_bound_poly_mul_exp :
    ∀ (c : ℝ),
    (0 : ℝ) < c →
      ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r → ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by
  intro c hc N
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * c)), fun r hr => ?_⟩
  have h1 : (1 + r) ^ N ≤ Real.exp r ^ N := by
    apply pow_le_pow_left₀ (by linarith)
    linarith [Real.add_one_le_exp r]
  have h2 : (N : ℝ) * r + -(c * r ^ 2) ≤ (N : ℝ) ^ 2 / (4 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((N : ℝ) - 2 * c * r)]
  calc (1 + r) ^ N * Real.exp (-(c * r ^ 2))
      ≤ Real.exp r ^ N * Real.exp (-(c * r ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * r + -(c * r ^ 2)) := by
        rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * c)) := Real.exp_le_exp.mpr h2
end

