module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0005
public import Formalism.PeriodIntegrals.Bundle0006

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EmbTraceSum
section
theorem sumEqTrace_holds : PI.EmbTraceSum := by
  intro E _ _ K φ₀ S _ emb hinj hext hcard y
  let _ : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  have hcomm : ∀ (s : S) (a : K), emb s (algebraMap K E a) = algebraMap K ℂ a := fun s a => hext s a
  let f : S → (E →ₐ[K] ℂ) := fun s => { emb s with commutes' := hcomm s }
  have hf : Function.Injective f := by
    intro s t hst
    apply hinj
    ext x
    exact AlgHom.congr_fun hst x
  have : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  have hcard' : Fintype.card S = Fintype.card (E →ₐ[K] ℂ) := by
    rw [hcard, AlgHom.card]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard'⟩
  have htr := trace_eq_sum_embeddings (K := K) (L := E) (E := ℂ) (x := y)
  calc ∑ s, emb s y = ∑ s, f s y := rfl
    _ = ∑ σ : E →ₐ[K] ℂ, σ y := Fintype.sum_bijective f hbij _ _ (fun _ => rfl)
    _ = algebraMap K ℂ (Algebra.trace K E y) := htr.symm
    _ = φ₀ ((Algebra.trace K E y : K) : E) := rfl
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormGramAtOrigin
section
private lemma hform_add_right_orbital_bounds_conclusion {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    PI.NormGramAtOrigin.hform σ J x (y + z) = PI.NormGramAtOrigin.hform σ J x y + PI.NormGramAtOrigin.hform σ J x z := by
  simp only [PI.NormGramAtOrigin.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma hform_smul_right_orbital_bounds_conclusion {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : E) :
    PI.NormGramAtOrigin.hform σ J x (c • y) = c * PI.NormGramAtOrigin.hform σ J x y := by
  simp only [PI.NormGramAtOrigin.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma hform_sum_right' {E : Type} [Field E] (σ : E →+* E) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (f : Fin k → Fin n → E) :
    PI.NormGramAtOrigin.hform σ J x (∑ a, f a) = ∑ a, PI.NormGramAtOrigin.hform σ J x (f a) := by
  simp only [PI.NormGramAtOrigin.hform, Finset.sum_apply, Finset.mul_sum]
  calc _ = ∑ i, ∑ a, ∑ j, σ (x i) * J i j * f a j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

private lemma Hf_sub_right' {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    PI.NormGramAtOrigin.hform σ J x (y - z) = PI.NormGramAtOrigin.hform σ J x y - PI.NormGramAtOrigin.hform σ J x z := by
  simp only [PI.NormGramAtOrigin.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma hform_symm_of_involutive_of_hermitian {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (PI.NormGramAtOrigin.hform σ J x y) = PI.NormGramAtOrigin.hform σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PI.NormGramAtOrigin.hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hJ j i]; ring

private lemma hform_add_smul_self_ne_zero_of_isotropic_pair {E : Type} [Field E] [CharZero E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (w y : Fin n → E)
    (hw : PI.NormGramAtOrigin.hform σ J w w = 0) (hy : PI.NormGramAtOrigin.hform σ J y y = 0) (t : E)
    (ht : PI.NormGramAtOrigin.hform σ J w y = t) (ht0 : t ≠ 0) :
    PI.NormGramAtOrigin.hform σ J (w + σ t • y) (w + σ t • y) ≠ 0 := by
  have e1 : PI.NormGramAtOrigin.hform σ J w (w + σ t • y) = σ t * t := by
    rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, hw, ht, zero_add]
  have e2 : PI.NormGramAtOrigin.hform σ J y w = σ t := by
    rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ w y, ht]
  have e3 : PI.NormGramAtOrigin.hform σ J y (w + σ t • y) = σ t := by
    rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, hy, e2, mul_zero, add_zero]
  have e4 : PI.NormGramAtOrigin.hform σ J (w + σ t • y) w = t * σ t := by
    rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ w, e1, map_mul, hσ]
  have e5 : PI.NormGramAtOrigin.hform σ J (w + σ t • y) y = t := by
    rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ y, e3, hσ]
  rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, e4, e5]
  have hs : σ t ≠ 0 := by
    intro h
    apply ht0
    rw [← hσ t, h, map_zero]
  have e6 : t * σ t + σ t * t = 2 * (t * σ t) := by ring
  rw [e6]
  exact mul_ne_zero two_ne_zero (mul_ne_zero ht0 hs)

private lemma exists_ne_zero_mulVec_eq_zero_of_lt {E : Type} [Field E] {k n : ℕ} (hk : k < n) (A : Fin k → Fin n → E) :
    ∃ y : Fin n → E, y ≠ 0 ∧ ∀ a, ∑ j, A a j * y j = 0 := by
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    (Matrix.det_eq_zero_of_row_eq_zero
      (A := Matrix.of fun (i j : Fin n) => if h : (i : ℕ) < k then A ⟨i, h⟩ j else 0)
      ⟨k, hk⟩ (fun j => by simp))
  refine ⟨y, hy0, fun a => ?_⟩
  have h := congrFun hy ⟨a, lt_trans a.isLt hk⟩
  simpa [Matrix.mulVec, dotProduct] using h

private lemma exists_hform_ne_zero_of_det_ne_zero {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJd : J.det ≠ 0) (y : Fin n → E) (hy : y ≠ 0) :
    ∃ z : Fin n → E, PI.NormGramAtOrigin.hform σ J z y ≠ 0 := by
  have hJy : Matrix.mulVec J y ≠ 0 := fun h => hJd (Matrix.exists_mulVec_eq_zero_iff.mp ⟨y, hy, h⟩)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hJy
  refine ⟨Pi.single i 1, ?_⟩
  have e : PI.NormGramAtOrigin.hform σ J (Pi.single i 1) y = Matrix.mulVec J y i := by
    unfold PI.NormGramAtOrigin.hform
    rw [Finset.sum_eq_single i]
    · simp [Matrix.mulVec, dotProduct]
    · intro l _ hl
      simp [Pi.single_apply, hl]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [e]
  exact hi

private lemma hermC_ppos_col_castLE {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (v : Fin k → Fin n → E)
    (hvo : ∀ a b, a ≠ b → PI.NormGramAtOrigin.hform σ J (v a) (v b) = 0)
    (hvd : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) (v a) ≠ 0) (z y0 : Fin n → E)
    (hy0W : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) y0 = 0) (hz : PI.NormGramAtOrigin.hform σ J z y0 ≠ 0) :
    ∃ p : Fin n → E, (∀ b, PI.NormGramAtOrigin.hform σ J (v b) p = 0) ∧ PI.NormGramAtOrigin.hform σ J p y0 ≠ 0 := by
  refine ⟨z - ∑ a, (PI.NormGramAtOrigin.hform σ J (v a) z / PI.NormGramAtOrigin.hform σ J (v a) (v a)) • v a,
    fun b => ?_, ?_⟩
  · rw [Hf_sub_right', hform_sum_right', Finset.sum_eq_single b]
    · rw [hform_smul_right_orbital_bounds_conclusion, div_mul_cancel₀ _ (hvd b), sub_self]
    · intro a _ hab
      rw [hform_smul_right_orbital_bounds_conclusion, hvo b a (Ne.symm hab), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ b) h
  · rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ y0, Hf_sub_right', hform_sum_right']
    have h0 : ∀ a, PI.NormGramAtOrigin.hform σ J y0
        ((PI.NormGramAtOrigin.hform σ J (v a) z / PI.NormGramAtOrigin.hform σ J (v a) (v a)) • v a) = 0 := by
      intro a
      rw [hform_smul_right_orbital_bounds_conclusion, ← hform_symm_of_involutive_of_hermitian σ hσ J hJ (v a) y0, hy0W a, map_zero, mul_zero]
    simp only [h0, Finset.sum_const_zero, sub_zero]
    rw [hform_symm_of_involutive_of_hermitian σ hσ J hJ]
    exact hz

private lemma Hf_e_e_eq_ite {E : Type} [Field E] [CharZero E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (hJd : J.det ≠ 0) :
    ∀ k, k ≤ n → ∃ v : Fin k → Fin n → E,
      (∀ a b, a ≠ b → PI.NormGramAtOrigin.hform σ J (v a) (v b) = 0) ∧
      ∀ a, PI.NormGramAtOrigin.hform σ J (v a) (v a) ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, hvo, hvd⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨y0, hy0, hW0⟩ := exists_ne_zero_mulVec_eq_zero_of_lt (Nat.lt_of_succ_le hk) (fun a j => ∑ l, σ (v a l) * J l j)
    have hy0W : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) y0 = 0 := by
      intro a
      calc _ = ∑ j, (∑ l, σ (v a l) * J l j) * y0 j := by
            simp only [PI.NormGramAtOrigin.hform, Finset.sum_mul]
            exact Finset.sum_comm
        _ = 0 := hW0 a
    obtain ⟨z, hz⟩ := exists_hform_ne_zero_of_det_ne_zero σ J hJd y0 hy0
    obtain ⟨p, hpW, hp⟩ := hermC_ppos_col_castLE σ hσ J hJ v hvo hvd z y0 hy0W hz
    have key : ∃ y, (∀ a, PI.NormGramAtOrigin.hform σ J (v a) y = 0) ∧
        PI.NormGramAtOrigin.hform σ J y y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      refine hform_add_smul_self_ne_zero_of_isotropic_pair σ hσ J hJ p y0 (hcon p hpW) (hcon y0 hy0W) _ rfl hp (hcon _ fun a => ?_)
      rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, hpW a, hy0W a, mul_zero, add_zero]
    obtain ⟨y, hyW, hyy⟩ := key
    refine ⟨Fin.snoc (α := fun _ => Fin n → E) v y, fun a b hab => ?_, fun a => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hvo a b fun h => hab (congrArg Fin.castSucc h)
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hyW a
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ, hyW b, map_zero]
      · exact absurd rfl hab
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hvd a
      · simp only [Fin.snoc_last]
        exact hyy

theorem exists_nondegenerate : PI.NormGramAtOrigin.Statement := by
  unfold PI.NormGramAtOrigin.Statement
  intro E _ _ _ n r hr J hJ hJd
  have hσ : ∀ a : E, starRingEnd E (starRingEnd E a) = a := fun a => by simp
  have hJ' : ∀ i j, starRingEnd E (J j i) = J i j := fun i j => by
    rw [starRingEnd_apply]
    exact hJ i j
  obtain ⟨v, hvo, hvd⟩ := Hf_e_e_eq_ite (starRingEnd E) hσ J hJ' hJd r hr
  refine ⟨v, ?_⟩
  have hg : PI.NormGramAtOrigin.gram (starRingEnd E) J v =
      Matrix.diagonal (fun a => PI.NormGramAtOrigin.hform (starRingEnd E) J (v a) (v a)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp [PI.NormGramAtOrigin.gram]
    · simp [PI.NormGramAtOrigin.gram, Matrix.diagonal_apply_ne _ h, hvo a b h]
  rw [hg, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => hvd a
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormLimit
section
private theorem coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero {K : Type*} [CommRing K] (a : MvPowerSeries Unit K)
    (ha : MvPowerSeries.constantCoeff a = 0) :
    ∀ (d : ℕ) (e : Unit →₀ ℕ), e () < d → MvPowerSeries.coeff e (a ^ d) = 0 := by
  intro d
  induction d with
  | zero => intro e he; exact absurd he (Nat.not_lt_zero _)
  | succ d ih =>
    intro e he
    rw [pow_succ, MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    have hsum : x.1 () + x.2 () = e () := by
      rw [← Finsupp.add_apply, Finset.HasAntidiagonal.mem_antidiagonal.mp hx]
    by_cases h0 : x.2 () = 0
    · have hx2 : x.2 = 0 := by
        ext
        simpa using h0
      rw [hx2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ha, mul_zero]
    · rw [ih x.1 (by omega), zero_mul]

private theorem coeff_subst_eq_sum_range_coeff_mul_coeff_pow {K : Type*} [CommRing K] (f : PowerSeries K)
    (a : MvPowerSeries Unit K) (ha : MvPowerSeries.constantCoeff a = 0) (e : Unit →₀ ℕ) :
    MvPowerSeries.coeff e (PowerSeries.subst a f) =
      ∑ d ∈ Finset.range (e () + 1), PowerSeries.coeff d f • MvPowerSeries.coeff e (a ^ d) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Function.mem_support, ne_eq] at hd
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hn
  exact hd (by rw [coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero a ha d e (by omega), smul_zero])

private theorem constantCoeff_subst_of_constantCoeff_eq_zero_orbital_bounds_conclusion {K : Type*} [CommRing K] (f : PowerSeries K)
    (a : MvPowerSeries Unit K) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst_eq_sum_range_coeff_mul_coeff_pow f a ha 0]
  simp

private theorem continuous_coeff_pow_of_continuous_coeff {K Y : Type*} [NormedField K] [TopologicalSpace Y]
    (F : Y → MvPowerSeries Unit K) (hF : ∀ e, Continuous fun y => MvPowerSeries.coeff e (F y)) :
    ∀ (n : ℕ) (e : Unit →₀ ℕ), Continuous fun y => MvPowerSeries.coeff e (F y ^ n) := by
  intro n
  induction n with
  | zero =>
    intro e
    simp only [pow_zero]
    exact continuous_const
  | succ n ih =>
    intro e
    simp only [pow_succ, MvPowerSeries.coeff_mul]
    exact continuous_finsetSum _ fun x _ => (ih x.1).mul (hF x.2)

private theorem continuous_coeff_subst_of_continuous_coeff {K Y : Type*} [NormedField K] [TopologicalSpace Y]
    (f : PowerSeries K) (a : Y → MvPowerSeries Unit K)
    (ha : ∀ y, MvPowerSeries.constantCoeff (a y) = 0)
    (hc : ∀ e, Continuous fun y => MvPowerSeries.coeff e (a y)) :
    ∀ e, Continuous fun y => MvPowerSeries.coeff e (PowerSeries.subst (a y) f) := by
  intro e
  have h : (fun y => MvPowerSeries.coeff e (PowerSeries.subst (a y) f)) =
      fun y => ∑ d ∈ Finset.range (e () + 1),
        PowerSeries.coeff d f • MvPowerSeries.coeff e (a y ^ d) :=
    funext fun y => coeff_subst_eq_sum_range_coeff_mul_coeff_pow f (a y) (ha y) e
  rw [h]
  exact continuous_finsetSum _ fun d _ =>
    Continuous.smul (f := fun _ => PowerSeries.coeff d f) continuous_const (continuous_coeff_pow_of_continuous_coeff a hc d e)

private theorem forall_mem_closure_of_isClosed_setOf {Y : Type*} [TopologicalSpace Y] (T : Set Y) (P : Y → Prop)
    (hc : IsClosed {y | P y}) (h : ∀ y ∈ T, P y) : ∀ y ∈ closure T, P y :=
  fun _ hy => closure_minimal h hc hy

private theorem isClosed_setOf_coeff_exp_norm_le_one {K Y : Type*} [NormedField K] [TopologicalSpace Y]
    (F G : Y → MvPowerSeries Unit K) (hF : ∀ e, Continuous fun y => MvPowerSeries.coeff e (F y))
    (hG : ∀ (n : Unit →₀ ℕ) (y : Y), MvPowerSeries.coeff n (G y) =
      ∑ k ∈ Finset.range ((n.sum fun _ k => k) + 1),
        MvPowerSeries.coeff n (F y ^ k) / (k.factorial : K)) :
    IsClosed {y | MvPowerSeries.constantCoeff (F y) = 0 ∧
      ∀ n : Unit →₀ ℕ, ‖MvPowerSeries.coeff n (G y)‖ ≤ 1} := by
  have h1 : IsClosed {y | MvPowerSeries.constantCoeff (F y) = 0} := by
    refine isClosed_eq ?_ continuous_const
    simpa only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hF 0
  have h2 : IsClosed {y | ∀ n : Unit →₀ ℕ, ‖MvPowerSeries.coeff n (G y)‖ ≤ 1} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun n => isClosed_le ?_ continuous_const
    simp only [hG]
    exact (continuous_finsetSum _ fun k _ => (continuous_coeff_pow_of_continuous_coeff F hF k n).div_const _).norm
  simpa only [Set.setOf_and] using h1.inter h2

private theorem continuous_coeff_subst_subst_C_mul_subst {K Y : Type*} [NormedField K] [TopologicalSpace Y]
    (l ex ph : PowerSeries K) (hl : PowerSeries.constantCoeff l = 0)
    (hex : PowerSeries.constantCoeff ex = 0) (c : Y → K) (hc : Continuous c) :
    ∀ e, Continuous fun y => MvPowerSeries.coeff e (PowerSeries.subst (PowerSeries.subst
        (MvPowerSeries.C (c y) * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l)
        ex) ph) := by
  have hin : ∀ y, MvPowerSeries.constantCoeff
      (MvPowerSeries.C (c y) * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) = 0 := by
    intro y
    rw [map_mul, MvPowerSeries.constantCoeff_C,
      constantCoeff_subst_of_constantCoeff_eq_zero_orbital_bounds_conclusion l _ (MvPowerSeries.constantCoeff_X ()), hl, mul_zero]
  have hmid : ∀ y, MvPowerSeries.constantCoeff (PowerSeries.subst
      (MvPowerSeries.C (c y) * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l)
      ex) = 0 :=
    fun y => (constantCoeff_subst_of_constantCoeff_eq_zero_orbital_bounds_conclusion ex _ (hin y)).trans hex
  refine continuous_coeff_subst_of_continuous_coeff ph _ hmid ?_
  refine continuous_coeff_subst_of_continuous_coeff ex _ hin ?_
  intro e
  simp only [MvPowerSeries.coeff_C_mul]
  exact hc.mul continuous_const

theorem phase_norm_limit_target : PI.PhNormLimit.Target := by
  unfold PI.PhNormLimit.Target
  intro p _ l ex ph T h0 h1 _ h3
  have hl : PowerSeries.constantCoeff l = 0 := by
    rw [← constantCoeff_subst_of_constantCoeff_eq_zero_orbital_bounds_conclusion l ex h0, h1]
    exact MvPowerSeries.constantCoeff_X ()
  refine forall_mem_closure_of_isClosed_setOf T _ ?_ h3
  refine isClosed_setOf_coeff_exp_norm_le_one _ _ ?_ ?_
  · intro e
    simp only [map_sub, MvPowerSeries.coeff_C_mul]
    refine Continuous.sub ?_ ((continuous_fst.mul continuous_snd).mul continuous_const)
    exact continuous_coeff_subst_subst_C_mul_subst l ex ph hl h0 _ continuous_fst e
  · intro n y
    rfl
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhProdConv
section
theorem isConvIdempotent_pi : PI.PhProdConv.ProdConv := by
  intro ι _ _ G _ _ _ _ _ _ μ _ _ _ ph m hint hconv
  refine ⟨MeasureTheory.Integrable.fintype_prod_dep hint, ?_⟩
  unfold PI.PhProdConv.PhConv
  refine ⟨?_, fun g => ?_, fun x y => ?_⟩
  · exact Finset.prod_eq_one (fun i _ => (hconv i).1)
  · change ∏ i, ph i ((g i)⁻¹) = starRingEnd ℂ (∏ i, ph i (g i))
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => (hconv i).2.1 (g i))
  · have key : (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) =
        fun g => ∏ i, (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)) i (g i) := by
      funext g
      rw [← Finset.prod_mul_distrib]
      rfl
    change MeasureTheory.Integrable
        (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i))
        (MeasureTheory.Measure.pi μ) ∧
      ∫ g, (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) g
        ∂(MeasureTheory.Measure.pi μ) = (∏ i, m i (x i)) * ∏ i, ph i (y i)
    rw [key]
    refine ⟨MeasureTheory.Integrable.fintype_prod_dep
      (fun i => ((hconv i).2.2 (x i) (y i)).1), ?_⟩
    rw [MeasureTheory.integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => ((hconv i).2.2 (x i) (y i)).2)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumAntidiagonalTuple
section
private theorem sum_range_add_choose_eq_choose_succ (E n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k + E).choose E = (n + E + 1).choose (E + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show n + 1 + E + 1 = (n + E + 1) + 1 by omega,
      Nat.choose_succ_succ (n + E + 1) E, show n + 1 + E = n + E + 1 by omega]
    simp only [Nat.succ_eq_add_one]
    omega

private theorem card_antidiagonal_tuple_succ_eq_sum_range (D k : ℕ) :
    (Finset.Nat.antidiagonalTuple (D + 1) k).card =
      ∑ i ∈ Finset.range (k + 1), (Finset.Nat.antidiagonalTuple D (k - i)).card := by
  calc (Finset.Nat.antidiagonalTuple (D + 1) k).card
      = ((Finset.range (k + 1)).sigma fun i => Finset.Nat.antidiagonalTuple D (k - i)).card := by
        refine Finset.card_nbij' (fun x => ⟨x 0, Fin.tail x⟩) (fun p => Fin.cons p.1 p.2)
          ?_ ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hx
          rw [Fin.sum_univ_succ] at hx
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range,
            Finset.Nat.mem_antidiagonalTuple, Fin.tail]
          omega
        · rintro ⟨i, y⟩ hp
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range,
            Finset.Nat.mem_antidiagonalTuple] at hp
          simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ,
            Fin.cons_zero, Fin.cons_succ]
          omega
        · intro x _
          simp
        · rintro ⟨i, y⟩ _
          simp
    _ = ∑ i ∈ Finset.range (k + 1), (Finset.Nat.antidiagonalTuple D (k - i)).card :=
        Finset.card_sigma _ _

private theorem card_antidiagonal_tuple_succ_eq_choose (D : ℕ) :
    ∀ k, (Finset.Nat.antidiagonalTuple (D + 1) k).card = (k + D).choose D := by
  induction D with
  | zero =>
    intro k
    rw [card_antidiagonal_tuple_succ_eq_sum_range, Finset.sum_eq_single k]
    · simp [Finset.Nat.antidiagonalTuple_zero_zero]
    · intro i hi hik
      simp only [Finset.mem_range] at hi
      obtain ⟨m, hm⟩ : ∃ m, k - i = m + 1 := ⟨k - i - 1, by omega⟩
      rw [hm, Finset.Nat.antidiagonalTuple_zero_succ, Finset.card_empty]
    · intro h
      simp at h
  | succ D ih =>
    intro k
    rw [card_antidiagonal_tuple_succ_eq_sum_range]
    simp only [ih]
    have h : ∑ j ∈ Finset.range (k + 1), (k - j + D).choose D =
        ∑ j ∈ Finset.range (k + 1), (j + D).choose D := by
      have := Finset.sum_range_reflect (fun i => (i + D).choose D) (k + 1)
      simpa only [Nat.add_sub_cancel] using this
    rw [h, sum_range_add_choose_eq_choose_succ, Nat.add_assoc]

theorem sum_antidiagonalTuple : PI.SumAntidiagonalTuple := by
  intro D T hDT
  cases D with
  | zero =>
    obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.choose_zero_right]
    rw [Finset.sum_range_succ']
    simp [Finset.Nat.antidiagonalTuple_zero_succ, Finset.Nat.antidiagonalTuple_zero_zero]
  | succ E =>
    obtain ⟨n, rfl⟩ : ∃ n, T = n + E + 2 := ⟨T - E - 2, by omega⟩
    have h1 : n + E + 2 - (E + 1) = n + 1 := by omega
    have h2 : n + E + 2 - 1 = n + E + 1 := by omega
    rw [h1, h2]
    simp only [card_antidiagonal_tuple_succ_eq_choose]
    exact sum_range_add_choose_eq_choose_succ E n
end

