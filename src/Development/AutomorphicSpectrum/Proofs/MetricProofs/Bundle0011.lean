module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0007
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticAtMobiusDetJacobianEq
section
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem analyticAt_entry_tail {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (z : Fin (d + 1) → ℂ) (p q : Fin 2) :
    AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => g (Fin.tail z') p q) z := by
  have hT : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => (Fin.tail z' : Fin d → ℂ)) z := by
    rw [analyticAt_pi_iff]
    intro i
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ).analyticAt z
  have hA : AnalyticAt ℂ (fun y' => g y' p q) (Fin.tail z) :=
    ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg p q).differentiableOn _ (Set.mem_univ _)
  exact hA.comp hT

theorem analyticAt_mobius_first {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (z : Fin (d + 1) → ℂ)
    (h : den (g (Fin.tail z)) (z 0) ≠ 0) : AnalyticAt ℂ (mob1 g) z := by
  have hc0 : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => z' 0) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) 0).analyticAt z
  have e := analyticAt_entry_tail g hg z
  have hnum : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ =>
      g (Fin.tail z') 1 0 + g (Fin.tail z') 1 1 * z' 0) z := (e 1 0).add ((e 1 1).mul hc0)
  have hden : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => den (g (Fin.tail z')) (z' 0)) z :=
    (e 0 0).add ((e 0 1).mul hc0)
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hnum.div hden h
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) j.succ).analyticAt z

theorem hasDerivAt_mob_shift (m : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) (h : den m a ≠ 0) :
    HasDerivAt (fun t : ℂ => mob m (a + t)) (mobD m a) 0 := by
  have hl : HasDerivAt (fun t : ℂ => a + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add a
  have hn : HasDerivAt (fun t : ℂ => m 1 0 + m 1 1 * (a + t)) (m 1 1 * 1) 0 :=
    (hl.const_mul (m 1 1)).const_add (m 1 0)
  have hd : HasDerivAt (fun t : ℂ => den m (a + t)) (m 0 1 * 1) 0 :=
    (hl.const_mul (m 0 1)).const_add (m 0 0)
  have h0 : den m (a + 0) ≠ 0 := by simpa using h
  have hq := hn.div hd h0
  have e1 : (m 1 1 * 1 * den m (a + 0) - (m 1 0 + m 1 1 * (a + 0)) * (m 0 1 * 1)) / den m (a + 0) ^ 2 =
      mobD m a := by
    simp only [add_zero, mobD, Matrix.det_fin_two]
    congr 1
    simp only [den]
    ring
  rw [e1] at hq
  exact hq

theorem det_jacobian_mobius_first {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a : ℂ)
    (h : den (g y) a ≠ 0) :
    (ReciprocityTheory.AnForm.A.jacC (mob1 g) (Fin.cons a y : Fin (d + 1) → ℂ)).det = mobD (g y) a := by
  set z : Fin (d + 1) → ℂ := Fin.cons a y with hz
  have htail : (Fin.tail z : Fin d → ℂ) = y := Fin.tail_cons _ _
  have hz0 : z 0 = a := Fin.cons_zero _ _
  have hF : HasFDerivAt (mob1 g) (fderiv ℂ (mob1 g) z) z :=
    (analyticAt_mobius_first g hg z (by rwa [htail, hz0])).differentiableAt.hasFDerivAt

  have hrow : ∀ (i : Fin d) (v : Fin (d + 1) → ℂ), fderiv ℂ (mob1 g) z v i.succ = v i.succ := by
    intro i v
    have h1 := (hasFDerivAt_pi'.1 hF) i.succ
    have h2 : HasFDerivAt (fun z' : Fin (d + 1) → ℂ => mob1 g z' i.succ)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ) z :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ).hasFDerivAt
    exact DFunLike.congr_fun (h1.unique h2) v

  have hcorner : fderiv ℂ (mob1 g) z (Pi.single 0 1) 0 = mobD (g y) a := by
    have hc : HasDerivAt (fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ))
        (Pi.single 0 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single 0 1 : Fin (d + 1) → ℂ)).const_add z
    have hF' : HasFDerivAt (mob1 g) (fderiv ℂ (mob1 g) z)
        (z + (0 : ℂ) • (Pi.single 0 1 : Fin (d + 1) → ℂ)) := by simpa using hF
    have hcomp := hF'.comp_hasDerivAt (0 : ℂ) hc
    have h0 := (hasDerivAt_pi.1 hcomp) 0
    have hline : ∀ t : ℂ, (mob1 g ∘ fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) t 0 =
        mob (g y) (a + t) := by
      intro t
      have ht : (Fin.tail (z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) : Fin d → ℂ) = y := by
        rw [← htail]
        funext i
        simp [Fin.tail, Pi.single_apply, Fin.succ_ne_zero]
      simp only [Function.comp, mob1, Fin.cons_zero, ht]
      simp [hz0]
    have h3 : HasDerivAt (fun t : ℂ => (mob1 g ∘ fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) t 0)
        (mobD (g y) a) 0 := by
      simpa only [hline] using hasDerivAt_mob_shift (g y) a h
    exact h0.unique h3
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz1 : ∀ i : Fin d, ReciprocityTheory.AnForm.A.jacC (mob1 g) z i.succ 0 = 0 := by
    intro i
    simp [ReciprocityTheory.AnForm.A.jacC, hrow, Pi.single_apply, Fin.succ_ne_zero]
  have hminor : (ReciprocityTheory.AnForm.A.jacC (mob1 g) z).submatrix (Fin.succAbove 0) Fin.succ = 1 := by
    ext i j
    simp [ReciprocityTheory.AnForm.A.jacC, hrow, Pi.single_apply, Matrix.one_apply, Fin.succ_inj]
  simp only [hz1, hminor]
  simp [ReciprocityTheory.AnForm.A.jacC, hcorner]

theorem analyticAt_mobius_and_det_jacobian : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a : ℂ),
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a ≠ 0 →
    AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y) ∧
      (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y)).det =
        GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a := by
  intro d g hg y a h
  refine ⟨analyticAt_mobius_first g hg _ ?_, det_jacobian_mobius_first g hg y a h⟩
  rwa [Fin.tail_cons, Fin.cons_zero]

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HorizontalDivSuppTwist
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

namespace GlobalTheory.CompanionTheory.Ar.Tw

theorem twist_sup_span_le {K : Type} {ι : K → Type} (p : ℕ) {P W : Ideal (MRing ι)}
    {s : MRing ι} (h : P ⊔ Ideal.span {s} ≤ W) :
    twist p P ⊔ Ideal.span {(inc s : MRing (Tb ι))} ≤ twist p W := by
  refine sup_le (sup_le ?_ le_sup_right) ?_
  · exact (Ideal.map_mono (le_sup_left.trans h)).trans le_sup_left
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (h (Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self s))))

theorem sup_span_le_comap_inc {K : Type} {ι : K → Type} (p : ℕ) {P : Ideal (MRing ι)}
    {s : MRing ι} {Q : Ideal (MRing (Tb ι))}
    (h : twist p P ⊔ Ideal.span {(inc s : MRing (Tb ι))} ≤ Q) :
    P ⊔ Ideal.span {s} ≤ Q.comap inc := by
  refine sup_le ?_ ?_
  · exact Ideal.map_le_iff_le_comap.mp ((le_sup_left.trans le_sup_left).trans h)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))

theorem twist_le_of_map_le {K : Type} {ι : K → Type} (p : ℕ) {P W : Ideal (MRing ι)}
    {s : MRing ι} {Q : Ideal (MRing (Tb ι))}
    (h : twist p P ⊔ Ideal.span {(inc s : MRing (Tb ι))} ≤ Q) (hW : W ≤ Q.comap inc) :
    twist p W ≤ Q :=
  sup_le (Ideal.map_le_iff_le_comap.mpr hW) ((le_sup_right.trans le_sup_left).trans h)

theorem horizontal_divSupp_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (P : Ideal (MRing ι)) (s : MRing ι)
    (hp : ∀ W, W ∈ divSupp P s → IsHorizontal W → (twist p W).IsPrime) :
    {W' | W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'} =
      twist p '' {W | W ∈ divSupp P s ∧ IsHorizontal W} := by
  ext W'
  constructor
  · rintro ⟨⟨hmin, hrel⟩, hhor⟩
    have hprime : W'.IsPrime := hmin.1.1
    have hle := hmin.1.2
    have hc : P ⊔ Ideal.span {s} ≤ W'.comap inc := sup_span_le_comap_inc p hle
    have : (W'.comap inc).IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨W0, hW0, hW0le⟩ := Ideal.exists_minimalPrimes_le hc
    have hrel0 : IsRelevant W0 := by
      intro k
      obtain ⟨i, hi⟩ := hrel (some k)
      refine ⟨i, fun h => hi ?_⟩
      have := hW0le h
      simpa [inc, oldIdx] using this
    have hhor0 : IsHorizontal W0 := by
      rw [IsHorizontal, eq_bot_iff] at hhor ⊢
      intro n hn
      refine hhor ?_
      have h1 : (C n : MRing ι) ∈ W'.comap inc := hW0le hn
      simpa [inc] using h1
    have hmem : W0 ∈ divSupp P s := ⟨hW0, hrel0⟩
    refine ⟨W0, ⟨hmem, hhor0⟩, ?_⟩
    have htw : twist p W0 ≤ W' := twist_le_of_map_le p hle hW0le
    exact le_antisymm htw (hmin.2 ⟨hp W0 hmem hhor0, twist_sup_span_le p hW0.1.2⟩ htw)
  · rintro ⟨W, ⟨⟨hmin, hrel⟩, hhor⟩, rfl⟩
    have hprime : W.IsPrime := hmin.1.1
    refine ⟨⟨⟨⟨hp W ⟨hmin, hrel⟩ hhor, twist_sup_span_le p hmin.1.2⟩, ?_⟩,
      isRelevant_twist p hprime.ne_top hrel⟩, isHorizontal_twist p hhor⟩
    rintro Q ⟨hQ, hQle⟩ hQtw
    have hcomap : Q.comap inc ≤ W := by
      have := Ideal.comap_mono (f := inc) hQtw
      rwa [comap_inc_twist] at this
    have := hQ
    have hW : W ≤ Q.comap inc :=
      hmin.2 ⟨Ideal.comap_isPrime _ _, sup_span_le_comap_inc p hQle⟩ hcomap
    exact twist_le_of_map_le p hQle hW

end GlobalTheory.CompanionTheory.Ar.Tw
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralNormSqMobDMulCompMob
section
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem subsingleton_affine_zero {p q : ℂ} (h : p ≠ 0 ∨ q ≠ 0) :
    {a : ℂ | p + q * a = 0}.Subsingleton := by
  intro a ha b hb
  have ha' : p + q * a = 0 := ha
  have hb' : p + q * b = 0 := hb
  have hq : q ≠ 0 := by
    rcases h with hp | hq
    · intro hq0
      rw [hq0, zero_mul, add_zero] at ha'
      exact hp ha'
    · exact hq
  exact mul_left_cancel₀ hq (by linear_combination ha' - hb')

theorem det_smulRight_restrictScalars (w : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w).restrictScalars ℝ).det = Complex.normSq w := by
  have e : ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w = w • ContinuousLinearMap.id ℂ ℂ := by
    ext
    simp
  rw [e, ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    ReciprocityTheory.AnForm.A.det_restrictScalars_real]
  simp

theorem hasDerivAt_mob (g : Matrix (Fin 2) (Fin 2) ℂ) {a : ℂ} (ha : den g a ≠ 0) :
    HasDerivAt (mob g) (mobD g a) a := by
  unfold mob mobD
  unfold den at *
  have h1 : HasDerivAt (fun a => g 1 0 + g 1 1 * a) (g 1 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 1 1)).const_add (g 1 0)
  have h2 : HasDerivAt (fun a => g 0 0 + g 0 1 * a) (g 0 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 0 1)).const_add (g 0 0)
  refine (h1.div h2 ha).congr_deriv ?_
  rw [det_fin_two]
  congr 1
  ring

theorem injOn_mob (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0) :
    Set.InjOn (mob g) {a | den g a ≠ 0} := by
  intro a ha b hb hab
  have ha' : den g a ≠ 0 := ha
  have hb' : den g b ≠ 0 := hb
  unfold mob at hab
  rw [div_eq_div_iff ha' hb'] at hab
  unfold den at hab
  rw [det_fin_two] at hg
  have h : (a - b) * (g 0 0 * g 1 1 - g 0 1 * g 1 0) = 0 := by linear_combination hab
  rcases mul_eq_zero.1 h with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hg

theorem mem_image_mob (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0) {b : ℂ}
    (hb : g 1 1 + (-g 0 1) * b ≠ 0) : b ∈ mob g '' {a | den g a ≠ 0} := by
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by rwa [det_fin_two] at hg
  have hci : (g 1 1 + -g 0 1 * b) * (g 1 1 + -g 0 1 * b)⁻¹ = 1 := mul_inv_cancel₀ hb
  have hden : den g ((g 0 0 * b - g 1 0) / (g 1 1 + (-g 0 1) * b)) =
      (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (g 1 1 + (-g 0 1) * b)⁻¹ := by
    unfold den
    rw [div_eq_mul_inv]
    linear_combination (-g 0 0) * hci
  refine ⟨(g 0 0 * b - g 1 0) / (g 1 1 + (-g 0 1) * b), ?_, ?_⟩
  · show den g _ ≠ 0
    rw [hden]
    exact mul_ne_zero hd (inv_ne_zero hb)
  · unfold mob
    rw [hden, div_eq_iff (mul_ne_zero hd (inv_ne_zero hb)), div_eq_mul_inv (g 0 0 * b - g 1 0)]
    linear_combination (-g 1 0) * hci

theorem integral_normSq_mobD_mul_comp_mob (g : Matrix (Fin 2) (Fin 2) ℂ) (hu : IsUnit g.det)
    (f : ℂ → ℝ) :
    ∫ a : ℂ, Complex.normSq (mobD g a) * f (mob g a) = ∫ b : ℂ, f b := by
  have hdet : g.det ≠ 0 := hu.ne_zero
  have hcont : Continuous (den g) := by
    unfold den
    fun_prop
  have hs : MeasurableSet {a : ℂ | den g a ≠ 0} := (isOpen_ne_fun hcont continuous_const).measurableSet
  have hderiv : ∀ a ∈ {a : ℂ | den g a ≠ 0}, HasFDerivWithinAt (mob g)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (mobD g a)).restrictScalars ℝ)
      {a : ℂ | den g a ≠ 0} a :=
    fun a ha => ((hasDerivAt_mob g ha).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hs hderiv (injOn_mob g hdet) f
  simp only [det_smulRight_restrictScalars, abs_of_nonneg (Complex.normSq_nonneg _), smul_eq_mul] at hcv
  rw [det_fin_two] at hdet
  have hnull1 : ∀ᵐ a ∂(volume : Measure ℂ), a ∈ {a : ℂ | den g a ≠ 0} := by
    have h01 : g 0 0 ≠ 0 ∨ g 0 1 ≠ 0 := by
      by_contra hc
      rw [not_or, not_not, not_not] at hc
      apply hdet
      rw [hc.1, hc.2]
      ring
    refine mem_ae_iff.2 (measure_mono_null ?_ ((subsingleton_affine_zero h01).countable.measure_zero _))
    intro a ha
    have ha' : ¬ den g a ≠ 0 := ha
    rw [not_not] at ha'
    exact ha'
  have hnull2 : ∀ᵐ b ∂(volume : Measure ℂ), b ∈ mob g '' {a : ℂ | den g a ≠ 0} := by
    have h11 : g 1 1 ≠ 0 ∨ -g 0 1 ≠ 0 := by
      by_contra hc
      rw [not_or, not_not, not_not, neg_eq_zero] at hc
      apply hdet
      rw [hc.1, hc.2]
      ring
    refine mem_ae_iff.2 (measure_mono_null ?_ ((subsingleton_affine_zero h11).countable.measure_zero _))
    intro b hb
    by_contra hne
    exact hb (mem_image_mob g hu.ne_zero hne)
  rw [Measure.restrict_eq_self_of_ae_mem hnull1, Measure.restrict_eq_self_of_ae_mem hnull2] at hcv
  exact hcv.symm

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MobiusPairAnalyticDetJacobianEq
section
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem det_eq_mul_minor_of_col_zero {n : ℕ} (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (h : ∀ i : Fin n, J i.succ 0 = 0) : J.det = J 0 0 * (J.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h]

theorem hasDerivAt_mob_line (G : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) (h : den G a ≠ 0) :
    HasDerivAt (fun t : ℂ => mob G (a + t)) (mobD G a) 0 := by
  have hl : HasDerivAt (fun t : ℂ => a + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add a
  have hn : HasDerivAt (fun t : ℂ => G 1 0 + G 1 1 * (a + t)) (G 1 1) 0 := by
    simpa using (hl.const_mul (G 1 1)).const_add (G 1 0)
  have hd : HasDerivAt (fun t : ℂ => den G (a + t)) (G 0 1) 0 := by
    simpa [den] using (hl.const_mul (G 0 1)).const_add (G 0 0)
  have h0 : den G (a + 0) ≠ 0 := by simpa using h
  have key := hn.div hd h0
  have e : mobD G a = (G 1 1 * den G (a + 0) - (G 1 0 + G 1 1 * (a + 0)) * G 0 1) / den G (a + 0) ^ 2 := by
    simp only [add_zero]
    unfold mobD
    rw [Matrix.det_fin_two]
    congr 1
    unfold den
    ring
  rw [e]
  exact key

theorem jacC_apply_of_line {D E : ℕ} (F : (Fin D → ℂ) → Fin E → ℂ) (z : Fin D → ℂ)
    (hF : DifferentiableAt ℂ F z) (a : Fin E) (k : Fin D) (c : ℂ)
    (h : HasDerivAt (fun t : ℂ => F (z + t • (Pi.single k 1 : Fin D → ℂ)) a) c 0) :
    ReciprocityTheory.AnForm.A.jacC F z a k = c := by
  have hl : HasDerivAt (fun t : ℂ => z + t • (Pi.single k 1 : Fin D → ℂ)) (Pi.single k 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single k 1 : Fin D → ℂ)).const_add z
  have hF' : HasFDerivAt F (fderiv ℂ F z) (z + (0 : ℂ) • (Pi.single k 1 : Fin D → ℂ)) := by
    simpa using hF.hasFDerivAt
  have h2 := hF'.comp_hasDerivAt (0 : ℂ) hl
  have h3 := (hasDerivAt_pi.1 h2) a
  exact h3.unique h

theorem mobius_pair_line_first_axis {d : ℕ} (y : Fin d → ℂ) (a₀ a₁ t : ℂ) :
    (Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) + t • (Pi.single 0 1 : Fin (d + 2) → ℂ) =
      Fin.cons (a₀ + t) (Fin.cons a₁ y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Pi.single_apply, Fin.succ_ne_zero]

theorem mobius_pair_line_second_axis {d : ℕ} (y : Fin d → ℂ) (a₀ a₁ t : ℂ) :
    (Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) + t • (Pi.single 1 1 : Fin (d + 2) → ℂ) =
      Fin.cons a₀ (Fin.cons (a₁ + t) y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Pi.single_apply]
  · refine Fin.cases ?_ (fun l => ?_) j
    · simp [Pi.single_apply]
    · have : (l.succ.succ : Fin (d + 2)) ≠ 1 := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [Pi.single_apply, this]

theorem mobius_pair_cons {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ) (b₀ b₁ : ℂ) :
    mob2 g (Fin.cons b₀ (Fin.cons b₁ y)) = Fin.cons (mob (g y) b₀) (Fin.cons (mob (g y) b₁) y) := rfl

theorem analyticAt_mobius_pair {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a₀ a₁ : ℂ)
    (h₀ : den (g y) a₀ ≠ 0) (h₁ : den (g y) a₁ ≠ 0) :
    AnalyticAt ℂ (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) := by
  set z₀ : Fin (d + 2) → ℂ := Fin.cons a₀ (Fin.cons a₁ y) with hz₀
  have hcoord : ∀ i : Fin (d + 2), AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => z i) z₀ := fun i =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 2) => ℂ) i).analyticAt z₀
  have hT : AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) z₀ := by
    rw [analyticAt_pi_iff]
    intro i
    exact hcoord i.succ.succ
  have hTz : Fin.tail (Fin.tail z₀) = y := by
    simp [hz₀]
  have hga : ∀ p q, AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => g (Fin.tail (Fin.tail z)) p q) z₀ := by
    intro p q
    have h1 : AnalyticAt ℂ (fun y' => g y' p q) (Fin.tail (Fin.tail z₀)) :=
      ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg p q).differentiableOn _ (Set.mem_univ _)
    exact AnalyticAt.comp (f := fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) h1 hT
  have hm : ∀ i : Fin (d + 2), den (g y) (z₀ i) ≠ 0 →
      AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => mob (g (Fin.tail (Fin.tail z))) (z i)) z₀ := by
    intro i hi
    unfold mob den
    refine AnalyticAt.div ?_ ?_ ?_
    · exact (hga 1 0).add ((hga 1 1).mul (hcoord i))
    · exact (hga 0 0).add ((hga 0 1).mul (hcoord i))
    · rw [hTz]
      exact hi
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hm 0 (by simpa [hz₀] using h₀)
  · refine Fin.cases ?_ (fun l => ?_) j
    · exact hm 1 (by simpa [hz₀] using h₁)
    · exact hcoord l.succ.succ

theorem det_jacobian_mobius_pair {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a₀ a₁ : ℂ)
    (h₀ : den (g y) a₀ ≠ 0) (h₁ : den (g y) a₁ ≠ 0) :
    (ReciprocityTheory.AnForm.A.jacC (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y))).det =
      mobD (g y) a₀ * mobD (g y) a₁ := by
  have hdiff : DifferentiableAt ℂ (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) :=
    (analyticAt_mobius_pair g hg y a₀ a₁ h₀ h₁).differentiableAt
  set J := ReciprocityTheory.AnForm.A.jacC (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) with hJ
  have hJ00 : J 0 0 = mobD (g y) a₀ := by
    refine jacC_apply_of_line _ _ hdiff 0 0 _ ?_
    simp only [mobius_pair_line_first_axis, mobius_pair_cons]
    simpa using hasDerivAt_mob_line (g y) a₀ h₀
  have hJ11 : J 1 1 = mobD (g y) a₁ := by
    refine jacC_apply_of_line _ _ hdiff 1 1 _ ?_
    simp only [mobius_pair_line_second_axis, mobius_pair_cons]
    simpa using hasDerivAt_mob_line (g y) a₁ h₁
  have hJ10 : J 1 0 = 0 := by
    refine jacC_apply_of_line _ _ hdiff 1 0 _ ?_
    simp only [mobius_pair_line_first_axis, mobius_pair_cons]
    simpa using hasDerivAt_const (0 : ℂ) (mob (g y) a₁)
  have hJss : ∀ (i : Fin d) (k : Fin (d + 2)), J i.succ.succ k = (Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ := by
    intro i k
    refine jacC_apply_of_line _ _ hdiff _ _ _ ?_
    have e : (fun t : ℂ => mob2 g ((Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) +
        t • (Pi.single k 1 : Fin (d + 2) → ℂ)) i.succ.succ) =
        fun t : ℂ => y i + t * (Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ := by
      funext t
      simp [mob2, Fin.tail]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const ((Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ)).const_add (y i)
  have hc0 : ∀ i : Fin (d + 1), J i.succ 0 = 0 := by
    intro i
    refine Fin.cases ?_ (fun l => ?_) i
    · exact hJ10
    · rw [hJss]
      simp [Pi.single_apply, Fin.succ_ne_zero]
  have hc1 : ∀ i : Fin d, (J.submatrix Fin.succ Fin.succ) i.succ 0 = 0 := by
    intro i
    simp only [Matrix.submatrix_apply]
    rw [hJss]
    have : (i.succ.succ : Fin (d + 2)) ≠ 1 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [Pi.single_apply, this]
  have hlast : ((J.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ) = 1 := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [hJss]
    simp [Pi.single_apply, Matrix.one_apply]
  rw [det_eq_mul_minor_of_col_zero J hc0, det_eq_mul_minor_of_col_zero _ hc1, hlast, Matrix.det_one, mul_one,
    hJ00]
  simp only [Matrix.submatrix_apply]
  congr 1

theorem mobius_pair_analyticAt_and_det_jacobian : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a₀ a₁ : ℂ),
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₀ ≠ 0 → GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₁ ≠ 0 →
    AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) ∧
    (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y))).det =
      GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₀ * GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₁ :=
  fun _ g hg y a₀ a₁ h₀ h₁ => ⟨analyticAt_mobius_pair g hg y a₀ a₁ h₀ h₁, det_jacobian_mobius_pair g hg y a₀ a₁ h₀ h₁⟩

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end
end

