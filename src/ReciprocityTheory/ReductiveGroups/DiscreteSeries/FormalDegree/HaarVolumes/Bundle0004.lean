module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExpB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
public import Formalism.LocalRingCardinality.DataCD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.ChartWRB
section
noncomputable section

open Finset Matrix MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

namespace ChartWRAux

variable {N : ℕ}

def skML : (UCo N × TriCo N) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := skMat p.1
  map_add' p q := by
    ext a b
    simp only [skMat, Prod.fst_add, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> (try simp [star_add]) <;> (try ring)
  map_smul' c p := by
    ext a b
    simp only [skMat, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply, Matrix.smul_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

def upML : (UCo N × TriCo N) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := upMat p.2
  map_add' p q := by
    ext a b
    simp only [upMat, Prod.snd_add, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> (try simp) <;> (try ring)
  map_smul' c p := by
    ext a b
    simp only [upMat, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, Matrix.smul_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem chartWR_strict :
    HasStrictFDerivAt (chartWR (N := N))
      ((lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ)) 0 := by
  let skL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ := LinearMap.toContinuousLinearMap skML
  let upL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ := LinearMap.toContinuousLinearMap upML
  let ofL : Matrix (Fin N) (Fin N) ℂ →L[ℝ] (Fin N → Fin N → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have hsk0 : skL 0 = 0 := map_zero _
  have hup0 : upL 0 = 0 := map_zero _
  have h1 : HasStrictFDerivAt (fun p : UCo N × TriCo N => NormedSpace.exp (skL p))
      ((1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) 0 := by
    have he := hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin N) (Fin N) ℂ)
    rw [← hsk0] at he
    exact he.comp 0 skL.hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun p : UCo N × TriCo N => 1 + upL p) upL 0 :=
    upL.hasStrictFDerivAt.const_add 1
  have h3 := h1.mul' h2
  have h4 := ofL.hasStrictFDerivAt.comp 0 h3
  have hF : (fun x => ofL (((fun p => NormedSpace.exp (skL p)) * fun p => 1 + upL p) x)) = chartWR := by
    funext p; rfl
  have hD : ofL.comp (NormedSpace.exp (skL 0) • upL + MulOpposite.op (1 + upL 0) •
      (1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) =
      ((lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ)) := by
    refine ContinuousLinearMap.ext fun p => ?_
    rw [hsk0, hup0, NormedSpace.exp_zero]
    simp
    exact (add_comm _ _).trans rfl
  rw [hF] at h4
  exact h4.congr_fderiv hD

end Deriv

end ChartWRAux

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.GaussB
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem gaussC_mat :
    ∫⁻ Z : Fin N → Fin N → ℂ, ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))) =
      ENNReal.ofReal (Real.pi ^ (N ^ 2)) := by
  have hpt : ∀ Z : Fin N → Fin N → ℂ, ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))) =
      ENNReal.ofReal (∏ i, (fun (_ : Fin N) (row : Fin N → ℂ) => ∏ j, Real.exp (-‖row j‖ ^ 2)) i (Z i)) := by
    intro Z
    congr 1
    simp only [hs, Matrix.of_apply, ← Real.exp_sum, ← Finset.sum_neg_distrib]
  have hrow : Integrable (fun row : Fin N → ℂ => ∏ j, Real.exp (-‖row j‖ ^ 2)) :=
    Integrable.fintype_prod (fun _ => gaussA_cint)
  have hrowi : ∫ row : Fin N → ℂ, ∏ j, Real.exp (-‖row j‖ ^ 2) = Real.pi ^ N := by
    rw [integral_fintype_prod_volume_eq_prod (fun (_ : Fin N) (z : ℂ) => Real.exp (-‖z‖ ^ 2))]
    simp only [gaussA_cintegral, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hpt]
  rw [show (volume : Measure (Fin N → Fin N → ℂ)) = Measure.pi (fun _ => volume) from rfl,
    gaussA_lint_pi_ofReal _ (fun _ => hrow)
      (fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
  simp only [hrowi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (pow_nonneg Real.pi_pos.le _), ← pow_mul, sq]

theorem gaussC_hs_upMat (t : TriCo N) :
    hs (upMat t) = ∑ j, t.1 j ^ 2 + ∑ ab : {ab : Fin N × Fin N // ab.1 < ab.2}, ‖t.2 ab‖ ^ 2 := by
  have hp : ∀ a b : Fin N, ‖upMat t a b‖ ^ 2 = (if a = b then t.1 a ^ 2 else 0) +
      (if h : a < b then ‖t.2 ⟨(a, b), h⟩‖ ^ 2 else 0) := by
    intro a b
    unfold upMat
    by_cases hab : a = b
    · subst hab; simp [Complex.norm_real, sq_abs]
    · by_cases h : a < b
      · simp [hab, h]
      · simp [hab, h]
  unfold hs
  simp_rw [hp, Finset.sum_add_distrib]
  congr 1
  · simp [Finset.sum_ite_eq]
  · rw [← Finset.sum_product' (f := fun a b => if h : a < b then ‖t.2 ⟨(a, b), h⟩‖ ^ 2 else 0),
      Finset.univ_product_univ,
      ← (Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)).sum_comp, Fintype.sum_sum_type]
    have h1 : ∀ a : {p : Fin N × Fin N // p.1 < p.2},
        (fun p : Fin N × Fin N => if h : p.1 < p.2 then ‖t.2 ⟨(p.1, p.2), h⟩‖ ^ 2 else 0)
          ((Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)) (Sum.inl a)) = ‖t.2 a‖ ^ 2 := by
      intro a; obtain ⟨⟨x, y⟩, h⟩ := a; simp [h]
    have h2 : ∀ b : {p : Fin N × Fin N // ¬ p.1 < p.2},
        (fun p : Fin N × Fin N => if h : p.1 < p.2 then ‖t.2 ⟨(p.1, p.2), h⟩‖ ^ 2 else 0)
          ((Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)) (Sum.inr b)) = 0 := by
      intro b; obtain ⟨⟨x, y⟩, h⟩ := b; simp [h]
    simp only [h1, h2, Finset.sum_const_zero, add_zero]

def gaussRadW (N : ℕ) (j : Fin N) (r : ℝ) : ℝ := Real.exp (-r ^ 2) * |r| ^ (2 * (N - 1 - (j : ℕ)) + 1)

theorem gaussD_integrand (t : TriCo N) (ht : t ∈ triPos N) :
    ENNReal.ofReal (Real.exp (-hs (upMat t))) * ENNReal.ofReal (qrWt t) =
      ENNReal.ofReal (∏ j, gaussRadW N j (t.1 j)) *
        ENNReal.ofReal (∏ ab : {ab : Fin N × Fin N // ab.1 < ab.2}, Real.exp (-‖t.2 ab‖ ^ 2)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul' (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
  congr 1
  rw [gaussC_hs_upMat, neg_add, Real.exp_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    Real.exp_sum, Real.exp_sum]
  have hw : ∀ j : Fin N, t.1 j ^ (2 * (N - (j : ℕ)) - 1) = |t.1 j| ^ (2 * (N - 1 - (j : ℕ)) + 1) := by
    intro j
    rw [abs_of_pos (ht j)]
    congr 1
    have := j.2
    omega
  unfold qrWt gaussRadW
  simp_rw [hw, Finset.prod_mul_distrib]
  ring

theorem gaussD_triPos_eq : triPos N = (Set.univ.pi fun _ : Fin N => Set.Ioi (0:ℝ)) ×ˢ Set.univ := by
  ext t
  simp [triPos]

theorem gaussD_tri :
    ∫⁻ t in triPos N, ENNReal.ofReal (Real.exp (-hs (upMat t))) * ENNReal.ofReal (qrWt t) =
      ENNReal.ofReal (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) := by
  have hms : MeasurableSet (triPos N) := by
    rw [gaussD_triPos_eq]
    exact (MeasurableSet.univ_pi fun _ => measurableSet_Ioi).prod MeasurableSet.univ
  rw [setLIntegral_congr_fun hms (fun t ht => gaussD_integrand t ht), gaussD_triPos_eq,
    show (volume : Measure (TriCo N)) = (volume : Measure (Fin N → ℝ)).prod
      (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)) from rfl,
    ← Measure.prod_restrict, Measure.restrict_univ,
    show (volume : Measure (Fin N → ℝ)) = Measure.pi (fun _ => volume) from rfl,
    Measure.restrict_pi_pi]
  rw [lintegral_prod_mul (f := fun x : Fin N → ℝ => ENNReal.ofReal (∏ j, gaussRadW N j (x j)))
    (g := fun y : {ab : Fin N × Fin N // ab.1 < ab.2} → ℂ =>
      ENNReal.ofReal (∏ ab, Real.exp (-‖y ab‖ ^ 2)))
    (by unfold gaussRadW; fun_prop)
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun y : {ab : Fin N × Fin N // ab.1 < ab.2} → ℂ =>
      ∏ ab, Real.exp (-‖y ab‖ ^ 2)).measurable).aemeasurable]
  rw [gaussA_lint_pi_ofReal (fun j => gaussRadW N j) (fun j => gaussA_rad_int _)
      (fun j r => mul_nonneg (Real.exp_pos _).le (pow_nonneg (abs_nonneg _) _)),
    show (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)) = Measure.pi (fun _ => volume) from rfl,
    gaussA_lint_pi_ofReal (fun (_ : {ab : Fin N × Fin N // ab.1 < ab.2}) (z : ℂ) => Real.exp (-‖z‖ ^ 2))
      (fun _ => gaussA_cint) (fun _ _ => (Real.exp_pos _).le)]
  simp only [gaussRadW, gaussA_rad, gaussA_cintegral, Finset.prod_const, Finset.card_univ, gaussB_card_lt]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity),
    ← ENNReal.ofReal_pow Real.pi_pos.le, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => by positivity),
    gaussB_prod_fact]
  congr 1
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExpC
section
noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric

namespace ReciprocityTheory.ChartRestriction.DS.HExp

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

theorem inG_iff_entry {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} :
    inG ε X ↔ ∀ i j, star (X j i) * sg ε j + sg ε i * X i j = 0 := by
  unfold inG Jm sg
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rwa [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply] at this
  · intro h
    ext i j
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply]
    exact h i j

theorem gMat_inG {ε : Fin n → Bool} (s : GCo ε) : inG ε (gMat s) := by
  rw [inG_iff_entry]
  intro i j
  simp only [gMat, Matrix.add_apply, kMat, pmat, sg]
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : ¬ j < i := lt_asymm h
    have h2 : i ≠ j := ne_of_lt h
    by_cases he : ε i = ε j
    · simp [h, h1, h2, h2.symm, he]
    · have he' : ε j ≠ ε i := Ne.symm he
      simp [h, h1, h2, h2.symm, he, he']
      rcases Bool.eq_false_or_eq_true (ε i) with hi | hi <;>
        rcases Bool.eq_false_or_eq_true (ε j) with hj | hj <;> simp [hi, hj] at he ⊢
  · apply Complex.ext <;> simp <;> split_ifs <;> simp
  · have h1 : ¬ i < j := lt_asymm h
    have h2 : j ≠ i := ne_of_lt h
    by_cases he : ε i = ε j
    · simp [h, h1, h2, h2.symm, he]
      split_ifs <;> ring
    · have he' : ε j ≠ ε i := Ne.symm he
      simp [h, h1, h2, h2.symm, he, he']
      rcases Bool.eq_false_or_eq_true (ε i) with hi | hi <;>
        rcases Bool.eq_false_or_eq_true (ε j) with hj | hj <;> simp [hi, hj] at he ⊢

def gCo (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : GCo ε :=
  ((fun a => (Z a a).im, fun p => Z p.1.1 p.1.2), fun p => Z p.1.1 p.1.2)

theorem gCo_gMat {ε : Fin n → Bool} (s : GCo ε) : gCo ε (gMat s) = s := by
  obtain ⟨⟨w, x⟩, z⟩ := s
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a
    simp [gCo, gMat, kMat, pmat]
  · funext p
    obtain ⟨⟨a, b⟩, hab, he⟩ := p
    have h1 : a ≠ b := (ne_of_lt hab).symm
    have h2 : ¬ a < b := lt_asymm hab
    simp [gCo, gMat, kMat, pmat, h1, hab, he, h2]
  · funext p
    obtain ⟨⟨a, b⟩, hab, he⟩ := p
    have h1 : a ≠ b := (ne_of_lt hab).symm
    have h2 : ¬ a < b := lt_asymm hab
    simp [gCo, gMat, kMat, pmat, h1, hab, he, h2]

theorem gMat_gCo {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) :
    gMat (gCo ε Z) = Z := by
  rw [inG_iff_entry] at hZ
  ext i j
  have hij := hZ i j
  simp only [gMat, Matrix.add_apply, kMat, pmat, gCo, sg] at hij ⊢
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : ¬ j < i := lt_asymm h
    have h2 : i ≠ j := ne_of_lt h
    cases hi : ε i <;> cases hj : ε j <;> simp [h, h1, h2, hi, hj] at hij ⊢ <;>
      first | linear_combination hij | linear_combination -hij
  · apply Complex.ext <;> simp
    · have := congrArg Complex.re hij
      cases hi : ε i <;> simp [hi] at this <;> linarith
  · have h1 : ¬ i < j := lt_asymm h
    have h2 : j ≠ i := ne_of_lt h
    simp [h, h1, h2.symm]
    split_ifs <;> simp

end ReciprocityTheory.ChartRestriction.DS.HExp
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.IntegralGaussEOmPhiOmE
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

def uToLieMat (x : UCo N) : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ :=
  Matrix.reindex (Equiv.sumEmpty (Fin N) (Fin 0)).symm (Equiv.sumEmpty (Fin N) (Fin 0)).symm (skMat x)

theorem uToLieMat_apply (x : UCo N) (i j : Fin N ⊕ Fin 0) :
    uToLieMat x i j = skMat x (Equiv.sumEmpty (Fin N) (Fin 0) i) (Equiv.sumEmpty (Fin N) (Fin 0) j) := by
  rfl

theorem uToLieMat_mem (x : UCo N) : uToLieMat x ∈ Formalism.BasicNotions.lieU N 0 := by
  rw [mem_lieU_zero_iff_om]
  ext i j
  have h := congrFun (congrFun (skMat_conjTranspose_om x) (Equiv.sumEmpty (Fin N) (Fin 0) i))
    (Equiv.sumEmpty (Fin N) (Fin 0) j)
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h ⊢
  rw [uToLieMat_apply, uToLieMat_apply]
  exact h

def uToLie (x : UCo N) : Formalism.BasicNotions.lieU N 0 := ⟨uToLieMat x, uToLieMat_mem x⟩

def uToLieLin : UCo N →ₗ[ℝ] Formalism.BasicNotions.lieU N 0 where
  toFun := uToLie
  map_add' x y := by
    apply Subtype.ext
    show uToLieMat (x + y) = uToLieMat x + uToLieMat y
    ext i j
    simp [uToLieMat_apply, skMat_add_om]
  map_smul' c x := by
    apply Subtype.ext
    show uToLieMat (c • x) = c • uToLieMat x
    ext i j
    simp [uToLieMat_apply, skMat_smul_om, Complex.real_smul]

theorem uToLieLin_bij : Function.Bijective (uToLieLin (N := N)) := by
  constructor
  · intro x y hxy
    have hm : ∀ a b : Fin N, skMat x a b = skMat y a b := fun a b => by
      have := congrArg (fun z : Formalism.BasicNotions.lieU N 0 =>
        (z : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) (Sum.inl a) (Sum.inl b)) hxy
      simpa [uToLieLin, uToLie, uToLieMat_apply] using this
    refine Prod.ext (funext fun a => ?_) (funext fun l => ?_)
    · have h := hm a a
      rw [skMat_diag_om, skMat_diag_om] at h
      have h' := mul_left_cancel₀ Complex.I_ne_zero h
      exact_mod_cast h'
    · have h := hm l.1.1 l.1.2
      rwa [skMat_low_om, skMat_low_om] at h
  · rintro ⟨X, hX⟩
    have hX' := (mem_lieU_zero_iff_om X).1 hX
    have hent : ∀ i j, star (X j i) = -X i j := fun i j => by
      have := congrFun (congrFun hX' i) j
      simpa [Matrix.conjTranspose_apply] using this
    refine ⟨((fun a => (X (Sum.inl a) (Sum.inl a)).im), fun l => X (Sum.inl l.1.1) (Sum.inl l.1.2)), ?_⟩
    apply Subtype.ext
    show uToLieMat _ = X
    ext i j
    rcases i with a | i
    · rcases j with b | j
      · rw [uToLieMat_apply]
        simp only [Equiv.sumEmpty_apply_inl]
        unfold skMat
        split_ifs with h1 h2 h3
        · subst h1
          have hre : (X (Sum.inl a) (Sum.inl a)).re = 0 := by
            have := congrArg Complex.re (hent (Sum.inl a) (Sum.inl a))
            simp at this
            linarith
          apply Complex.ext <;> simp [hre]
        · rfl
        · show -star (X (Sum.inl b) (Sum.inl a)) = X (Sum.inl a) (Sum.inl b)
          rw [hent (Sum.inl a) (Sum.inl b), neg_neg]
        · exact absurd (lt_trichotomy a b) (by tauto)
      · exact j.elim0
    · exact i.elim0

def uToLieE : UCo N ≃L[ℝ] Formalism.BasicNotions.lieU N 0 :=
  (LinearEquiv.ofBijective uToLieLin uToLieLin_bij).toContinuousLinearEquiv

theorem uToLieE_coe : ⇑(uToLieE (N := N)) = uToLie := rfl

def phiOmE : (UCo N × UCo N) ≃L[ℝ] ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ) :=
  (uToLieE.prodCongr uToLieE).trans complexifyLieEquiv

theorem phiOmE_apply (x y : UCo N) (p : (Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0)) :
    phiOmE (x, y) p = skMat x (Equiv.sumEmpty (Fin N) (Fin 0) p.1) (Equiv.sumEmpty (Fin N) (Fin 0) p.2) +
      Complex.I * skMat y (Equiv.sumEmpty (Fin N) (Fin 0) p.1) (Equiv.sumEmpty (Fin N) (Fin 0) p.2) := by
  show complexifyLieEquiv (uToLieE x, uToLieE y) p = _
  rw [complexifyLieEquiv_coe, uToLieE_coe]
  simp [Formalism.BasicNotions.entries, uToLie, uToLieMat_apply]

theorem phiOmE_haar : ((volume : Measure (UCo N × UCo N)).map (phiOmE (N := N))).IsAddHaarMeasure := by
  exact phiOmE.isAddHaarMeasure_map volume
theorem gaussEOm_phiOmE (x y : UCo N) : gaussEOm (phiOmE (x, y)) = gaussUOm x * gaussUOm y := by
  have hsum : ∑ p : (Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0), Complex.normSq (phiOmE (x, y) p) =
      ∑ a, (x.1 a ^ 2 + y.1 a ^ 2) + ∑ l : LoOm N, 2 * (Complex.normSq (x.2 l) + Complex.normSq (y.2 l)) := by
    rw [← normSq_skMat_sum]
    exact Fintype.sum_equiv ((Equiv.sumEmpty (Fin N) (Fin 0)).prodCongr (Equiv.sumEmpty (Fin N) (Fin 0))) _ _
      (fun p => by rw [phiOmE_apply]; rfl)
  calc gaussEOm (phiOmE (x, y)) = Real.exp (-(∑ p, Complex.normSq (phiOmE (x, y) p))) := by
        rw [gaussEOm, ← Real.exp_sum]
        congr 1
        simp [Finset.sum_neg_distrib]
    _ = gaussUOm x * gaussUOm y := by
        rw [hsum]
        simp only [gaussUOm, ← Real.exp_sum, ← Real.exp_add]
        congr 1
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
        ring

theorem integral_gaussEOm_phiOmE : ∫ Z, gaussEOm Z ∂((volume : Measure (UCo N × UCo N)).map (phiOmE (N := N))) =
    (Real.sqrt Real.pi ^ N * (Real.pi / 2) ^ Fintype.card (LoOm N)) ^ 2 := by
  rw [MeasureTheory.integral_map phiOmE.continuous.measurable.aemeasurable
    continuous_gaussEOm.aestronglyMeasurable]
  show ∫ z : UCo N × UCo N, gaussEOm (phiOmE (z.1, z.2)) = _
  simp_rw [gaussEOm_phiOmE]
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod_mul (f := gaussUOm) (g := gaussUOm), integral_gaussUOm, sq]

theorem map_uToLie_haar : (Measure.map (uToLie (N := N)) volume).IsAddHaarMeasure := by
  rw [← uToLieE_coe]
  exact uToLieE.isAddHaarMeasure_map volume

private lemma prod_map_lemma (c : ENNReal) :
    ((c • Measure.map (uToLie (N := N)) volume).prod (c • Measure.map (uToLie (N := N)) volume)).map
      (fun ab : Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0 =>
        Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) +
          Complex.I • (ab.2 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))) =
      (c * c) • (volume : Measure (UCo N × UCo N)).map (phiOmE (N := N)) := by
  have hm : Measurable (uToLie (N := N)) := by
    rw [← uToLieE_coe]
    exact uToLieE.continuous.measurable
  have hp : Measurable (fun ab : Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0 =>
      Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))) := by
    rw [← complexifyLieEquiv_coe]
    exact complexifyLieEquiv.continuous.measurable
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul (c * c) hp.aemeasurable,
    Measure.map_prod_map _ _ hm hm, Measure.map_map hp (hm.prodMap hm)]
  congr 2

private lemma vol_eq_lemma_2 :
    (volume : Measure ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ)) =
      ENNReal.ofReal (2 ^ (N * (N - 1) / 2) * 2 ^ (N * (N - 1) / 2)) •
        (volume : Measure (UCo N × UCo N)).map (phiOmE (N := N)) := by
  haveI := phiOmE_haar (N := N)
  have h1 := Measure.isAddLeftInvariant_eq_smul (volume : Measure ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ))
    ((volume : Measure (UCo N × UCo N)).map (phiOmE (N := N)))
  rw [ENNReal.smul_def] at h1
  have hI := integral_gaussEOm (N := N)
  rw [h1, integral_smul_measure, integral_gaussEOm_phiOmE, smul_eq_mul, ENNReal.coe_toReal] at hI
  have hk := omega_key_real (N := N)
  have hI2 : (0 : ℝ) < (Real.sqrt Real.pi ^ N * (Real.pi / 2) ^ Fintype.card (LoOm N)) ^ 2 := by positivity
  have hs := mul_right_cancel₀ hI2.ne' (hI.trans hk.symm)
  rw [h1, ← ENNReal.ofReal_coe_nnreal, hs]

theorem isOmegaLeb_uToLie :
    Formalism.BasicNotions.IsOmegaLeb (ENNReal.ofReal (2 ^ (N * (N - 1) / 2)) • Measure.map (uToLie (N := N)) volume) := by
  refine ⟨?_, ?_⟩
  · haveI := map_uToLie_haar (N := N)
    exact Measure.IsAddHaarMeasure.smul _ (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top
  · rw [prod_map_lemma, ← ENNReal.ofReal_mul (by positivity), vol_eq_lemma_2]

end ReciprocityTheory.ChartRestriction.DS
end
end

