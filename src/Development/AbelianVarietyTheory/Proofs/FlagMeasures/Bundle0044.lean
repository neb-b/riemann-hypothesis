module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidChartMeasureFormula
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace GlobalTheory.HypChartPf

open PI.RhsWLim PI.RhsWLim.W

private lemma ofLp_qFw_kapT (k : ℕ) (v : (Fin k → ℂ) × ℂ) :
    WithLp.ofLp (qFw k (kapT k v)) = (WithLp.toLp 2 v.1, Complex.arg v.2) := by
  ext a
  · simp [qFw, kapT, Complex.re_add_im]
  · simp [qFw, kapT]

private lemma hypPar_toLp_arg_of_mem_hypS (k : ℕ) (T' : ℝ) (v : (Fin k → ℂ) × ℂ) (hv : v ∈ hypS k T') :
    hypPar k T' (WithLp.toLp 2 v.1, Complex.arg v.2) = v := by
  simp only [hypS, Set.mem_ofPred_eq] at hv
  have hn : ‖(WithLp.toLp 2 v.1 : EuclideanSpace ℂ (Fin k))‖ ^ 2 + T' = ‖v.2‖ ^ 2 := by
    rw [← normSq_sum_eq, ← Complex.normSq_eq_norm_sq]
    simp only []
    linarith
  simp only [hypPar, hn, Real.sqrt_sq (norm_nonneg _), Complex.norm_mul_exp_arg_mul_I, ]

private lemma kapT_hypPar_ofLp_qFw (k : ℕ) (T' : ℝ) (hT' : 0 < T') (x : TrE k)
    (hx : (WithLp.ofLp (qFw k x)).2 ∈ Set.Ioc (-Real.pi) Real.pi) :
    kapT k (hypPar k T' (WithLp.ofLp (qFw k x))) = x := by
  ext o
  rcases o with _ | ⟨a, b⟩
  · simp only [kapT, hypPar]
    simp only [qFw] at hx ⊢
    simp only [WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
    rw [Complex.arg_real_mul _ (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) hT')),
      Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I hx]
  · cases b <;> simp [kapT, hypPar, qFw]

theorem restrict_periodic (A : Set ℝ) (hA : MeasurableSet A) (hp : ∀ x, x + 2 * Real.pi ∈ A ↔ x ∈ A) :
    volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)) A = volume.restrict (Set.Ioc (-Real.pi) Real.pi) A := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 := isAddFundamentalDomain_Ioc hpos 0 (volume : Measure ℝ)
  have h2 := isAddFundamentalDomain_Ioc hpos (-Real.pi) (volume : Measure ℝ)
  rw [zero_add] at h1
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h2
  have key : ∀ n : ℤ, ∀ x, n • (2 * Real.pi) + x ∈ A ↔ x ∈ A := by
    intro n
    induction n using Int.induction_on with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [← ih x, ← hp ((m : ℤ) • (2 * Real.pi) + x)]
      rw [show ((m : ℤ) + 1) • (2 * Real.pi) + x = (m : ℤ) • (2 * Real.pi) + x + 2 * Real.pi by
        rw [add_smul, one_smul]; abel]
    | pred m ih =>
      intro x
      have h := hp ((-(m : ℤ) - 1) • (2 * Real.pi) + x)
      rw [show (-(m : ℤ) - 1) • (2 * Real.pi) + x + 2 * Real.pi = (-(m : ℤ)) • (2 * Real.pi) + x by
        rw [sub_smul, one_smul]; abel, ih x] at h
      exact h.symm
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  refine h1.measure_set_eq h2 hA ?_
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hg
  ext x
  exact key n x

theorem hypM_eq (k : ℕ) (T' : ℝ) (E : Set ((Fin k → ℂ) × ℂ)) (hE : MeasurableSet E) :
    hypM k T' E = (1 / 2) * (volume.prod volume)
      (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) := by
  have hmeas : Measurable (hypPar k T') := (continuous_hypPar k T').measurable
  have hP : MeasurableSet (hypPar k T' ⁻¹' E) := hmeas hE
  unfold hypM
  rw [Measure.smul_apply, Measure.map_apply hmeas hE, smul_eq_mul]
  congr 1
  rw [Measure.prod_apply hP, Measure.prod_apply (hP.inter (MeasurableSet.univ.prod measurableSet_Ioc))]
  refine lintegral_congr (fun y => ?_)
  have hs : MeasurableSet (Prod.mk y ⁻¹' (hypPar k T' ⁻¹' E)) := measurable_prodMk_left hP
  rw [restrict_periodic _ hs ?_, Measure.restrict_apply hs]
  · congr 1
    ext θ
    simp
  · intro x
    have e : hypPar k T' (y, x + 2 * Real.pi) = hypPar k T' (y, x) := by
      simp only [hypPar, Prod.mk.injEq, true_and]
      rw [show ((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I = (x : ℂ) * Complex.I + 2 * Real.pi * Complex.I by
        push_cast; ring, Complex.exp_periodic]
    simp only [Set.mem_preimage]
    rw [e]

theorem hypM_eq_kapT (k : ℕ) (T' : ℝ) (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) (hE : MeasurableSet E)
    (hS : E ⊆ hypS k T') : hypM k T' E = (1 / 2) * volume (kapT k '' E) := by
  rw [hypM_eq k T' E hE]
  congr 1
  have hFm : MeasurableSet (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) :=
    ((continuous_hypPar k T').measurable hE).inter (MeasurableSet.univ.prod measurableSet_Ioc)
  have hset : kapT k '' E =
      (fun x : TrE k => WithLp.ofLp (qFw k x)) ⁻¹' (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [ofLp_qFw_kapT k v, hypPar_toLp_arg_of_mem_hypS k T' v (hS hv)]
      exact ⟨hv, Complex.arg_mem_Ioc _⟩
    · rintro ⟨h1, h2⟩
      exact ⟨_, h1, kapT_hypPar_ofLp_qFw k T' hT' x h2⟩
  rw [hset, (qIso_measurePreserving k).measure_preimage hFm.nullMeasurableSet]

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if r ≤ i.val ∧ i.val < r + k then 1 else if i.val = r + k then -1 else 0

theorem gen_semiconj (k r : ℕ) (q : TrE k) :
    SemiconjBy (Matrix.diagonal (sgn k r)) (-opGen k r q) (opGen k r q)ᴴ := by
  show _ = _
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply]
  unfold opGen sgn
  split_ifs <;> (try (exfalso; omega)) <;> simp

private lemma exp_conjTranspose_mul_mul_exp_of_skew {n : Type*} [Fintype n] [DecidableEq n] (U X : Matrix n n ℂ)
    (hU : IsUnit U) (h : U * -X = Xᴴ * U) : (NormedSpace.exp X)ᴴ * U * NormedSpace.exp X = U := by
  have hdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have h1 : Xᴴ = U * -X * U⁻¹ := by rw [h, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  have h3 : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hU]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hdet, h3, Matrix.mul_one]

private lemma exp_opGen_conjTranspose_mul_diagonal_mul (k r : ℕ) (q : TrE k) (u : ℂ) (hu : u ≠ 0) :
    (NormedSpace.exp (opGen k r q))ᴴ * Matrix.diagonal (fun i => if sgn k r i = 0 then u else sgn k r i) *
      NormedSpace.exp (opGen k r q) = Matrix.diagonal (fun i => if sgn k r i = 0 then u else sgn k r i) := by
  have hsemi := gen_semiconj k r q
  unfold SemiconjBy at hsemi
  have hent : ∀ i j, sgn k r i * -opGen k r q i j = star (opGen k r q j i) * sgn k r j := by
    intro i j
    have := congrFun (congrFun hsemi i) j
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply] at this
  have hz : ∀ i j, sgn k r i = 0 → opGen k r q i j = 0 ∧ opGen k r q j i = 0 := by
    intro i j hi
    unfold sgn at hi
    split_ifs at hi with h1 h2
    · norm_num at hi
    · norm_num at hi
    · unfold opGen
      constructor <;> split_ifs <;> rfl
  apply exp_conjTranspose_mul_mul_exp_of_skew
  · refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
    rw [Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    split_ifs with h
    · exact hu
    · exact h
  · ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply]
    by_cases hi : sgn k r i = 0
    · obtain ⟨h1, h2⟩ := hz i j hi
      simp [h1, h2]
    by_cases hj : sgn k r j = 0
    · obtain ⟨h1, h2⟩ := hz j i hj
      simp [h1, h2]
    simp only [if_neg hi, if_neg hj]
    exact hent i j

theorem exp_form (k r : ℕ) (q : TrE k) :
    (NormedSpace.exp (opGen k r q))ᴴ * Matrix.diagonal (sgn k r) * NormedSpace.exp (opGen k r q) =
      Matrix.diagonal (sgn k r) := by
  have hD : Matrix.diagonal (sgn k r) = (1 / 2 : ℂ) •
      (Matrix.diagonal (fun i => if sgn k r i = 0 then 1 else sgn k r i) +
        Matrix.diagonal (fun i => if sgn k r i = 0 then -1 else sgn k r i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      split_ifs with h <;> [rw [h]; skip] <;> ring
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [hD, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    exp_opGen_conjTranspose_mul_diagonal_mul k r q 1 one_ne_zero, exp_opGen_conjTranspose_mul_diagonal_mul k r q (-1) (neg_ne_zero.2 one_ne_zero)]

private lemma wI_injective' (k r : ℕ) : Function.Injective (wI k r) := by
  intro a b h
  ext
  have := congrArg Fin.val h
  simp [wI] at this
  omega

theorem form_eq (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) :
    star v ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ v) =
      ((∑ i, Complex.normSq ((opCo k r v).1 i) - Complex.normSq (opCo k r v).2 : ℝ) : ℂ) := by
  have hs : star v ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ v) =
      ∑ j : Fin (k + 1), star (v (wI k r j)) * (sgn k r (wI k r j) * v (wI k r j)) := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
    symm
    refine Fintype.sum_of_injective _ (wI_injective' k r) _ (fun i => star (v i) * (sgn k r i * v i)) ?_ (fun _ => rfl)
    intro i hi
    have : sgn k r i = 0 := by
      unfold sgn
      rw [if_neg, if_neg]
      · intro h; exact hi ⟨⟨i.val - r, by omega⟩, by ext; simp [wI]; omega⟩
      · rintro ⟨h1, h2⟩; exact hi ⟨⟨i.val - r, by omega⟩, by ext; simp [wI]; omega⟩
    simp [this]
  have h1 : ∀ j : Fin k, sgn k r (wI k r j.castSucc) = 1 := by
    intro j; unfold sgn; rw [if_pos]; simp [wI]
  have h2 : sgn k r (wI k r (Fin.last k)) = -1 := by
    unfold sgn; rw [if_neg, if_pos] <;> simp [wI]
  rw [hs, Fin.sum_univ_castSucc, h2]
  simp only [h1, opCo]
  push_cast
  simp [Complex.normSq_eq_conj_mul_self, sub_eq_add_neg]

theorem opE_subset (k r : ℕ) (T' : ℝ) (hT' : 0 < T') (ρ : ℝ) : opE k r T' ρ ⊆ hypS k T' := by
  rintro p ⟨q, -, rfl⟩
  have hq : star (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T') ⬝ᵥ
      (Matrix.diagonal (sgn k r) *ᵥ (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) =
      star (opBase k r T') ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ opBase k r T') := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, exp_form]
  rw [form_eq, form_eq] at hq
  have hb : ∀ i : Fin k, opBase k r T' (wI k r i.castSucc) = 0 := by
    intro i
    have hne : wI k r i.castSucc ≠ wI k r (Fin.last k) := fun h => (Fin.castSucc_lt_last i).ne (wI_injective' k r h)
    simp [opBase, wLast, bvec, hne]
  have hl : opBase k r T' (wI k r (Fin.last k)) = (Real.sqrt T' : ℂ) := by
    simp [opBase, wLast, bvec]
  simp only [opCo, hb, hl, map_zero, Finset.sum_const_zero, Complex.normSq_ofReal,
    Real.mul_self_sqrt hT'.le] at hq
  simp only [hypS, Set.mem_ofPred_eq, opCo]
  linarith [Complex.ofReal_injective hq]

theorem hypChart : HypChart := by
  unfold HypChart
  intro k r T' hk hT'
  refine ⟨1, one_pos, fun ρ _ _ => ?_⟩
  have himg : phiT k r T' '' Metric.ball 0 ρ = kapT k '' opE k r T' ρ := by
    rw [opE, Set.image_image]; rfl
  rw [himg, hypM_eq_kapT k T' hT' _ (opEMeas k r T' ρ) (opE_subset k r T' hT' ρ)]

end GlobalTheory.HypChartPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PlacesInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem val_le_iff (T : LocAt F E sig p) (x y : F) :
    valuation T.Fp (T.ιF x) ≤ valuation T.Fp (T.ιF y) ↔ p.valuation F x ≤ p.valuation F y := by
  rw [← T.val, (valuation T.Fp).vle_iff_le]

theorem mem_int_iff (T : LocAt F E sig p) (x : F) :
    T.ιF x ∈ 𝒪[T.Fp] ↔ p.valuation F x ≤ 1 := by
  have h := val_le_iff T x 1
  simp only [map_one] at h
  rw [← h]; rfl

theorem val_lt_one_iff (T : LocAt F E sig p) (x : F) :
    valuation T.Fp (T.ιF x) < 1 ↔ p.valuation F x < 1 := by
  have h := val_le_iff T 1 x
  simp only [map_one] at h
  rw [← not_le, ← not_le, h]

theorem resQ_eq_absNorm (T : LocAt F E sig p) (ϖ : 𝒪[T.Fp]) (h : Irreducible ϖ) :
    resQ ϖ = Ideal.absNorm p.asIdeal := by
  haveI := T.lf
  have hm : ∀ z : 𝒪[T.Fp], z ∈ Ideal.span {ϖ} ↔ valuation T.Fp (z : T.Fp) < 1 := by
    intro z
    rw [← h.maximalIdeal_eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  let φ : 𝓞 F →+* 𝒪[T.Fp] := (T.ιF.comp (algebraMap (𝓞 F) F)).codRestrict _
    (fun a => (mem_int_iff T _).2 (p.valuation_le_one a))
  have hφ : ∀ a, ((φ a : 𝒪[T.Fp]) : T.Fp) = T.ιF (algebraMap (𝓞 F) F a) := fun a => rfl
  let ψ : 𝓞 F →+* 𝒪[T.Fp] ⧸ Ideal.span {ϖ} := (Ideal.Quotient.mk _).comp φ
  have hker : RingHom.ker ψ = p.asIdeal := by
    ext a
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (φ a) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, hm, hφ, val_lt_one_iff]
    exact p.valuation_lt_one_iff_mem (K := F) a
  have hsurj : Function.Surjective ψ := by
    intro w
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    have hn : {z : T.Fp | valuation T.Fp (z - y) < 1} ∈ nhds (y : T.Fp) :=
      IsValuativeTopology.mem_nhds_iff'.2 ⟨1, fun z hz => by simpa using hz⟩
    obtain ⟨x, hx⟩ := T.dense.mem_nhds hn
    have hx' : valuation T.Fp (T.ιF x - y) < 1 := hx
    have hy : valuation T.Fp (y : T.Fp) ≤ 1 := y.2
    have hx1 : valuation T.Fp (T.ιF x) ≤ 1 := by
      have : T.ιF x = (T.ιF x - y) + y := by ring
      rw [this]
      exact (valuation T.Fp).map_add_le hx'.le hy
    obtain ⟨a, ha⟩ := p.exists_valuation_sub_lt_of_integer ((mem_int_iff T x).1 hx1) 1
    refine ⟨a, ?_⟩
    change Ideal.Quotient.mk _ (φ a) = _
    rw [Ideal.Quotient.eq, hm]
    have ha' := (val_lt_one_iff T _).2 (by simpa using ha : p.valuation F (algebraMap (𝓞 F) F a - x) < 1)
    have : ((φ a - y : 𝒪[T.Fp]) : T.Fp) = T.ιF (algebraMap (𝓞 F) F a - x) + (T.ιF x - y) := by
      rw [map_sub, ← hφ]; push_cast; ring
    rw [this]
    exact (valuation T.Fp).map_add_lt ha' hx'
  rw [resQ, Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm

theorem nontrivial_Ep (T : LocAt F E sig p) : Nontrivial T.Ep :=
  Module.nontrivial_of_finrank_pos (R := T.Fp) (by rw [T.rank]; norm_num)

theorem exists_trace_norm (A : Places F E sig) (x : E) :
    ∃ t n : F, algebraMap F E t = x + sig x ∧ algebraMap F E n = x * sig x := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  haveI := nontrivial_Ep (A.loc p)
  have hss : ∀ y, sig (sig y) = y := by
    intro y
    apply (A.loc p).ιE.injective
    rw [← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]
  have hfix : ∀ y, sig y = y → ∃ a, algebraMap F E a = y := by
    haveI := Subalgebra.isSimpleOrder_of_finrank A.quad
    rcases eq_bot_or_eq_top (AlgHom.equalizer sig (AlgHom.id F E)) with h | h
    · intro y hy
      have : y ∈ AlgHom.equalizer sig (AlgHom.id F E) := hy
      rw [h, Algebra.mem_bot] at this
      exact this
    · exfalso
      have h1 : ∀ y, sig y = y := fun y => by
        have : y ∈ AlgHom.equalizer sig (AlgHom.id F E) := by rw [h]; trivial
        exact this
      have h2 : ∀ z, (A.loc p).cj z = z := by
        intro z
        have hz : z ∈ Submodule.span (A.loc p).Fp (Set.range (A.loc p).ιE) := by
          rw [(A.loc p).span]; trivial
        induction hz using Submodule.span_induction with
        | mem z hz => obtain ⟨y, rfl⟩ := hz; rw [(A.loc p).cj_ιE, h1]
        | zero => simp
        | add a b _ _ ha hb => rw [map_add (f := _), ha, hb]
        | smul c a _ ha => rw [map_smul, ha]
      have h3 : Function.Surjective (Algebra.linearMap (A.loc p).Fp (A.loc p).Ep) := by
        intro z
        exact ((A.L p).cj_fix z).1 (by rw [A.L_cj]; exact h2 z)
      have h4 := LinearMap.finrank_le_finrank_of_surjective h3
      rw [(A.loc p).rank, Module.finrank_self] at h4
      omega
  obtain ⟨t, ht⟩ := hfix (x + sig x) (by rw [map_add (f := _), hss, add_comm])
  obtain ⟨n, hn⟩ := hfix (x * sig x) (by rw [map_mul, hss, mul_comm])
  exact ⟨t, n, ht, hn⟩

theorem isIntegral_of_quad {R S : Type} [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S]
    (x y : S) (t n : R) (ht : algebraMap R S t = x + y) (hn : algebraMap R S n = x * y) :
    IsIntegral R x := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, ht, hn]
    ring

theorem mem_O_iff (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (x : E) (t n : F)
    (ht : algebraMap F E t = x + sig x) (hn : algebraMap F E n = x * sig x) :
    (A.loc p).ιE x ∈ (A.L p).O ↔ p.valuation F t ≤ 1 ∧ p.valuation F n ≤ 1 := by
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  haveI := nontrivial_Ep (A.loc p)
  have ht' : algebraMap _ (A.loc p).Ep ((A.loc p).ιF t)
      = (A.loc p).ιE x + (A.L p).cj ((A.loc p).ιE x) := by
    rw [← (A.loc p).compat, ht, map_add (f := _), A.L_cj, (A.loc p).cj_ιE]
  have hn' : algebraMap _ (A.loc p).Ep ((A.loc p).ιF n)
      = (A.loc p).ιE x * (A.L p).cj ((A.loc p).ιE x) := by
    rw [← (A.loc p).compat, hn, map_mul, A.L_cj, (A.loc p).cj_ιE]
  rw [← mem_int_iff (A.loc p), ← mem_int_iff (A.loc p)]
  constructor
  · intro hx
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[(A.loc p).Fp]
    obtain ⟨-, ⟨c, hc⟩, d, hd⟩ := (GlobalTheory.UnramOrder.order_facts (A.L p) ϖ hϖ).2.1 _ hx
    have hinj := (algebraMap (A.loc p).Fp (A.loc p).Ep).injective
    rw [hinj (ht'.trans hc), hinj (hn'.trans hd)]
    exact ⟨c.2, d.2⟩
  · rintro ⟨h1, h2⟩
    rw [(A.L p).O_def]
    exact isIntegral_of_quad (R := 𝒪[(A.loc p).Fp]) _ _ ⟨_, h1⟩ ⟨_, h2⟩ ht' hn'

theorem integers_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), (∀ x : E, (∀ p, (A.loc p).ιE x ∈ (A.L p).O) ↔ ∃ o : 𝓞 E, (o : E) = x) ∧ (∀ x : E, {p | (A.loc p).ιE x ∉ (A.L p).O}.Finite) ∧ (∀ (x : F) p, (A.loc p).ιF x ∈ 𝒪[(A.loc p).Fp] ↔ p.valuation F x ≤ 1) ∧ ∀ p (ϖ : 𝒪[(A.loc p).Fp]), Irreducible ϖ → resQ ϖ = Ideal.absNorm p.asIdeal := by
  intro F E _ _ _ _ _ sig A
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun x => ?_, fun x p => mem_int_iff _ x,
    fun p ϖ h => resQ_eq_absNorm _ ϖ h⟩
  · obtain ⟨t, n, ht, hn⟩ := exists_trace_norm A x
    have h := fun p => (mem_O_iff A p x t n ht hn).1 (hx p)
    obtain ⟨t', ht'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F t
      (fun p => (h p).1)
    obtain ⟨n', hn'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F n
      (fun p => (h p).2)
    have hi : IsIntegral (𝓞 F) x := isIntegral_of_quad x (sig x) t' n'
      (by rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, ht', ht])
      (by rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, hn', hn])
    exact ⟨⟨x, isIntegral_trans (R := ℤ) x hi⟩, rfl⟩
  · rintro ⟨o, rfl⟩ p
    rw [(A.L p).O_def]
    have h : IsIntegral ℤ ((A.loc p).ιE (o : E)) :=
      map_isIntegral_int (A.loc p).ιE o.isIntegral_coe
    exact h.tower_top
  · obtain ⟨t, n, ht, hn⟩ := exists_trace_norm A x
    refine ((HeightOneSpectrum.Support.finite (𝓞 F) t).union
      (HeightOneSpectrum.Support.finite (𝓞 F) n)).subset fun p hp => ?_
    have hp' : ¬ ((A.loc p).ιE x ∈ (A.L p).O) := hp
    rw [mem_O_iff A p x t n ht hn, not_and_or, not_le, not_le] at hp'
    exact hp'

end GlobalTheory.HL.PlacesInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexComapPairOfDenseImage
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem index_comap_of_dense_image {A B : Type} [Group A] [Group B] (f : A →* B) (H : Subgroup B)
    (hf : ∀ b, ∃ a, (f a)⁻¹ * b ∈ H) : (H.comap f).index = H.index := by
  first
  | exact @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | (apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit ..)

theorem relIndex_comap_of_dense_image {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G)
    (K U : Subgroup G) (h : ∀ g ∈ U, ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) :
    (K.comap φ).relIndex (U.comap φ) = K.relIndex U := by
  let f : U.comap φ →* U := φ.subgroupComap U
  have hc : (K.comap φ).subgroupOf (U.comap φ) = (K.subgroupOf U).comap f := by
    ext x
    exact Iff.rfl
  have key := index_comap_of_dense_image f (K.subgroupOf U) (by
    rintro ⟨b, hb⟩
    obtain ⟨γ, hγK, hγU⟩ := h b hb
    have hγ : φ γ ∈ U := by
      have := U.mul_mem hb (U.inv_mem hγU)
      simpa using this
    refine ⟨⟨γ, hγ⟩, ?_⟩
    exact hγK)
  simp only [Subgroup.relIndex]
  rw [hc, key]

theorem relIndex_pair_comap_of_dense_image : ∀ {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G) (K U : Subgroup G), (∀ g, g ∈ K ∨ g ∈ U → ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) → (K.comap φ).relIndex (U.comap φ) = K.relIndex U ∧ (U.comap φ).relIndex (K.comap φ) = U.relIndex K := by
  intro Γ G _ _ φ K U h
  refine ⟨relIndex_comap_of_dense_image φ K U fun g hg => h g (Or.inr hg), ?_⟩
  refine relIndex_comap_of_dense_image φ U K fun g hg => ?_
  obtain ⟨γ, hγ⟩ := h g (Or.inl hg)
  exact ⟨γ, by rwa [inf_comm]⟩

end GlobalTheory.HL
end

