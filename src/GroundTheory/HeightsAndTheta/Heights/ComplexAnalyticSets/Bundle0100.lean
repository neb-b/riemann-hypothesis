module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsPiola
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0089
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0084

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensLogPow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology Matrix

noncomputable section

namespace MaDensLogPow

variable {D : ℕ}

theorem det_eq_zero_of_rows_smul (M : Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ℂ) {i j : Fin D}
    (hij : i ≠ j) (a b : ℂ) (hi : M i = a • w) (hj : M j = b • w) : M.det = 0 := by
  by_cases ha : a = 0
  · exact Matrix.det_eq_zero_of_row_eq_zero i fun k => by simp [hi, ha]
  · rw [← Matrix.det_updateRow_add_smul_self M hij.symm (-(b / a))]
    refine Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [updateRow_self, hi, hj]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

theorem mdisc_eq_zero_of_two_rankOne (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ℂ)
    {a b : Fin D} (hab : a ≠ b) (x x' : Fin D → ℂ) (ha : A a = vecMulVec x w)
    (hb : A b = vecMulVec x' w) : mdisc A = 0 := by
  rw [mdisc_eq_sum_polCoef]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun r _ => ?_)
  by_cases hr : Function.Surjective r
  · obtain ⟨i, hi⟩ := hr a
    obtain ⟨j, hj⟩ := hr b
    have hij : i ≠ j := fun h => hab (by rw [← hi, ← hj, h])
    refine mul_eq_zero_of_right _ (det_eq_zero_of_rows_smul _ w hij (x i) (x' j) ?_ ?_)
    · funext k; simp [hi, ha, vecMulVec_apply]
    · funext k; simp [hj, hb, vecMulVec_apply]
  · rw [polCoef_eq_zero r hr, zero_mul]

theorem mdisc_expand (α β : ℂ) (H G : Matrix (Fin D) (Fin D) ℂ)
    (hG : ∀ (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (i j : Fin D), i ≠ j → A i = G → A j = G →
      mdisc A = 0) :
    ∀ (s : Finset (Fin D)) (C : Fin D → Matrix (Fin D) (Fin D) ℂ), (∀ i ∈ s, C i = H) →
      mdisc (fun i => if i ∈ s then α • H + β • G else C i) =
        α ^ s.card * mdisc C + α ^ (s.card - 1) * β * ∑ i ∈ s, mdisc (Function.update C i G) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro C _; simp
  | insert j s hj ih =>
    intro C hC
    have hCj : C j = H := hC j (Finset.mem_insert_self j s)
    have hCs : ∀ i ∈ s, C i = H := fun i hi => hC i (Finset.mem_insert_of_mem hi)
    have e1 : (fun i => if i ∈ insert j s then α • H + β • G else C i) =
        Function.update (fun i => if i ∈ s then α • H + β • G else C i) j (α • H + β • G) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have e2 : Function.update (fun i => if i ∈ s then α • H + β • G else C i) j H =
        (fun i => if i ∈ s then α • H + β • G else C i) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp [hj, hCj]
      · simp [Function.update_of_ne hij]
    have e3 : Function.update (fun i => if i ∈ s then α • H + β • G else C i) j G =
        (fun i => if i ∈ s then α • H + β • G else Function.update C j G i) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp [hj]
      · simp [Function.update_of_ne hij]
    have hCs' : ∀ i ∈ s, Function.update C j G i = H := fun i hi => by
      rw [Function.update_of_ne (by rintro rfl; exact hj hi)]; exact hCs i hi
    have hz : ∀ i ∈ s, mdisc (Function.update (Function.update C j G) i G) = 0 := fun i hi =>
      hG _ i j (by rintro rfl; exact hj hi) (by simp)
        (by rw [Function.update_of_ne (by rintro rfl; exact hj hi)]; simp)
    rw [e1, mdisc_update_add, mdisc_update_smul, mdisc_update_smul, e2, e3, ih C hCs,
      ih _ hCs', Finset.sum_eq_zero hz, Finset.card_insert_of_notMem hj, Finset.sum_insert hj]
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [h0, Finset.card_eq_zero.mp h0]; simp
    · obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      ring

theorem cons_const_apply {n : ℕ} (A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (k : Fin (n + 1 + 1)) :
    (Fin.cons A₀ (fun _ : Fin (n + 1) => H) : Fin (n + 1 + 1) → _) k = if k = 0 then A₀ else H := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · simp [Fin.succ_ne_zero]

theorem cons_cons_const_apply {n : ℕ} (G A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (k : Fin (n + 1 + 1)) :
    (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _) k =
      if k = 0 then G else if k = 1 then A₀ else H := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · refine Fin.cases ?_ (fun l => ?_) i
    · simp
    · have h1 : (l.succ.succ : Fin (n + 1 + 1)) ≠ 1 := by
        rw [← Fin.succ_zero_eq_one]; exact fun h => Fin.succ_ne_zero l (Fin.succ_injective _ h)
      simp [Fin.succ_ne_zero, h1]

theorem mdisc_update_eq {n : ℕ} (G A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (i : Fin (n + 1 + 1))
    (hi : i ≠ 0) :
    mdisc (Function.update (Fin.cons A₀ (fun _ : Fin (n + 1) => H) : Fin (n + 1 + 1) → _) i G) =
      mdisc (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _) := by
  rw [← mdisc_comp_perm (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _)
    ((Equiv.swap 1 i).trans (Equiv.swap 0 1))]
  congr 1
  funext k
  simp only [Function.comp_apply, cons_const_apply, cons_cons_const_apply, Function.update_apply,
    Equiv.trans_apply, Equiv.swap_apply_def]
  have h01 : (0 : Fin (n + 1 + 1)) ≠ 1 := by
    rw [← Fin.succ_zero_eq_one]; exact (Fin.succ_ne_zero 0).symm
  by_cases hki : k = i
  · subst hki
    by_cases hk1 : k = 1
    · subst hk1; simp [Ne.symm h01]
    · simp [hk1]
  · by_cases hk0 : k = 0
    · subst hk0; simp [Ne.symm hi, h01]
    · by_cases hk1 : k = 1
      · subst hk1; simp [hki, Ne.symm hki, hi, Ne.symm h01]
      · simp [hki, hk0, hk1]

theorem hessC_log_comp {p : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (hp : ContDiffAt ℝ 2 p y) (hpos : 0 < p y) :
    hessC (Real.log ∘ p) y =
      (((p y)⁻¹ : ℝ) : ℂ) • hessC p y + ((-((p y) ^ 2)⁻¹ : ℝ) : ℂ) • gradMat p p y := by
  set c := p y / 2 with hc
  have hc0 : 0 < c := by positivity
  set h : ℝ → ℝ := fun t => c / 2 + Real.smoothTransition ((t - c / 2) / (c / 2)) * (t - c / 2) with hh
  have hhpos : ∀ t, 0 < h t := by
    intro t
    by_cases ht : t ≤ c / 2
    · have : (t - c / 2) / (c / 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      simp only [hh, Real.smoothTransition.zero_of_nonpos this, zero_mul, add_zero]; positivity
    · have := Real.smoothTransition.nonneg ((t - c / 2) / (c / 2))
      have : 0 ≤ Real.smoothTransition ((t - c / 2) / (c / 2)) * (t - c / 2) :=
        mul_nonneg this (by linarith)
      simp only [hh]; linarith
  have hhc : ContDiff ℝ 2 h := by
    have hs : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff (n := 2)
    exact contDiff_const.add ((hs.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
      (contDiff_id.sub contDiff_const))
  set F : ℝ → ℝ := Real.log ∘ h with hF
  have hFc : ContDiff ℝ 2 F := hhc.log fun t => (hhpos t).ne'
  have hFeq : F =ᶠ[𝓝 (p y)] Real.log := by
    filter_upwards [Ioi_mem_nhds (show c < p y by rw [hc]; linarith)] with t ht
    have h1 : 1 ≤ (t - c / 2) / (c / 2) := by
      rw [le_div_iff₀ (by positivity)]; simp only [Set.mem_Ioi] at ht; linarith
    simp only [hF, hh, Function.comp_apply, Real.smoothTransition.one_of_one_le h1, one_mul]
    ring_nf
  have hgerm : Real.log ∘ p =ᶠ[𝓝 y] F ∘ p :=
    ((hp.continuousAt.tendsto.eventually hFeq).mono fun x hx => hx.symm)
  have hgerm2 : hessC (Real.log ∘ p) y = hessC (F ∘ p) y := by
    unfold hessC
    rw [hgerm.fderiv.fderiv_eq]
  have hd1 : deriv F (p y) = (p y)⁻¹ := by rw [hFeq.deriv_eq, Real.deriv_log]
  have hd2 : deriv (deriv F) (p y) = -((p y) ^ 2)⁻¹ := by
    rw [hFeq.deriv.deriv_eq, Real.deriv_log', deriv_inv]
  rw [hgerm2, MaDensChain.hessC_comp_real F p y hFc hp, hd1, hd2]

theorem proof : MaDensLogPow.Statement := by
  intro e φ₀ p y hp hpos
  set H := hessC p y with hH
  set G := gradMat p p y with hGdef
  set A₀ := hessC φ₀ y with hA₀
  set a : ℝ := (p y)⁻¹ with ha
  set b : ℝ := -((p y) ^ 2)⁻¹ with hb
  have hlog : hessC (Real.log ∘ p) y = (a : ℂ) • H + (b : ℂ) • G := hessC_log_comp hp hpos
  have hG : ∀ (A : Fin (e + 1 + 1) → Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (i j : Fin (e + 1 + 1)),
      i ≠ j → A i = G → A j = G → mdisc A = 0 := fun A i j hij hi hj =>
    mdisc_eq_zero_of_two_rankOne A _ hij _ _ (hi.trans (gradMat_eq_vecMulVec p p y))
      (hj.trans (gradMat_eq_vecMulVec p p y))
  set s : Finset (Fin (e + 1 + 1)) := Finset.univ.erase 0 with hs
  have hscard : s.card = e + 1 := by simp [hs]
  set C : Fin (e + 1 + 1) → Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
    Fin.cons A₀ (fun _ : Fin (e + 1) => H) with hC
  have hCs : ∀ i ∈ s, C i = H := fun i hi => by
    rw [hC, cons_const_apply, if_neg (Finset.ne_of_mem_erase hi)]
  have key := mdisc_expand (a : ℂ) (b : ℂ) H G hG s C hCs
  rw [Finset.sum_congr rfl fun i hi => mdisc_update_eq G A₀ H i (Finset.ne_of_mem_erase hi),
    Finset.sum_const, hscard, Nat.add_sub_cancel, nsmul_eq_mul] at key
  have hfam1 : (fun k => hessC ((Fin.cons φ₀ fun _ : Fin (e + 1) => Real.log ∘ p :
      Fin (e + 1 + 1) → (Fin (e + 1 + 1) → ℂ) → ℝ) k) y) =
      fun i => if i ∈ s then (a : ℂ) • H + (b : ℂ) • G else C i := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [hs, hC, hA₀]
    · simp [hs, Fin.succ_ne_zero, hlog]
  have hfam2 : (fun k => hessC ((Fin.cons φ₀ fun _ : Fin (e + 1) => p :
      Fin (e + 1 + 1) → (Fin (e + 1 + 1) → ℂ) → ℝ) k) y) = C := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [hC, hA₀]
    · simp [hC, hH]
  have hfam3 : (fun i => hessC ((Fin.cons φ₀ fun _ : Fin e => p :
      Fin (e + 1) → (Fin (e + 1 + 1) → ℂ) → ℝ) i) y) = Fin.cons A₀ (fun _ : Fin e => H) := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [hA₀]
    · simp [hH]
  unfold maDens gradDens
  rw [hfam1, hfam2, hfam3, key]
  have hp0 : p y ≠ 0 := hpos.ne'
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.add_re,
    Complex.re_ofReal_mul]
  rw [← hGdef, ha, hb]
  simp only [inv_pow, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

end MaDensLogPow

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCodimOneUniformiser
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

noncomputable section

theorem isDiscreteValuationRing_localization_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (hq : q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  have hbot : q ≠ ⊥ := by
    intro h
    rw [← Ideal.height_eq_zero_iff_eq_bot] at h
    rw [h] at hq
    exact zero_ne_one hq
  have : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  have hdim : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
    rfl
  have : Ring.KrullDimLE 1 (Localization.AtPrime q) := by
    rw [Ring.krullDimLE_iff, hdim]
    rfl
  have hnf : ¬ IsField (Localization.AtPrime q) := IsLocalization.AtPrime.not_isField A hbot _
  have huniq : ∃! P : Ideal (Localization.AtPrime q), P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨maximalIdeal (Localization.AtPrime q), ?_, fun P hP => ?_⟩
    · exact And.intro (isField_iff_maximalIdeal_eq.not.mp hnf) inferInstance
    have : P.IsPrime := hP.2
    exact IsLocalRing.eq_maximalIdeal (this.isMaximal_of_ne_bot hP.1)
  have h3 : IsIntegrallyClosed (Localization.AtPrime q) ∧
      ∃! P : Ideal (Localization.AtPrime q), P ≠ ⊥ ∧ P.IsPrime := And.intro inferInstance huniq
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q) hnf).out 1 4).mpr h3

theorem NormalCodimOneUniformiser.proof : NormalCodimOneUniformiser.Statement := by
  intro σ _ P Q e x hP hQ hPQ hnorm hdimP hdimQ hxQ hxP
  let π : MvPolynomial σ ℂ →+* MvPolynomial σ ℂ ⧸ P := Ideal.Quotient.mk P
  have : IsDomain (MvPolynomial σ ℂ ⧸ P) := Ideal.Quotient.isDomain P
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)
  have : IsNoetherianRing (MvPolynomial σ ℂ ⧸ P) := Algebra.FiniteType.isNoetherianRing ℂ _
  have : FiniteRingKrullDim (MvPolynomial σ ℂ ⧸ P) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨by rw [hdimP]; exact WithBot.natCast_ne_bot _, by
      rw [hdimP]
      rw [← WithBot.coe_natCast, Ne, WithBot.coe_eq_top]
      exact ENat.natCast_ne_top _⟩
  set q : Ideal (MvPolynomial σ ℂ ⧸ P) := Q.map π with hqdef
  have : q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hPQ
  have hmem : ∀ r, π r ∈ q ↔ r ∈ Q := fun r => by
    rw [← Ideal.mem_comap, hqdef, Ideal.comap_map_mk hPQ]

  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ (MvPolynomial σ ℂ ⧸ P)
  have key := ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (A := MvPolynomial σ ℂ ⧸ P)
    (fun M N hM hN => (hs M hM).trans (hs N hN).symm) q
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ), hdimQ, hdimP] at key
  obtain ⟨n, hn⟩ : ∃ n : ℕ, q.height = n :=
    ⟨q.height.toNat, (ENat.natCast_toNat (Ideal.height_ne_top Ideal.IsPrime.ne_top')).symm⟩
  rw [hn] at key
  have hn1 : n = 1 := by
    have : ((e + n : ℕ) : WithBot ℕ∞) = ((e + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast key
    have : e + n = e + 1 := by exact_mod_cast this
    omega
  have hht : q.height = 1 := by rw [hn, hn1]; rfl

  have : IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ P) := hnorm
  have : IsDiscreteValuationRing (Localization.AtPrime q) :=
    isDiscreteValuationRing_localization_of_height_eq_one q hht
  have hinj : Function.Injective (algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q)) :=
    IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors
  have hmax : ∀ y, algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) y ∈ maximalIdeal (Localization.AtPrime q) ↔ y ∈ q := fun y =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q y

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)
  obtain ⟨⟨a₀, s₀⟩, hs₀⟩ := IsLocalization.mk'_surjective q.primeCompl ϖ
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a₀
  have hgirr : Irreducible (algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π g)) := by
    have h1 : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π g) = ϖ * algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) s₀ := by
      rw [← hs₀]; exact (IsLocalization.mk'_spec (Localization.AtPrime q) (Ideal.Quotient.mk P g) s₀).symm
    rw [h1]
    exact (irreducible_mul_isUnit (IsLocalization.map_units (Localization.AtPrime q) s₀)).mpr hϖ
  have hgQ : g ∈ Q := by
    rw [← hmem, ← hmax, IsLocalRing.mem_maximalIdeal]
    exact hgirr.not_isUnit

  have hx0 : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π x) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q)), hinj.eq_iff]
    intro h
    exact hxP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (R := Localization.AtPrime q) hx0 hgirr
  have hxmax : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π x) ∈ maximalIdeal (Localization.AtPrime q) := (hmax _).mpr ((hmem x).mpr hxQ)
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero, mul_one] at hu
      rw [IsLocalRing.mem_maximalIdeal, hu] at hxmax
      exact absurd u.isUnit hxmax
    · exact h
  obtain ⟨⟨c, d⟩, hcd⟩ := IsLocalization.mk'_surjective q.primeCompl (u : (Localization.AtPrime q))
  have hcu : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) c = (u : (Localization.AtPrime q)) * algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) d := by
    rw [← hcd]; exact (IsLocalization.mk'_spec (Localization.AtPrime q) c d).symm
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (d : MvPolynomial σ ℂ ⧸ P)
  have haQ : a ∉ Q := by
    rw [← hmem, ← hmax, IsLocalRing.mem_maximalIdeal, hcu]
    exact fun h => h ((u.isUnit).mul (IsLocalization.map_units (Localization.AtPrime q) d))
  have hbQ : b ∉ Q := by
    rw [← hmem]
    change Ideal.Quotient.mk P b ∈ q → False
    rw [hb]
    exact d.2
  have hrel : b * x - a * g ^ k ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change π (b * x - a * g ^ k) = 0
    apply hinj
    simp only [map_zero, map_sub, map_mul, map_pow]
    change algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (Ideal.Quotient.mk P b) * _ - algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (Ideal.Quotient.mk P a) * _ = 0
    rw [hb, hcu, hu]
    ring

  have hunif := (IsDiscreteValuationRing.irreducible_iff_uniformizer (R := Localization.AtPrime q) _).mp hgirr
  have hgen : ∀ p ∈ Q, ∃ t : MvPolynomial σ ℂ, t ∉ Q ∧ t * p ∈ P ⊔ Ideal.span {g} := by
    intro p hp
    have hpm : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π p) ∈ maximalIdeal (Localization.AtPrime q) := (hmax _).mpr ((hmem p).mpr hp)
    rw [hunif] at hpm
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hpm
    obtain ⟨⟨c', d'⟩, hcd'⟩ := IsLocalization.mk'_surjective q.primeCompl y
    obtain ⟨c₁, rfl⟩ := Ideal.Quotient.mk_surjective c'
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (d' : MvPolynomial σ ℂ ⧸ P)
    refine ⟨t, ?_, ?_⟩
    · rw [← hmem]
      change Ideal.Quotient.mk P t ∈ q → False
      rw [ht]
      exact d'.2
    · have hrel' : t * p - c₁ * g ∈ P := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        change π (t * p - c₁ * g) = 0
        apply hinj
        simp only [map_zero, map_sub, map_mul]
        change algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (Ideal.Quotient.mk P t) * _ - _ = 0
        have hspec : IsLocalization.mk' (Localization.AtPrime q) (Ideal.Quotient.mk P c₁) d' *
            algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) d' =
            algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π c₁) :=
          IsLocalization.mk'_spec _ _ _
        dsimp only at hcd'
        rw [ht, ← hy, ← hcd', ← hspec]
        ring
      have : t * p = (t * p - c₁ * g) + c₁ * g := by ring
      rw [this]
      exact add_mem (Ideal.mem_sup_left hrel')
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian Q : Q.FG)
  have hgenS : ∀ y ∈ S, ∃ t : MvPolynomial σ ℂ, t ∉ Q ∧ t * y ∈ P ⊔ Ideal.span {g} := fun y hy =>
    hgen y (hS ▸ Submodule.subset_span hy)
  choose! T hTQ hT using hgenS
  refine ⟨g, a, b, ∏ y ∈ S, T y, k, hgQ, hk, haQ, hbQ, ?_, hrel, fun p hp => ⟨1, ?_⟩⟩
  · rw [hQ.prod_mem_iff]
    rintro ⟨y, hy, h⟩
    exact hTQ y hy h
  · rw [pow_one]
    rw [← hS] at hp
    induction hp using Submodule.span_induction with
    | mem y hy =>
      rw [← Finset.prod_erase_mul S T hy, mul_assoc]
      exact Ideal.mul_mem_left _ _ (hT y hy)
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ r hy

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeGermFiniteProjection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem PrimeGermFiniteProjection.exists_of_step (hStep : PrimeGermProjectionStep.Statement) :
    ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (P : Ideal (holGerms w)), P.IsPrime →
      ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A := by
  have key : ∀ (n : ℕ) (σ : Type) [Fintype σ], Fintype.card σ = n → ∀ (w : σ → ℂ) (P : Ideal (holGerms w)),
      P.IsPrime → ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro σ _ hn w P hP
      by_cases h0 : P = ⊥
      · subst h0
        exact isFiniteGermProjection_bot w
      · exact hStep σ w P hP h0 fun τ _ hτ v Q hQ => ih _ (hn ▸ hτ) τ rfl v Q hQ
  intro σ _ w P hP
  exact key _ σ rfl w P hP

theorem PrimeGermFiniteProjection.proof (hStep : PrimeGermProjectionStep.Statement)
    (hFF : GermProjectionFunctionForm.Statement) : PrimeGermFiniteProjection.Statement := by
  intro σ _ w k p hp hP
  obtain ⟨d, A, hA⟩ := PrimeGermFiniteProjection.exists_of_step hStep σ w _ hP
  exact ⟨d, A, hFF σ w k p d A hp hA⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open scoped nonZeroDivisors

noncomputable section

theorem SliceIdeal.isHomogeneous_linForm {n : ℕ} (u : Fin n → ℂ) : (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j

theorem SliceIdeal.exists_homogeneous_sub_mem {n : ℕ} (ℓ : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    ∃ d, ∃ G : MvPolynomial (Fin n) ℂ, G.IsHomogeneous d ∧ G - f ∈ Ideal.span {linForm ℓ - 1} := by
  classical
  refine ⟨f.totalDegree, ∑ i ∈ Finset.range (f.totalDegree + 1),
      linForm ℓ ^ (f.totalDegree - i) * homogeneousComponent i f, ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h := ((SliceIdeal.isHomogeneous_linForm ℓ).pow (f.totalDegree - i)).mul
      (homogeneousComponent_isHomogeneous i f)
    convert h using 1
    omega
  · have hsum : (∑ i ∈ Finset.range (f.totalDegree + 1),
          linForm ℓ ^ (f.totalDegree - i) * homogeneousComponent i f) - f =
        ∑ i ∈ Finset.range (f.totalDegree + 1),
          (linForm ℓ ^ (f.totalDegree - i) - 1) * homogeneousComponent i f := by
      conv_lhs => arg 2; rw [← sum_homogeneousComponent f]
      rw [← Finset.sum_sub_distrib]
      simp only [sub_one_mul]
    rw [hsum]
    refine Ideal.sum_mem _ fun i _ => ?_
    refine Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr ?_)
    simpa using sub_dvd_pow_sub_pow (linForm ℓ) 1 (f.totalDegree - i)

end

end GroundTheory.Heights₂.Heights
end

