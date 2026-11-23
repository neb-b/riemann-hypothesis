module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CMDepthAssoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence Pointwise

theorem length_le_ringKrullDim_quotient_colon {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (rs : List R) : ∀ {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (y : M), y ≠ 0 →
      (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular M rs →
        (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R M) {y}) := by
  induction rs with
  | nil =>
    intro M _ _ _ y hy _ _
    have hne : Submodule.colon (⊥ : Submodule R M) {y} ≠ ⊤ := by
      intro h
      have h1 : (1 : R) ∈ Submodule.colon (⊥ : Submodule R M) {y} := h ▸ Submodule.mem_top
      rw [Submodule.mem_colon_singleton, one_smul] at h1
      exact hy ((Submodule.mem_bot R).mp h1)
    have := Ideal.Quotient.nontrivial_iff.mpr hne
    simpa using (ringKrullDim_nonneg_of_nontrivial : 0 ≤ ringKrullDim (R ⧸ _))
  | cons x rs ih =>
    intro M _ _ _ y hy hmem hreg
    have hx : x ∈ maximalIdeal R := hmem x List.mem_cons_self
    have hmem' : ∀ r ∈ rs, r ∈ maximalIdeal R := fun r hr => hmem r (List.mem_cons_of_mem x hr)
    obtain ⟨hxreg, hrs⟩ := (isWeaklyRegular_cons_iff M x rs).mp hreg

    have hspan : Ideal.span {x} ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ (Ideal.span_le.mpr (by simpa using hx))))
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) (Ideal.span {x}) hspan
    have hpow : ∀ k : ℕ, (Ideal.span {x} ^ k • ⊤ : Submodule R M) = x ^ k • ⊤ := fun k => by
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
    have hex : ∃ n : ℕ, y ∉ (Ideal.span {x} ^ n • ⊤ : Submodule R M) := by
      by_contra! h
      exact hy ((Submodule.mem_bot R).mp (hK ▸ Submodule.mem_iInf _ |>.mpr h))
    classical
    let n := Nat.find hex
    have hn : y ∉ (Ideal.span {x} ^ n • ⊤ : Submodule R M) := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h0
      apply hn
      rw [h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hyk : y ∈ (Ideal.span {x} ^ k • ⊤ : Submodule R M) := by
      have := Nat.find_min hex (show k < n by omega)
      simpa using this
    rw [hpow] at hyk hn
    obtain ⟨y₁, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hyk
    have hy₁ : y₁ ∉ (x • ⊤ : Submodule R M) := by
      intro h
      obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h
      apply hn
      rw [hk, smul_smul, ← pow_succ]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    have hcolon : Submodule.colon (⊥ : Submodule R M) {x ^ k • y₁} =
        Submodule.colon (⊥ : Submodule R M) {y₁} := by
      ext r
      simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
      rw [smul_comm]
      constructor
      · intro h
        exact (hxreg.pow k) (show x ^ k • r • y₁ = x ^ k • 0 by rw [h, smul_zero])
      · intro h
        rw [h, smul_zero]
    rw [hcolon]

    set I := Submodule.colon (⊥ : Submodule R M) {y₁} with hI
    set ybar : QuotSMulTop x M := Submodule.Quotient.mk y₁ with hybar
    have hybar0 : ybar ≠ 0 := by
      rw [hybar, Ne, Submodule.Quotient.mk_eq_zero]
      exact hy₁
    have hih := ih ybar hybar0 hmem' hrs

    have hle : I ⊔ Ideal.span {x} ≤ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar} := by
      refine sup_le ?_ ?_
      · intro r hr
        rw [hI, Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hybar, ← Submodule.Quotient.mk_smul, hr,
          Submodule.Quotient.mk_zero]
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_colon_singleton,
          Submodule.mem_bot, hybar, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    have hd1 : ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar}) ≤
        ringKrullDim (R ⧸ (I ⊔ Ideal.span {x})) :=
      ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)

    have hnzd : Ideal.Quotient.mk I x ∈ nonZeroDivisors (R ⧸ I) := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI, Submodule.mem_colon_singleton,
        Submodule.mem_bot, mul_smul, smul_comm] at hz
      rw [Ideal.Quotient.eq_zero_iff_mem, hI, Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact hxreg (show x • r • y₁ = x • 0 by rw [hz, smul_zero])
    have hd2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
    have heq : (R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x} ≃+* R ⧸ (I ⊔ Ideal.span {x}) := by
      have : Ideal.span {Ideal.Quotient.mk I x} = (Ideal.span {x}).map (Ideal.Quotient.mk I) := by
        rw [Ideal.map_span, Set.image_singleton]
      rw [this]
      exact DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {x})
    rw [ringKrullDim_eq_of_ringEquiv heq] at hd2
    calc ((x :: rs).length : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar}) + 1 := by
          gcongr
      _ ≤ ringKrullDim (R ⧸ (I ⊔ Ideal.span {x})) + 1 := by gcongr
      _ ≤ ringKrullDim (R ⧸ I) := hd2

theorem ringKrullDim_quotient_eq_of_mem_minimalPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B]
    {P : Ideal B} (hP : P ∈ minimalPrimes B) : ringKrullDim (B ⧸ P) = ringKrullDim B := by
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hann : Module.annihilator B B = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hP' : P ∈ (Module.annihilator B B).minimalPrimes := by
    rw [hann]
    exact hP
  have hA := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B B hP'
  obtain ⟨hprime, y, hy⟩ := (isAssociatedPrime_iff.mp hA)
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs y hy0 hm hreg
  rw [← hy, ← hdim] at hD
  exact le_antisymm (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective) hD

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.MeasurableOfContinuousOnNeZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix

noncomputable section

theorem le_ringKrullDim_slice {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    (hJ : IsAffVariety J (e + 1)) (hH : IsHomogIdeal J) (hℓ : linForm ℓ ∉ J) :
    ((e : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) := by
  have hP := hJ.isPrime
  have hne : J ⊔ Ideal.span {linForm ℓ - 1} ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial (Fin n) ℂ) ∈ J :=
      GroundTheory.Heights₂.Heights.ChartDehomog.proof ℂ n J ℓ 1 0 hP hH hℓ (isHomogeneous_one _ _)
        (htop ▸ Submodule.mem_top)
    exact hP.ne_top ((Ideal.eq_top_iff_one J).mpr h1)
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
  have hpP : p.IsPrime := hp.1.1
  have hJp : J ≤ p := le_sup_left.trans hp.1.2
  have hht := Ideal.map_height_le_one_of_mem_minimalPrimes hp
  have hpm : (p.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := ℂ)
    (p.map (Ideal.Quotient.mk J))
  rw [hJ.dim, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJp)] at hform
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hp.1.2)
      (Ideal.Quotient.factor_surjective hp.1.2)
  refine le_trans ?_ hle
  have key : ∀ a b : ℕ∞, a ≤ 1 → a + b = ((e + 1 : ℕ) : ℕ∞) → (e : ℕ∞) ≤ b := by
    intro a b ha hab
    induction b using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      induction a using ENat.recTopCoe with
      | top => simp at ha
      | coe k =>
        have h1 : k ≤ 1 := by exact_mod_cast ha
        have h2 : k + m = e + 1 := by exact_mod_cast hab
        exact_mod_cast (by omega : e ≤ m)
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) = D at hform ⊢
  induction D using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.add_bot] at hform
    exact WithBot.bot_ne_coe hform
  | coe b =>
    have hab : (p.map (Ideal.Quotient.mk J)).height + b = ((e + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast hform
    exact_mod_cast key _ b hht hab

theorem exists_isChowForm_iff {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : IsProjPrime J) :
    (∃ F : MvPolynomial (Fin (e + 1) × Fin n) ℂ, IsChowForm J (e + 1) F) ↔
      IsAffVariety J (e + 1) :=
  ⟨fun ⟨F, hF⟩ => ⟨hJ.isPrime, GroundTheory.Heights₂.Heights.ConeDimOfChowForm.of_affineChartTrdeg
      GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof ℂ n (e + 1) J F hJ hF⟩,
    fun hA => GroundTheory.Heights₂.Heights.ChowFormExists.of_affineChartTrdeg
      GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof ℂ n (e + 1) J hJ hA.dim⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchAwayFromRim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem BranchAwayFromRim.proof (hex : NormalModelExists.Statement)
    (hprop : NormalModelProper.Statement) (hlift : BranchLift.Statement)
    (hirr : NormalLocallyIrreducible.Statement) (hext : BranchContainsNormalPoint.Statement) :
    BranchAwayFromRim.Statement := by
  intro n k J u p x m γ hJ hdim hu hcov hdisj b
  obtain ⟨N, hN, hcovN⟩ := hcov
  obtain ⟨M⟩ := hex n J hJ
  set Z' := zeroSetIn M.ideal with hZ'
  have hcontν : Continuous (firstCoords : (Fin n ⊕ Fin M.m → ℂ) → Fin n → ℂ) :=
    continuous_pi fun i => continuous_apply _
  have hZc : IsClosed Z' := by
    have hZ'eq : Z' = ⋂ q ∈ M.ideal, {z | eval z q = 0} := by ext z; simp [Z', zeroSetIn]
    rw [hZ'eq]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hνZ : ∀ w ∈ Z', firstCoords w ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J := by
    intro w hw q hq
    have hq' : rename Sum.inl q ∈ M.ideal := by rw [← M.comap_eq] at hq; exact hq
    have := hw _ hq'
    rwa [eval_rename] at this

  choose Γ hΓd hΓZ hΓopen using fun c => hlift n k J p M (γ c) hJ hdim
  have hΓinj : ∀ c, Set.InjOn (Γ c) (Metric.ball 0 (γ c).radius) := by
    intro c s hs t ht hst
    apply (γ c).injOn hs ht
    rw [← (hΓZ c s hs).2, ← (hΓZ c t ht).2, hst]
  choose O hOo hOeq using fun c => hΓopen c (Metric.ball 0 (γ c).radius) subset_rfl Metric.isOpen_ball

  choose a bd hbJ hab using M.birational
  set g : MvPolynomial (Fin n) ℂ := GroundTheory.Heights₂.Heights.linForm u * ∏ i, bd i with hg
  have hgJ : g ∉ J := by
    have := hJ
    intro hgm
    rcases hJ.mem_or_mem hgm with h1 | h2
    · exact hu h1
    · obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h2
      exact hbJ i hi
  set h : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := rename Sum.inl g with hh_def
  have hh : h ∉ M.ideal := by
    intro hm
    apply hgJ
    rw [← M.comap_eq]
    exact hm
  have heval : ∀ w : Fin n ⊕ Fin M.m → ℂ,
      eval w h = GroundTheory.Heights₂.Heights.linEval u (firstCoords w) *
        ∏ i, eval (firstCoords w) (bd i) := by
    intro w
    simp only [h, g, eval_rename, map_mul, map_prod]
    congr 1
    simp [GroundTheory.Heights₂.Heights.linForm, GroundTheory.Heights₂.Heights.linEval, firstCoords, Function.comp_def]
  have hinj : ∀ w ∈ Z', ∀ w' ∈ Z', firstCoords w = firstCoords w' → eval w h ≠ 0 → w = w' := by
    intro w hw w' hw' hνw hne
    rw [heval] at hne
    have hb : ∀ i, eval (firstCoords w) (bd i) ≠ 0 := fun i hi =>
      hne (by rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero])
    funext s
    rcases s with j | i
    · exact congrFun hνw j
    · have e1 := hw _ (hab i)
      have e2 := hw' _ (hab i)
      simp only [map_sub, map_mul, eval_rename, eval_X] at e1 e2
      have c1 : w ∘ Sum.inl = firstCoords w := rfl
      have c2 : w' ∘ Sum.inl = firstCoords w := by rw [hνw]; rfl
      rw [c1] at e1
      rw [c2] at e2
      apply mul_left_cancel₀ (hb i)
      linear_combination e1 - e2

  by_contra hcon
  push Not at hcon
  set r := (γ b).radius with hr
  have hseq : ∀ j : ℕ, ∃ τ ∈ Metric.ball (0 : Fin k → ℂ) r,
      (γ b).toFun τ ∈ Metric.ball x (1 / ((j : ℝ) + 1)) ∧ r - 1 / ((j : ℝ) + 1) < ‖τ‖ := by
    intro j
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    exact hcon _ hpos _ (by linarith)
  choose τ hτr hτx hτn using hseq
  have hmem : ∀ j, Γ b (τ j) ∈ {w | w ∈ Z' ∧ firstCoords w ∈ Metric.closedBall x 1} := by
    intro j
    refine ⟨(hΓZ b (τ j) (hτr j)).1, ?_⟩
    rw [(hΓZ b (τ j) (hτr j)).2, Metric.mem_closedBall]
    have h1 := Metric.mem_ball.mp (hτx j)
    have h2 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    linarith
  obtain ⟨xh, hxcl, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (hprop n J M _ Metric.isBounded_closedBall) hmem
  have hlim' : Tendsto (fun j => Γ b (τ (φ j))) atTop (𝓝 xh) := hlim
  have hxZ : xh ∈ Z' := hZc.closure_subset_iff.mpr (by exact fun w hw => hw.1) hxcl
  have h1j : Tendsto (fun j => 1 / ((φ j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hγlim : Tendsto (fun j => (γ b).toFun (τ (φ j))) atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun j => dist_nonneg) (fun j => (Metric.mem_ball.mp (hτx (φ j))).le) h1j
  have hνx : firstCoords xh = x := by
    refine tendsto_nhds_unique ((hcontν.tendsto xh).comp hlim') ?_
    refine hγlim.congr fun j => ?_
    exact ((hΓZ b _ (hτr _)).2).symm

  have hUN : firstCoords ⁻¹' N ∈ 𝓝 xh :=
    hcontν.continuousAt.preimage_mem_nhds (by rw [hνx]; exact hN)
  obtain ⟨B, hBo, hxB, hBU, hpre, hdense⟩ :=
    hirr (Fin n ⊕ Fin M.m) M.ideal h xh M.isPrime M.isIntegrallyClosed hh hxZ _ hUN
  set P := (Z' ∩ B) \ {z | eval z h = 0} with hP

  have hPcov : ∀ q ∈ P, ∃ c, q ∈ Γ c '' Metric.ball 0 (γ c).radius := by
    rintro q ⟨⟨hqZ, hqB⟩, hqh⟩
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcovN ⟨hνZ q hqZ, hBU hqB⟩)
    obtain ⟨t, ht, hteq⟩ := hc
    refine ⟨c, t, ht, ?_⟩
    have hν : firstCoords (Γ c t) = firstCoords q := by rw [(hΓZ c t ht).2, hteq]
    refine hinj _ (hΓZ c t ht).1 q hqZ hν ?_
    rw [heval, hν, ← heval]
    exact hqh
  have hPdisj : ∀ q ∈ P, ∀ c c', c ≠ c' → q ∈ Γ c '' Metric.ball 0 (γ c).radius →
      q ∉ Γ c' '' Metric.ball 0 (γ c').radius := by
    rintro q ⟨-, hqh⟩ c c' hcc' ⟨t, ht, rfl⟩ ⟨t', ht', hteq⟩
    have h1 : firstCoords (Γ c t) ∈ (γ c).image := ⟨t, ht, ((hΓZ c t ht).2).symm⟩
    have h2 : firstCoords (Γ c t) ∈ (γ c').image :=
      ⟨t', ht', by rw [← (hΓZ c' t' ht').2, hteq]⟩
    have h3 := hdisj c c' hcc' ⟨h1, h2⟩
    apply hqh
    show eval (Γ c t) h = 0
    rw [heval]
    rw [show GroundTheory.Heights₂.Heights.linEval u (firstCoords (Γ c t)) = 0 from h3, zero_mul]

  have hPsub : P ⊆ Γ b '' Metric.ball 0 r := by
    have hsplit := isPreconnected_iff_subset_of_disjoint.mp hpre (O b) (⋃ c ∈ {c | c ≠ b}, O c)
      (hOo b) (isOpen_biUnion fun c _ => hOo c) ?_ ?_
    · rcases hsplit with hs | hs
      · intro q hq
        rw [hOeq b]
        exact ⟨hq.1.1, hs hq⟩
      · exfalso
        obtain ⟨j, hjB⟩ := (hlim'.eventually (hBo.mem_nhds hxB)).exists
        have hw0 : Γ b (τ (φ j)) ∈ Γ b '' Metric.ball 0 r := ⟨_, hτr _, rfl⟩
        have hw0O : Γ b (τ (φ j)) ∈ O b := by
          have := hw0
          rw [hOeq b] at this
          exact this.2
        have hw0P := hdense ⟨(hΓZ b _ (hτr _)).1, hjB⟩
        obtain ⟨q, hqO, hqP⟩ := mem_closure_iff.mp hw0P (O b) (hOo b) hw0O
        obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.mp (hs hqP)
        have hqb : q ∈ Γ b '' Metric.ball 0 r := by rw [hOeq b]; exact ⟨hqP.1.1, hqO⟩
        have hqc' : q ∈ Γ c '' Metric.ball 0 (γ c).radius := by rw [hOeq c]; exact ⟨hqP.1.1, hqc⟩
        exact hPdisj q hqP b c (Ne.symm hc) hqb hqc'
    · intro q hq
      obtain ⟨c, hc⟩ := hPcov q hq
      rw [hOeq c] at hc
      by_cases hcb : c = b
      · subst hcb
        exact Or.inl hc.2
      · exact Or.inr (Set.mem_biUnion hcb hc.2)
    · ext q
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hqP hqb hqv
      obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.mp hqv
      have h1 : q ∈ Γ b '' Metric.ball 0 r := by rw [hOeq b]; exact ⟨hqP.1.1, hqb⟩
      have h2 : q ∈ Γ c '' Metric.ball 0 (γ c).radius := by rw [hOeq c]; exact ⟨hqP.1.1, hqc⟩
      exact hPdisj q hqP b c (Ne.symm hc) h1 h2

  obtain ⟨σ0, hσ0, hσx⟩ := hext (Fin n ⊕ Fin M.m) M.ideal h xh k r (Γ b) B M.isPrime
    M.isIntegrallyClosed hh hxZ (hΓd b) (hΓinj b) (fun t ht => (hΓZ b t ht).1)
    (hBo.mem_nhds hxB) hPsub

  have hσ0' : ‖σ0‖ < r := mem_ball_zero_iff.mp hσ0
  set δ := (r - ‖σ0‖) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hVsub : Metric.ball σ0 δ ⊆ Metric.ball 0 r := by
    intro t ht
    rw [mem_ball_zero_iff]
    have h1 : ‖t‖ ≤ ‖σ0‖ + dist t σ0 := by
      rw [dist_eq_norm]
      calc ‖t‖ = ‖σ0 + (t - σ0)‖ := by rw [add_sub_cancel]
        _ ≤ ‖σ0‖ + ‖t - σ0‖ := norm_add_le _ _
    have h2 := Metric.mem_ball.mp ht
    linarith
  obtain ⟨O', hO'o, hO'eq⟩ := hΓopen b (Metric.ball σ0 δ) hVsub Metric.isOpen_ball
  have hxO' : xh ∈ O' := by
    have : xh ∈ Γ b '' Metric.ball σ0 δ := ⟨σ0, Metric.mem_ball_self hδpos, hσx⟩
    rw [hO'eq] at this
    exact this.2
  obtain ⟨j, hjO, hjδ⟩ :=
    ((hlim'.eventually (hO'o.mem_nhds hxO')).and (h1j.eventually (gt_mem_nhds hδpos))).exists
  have hjV : Γ b (τ (φ j)) ∈ Γ b '' Metric.ball σ0 δ := by
    rw [hO'eq]
    exact ⟨(hΓZ b _ (hτr _)).1, hjO⟩
  obtain ⟨t, ht, hteq⟩ := hjV
  have htτ : t = τ (φ j) := hΓinj b (hVsub ht) (hτr _) hteq
  have hn1 : ‖τ (φ j)‖ < ‖σ0‖ + δ := by
    rw [← htτ]
    have h2 := Metric.mem_ball.mp ht
    rw [dist_eq_norm] at h2
    calc ‖t‖ = ‖σ0 + (t - σ0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖σ0‖ + ‖t - σ0‖ := norm_add_le _ _
      _ < ‖σ0‖ + δ := by linarith
  have hn2 := hτn (φ j)
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveProperClosedFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem CurveProperClosedFinite.no_chain_two {R : Type*} [CommRing R] {W P Q : Ideal R}
    (hW : W.IsPrime) (hP : P.IsPrime) (hQ : Q.IsPrime) (hdim : ringKrullDim (R ⧸ W) = 1)
    (hWP : W < P) (hPQ : P < Q) : False := by
  let a : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨W, hW⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 le_rfl⟩
  let b : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨P, hP⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 hWP.le⟩
  let c : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨Q, hQ⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 (hWP.trans hPQ).le⟩
  have hab : a < b := hWP
  have hbc : b < c := hPQ
  let p0 : LTSeries (PrimeSpectrum.zeroLocus (R := R) (W : Set R)) := RelSeries.singleton _ a
  have h2 := Order.LTSeries.length_le_krullDim ((p0.snoc b hab).snoc c hbc)
  rw [← ringKrullDim_quotient, hdim] at h2
  have hl : ((p0.snoc b hab).snoc c hbc).length = 2 := by
    rfl
  rw [hl] at h2
  norm_num at h2

theorem CurveProperClosedFinite.proof : CurveProperClosedFinite.Statement := by
  intro n W K hW hdim hK
  let m : (Fin n → ℂ) → Ideal (MvPolynomial (Fin n) ℂ) := fun x => RingHom.ker (eval x)
  have hinj : Function.Injective m := by
    intro x y hxy
    funext i
    have hx : X i - C (x i) ∈ m x := by simp [m, RingHom.mem_ker]
    have hy : X i - C (x i) ∈ m y := hxy ▸ hx
    have hy' : y i - x i = 0 := by simpa [m, RingHom.mem_ker] using hy
    exact (sub_eq_zero.1 hy').symm
  have hsub : m '' (zeroSet W ∩ zeroSet K) ⊆ (W ⊔ K).minimalPrimes := by
    rintro _ ⟨x, ⟨hxW, hxK⟩, rfl⟩
    have hmax : (m x).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective (eval x) (fun c => ⟨C c, by simp⟩)
    have hle : W ⊔ K ≤ m x := sup_le (fun q hq => hxW q hq) (fun q hq => hxK q hq)
    refine ⟨⟨hmax.isPrime, hle⟩, fun Q ⟨hQ, hJQ⟩ hQm => ?_⟩
    by_contra hmQ
    have hWQ : W < Q := by
      refine lt_of_le_of_ne (le_sup_left.trans hJQ) ?_
      rintro rfl
      exact hK (le_sup_right.trans hJQ)
    exact CurveProperClosedFinite.no_chain_two hW hQ hmax.isPrime hdim hWQ (lt_of_le_of_ne hQm
      (fun h => hmQ (h ▸ le_rfl)))
  exact Set.Finite.of_finite_image
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset hsub) hinj.injOn

end GroundTheory.Heights₂.Heights
end

