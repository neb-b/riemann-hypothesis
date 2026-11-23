module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PullEqGaussSmulIntertwiner
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.UnitaryTheta.Constant

section General

open Complex MeasureTheory
open scoped Real ComplexConjugate

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [MeasurableSpace V] [BorelSpace V]

theorem const_eq (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V) (hH : IsPosHerm H) (a : V ≃ₗ[ℂ] V)
    (ha : ∀ z w, H (a z) (a w) = H z w) (hdet : LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0)
    (C : V →ₗ[ℂ] V) (hC : ∀ x, C (x - a x) = (1 / 2 : ℂ) • (x + a x))
    (A A₁ : AddSubgroup V) [DiscreteTopology A] (hfg : A.FG) (hsp : Submodule.span ℝ (A : Set V) = ⊤)
    [Finite (A₁ ⧸ A.addSubgroupOf A₁)] (hA₁ : ∀ y, a y ∈ A → y ∈ A₁)
    (hint : ∀ x ∈ A₁, ∀ y ∈ A₁, ∃ m : ℤ, (H x y).im = m)
    (α : V → ℂ) (hα : IsSemichar H A α) (hαa : ∀ y, α (a y) = α y) (hαn : ∀ y, α (-y) = α y)
    (m : ℕ) (hm : 0 < m) (hmA : ∀ x ∈ A, ∃ y ∈ A, a y ∈ A ∧ m • x = y - a y)
    (c : ℂ) (n : ℝ) (hn : 0 < n)
    (hc : ∀ z w, kerSum H A α z (a w) = c * ((n : ℂ) * ∑ᶠ q : A₁ ⧸ A.addSubgroupOf A₁,
      α ((q.out : A₁) : V) * Heisenberg₂ H ((q.out : A₁) : V) (kerSum H A α z) w)) :
    ∃ r : ℝ, 0 < r ∧ c = r * (LinearMap.det (1 - (a : V →ₗ[ℂ] V)))⁻¹ *
      ∑ᶠ q : A ⧸ (subLa m A).addSubgroupOf A, α ((q.out : A) : V) *
        cexp (-(π : ℂ) * H (C ((q.out : A) : V)) ((q.out : A) : V)) := by
  set B : V →ₗ[ℂ] V := C + (1 / 2 : ℂ) • LinearMap.id with hBdef
  have hB1 : ∀ y, B (y - a y) = y := by
    intro y
    simp only [hBdef, LinearMap.add_apply, hC, LinearMap.smul_apply, LinearMap.id_apply]
    module
  have hsurj : ∀ x, ∃ y, x = y - a y := by
    intro x
    have hu : IsUnit (1 - (a : V →ₗ[ℂ] V)) := (LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet)
    obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 hu).2 x
    exact ⟨y, by rw [← hy]; simp⟩
  have hB2 : ∀ x, B x - a (B x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    rw [hB1]
  have hCB : ∀ x, H (C x) x = I * ((H (B x) x).im : ℂ) := by
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    rw [hB1, hC]
    have h1 := hH.1 (a y) y
    have h2 : (H y y).im = 0 := Complex.conj_eq_iff_im.1 (hH.1 y y).symm
    simp only [map_smul, map_add (f := _), map_sub, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, ha, h1,
      smul_eq_mul]
    apply Complex.ext <;> simp [h2] <;> ring
  let Λ : AddSubgroup V := (subLa m A).comap (1 - (a : V →ₗ[ℂ] V)).toAddMonoidHom
  have hΛ : ∀ y, y ∈ Λ ↔ y - a y ∈ subLa m A := fun y => by simp [Λ]
  have hΛ' : ∀ y ∈ Λ, y ∈ A ∧ a y ∈ A := by
    intro y hy
    obtain ⟨x, hx, e⟩ := (hΛ y).1 hy
    obtain ⟨y', h1, h2, h3⟩ := hmA x hx
    have : y = y' := by
      rw [← hB1 y, ← hB1 y', ← h3, ← e]; rfl
    rw [this]; exact ⟨h1, h2⟩
  have hle : Λ ≤ A := fun y hy => (hΛ' y hy).1
  have hdisc : DiscreteTopology Λ := DiscreteTopology.of_subset (s := (A : Set V)) inferInstance hle
  have hspan : Submodule.span ℝ (Λ : Set V) = ⊤ := by
    have h1 : ∀ x ∈ Submodule.span ℝ (A : Set V), B x ∈ Submodule.span ℝ (Λ : Set V) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        have h2 : B (m • x) ∈ Λ := by
          rw [hΛ, hB2]; exact ⟨x, hx, rfl⟩
        have h3 : B x = (m : ℝ)⁻¹ • B (m • x) := by
          rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
        rw [h3]
        exact Submodule.smul_mem _ _ (Submodule.subset_span h2)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
      | smul t x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro y _
    rw [← hB1 y]
    exact h1 _ (hsp ▸ Submodule.mem_top)
  obtain ⟨k, b, hb⟩ := GlobalTheory.ThetaInter.exists_basis hdisc hspan
  have hFd : IsAddFundamentalDomain Λ (ZSpan.fundamentalDomain b) μ := by
    rw [← hb]; exact ZSpan.isAddFundamentalDomain' b μ
  have hfin : μ (ZSpan.fundamentalDomain b) ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne
  have hpos : 0 < μ.real (ZSpan.fundamentalDomain b) :=
    ENNReal.toReal_pos (ZSpan.measure_fundamentalDomain_ne_zero b) hfin
  haveI : Finite (A ⧸ (subLa m A).addSubgroupOf A) :=
    GlobalTheory.ThetaInter.finite_quot hfg fun x hx => ⟨m, hm, x, hx, rfl⟩
  letI := Fintype.ofFinite (A ⧸ (subLa m A).addSubgroupOf A)
  letI := Fintype.ofFinite (A₁ ⧸ A.addSubgroupOf A₁)
  obtain ⟨κ, hκ, hL⟩ := Graph.integral_kerSum_graph_eq V μ H hH a ha hdet B hB2 A Λ hle (fun y hy => (hΛ' y hy).2) α hα
    (fun y _ => hαa y) _ hFd (A ⧸ (subLa m A).addSubgroupOf A) (fun q => ((q.out : A) : V)) (fun q => (q.out : A).2) (by
      intro x hx
      have h1 : ((((⟨x, hx⟩ : A) : A ⧸ (subLa m A).addSubgroupOf A).out : A) : V) - x ∈ subLa m A := by
        have := QuotientAddGroup.eq.1
          (Quotient.out_eq ((⟨x, hx⟩ : A) : A ⧸ (subLa m A).addSubgroupOf A)).symm
        rw [AddSubgroup.mem_addSubgroupOf] at this
        simpa [neg_add_eq_sub] using this
      refine ⟨(((⟨x, hx⟩ : A) : A ⧸ (subLa m A).addSubgroupOf A), ⟨B _, by rw [hΛ, hB2]; exact h1⟩), ?_, ?_⟩
      · simp only [hB2]; abel
      · rintro ⟨q, y, hy⟩ e
        simp only at e
        have hq : q = ((⟨x, hx⟩ : A) : A ⧸ (subLa m A).addSubgroupOf A) := by
          rw [← Quotient.out_eq q]
          refine (QuotientAddGroup.eq.2 ?_).symm
          rw [AddSubgroup.mem_addSubgroupOf]
          convert (hΛ y).1 hy using 1
          simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
          rw [e]; abel
        subst hq
        refine Prod.ext rfl (Subtype.ext ?_)
        simp only
        rw [← hB1 y]
        congr 1
        exact (sub_sub_cancel _ _).symm.trans (congrArg _ e.symm))
  have hR := fun q : A₁ ⧸ A.addSubgroupOf A₁ => integral_heis_kerSum_diag V μ H hH A Λ hle α hα _ hFd hfin
    ((q.out : A₁) : V) fun y hy => hint _ (q.out : A₁).2 y (hA₁ y (hΛ' y hy).2)
  have hsum : ∫ z in ZSpan.fundamentalDomain b, kerSum H A α z (a z) * cexp (-(π : ℂ) * H z z) ∂μ =
      c * n * (μ.real (ZSpan.fundamentalDomain b) : ℂ) := by
    have e : ∀ z, kerSum H A α z (a z) * cexp (-(π : ℂ) * H z z) = c * n * ∑ q : A₁ ⧸ A.addSubgroupOf A₁,
        α ((q.out : A₁) : V) * (Heisenberg₂ H ((q.out : A₁) : V) (kerSum H A α z) z * cexp (-(π : ℂ) * H z z)) := by
      intro z
      rw [hc, finsum_eq_sum_of_fintype]
      simp only [← mul_assoc, ← Finset.sum_mul]
    simp only [e]
    rw [integral_const_mul, integral_finsetSum _ fun q _ => (hR q).1.const_mul _]
    congr 1
    rw [Finset.sum_eq_single 0]
    · have h0 := (GlobalTheory.ThetaInter.out_mem_iff (A₁ := A) (A₂ := A₁) 0).2 rfl
      rw [integral_const_mul, (hR 0).2, if_pos h0, hαn, ← mul_assoc]
      rcases hα.1 _ h0 with h | h <;> simp [h]
    · intro q _ hq
      rw [integral_const_mul, (hR q).2, if_neg (fun h => hq ((GlobalTheory.ThetaInter.out_mem_iff q).1 h)), mul_zero]
    · simp
  refine ⟨κ / (n * μ.real (ZSpan.fundamentalDomain b)), by positivity, ?_⟩
  rw [finsum_eq_sum_of_fintype]
  simp only [hCB]
  have e : ∀ t : ℂ, -(π : ℂ) * (I * t) = -((π : ℂ) * I) * t := fun t => by ring
  simp only [e]
  rw [hsum] at hL
  have h1 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2 : (μ.real (ZSpan.fundamentalDomain b) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast
  field_simp
  field_simp at hL
  linear_combination hL

end General


open MeasureTheory GlobalTheory.ThetaInter in
theorem pull_eq_gauss_smul_intertwiner : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → ∀ (C : VC D N N' →ₗ[ℂ] VC D N N'), (∀ x, C (x - u.symm x) = (1 / 2 : ℂ) • (x + u.symm x)) → ∀ m : ℕ, 0 < m → (∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → ∀ th ∈ ThSp D (tor0 D cc δ) A, th ≠ 0 → ∃ (c : ℂ) (r : ℝ), ‖c‖ = 1 ∧ 0 < r ∧ c = r * (LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')))⁻¹ * (∑ᶠ q : A ⧸ (subLa m A).addSubgroupOf A, al D (tor0 D cc δ) ((q.out : A) : VC D N N') * Complex.exp (-(Real.pi : ℂ) * Hf D (tor0 D cc δ) (C ((q.out : A) : VC D N N')) ((q.out : A) : VC D N N'))) ∧ (fun z => th (u.symm z)) = c • Iop D (tor0 D cc δ) A A₁ th := by
  intro D cc δ hc N N' A A₁ h₁ h₂ u hu hA hdet C hC m hm hmA th hth hne
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨f₁, s₁, d₁, c₁⟩ := klat_facts hc h₁
  obtain ⟨f₂, -, -, -⟩ := klat_facts hc h₂
  obtain ⟨l₁, -, i₁, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hc N N' A h₁
  obtain ⟨l₂, -, i₂, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hc N N' A₁ h₂
  have := klat_finite hG.1 hc.1.1 h₁ h₂ f₂
  have : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (VC D N N')).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have t₁ := discrete_of_selfDual (isHerm_sesqOf D (tor0 D cc δ) N N') d₁ f₁
  obtain ⟨L, hL⟩ := _root_.GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  have hH := isPosHerm_formV D (tor0 D cc δ) N N' (_root_.GlobalTheory.PlaneLattice.area_pos_and_selfDual L _ hL).1
  have hα : IsSemichar (formV D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) := by
    refine ⟨c₁.1, i₁, fun x hx y hy => ?_⟩
    rw [c₁.2 x hx y hy]
    obtain ⟨k, hk⟩ := i₁ x hx y hy
    congr 1
    change Complex.exp (_ * ((Hf D _ x y).im : ℂ)) = Complex.exp (_ * ((Hf D _ x y).im : ℂ))
    rw [hk, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨k, by push_cast; ring⟩
  obtain ⟨p₁, p₂, p₃⟩ := GlobalTheory.ThetaIso.theta_transport D cc δ hc N N' A A₁ h₁ h₂ u hu hA th hth
  obtain ⟨-, q₁, q₂, q₃⟩ := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' A A₁ h₁ h₂ th hth
  have hsm : ∀ (B B' : AddSubgroup (VC D N N')) [Finite (B' ⧸ B.addSubgroupOf B')] (t : ℂ) (G : VC D N N' → ℂ),
      Iop D (tor0 D cc δ) B B' (t • G) = t • Iop D (tor0 D cc δ) B B' G := by
    intro B B' _ t G
    letI := Fintype.ofFinite (B' ⧸ B.addSubgroupOf B')
    funext z
    simp only [Iop, U, finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hI : Iop D (tor0 D cc δ) A A₁ th ≠ 0 := by
    intro h
    apply hne
    rw [← q₃, h]
    funext z
    simp [Iop, U]
  obtain ⟨c, hcI⟩ := l₂ _ p₁ _ q₁ hI
  have hnorm : ‖c‖ = 1 := by
    have h1 : normSq D (tor0 D cc δ) A₁ (c • Iop D (tor0 D cc δ) A A₁ th) =
        ‖c‖ ^ 2 * normSq D (tor0 D cc δ) A₁ (Iop D (tor0 D cc δ) A A₁ th) := by
      simp only [normSq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_assoc, average_eq, integral_const_mul]
      ring
    rw [← hcI, p₂, q₂] at h1
    have h2 : ‖c‖ ^ 2 = 1 := by
      have := (p₃ hne).ne'
      field_simp at h1
      exact h1.symm
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [h2, one_pow])
  have hu' : ∀ z w, Hf D (tor0 D cc δ) (u.symm z) (u.symm w) = Hf D (tor0 D cc δ) z w := fun z w => by
    rw [← hu, u.apply_symm_apply, u.apply_symm_apply]
  obtain ⟨-, k₁, k₂⟩ := KerSum.kerSum_spec _ _ hH A _ hα
  have hidx : 0 < ((A.addSubgroupOf A₁).index : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero AddSubgroup.index_ne_zero_of_finite
  obtain ⟨r, hr, hrc⟩ := const_eq volume (formV D (tor0 D cc δ) N N') hH u.symm hu' hdet C hC A A₁ f₁ s₁
    (fun y hy => by simpa using (hA _).1 hy) i₂ (al D (tor0 D cc δ)) hα (fun y => by simp only [al, hu'])
    (fun y => by simp [al, Hf]) m hm hmA c (Real.sqrt ((A.addSubgroupOf A₁).index : ℝ))⁻¹
    (inv_pos.2 (Real.sqrt_pos.2 hidx)) (by
      intro z w
      obtain ⟨t, ht⟩ := l₁ _ ⟨k₁ z, k₂ z⟩ th hth hne
      have h1 : kerSum (formV D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) z (u.symm w) =
          c * Iop D (tor0 D cc δ) A A₁ (kerSum (formV D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) z) w := by
        rw [ht, hsm]
        have := congrFun hcI w
        simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
        rw [this]; ring
      rw [h1, Iop, Complex.ofReal_inv]
      rfl)
  exact ⟨c, r, hnorm, hr, hrc, hcI⟩

end GlobalTheory.UnitaryTheta.Constant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarMulSqEqProdKernelQuotients
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

noncomputable section

namespace GlobalTheory.EvenTheta.MulLat

variable {Λ : AddSubgroup ℂ}

theorem trFac_ne (z ω : ℂ) : GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ≠ 0 := Complex.exp_ne_zero _

theorem differentiable_trFac (ω : ℂ) : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ z ω := by
  unfold GlobalTheory.EvenTheta.Fibres.trFac
  fun_prop

theorem exists_sg_mul_sq (h : IsLat Λ) {β : ℂ} (hβ : ∀ ω ∈ Λ, β * ω ∈ Λ) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, sgStar Λ (β * z) ^ 2 = sgStar Λ z ^ 2 * G z := by
  have hσ := h.differentiable
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (h.sg_eq_zero z).not.2 hz
  set u := dslope (sgStar Λ) 0 with hu_def
  have hU : Differentiable ℂ u :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 hσ.differentiableOn)
  have hu0 : u 0 = 1 := by
    rw [hu_def, dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.1]
  have eu : ∀ z, sgStar Λ z = z * u z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(h.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  refine exists_entire_of_locally_dvd (F := fun z => sgStar Λ (β * z) ^ 2) (S := fun z => sgStar Λ z ^ 2)
    (h.dense_compl.mono fun z hz => pow_ne_zero 2 (hne z hz)) fun w => ?_
  by_cases hw : w ∈ Λ
  · have hT := differentiable_trFac (Λ := Λ) w
    have hT' := differentiable_trFac (Λ := Λ) (β * w)
    set D : ℂ → ℂ := fun z => u (z - w) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) ^ 2
      with hD_def
    have hD : Differentiable ℂ D := by
      rw [hD_def]
      have h1 : Differentiable ℂ fun z => u (z - w) := hU.comp (by fun_prop)
      have h2 : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) :=
        hT'.comp (by fun_prop)
      fun_prop
    have hD0 : D w ≠ 0 := by
      simp only [hD_def, sub_self, hu0]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (trFac_ne _ _))
    set N : ℂ → ℂ := fun z => β ^ 2 * u (β * (z - w)) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (z - w) w ^ 2
      with hN_def
    have hN : Differentiable ℂ N := by
      rw [hN_def]
      have h1 : Differentiable ℂ fun z => u (β * (z - w)) := hU.comp (by fun_prop)
      have h2 : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ (z - w) w :=
        hT.comp (by fun_prop)
      fun_prop
    refine ⟨fun z => N z / D z, (hN.analyticAt w).div (hD.analyticAt w) hD0, ?_⟩
    filter_upwards [hD.continuous.continuousAt.eventually_ne hD0] with z hz
    have hz1 : u (z - w) ≠ 0 := fun h0 => hz (by simp [hD_def, h0])
    have e1 := GlobalTheory.EvenTheta.Fibres.sg_sq h hw (z - w)
    have e2 := GlobalTheory.EvenTheta.Fibres.sg_sq h (hβ w hw) (β * (z - w))
    rw [sub_add_cancel] at e1
    rw [show β * (z - w) + β * w = β * z by ring] at e2
    have t1 := trFac_ne (Λ := Λ) (z - w) w
    have t2 := trFac_ne (Λ := Λ) (β * (z - w)) (β * w)
    simp only [hN_def, hD_def]
    rw [eu (z - w)] at e1
    rw [eu (β * (z - w))] at e2
    have hz' : u (z - w) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) ^ 2 ≠ 0 := hz
    rw [mul_div_assoc', eq_div_iff hz']
    linear_combination u (z - w) ^ 2 * e2 - β ^ 2 * u (β * (z - w)) ^ 2 * e1
  · refine ⟨fun z => sgStar Λ (β * z) ^ 2 / sgStar Λ z ^ 2,
      (((hσ.comp (by fun_prop : Differentiable ℂ fun z => β * z)).pow 2).analyticAt w).div
        ((hσ.analyticAt w).pow 2) (pow_ne_zero 2 (hne w hw)), ?_⟩
    filter_upwards [hσ.continuous.continuousAt.eventually_ne (hne w hw)] with y hy
    field_simp

end GlobalTheory.EvenTheta.MulLat

namespace GlobalTheory.EvenTheta.MulLat

variable {Λ : AddSubgroup ℂ}

theorem val_zero (h : IsLat Λ) {β : ℂ} {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (eG : ∀ z, sgStar Λ (β * z) ^ 2 = sgStar Λ z ^ 2 * G z) : G 0 = β ^ 2 := by
  have hσ := h.differentiable
  set u := dslope (sgStar Λ) 0 with hu_def
  have hU : Differentiable ℂ u :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 hσ.differentiableOn)
  have hu0 : u 0 = 1 := by
    rw [hu_def, dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.1]
  have eu : ∀ z, sgStar Λ z = z * u z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(h.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  have hGc := hG.continuous
  have hUc := hU.continuous
  have key := congrFun (Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    (f := fun z => u z ^ 2 * G z) (g := fun z => β ^ 2 * u (β * z) ^ 2) (by fun_prop)
    (by fun_prop) fun z hz => by
      have hz : z ≠ 0 := hz
      have e := eG z
      rw [eu, eu z] at e
      refine mul_left_cancel₀ (pow_ne_zero 2 hz) ?_
      beta_reduce
      linear_combination -e) 0
  simpa [hu0] using key

theorem sg_mul_sq : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (β : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β * starRingEnd ℂ β = ((k + 1 : ℕ) : ℂ) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ ∧ β * Q i ∈ Λ) ∧ ∀ z, sgStar Λ (β * z) ^ 2 = β ^ 2 * sgStar Λ z ^ 2 * ∏ i, sqTh Λ (Q i) z := by
  intro Λ h β k hβ hN
  have hβ0 : β ≠ 0 := by
    rintro rfl
    norm_num at hN
    exact Nat.cast_add_one_ne_zero k hN.symm
  have hσ := h.differentiable
  have hσc := hσ.continuous
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (h.sg_eq_zero z).not.2 hz
  obtain ⟨G, hG, eG⟩ := exists_sg_mul_sq h hβ
  have hGc := hG.continuous
  have hG0 := val_zero h hG eG
  have hev : ∀ z, G (-z) = G z := fun z => by
    refine congrFun (Continuous.ext_on h.dense_compl (f := fun z => G (-z)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have h1 := eG (-z)
    rw [h.sg_neg, neg_sq, mul_neg, h.sg_neg, neg_sq] at h1
    exact h1.symm.trans (eG z)
  have hlaw : ∀ ω ∈ Λ, ∀ z, G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k) = G z := by
    intro ω hω z
    have hTc : Continuous fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ z ω :=
      (differentiable_trFac ω).continuous
    refine congrFun (Continuous.ext_on h.dense_compl
      (f := fun z => G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have ea := GlobalTheory.EvenTheta.Fibres.sg_sq h hω z
    have eb := GlobalTheory.EvenTheta.Fibres.sg_sq h (hβ ω hω) (β * z)
    rw [GlobalTheory.EvenTheta.Fibres.trFac_mul hN] at eb
    have egz := eG z
    have egw := eG (z + ω)
    rw [mul_add] at egw
    beta_reduce
    linear_combination egz + eb - GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k + 2) * egw -
      G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k) * ea
  obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.EvenTheta.exists_eq_prod_sqTh Λ h k (fun z => G z / β ^ 2)
    (hG.div_const _) (fun z => by simp only [hev]) (by simp only [hG0]; exact div_self (pow_ne_zero 2 hβ0))
    (fun ω hω z => GlobalTheory.EvenTheta.Fibres.law_of_fac h (F := fun z => G z / β ^ 2) (k := k) hω z (by
      show G (z + ω) / β ^ 2 * _ = G z / β ^ 2
      rw [div_mul_eq_mul_div, hlaw ω hω z]))
  have hfac : ∀ z, sgStar Λ (β * z) ^ 2 = β ^ 2 * sgStar Λ z ^ 2 * ∏ i, sqTh Λ (Q i) z := fun z => by
    rw [eG z, ← hQe z]
    field_simp
  refine ⟨Q, fun i => ⟨hQ i, ?_⟩, hfac⟩
  refine (h.sg_eq_zero _).1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ?_)
  rw [hfac, Finset.prod_eq_zero (Finset.mem_univ i)
    ((h.sqTh_eq_zero (hQ i) _).2 (Or.inr (by rw [sub_self]; exact Λ.zero_mem))), mul_zero]

end GlobalTheory.EvenTheta.MulLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumNormEntriesLeSumSingularValues
section
namespace GlobalTheory.CartanInt.Frob
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem sq_col_le {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (a : Fin n) : (∑ i, ‖U i a‖) ^ 2 ≤ n := by
  have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have h2 := congrFun (congrFun h1 a) a
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def,
    Complex.conj_mul'] at h2
  have h3 : ∑ i, ‖U i a‖ ^ 2 = 1 := by exact_mod_cast h2
  have h4 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖U i a‖)
  simpa [h3] using h4

theorem sum_diag (p q : ℕ) (s : ℕ → ℝ) :
    ∑ a : Fin p, ∑ b : Fin q, (if (a : ℕ) = (b : ℕ) then s a else 0) =
      ∑ i ∈ Finset.range (min p q), s i := by
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin q, (if a = (b : ℕ) then s a else 0)) p]
  have h : ∀ a : ℕ, ∑ b : Fin q, (if a = (b : ℕ) then s a else 0) =
      if a ∈ Finset.range q then s a else 0 := fun a => by
    rw [Fin.sum_univ_eq_sum_range (fun b => if a = b then s a else 0) q, Finset.sum_ite_eq]
  simp only [h]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

theorem sum_norm_le_sum_singVal : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ),
    ∑ i, ∑ j, ‖B i j‖ ≤
      (((p + q : ℕ) : ℝ) + 1) / 2 * ∑ i ∈ Finset.range (min p q), singVal B i := by
  intro p q B
  obtain ⟨U, hU, V, hV, hB⟩ := GlobalTheory.RectSVD.exists_svd_singularValues p q B
  set d : Fin p → Fin q → ℝ := fun a b => if (a : ℕ) = (b : ℕ) then singVal B a else 0 with hd
  have hd0 : ∀ a b, 0 ≤ d a b := fun a b => by
    simp only [hd]; split_ifs
    · exact singVal_nonneg _ _
    · exact le_rfl
  have h1 : ∀ i j, ‖B i j‖ ≤ ∑ b, ∑ a, ‖U i a‖ * d a b * ‖V j b‖ := by
    intro i j
    have e := congrFun (congrFun hB i) j
    rw [e, Matrix.mul_apply]
    refine norm_sum_le_of_le _ fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun a _ => le_of_eq ?_
    rw [norm_mul, norm_mul, Matrix.conjTranspose_apply, norm_star, Matrix.of_apply]
    congr 2
    simp only [hd]
    split_ifs
    · rw [Complex.norm_real]; exact Real.norm_of_nonneg (singVal_nonneg B a)
    · simp
  calc ∑ i, ∑ j, ‖B i j‖ ≤ ∑ i, ∑ j, ∑ b, ∑ a, ‖U i a‖ * d a b * ‖V j b‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = ∑ b, ∑ a, ((∑ i, ‖U i a‖) * ∑ j, ‖V j b‖) * d a b := by
        simp only [Finset.sum_mul_sum, Finset.sum_mul]
        simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin q))) (t := (Finset.univ : Finset (Fin q))) (f := fun j b => ∑ a, ‖U _ a‖ * d a b * ‖V j b‖)]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin q))) (t := (Finset.univ : Finset (Fin p))) (f := fun j a => ‖U _ a‖ * d a b * ‖V j b‖)]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]; ring
    _ ≤ ∑ b, ∑ a, (((p + q : ℕ) : ℝ) + 1) / 2 * d a b := by
        refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_right ?_ (hd0 a b)
        have := sq_col_le hU a
        have := sq_col_le hV b
        push_cast
        nlinarith [sq_nonneg ((∑ i, ‖U i a‖) - ∑ j, ‖V j b‖)]
    _ = _ := by
        rw [← sum_diag, Finset.sum_comm]
        simp only [Finset.mul_sum, hd]

end GlobalTheory.CartanInt.Frob
end

