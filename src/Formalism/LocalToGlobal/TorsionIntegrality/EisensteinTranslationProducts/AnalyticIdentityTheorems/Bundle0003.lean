module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Legendre

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaLog
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace SigmaLog

lemma hasDerivAt_wFactor (l z : ℂ) :
    HasDerivAt (wFactor l)
      (-(1 / l) * Complex.exp (z / l + z ^ 2 / (2 * l ^ 2))
        + (1 - z / l) * (Complex.exp (z / l + z ^ 2 / (2 * l ^ 2)) * (1 / l + 2 * z / (2 * l ^ 2)))) z := by
  have h1 : HasDerivAt (fun z : ℂ => 1 - z / l) (-(1 / l)) z := by
    simpa using ((hasDerivAt_id z).div_const l).const_sub 1
  have h2 : HasDerivAt (fun z : ℂ => z / l + z ^ 2 / (2 * l ^ 2)) (1 / l + 2 * z / (2 * l ^ 2)) z := by
    have := ((hasDerivAt_id z).div_const l).fun_add ((hasDerivAt_pow 2 z).div_const (2 * l ^ 2))
    simpa using this
  exact h1.mul h2.cexp

lemma differentiable_wFactor (l : ℂ) : Differentiable ℂ (wFactor l) :=
  fun z => (hasDerivAt_wFactor l z).differentiableAt

lemma wFactor_ne_zero {l z : ℂ} (h : z ≠ l) : wFactor l z ≠ 0 := by
  unfold wFactor
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  by_cases hl : l = 0
  · simp [hl]
  · intro h0
    apply h
    field_simp at h0
    linear_combination -h0

lemma logDeriv_wFactor {l z : ℂ} (h : z ≠ l) :
    logDeriv (wFactor l) z
      = (1 / (z - l) + 1 / l + z / l ^ 2) - (if l = 0 then 1 / z else 0) := by
  rw [logDeriv_apply, (hasDerivAt_wFactor l z).deriv]
  by_cases hl : l = 0
  · simp [hl, wFactor]
  · have h1 : z - l ≠ 0 := sub_ne_zero.mpr h
    have h2 : 1 - z / l ≠ 0 := by
      intro h0
      apply h
      field_simp at h0
      linear_combination -h0
    have h3 : l - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have he := Complex.exp_ne_zero (z / l + z ^ 2 / (2 * l ^ 2))
    rw [if_neg hl, wFactor, sub_zero, div_eq_iff (mul_ne_zero h2 he)]
    field_simp
    ring

end SigmaLog

open SigmaLog in
theorem sigmaLogDeriv_of (h1 : SigmaProdLU) (h2 : SigmaSummable) (h3 : ZetaSummable) :
    SigmaLogDeriv := by
  intro L z hz
  have hne : ∀ l : L.lattice, z ≠ (l : ℂ) := fun l h => hz (h ▸ l.2)
  have hz0 : z ≠ 0 := fun h => hz (h ▸ L.lattice.zero_mem)
  set P : ℂ → ℂ := fun z => ∏' l : L.lattice, wFactor (l : ℂ) z with hP

  have hPne : P z ≠ 0 := by
    have := tprod_one_add_ne_zero_of_summable (f := fun l : L.lattice => wFactor (l : ℂ) z - 1)
      (fun l => by simpa using wFactor_ne_zero (hne l)) (h2 L z)
    simpa [hP] using this

  have hPd : DifferentiableOn ℂ P Set.univ := by
    have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp (h1 L)
    refine ht.differentiableOn (.of_forall fun s => ?_) isOpen_univ
    exact DifferentiableOn.fun_finsetProd fun i _ => (differentiable_wFactor _).differentiableOn
  have hPdz : DifferentiableAt ℂ P z := (hPd z (Set.mem_univ z)).differentiableAt Filter.univ_mem

  have hc : HasSum (fun l : L.lattice => if (l : ℂ) = 0 then 1 / z else 0) (1 / z) := by
    have : (fun l : L.lattice => if (l : ℂ) = 0 then 1 / z else 0)
        = fun l : L.lattice => if l = 0 then 1 / z else 0 := by
      funext l; simp
    rw [this]
    exact hasSum_ite_eq 0 (1 / z)
  have hs : HasSum (fun l : L.lattice => logDeriv (wFactor (l : ℂ)) z) (wZeta L z - 1 / z) := by
    have := (h3 L z).hasSum.sub hc
    have he : (fun l : L.lattice => logDeriv (wFactor (l : ℂ)) z)
        = fun l : L.lattice => (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
            - (if (l : ℂ) = 0 then 1 / z else 0) := by
      funext l
      exact logDeriv_wFactor (hne l)
    rw [he]
    exact this
  have hlog : logDeriv P z = wZeta L z - 1 / z := by
    have := logDeriv_tprod_eq_tsum (s := Set.univ) isOpen_univ (Set.mem_univ z)
      (f := fun (l : L.lattice) (z : ℂ) => wFactor (l : ℂ) z) (fun l => wFactor_ne_zero (hne l))
      (fun l => (differentiable_wFactor _).differentiableOn) hs.summable
      (h1 L).multipliableLocallyUniformlyOn hPne
    rw [hs.tsum_eq] at this
    exact this
  have hPderiv : HasDerivAt P ((wZeta L z - 1 / z) * P z) z := by
    have := hPdz.hasDerivAt
    rw [← hlog, logDeriv_apply, div_mul_cancel₀ _ hPne]
    exact this
  have := (hasDerivAt_id z).mul hPderiv
  have he : wZeta L z * wSigma L z = 1 * P z + id z * ((wZeta L z - 1 / z) * P z) := by
    simp only [wSigma, id, hP]
    field_simp
    ring
  rw [he]
  exact this

end Formalism.L2.Th1.F
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ZetaQuasi
section
noncomputable section

namespace Formalism.L2.Th1.F

namespace WeierstrassZetaQuasiPeriod

lemma isOpen_compl (L : PeriodPair) : IsOpen ((L.lattice : Set ℂ)ᶜ) :=
  L.isClosed_lattice.isOpen_compl

lemma isPreconnected_compl (L : PeriodPair) : IsPreconnected ((L.lattice : Set ℂ)ᶜ) :=
  (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
    (countable_of_Lindelof_of_discrete (X := L.lattice))).2

lemma add_notMem {L : PeriodPair} {ω z : ℂ} (hω : ω ∈ L.lattice) (hz : z ∉ L.lattice) :
    z + ω ∉ L.lattice := fun h => hz (by simpa using sub_mem h hω)

lemma diff_const (hd : ZetaHasDeriv) (L : PeriodPair) {ω : ℂ} (hω : ω ∈ L.lattice) {x y : ℂ}
    (hx : x ∉ L.lattice) (hy : y ∉ L.lattice) :
    wZeta L (x + ω) - wZeta L x = wZeta L (y + ω) - wZeta L y := by
  have hD : ∀ z, z ∉ L.lattice → HasDerivAt (fun z => wZeta L (z + ω) - wZeta L z) 0 z := by
    intro z hz
    have h1 := (hd L (z + ω) (add_notMem hω hz)).comp_add_const z ω
    have h2 := h1.sub (hd L z hz)
    have h3 : L.weierstrassP (z + ω) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨ω, hω⟩
    have e : -L.weierstrassP (z + ω) - -L.weierstrassP z = 0 := by rw [h3]; ring
    rw [e] at h2
    exact h2
  exact (isOpen_compl L).is_const_of_deriv_eq_zero (f := fun z => wZeta L (z + ω) - wZeta L z)
    (isPreconnected_compl L)
    (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hD z hz).deriv) hx hy

lemma diff_eq (hd : ZetaHasDeriv) (ho : ZetaOdd) (L : PeriodPair) {ω : ℂ} (hω : ω ∈ L.lattice)
    (hω2 : ω / 2 ∉ L.lattice) {z : ℂ} (hz : z ∉ L.lattice) :
    wZeta L (z + ω) = wZeta L z + 2 * wZeta L (ω / 2) := by
  have hm : -(ω / 2) ∉ L.lattice := fun h => hω2 (by simpa using neg_mem h)
  have h := diff_const hd L hω hz hm
  have e : -(ω / 2) + ω = ω / 2 := by ring
  rw [e, ho L (ω / 2)] at h
  linear_combination h

lemma wEta_ω₁ (L : PeriodPair) : wEta L L.ω₁ = 2 * wZeta L (L.ω₁ / 2) := by
  have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 0
  simpa [wEta] using this

lemma wEta_ω₂ (L : PeriodPair) : wEta L L.ω₂ = 2 * wZeta L (L.ω₂ / 2) := by
  have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 1
  simpa [wEta] using this

end WeierstrassZetaQuasiPeriod


open WeierstrassZetaQuasiPeriod in
theorem zetaQuasi_of (hd : ZetaHasDeriv) (ho : ZetaOdd) : ZetaQuasi := by
  intro L ω z hω hz
  let G : AddSubgroup ℂ :=
    { carrier := { w | w ∈ L.lattice ∧
        ∀ x, x ∉ L.lattice → wZeta L (x + w) = wZeta L x + wEta L w }
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun x hx => ?_⟩
        calc
          wZeta L (x + (a + b)) = wZeta L (x + a + b) := by congr 1; abel
          _ = wZeta L (x + a) + wEta L b :=
            hb' (x + a) (WeierstrassZetaQuasiPeriod.add_notMem ha hx)
          _ = (wZeta L x + wEta L a) + wEta L b := by rw [ha' x hx]
          _ = wZeta L x + wEta L (a + b) := by rw [map_add]; abel
      zero_mem' := ⟨zero_mem _, fun x _ => by simp⟩
      neg_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨neg_mem ha, fun x hx => ?_⟩
        have h := ha' (x + -a) (WeierstrassZetaQuasiPeriod.add_notMem (neg_mem ha) hx)
        rw [neg_add_cancel_right] at h
        rw [map_neg, h]; ring }
  have hG : L.lattice ≤ G.toIntSubmodule := by
    rw [PeriodPair.lattice, Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact ⟨L.ω₁_mem_lattice, fun x hx => by
        rw [WeierstrassZetaQuasiPeriod.wEta_ω₁]; exact WeierstrassZetaQuasiPeriod.diff_eq hd ho L L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice hx⟩
    · exact ⟨L.ω₂_mem_lattice, fun x hx => by
        rw [WeierstrassZetaQuasiPeriod.wEta_ω₂]; exact WeierstrassZetaQuasiPeriod.diff_eq hd ho L L.ω₂_mem_lattice L.ω₂_div_two_notMem_lattice hx⟩
  exact (hG hω).2 z hz

end Formalism.L2.Th1.F
end
end

