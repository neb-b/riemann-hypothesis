module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

theorem exists_periodPair_of_isLat (Λ : AddSubgroup ℂ) (hΛ : IsLat Λ) :
    ∃ L : PeriodPair, (L.lattice : Set ℂ) = Λ := by
  classical
  obtain ⟨hd, hs⟩ := hΛ
  let Λ' : Submodule ℤ ℂ := Λ.toIntSubmodule
  haveI : DiscreteTopology Λ' := hd
  haveI : IsZLattice ℝ Λ' := ⟨by simpa [Λ'] using hs⟩
  have hr : Module.finrank ℤ Λ' = 2 := by
    rw [ZLattice.rank ℝ (L := Λ'), Complex.finrank_real_complex]
  let b : Module.Basis (Fin 2) ℤ Λ' := Module.finBasisOfFinrankEq ℤ Λ' hr
  let B : Module.Basis (Fin 2) ℝ ℂ := Module.Basis.ofZLatticeBasis ℝ Λ' b
  have hB : ∀ i, B i = (b i : ℂ) := fun i => Module.Basis.ofZLatticeBasis_apply ℝ Λ' b i
  have hfun : (⇑B) = ![(b 0 : ℂ), (b 1 : ℂ)] := by
    funext i
    fin_cases i <;> simp [hB]
  have hind : LinearIndependent ℝ ![(b 0 : ℂ), (b 1 : ℂ)] := hfun ▸ B.linearIndependent
  refine ⟨⟨(b 0 : ℂ), (b 1 : ℂ), hind⟩, ?_⟩
  have hrange : Set.range ⇑B = {(b 0 : ℂ), (b 1 : ℂ)} := by
    rw [hfun]
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
  have hspan : Submodule.span ℤ {(b 0 : ℂ), (b 1 : ℂ)} = Λ' := by
    rw [← hrange]
    exact Module.Basis.ofZLatticeBasis_span ℝ Λ' b
  show ((Submodule.span ℤ {(b 0 : ℂ), (b 1 : ℂ)} : Submodule ℤ ℂ) : Set ℂ) = Λ
  rw [hspan]
  rfl

theorem eisG_eq_G_of_lattice (Λ : AddSubgroup ℂ) (L : PeriodPair) (hL : (L.lattice : Set ℂ) = Λ)
    (n : ℕ) (hn : n ≠ 0) : Formalism.MainNotions.TaylorLogMetric.eisG Λ n = L.G (2 * n) := by
  unfold Formalism.MainNotions.TaylorLogMetric.eisG PeriodPair.G
  have h1 := tsum_subtype ({w : ℂ | w ∈ Λ ∧ w ≠ 0}) (fun w : ℂ => 1 / w ^ (2 * n))
  have h2 := tsum_subtype ((L.lattice : Set ℂ)) (fun w : ℂ => (w ^ (2 * n))⁻¹)
  refine h1.trans (Eq.trans ?_ h2.symm)
  congr 1
  funext x
  by_cases hx : x = 0
  · subst hx
    have h0 : (0 : ℂ) ^ (2 * n) = 0 := zero_pow (by omega)
    simp [Set.indicator, h0]
  · have hm : x ∈ L.lattice ↔ x ∈ Λ := by
      rw [← SetLike.mem_coe, hL, SetLike.mem_coe]
    simp only [Set.indicator, Set.mem_setOf_eq, hx, ne_eq, not_false_eq_true, and_true,
      SetLike.mem_coe, hm, one_div]

theorem g2_g3_eq_periodPair (Λ : AddSubgroup ℂ) (L : PeriodPair) (hL : (L.lattice : Set ℂ) = Λ) :
    Formalism.MainNotions.TaylorLogMetric.g2 Λ = L.g₂ ∧ Formalism.MainNotions.TaylorLogMetric.g3 Λ = L.g₃ := by
  refine ⟨?_, ?_⟩
  · unfold Formalism.MainNotions.TaylorLogMetric.g2 PeriodPair.g₂
    rw [eisG_eq_G_of_lattice Λ L hL 2 (by norm_num)]
  · unfold Formalism.MainNotions.TaylorLogMetric.g3 PeriodPair.g₃
    rw [eisG_eq_G_of_lattice Λ L hL 3 (by norm_num)]

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.LatOfDiscrHolds
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

theorem dg_tsum_int (k : ℕ) (hk : 1 ≤ k) :
    ∑' n : ℤ, 1 / (n : ℂ) ^ (2 * k) = 2 * riemannZeta (2 * k) := by
  have hk2 : 1 < 2 * k := by omega
  have hsR : Summable fun n : ℤ ↦ 1 / (n : ℝ) ^ (2 * k) := Real.summable_one_div_int_pow.mpr hk2
  have hs : Summable fun n : ℤ ↦ 1 / (n : ℂ) ^ (2 * k) := by
    have := (Complex.summable_ofReal).mpr hsR
    refine this.congr fun n => ?_
    push_cast; rfl
  rw [← tsum_nat_add_neg_add_one hs]
  have hN : Summable fun n : ℕ ↦ 1 / (n : ℂ) ^ (2 * k) := by
    have := hs.comp_injective Nat.cast_injective
    refine this.congr fun n => ?_
    simp
  have hN1 : Summable fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ (2 * k) := by
    have := (summable_nat_add_iff 1).mpr hN
    refine this.congr fun n => ?_
    push_cast; rfl
  have e : ∀ n : ℕ, 1 / (((n : ℤ) : ℂ)) ^ (2 * k) + 1 / (((-(n + 1) : ℤ)) : ℂ) ^ (2 * k)
      = 1 / (n : ℂ) ^ (2 * k) + 1 / ((n : ℂ) + 1) ^ (2 * k) := by
    intro n; push_cast; rw [(even_two_mul k).neg_pow]
  rw [tsum_congr e, hN.tsum_add hN1]
  have h0 : ∑' n : ℕ, 1 / (n : ℂ) ^ (2 * k) = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (2 * k) := by
    rw [hN.tsum_eq_zero_add]
    have hz : (1 : ℂ) / ((0 : ℕ) : ℂ) ^ (2 * k) = 0 := by simp; omega
    rw [hz, zero_add]
    push_cast; rfl
  have hz := zeta_nat_eq_tsum_of_gt_one hk2
  push_cast at hz
  rw [← h0, ← hz]; ring

theorem dg_eisG_cyc (v : ℂ) (hv : v ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    Formalism.MainNotions.TaylorLogMetric.eisG (AddSubgroup.zmultiples v) k = 2 * riemannZeta (2 * k) / v ^ (2 * k) := by
  unfold Formalism.MainNotions.TaylorLogMetric.eisG
  let f : {n : ℤ | n ≠ 0} → {w : ℂ // w ∈ AddSubgroup.zmultiples v ∧ w ≠ 0} := fun n =>
    ⟨(n : ℂ) * v, ⟨n, by simp [zsmul_eq_mul]⟩, mul_ne_zero (by exact_mod_cast n.2) hv⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have := congrArg Subtype.val hab
      simp only [f, mul_left_inj' hv, Int.cast_inj] at this
      exact Subtype.ext this
    · rintro ⟨w, ⟨n, rfl⟩, hw⟩
      refine ⟨⟨n, ?_⟩, ?_⟩
      · rintro rfl; simp at hw
      · simp [f, zsmul_eq_mul]
  rw [← (Equiv.ofBijective f hf).tsum_eq]
  simp only [Equiv.ofBijective_apply, f]
  have hc : ∀ n : {n : ℤ | n ≠ 0}, 1 / ((n : ℂ) * v) ^ (2 * k)
      = (1 / v ^ (2 * k)) * (1 / ((n : ℤ) : ℂ) ^ (2 * k)) := by
    intro n; rw [mul_pow]; field_simp
  rw [tsum_congr hc, tsum_mul_left,
    tsum_subtype_eq_of_support_subset (f := fun n : ℤ => 1 / (n : ℂ) ^ (2 * k)) ?_, dg_tsum_int k hk]
  · ring
  · intro n hn
    simp only [Function.mem_support] at hn
    simp only [Set.mem_ofPred_eq]
    rintro rfl; simp at hn; omega

theorem dg_discr_cyc (v : ℂ) : Formalism.MainNotions.TaylorLogMetric.discr (AddSubgroup.zmultiples v) = 0 := by
  by_cases hv : v = 0
  · subst hv
    have h : ∀ k, Formalism.MainNotions.TaylorLogMetric.eisG (AddSubgroup.zmultiples (0 : ℂ)) k = 0 := by
      intro k
      unfold Formalism.MainNotions.TaylorLogMetric.eisG
      have : IsEmpty {w : ℂ // w ∈ AddSubgroup.zmultiples (0 : ℂ) ∧ w ≠ 0} :=
        ⟨fun w => w.2.2 (by simpa using w.2.1)⟩
      exact tsum_empty
    simp only [Formalism.MainNotions.TaylorLogMetric.discr, Formalism.MainNotions.TaylorLogMetric.g2, Formalism.MainNotions.TaylorLogMetric.g3, h]
    norm_num
  · unfold Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3
    rw [dg_eisG_cyc v hv 2 (by norm_num), dg_eisG_cyc v hv 3 (by norm_num)]
    push_cast
    rw [show (2 : ℂ) * 2 = 4 by norm_num, show (2 : ℂ) * 3 = 6 by norm_num, riemannZeta_four,
      jac_riemannZeta_six]
    field_simp
    ring

theorem dg_sep (Λ : AddSubgroup ℂ) (h : Formalism.MainNotions.TaylorLogMetric.discr Λ ≠ 0) :
    ∃ r > 0, ∀ w ∈ Λ, ‖w‖ < r → w = 0 := by
  have hsum : ∃ k : ℕ, 1 ≤ k ∧
      Summable (fun w : {w : ℂ // w ∈ Λ ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k)) := by
    by_contra hn
    push Not at hn
    apply h
    have h2 : Formalism.MainNotions.TaylorLogMetric.eisG Λ 2 = 0 := tsum_eq_zero_of_not_summable (hn 2 (by norm_num))
    have h3 : Formalism.MainNotions.TaylorLogMetric.eisG Λ 3 = 0 := tsum_eq_zero_of_not_summable (hn 3 (by norm_num))
    simp [Formalism.MainNotions.TaylorLogMetric.discr, Formalism.MainNotions.TaylorLogMetric.g2, Formalism.MainNotions.TaylorLogMetric.g3, h2, h3]
  obtain ⟨k, hk, hs⟩ := hsum
  have hfin : Set.Finite {w : {w : ℂ // w ∈ Λ ∧ w ≠ 0} | 1 ≤ ‖1 / (w : ℂ) ^ (2 * k)‖} := by
    have := hs.tendsto_cofinite_zero (Metric.ball_mem_nhds (0 : ℂ) one_pos)
    refine (Filter.mem_cofinite.mp this).subset ?_
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right, not_lt]
    exact hw
  set F : Set ℂ := Subtype.val '' {w : {w : ℂ // w ∈ Λ ∧ w ≠ 0} | 1 ≤ ‖1 / (w : ℂ) ^ (2 * k)‖}
  have hF : F.Finite := hfin.image _
  have h0 : (0 : ℂ) ∈ Fᶜ := by
    rintro ⟨w, _, hw⟩
    exact w.2.2 hw
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hF.isClosed.isOpen_compl 0 h0
  refine ⟨min r 1, lt_min hr one_pos, fun w hw hlt => ?_⟩
  by_contra hne
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hne
  have hlt1 : ‖w‖ < 1 := lt_of_lt_of_le hlt (min_le_right _ _)
  have hltr : ‖w‖ < r := lt_of_lt_of_le hlt (min_le_left _ _)
  have hwF : w ∈ F := by
    refine ⟨⟨w, hw, hne⟩, ?_, rfl⟩
    simp only [Set.mem_ofPred_eq, norm_div, norm_one, norm_pow]
    exact one_le_one_div (pow_pos hpos _) (pow_le_one₀ hpos.le hlt1.le)
  exact hball (by simpa using hltr) hwF

theorem dg_discrete (Λ : AddSubgroup ℂ) {r : ℝ} (hr : 0 < r) (H : ∀ w ∈ Λ, ‖w‖ < r → w = 0) :
    DiscreteTopology Λ := by
  apply discreteTopology_of_isOpen_singleton_zero
  have : ({0} : Set Λ) = Subtype.val ⁻¹' Metric.ball (0 : ℂ) r := by
    ext ⟨w, hw⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · intro h0
      have : w = 0 := congrArg Subtype.val h0
      simpa [this] using hr
    · intro h
      exact Subtype.ext (H w hw h)
  rw [this]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

theorem dg_span (Λ : AddSubgroup ℂ) (h : Formalism.MainNotions.TaylorLogMetric.discr Λ ≠ 0) {r : ℝ} (hr : 0 < r)
    (H : ∀ w ∈ Λ, ‖w‖ < r → w = 0) : Submodule.span ℝ (Λ : Set ℂ) = ⊤ := by
  by_contra htop
  by_cases hb : ∀ w ∈ Λ, w = 0
  · apply h
    have : Λ = AddSubgroup.zmultiples 0 := by
      ext w
      simp only [AddSubgroup.zmultiples_zero_eq_bot, AddSubgroup.mem_bot]
      exact ⟨hb w, fun hw => hw ▸ Λ.zero_mem⟩
    rw [this]; exact dg_discr_cyc 0
  push Not at hb
  obtain ⟨w0, hw0, hw0ne⟩ := hb
  have hline : ∀ w ∈ Λ, ∃ t : ℝ, w = (t : ℂ) * w0 := by
    intro w hw
    by_contra hno
    push Not at hno
    apply htop
    have hli : LinearIndependent ℝ ![w0, w] := by
      rw [LinearIndependent.pair_iff' hw0ne]
      intro a ha
      exact hno a (by rw [← ha, Complex.real_smul])
    have := hli.span_eq_top_of_card_eq_finrank' (by simp [Complex.finrank_real_complex])
    rw [eq_top_iff, ← this]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hw0
    · exact hw
  let φ : ℝ →+ ℂ :=
    { toFun := fun t => (t : ℂ) * w0
      map_zero' := by simp
      map_add' := fun a b => by push_cast; ring }
  set A : AddSubgroup ℝ := Λ.comap φ with hA
  have hn0 : 0 < ‖w0‖ := norm_pos_iff.mpr hw0ne
  have hdis : Disjoint (A : Set ℝ) (Set.Ioo 0 (r / ‖w0‖)) := by
    rw [Set.disjoint_left]
    intro t ht hto
    have hmem : (t : ℂ) * w0 ∈ Λ := ht
    have hnorm : ‖(t : ℂ) * w0‖ < r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hto.1]
      have := hto.2
      rwa [lt_div_iff₀ hn0] at this
    have := H _ hmem hnorm
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hto.1.ne' (by exact_mod_cast h1)
    · exact hw0ne h1
  have hcyc := AddSubgroup.isAddCyclic_of_disjoint_Ioo_zero (div_pos hr hn0) hdis
  obtain ⟨b, hb⟩ := A.isAddCyclic_iff_exists_zmultiples_eq.mp hcyc
  have hbA : A = AddSubgroup.closure {b} := by
    rw [← AddSubgroup.zmultiples_eq_closure, hb]
  apply h
  have hbmem : (b : ℂ) * w0 ∈ Λ := by
    have : b ∈ A := by rw [hbA]; exact AddSubgroup.subset_closure rfl
    exact this
  have : Λ = AddSubgroup.zmultiples ((b : ℂ) * w0) := by
    ext w
    constructor
    · intro hw
      obtain ⟨t, rfl⟩ := hline w hw
      have htA : t ∈ A := hw
      rw [hbA, ← AddSubgroup.zmultiples_eq_closure, AddSubgroup.mem_zmultiples_iff] at htA
      obtain ⟨n, rfl⟩ := htA
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp [zsmul_eq_mul]; ring⟩
    · intro hw
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hw
      exact Λ.zsmul_mem hbmem n
  rw [this]; exact dg_discr_cyc _

theorem latOfDiscr_holds : LatOfDiscr := by
  intro Λ h
  obtain ⟨r, hr, H⟩ := dg_sep Λ h
  exact ⟨dg_discrete Λ hr H, dg_span Λ h hr H⟩

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.WeierstrassPEventuallyEq
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.WeierstrassODE

open Filter Topology

lemma wp_eq (L : PeriodPair) (z : ℂ) :
    L.weierstrassP z = L.weierstrassPExcept 0 z + 1 / z ^ 2 := by
  have h := L.weierstrassPExcept_def 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero] at h
  rw [h]; simp

lemma dwp_eq (L : PeriodPair) (z : ℂ) :
    L.derivWeierstrassP z = L.derivWeierstrassPExcept 0 z - 2 / z ^ 3 := by
  have h := L.derivWeierstrassPExcept_def 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero] at h
  rw [h]; ring

lemma ode_shape (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) (hz0 : z ≠ 0) :
    (z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) ^ 2 =
      4 * (z ^ 2 * L.weierstrassPExcept 0 z + 1) ^ 3
        - L.g₂ * (z ^ 6 * L.weierstrassPExcept 0 z + z ^ 4) - L.g₃ * z ^ 6 := by
  have e := L.derivWeierstrassP_sq z hz
  rw [wp_eq, dwp_eq] at e
  set f := L.weierstrassPExcept 0 z
  set f' := L.derivWeierstrassPExcept 0 z
  have key : (z ^ 3 * f' - 2) ^ 2 - (4 * (z ^ 2 * f + 1) ^ 3
        - L.g₂ * (z ^ 6 * f + z ^ 4) - L.g₃ * z ^ 6) =
      z ^ 6 * ((f' - 2 / z ^ 3) ^ 2 - (4 * (f + 1 / z ^ 2) ^ 3 - L.g₂ * (f + 1 / z ^ 2) - L.g₃)) := by
    field_simp
  rw [e, sub_self, mul_zero] at key
  exact sub_eq_zero.mp key

lemma hasDerivAt_wpe (L : PeriodPair) {z : ℂ} (hz : z ∈ ((L.lattice : Set ℂ) \ {0})ᶜ) :
    HasDerivAt (L.weierstrassPExcept 0) (L.derivWeierstrassPExcept 0 z) z := by
  have h1 := (L.analyticOnNhd_weierstrassPExcept 0 z hz).differentiableAt.hasDerivAt
  rwa [L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hz] at h1

lemma wpe_eventually (L : PeriodPair) :
    ∀ᶠ z in 𝓝 (0:ℂ), HasDerivAt (L.weierstrassPExcept 0) (L.derivWeierstrassPExcept 0 z) z ∧
      (z ≠ 0 → z ∉ L.lattice) := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  refine ⟨hasDerivAt_wpe L hz, fun h0 hl => hz ⟨hl, h0⟩⟩

lemma diff_identity (L L' : PeriodPair) (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) (z : ℂ)
    (hz0 : z ≠ 0) (hz : z ∉ L.lattice) (hz' : z ∉ L'.lattice) :
    z * (L.derivWeierstrassPExcept 0 z - L'.derivWeierstrassPExcept 0 z) *
        (z ^ 3 * (L.derivWeierstrassPExcept 0 z + L'.derivWeierstrassPExcept 0 z) - 4) =
      (L.weierstrassPExcept 0 z - L'.weierstrassPExcept 0 z) *
        (4 * ((1 + z ^ 2 * L.weierstrassPExcept 0 z) ^ 2
          + (1 + z ^ 2 * L.weierstrassPExcept 0 z) * (1 + z ^ 2 * L'.weierstrassPExcept 0 z)
          + (1 + z ^ 2 * L'.weierstrassPExcept 0 z) ^ 2) - L.g₂ * z ^ 4) := by
  have e1 := ode_shape L z hz hz0
  have e2 := ode_shape L' z hz' hz0
  rw [← h2, ← h3] at e2
  apply mul_left_cancel₀ (pow_ne_zero 2 hz0)
  linear_combination e1 - e2

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.WeierstrassODE

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)


open Filter Topology in
theorem weierstrassP_eventuallyEq (L L' : PeriodPair) (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) :
    L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP := by
  set f := L.weierstrassPExcept 0
  set F := L'.weierstrassPExcept 0
  set f' := L.derivWeierstrassPExcept 0
  set F' := L'.derivWeierstrassPExcept 0
  have hf : AnalyticAt ℂ f 0 := L.analyticAt_weierstrassPExcept 0
  have hF : AnalyticAt ℂ F 0 := L'.analyticAt_weierstrassPExcept 0
  have hf' : AnalyticAt ℂ f' 0 := L.analyticAt_derivWeierstrassPExcept 0
  have hF' : AnalyticAt ℂ F' 0 := L'.analyticAt_derivWeierstrassPExcept 0
  have hw : AnalyticAt ℂ (fun z => f z - F z) 0 := hf.sub hF
  suffices hw0 : ∀ᶠ z in 𝓝 (0:ℂ), f z - F z = 0 by
    filter_upwards [nhdsWithin_le_nhds hw0] with z hz
    rw [WeierstrassODE.wp_eq, WeierstrassODE.wp_eq]; linear_combination hz
  by_contra hne
  obtain ⟨n, g, hg, hg0, hwg⟩ := hw.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  simp only [sub_zero, smul_eq_mul] at hwg

  have hder : ∀ᶠ z in 𝓝 (0:ℂ), z * (f' z - F' z) = z ^ n * (n * g z + z * deriv g z) := by
    filter_upwards [WeierstrassODE.wpe_eventually L, WeierstrassODE.wpe_eventually L', hg.eventually_analyticAt,
      hwg.eventually_nhds] with z h1 h1' hgz hwz
    have d1 : HasDerivAt (fun y => f y - F y) (f' z - F' z) z := h1.1.sub h1'.1
    have d2 : HasDerivAt (fun y => f y - F y) (n * z ^ (n - 1) * g z + z ^ n * deriv g z) z :=
      ((hasDerivAt_pow n z).mul hgz.differentiableAt.hasDerivAt).congr_of_eventuallyEq hwz
    rw [d1.unique d2]
    rcases n with _ | m
    · simp
    · push_cast; ring
  have hid : ∀ᶠ z in 𝓝[≠] (0:ℂ), (n * g z + z * deriv g z) *
        (z ^ 3 * (f' z + F' z) - 4) - g z *
        (4 * ((1 + z ^ 2 * f z) ^ 2 + (1 + z ^ 2 * f z) * (1 + z ^ 2 * F z)
          + (1 + z ^ 2 * F z) ^ 2) - L.g₂ * z ^ 4) = 0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hder,
      nhdsWithin_le_nhds (WeierstrassODE.wpe_eventually L), nhdsWithin_le_nhds (WeierstrassODE.wpe_eventually L'),
      nhdsWithin_le_nhds hwg] with z hz0 hd h1 h1' hwz
    have hz0' : z ≠ 0 := hz0
    have e := WeierstrassODE.diff_identity L L' h2 h3 z hz0' (h1.2 hz0') (h1'.2 hz0')
    rw [hd, hwz] at e
    apply mul_left_cancel₀ (pow_ne_zero n hz0')
    linear_combination e
  have hcont : ContinuousAt (fun z => (n * g z + z * deriv g z) *
        (z ^ 3 * (f' z + F' z) - 4) - g z *
        (4 * ((1 + z ^ 2 * f z) ^ 2 + (1 + z ^ 2 * f z) * (1 + z ^ 2 * F z)
          + (1 + z ^ 2 * F z) ^ 2) - L.g₂ * z ^ 4)) 0 := by
    have hgd : AnalyticAt ℂ (deriv g) 0 := hg.deriv
    apply AnalyticAt.continuousAt (𝕜 := ℂ)
    fun_prop
  have hlim := tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' (EventuallyEq.symm hid))
  simp at hlim
  have : (4 * (n : ℂ) + 12) * g 0 = 0 := by linear_combination -hlim
  rcases mul_eq_zero.mp this with h | h
  · have : (4 * n + 12 : ℕ) = (0 : ℂ) := by push_cast; exact h
    exact absurd (Nat.cast_eq_zero.mp this) (by omega)
  · exact hg0 h

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.WeierstrassPEventuallyEqNhdsNEOfZero
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)


open Filter Topology in
theorem weierstrassP_eventuallyEq_nhdsNE_of_zero (L L' : PeriodPair)
    (h : L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP) (x : ℂ) :
    L.weierstrassP =ᶠ[𝓝[≠] x] L'.weierstrassP := by
  set f : ℂ → ℂ := fun z => L.weierstrassP z - L'.weierstrassP z with hf
  have hm : MeromorphicOn f Set.univ := fun z _ =>
    (L.meromorphic_weierstrassP z).sub (L'.meromorphic_weierstrassP z)
  have h0 : meromorphicOrderAt f 0 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [h] with z hz
    simp [hf, hz]
  have hx : meromorphicOrderAt f x = ⊤ := by
    by_contra hne
    have := (hm.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1
      ⟨⟨x, Set.mem_univ _⟩, hne⟩ ⟨0, Set.mem_univ _⟩
    exact this h0
  rw [meromorphicOrderAt_eq_top_iff] at hx
  filter_upwards [hx] with z hz
  exact sub_eq_zero.1 hz


open Filter Topology in
theorem lattice_subset_of_weierstrassP (L L' : PeriodPair)
    (h : L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP) :
    (L.lattice : Set ℂ) ⊆ L'.lattice := by
  intro l hl
  by_contra hl'
  have h1 := L.order_weierstrassP l hl
  have h2 : 0 ≤ meromorphicOrderAt L'.weierstrassP l :=
    (L'.analyticOnNhd_weierstrassP l hl').meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr (weierstrassP_eventuallyEq_nhdsNE_of_zero L L' h l), h1] at h2
  exact absurd h2 (by decide)


open Filter Topology in
theorem lattice_eq_of_weierstrassP (L L' : PeriodPair)
    (h : L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP) :
    (L.lattice : Set ℂ) = L'.lattice :=
  Set.Subset.antisymm (lattice_subset_of_weierstrassP L L' h)
    (lattice_subset_of_weierstrassP L' L h.symm)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end

