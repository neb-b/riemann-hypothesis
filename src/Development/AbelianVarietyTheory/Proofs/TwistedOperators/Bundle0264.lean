module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaRuleExchangePairMembers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHilbertSchmidtOfAePointwiseBoundedLpTwo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HSAbs

theorem coeFn_finsum {X : Type} [MeasurableSpace X] {ν : Measure X} {κ : Type} (s : Finset κ)
    (f : κ → Lp ℂ 2 ν) : (⇑(∑ i ∈ s, f i) : X → ℂ) =ᵐ[ν] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 ν
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

theorem pointwise {X : Type} [MeasurableSpace X] {ν : Measure X}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type} (e : ι → H) (he : Orthonormal ℂ e) (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ)
    (hT : ∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) (s : Finset ι) :
    ∀ᵐ x ∂ν, ∑ i ∈ s, ‖T (e i) x‖ ^ 2 ≤ C ^ 2 := by
  classical

  let w : (s → ℂ) → H := fun c => ∑ j : s, c j • e j
  have hon : Orthonormal ℂ (fun j : s => e j) := he.comp _ Subtype.val_injective
  have hw2 : ∀ c, ‖w c‖ ^ 2 = ∑ j : s, ‖c j‖ ^ 2 := by
    intro c
    have h := hon.inner_sum c c Finset.univ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [@norm_sq_eq_re_inner ℂ, h, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (s → ℂ)
  have hD : ∀ c ∈ D, ∀ᵐ x ∂ν, ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖ := by
    intro c _
    have hlin : T (w c) = ∑ j : s, c j • T (e j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [w, map_sum, map_smul]
    have hsm : ∀ᵐ x ∂ν, ∀ j : s, (c j • T (e j) : Lp ℂ 2 ν) x = c j * T (e j) x := by
      rw [ae_all_iff]
      intro j
      filter_upwards [Lp.coeFn_smul (c j) (T (e j))] with x hx
      rw [hx]; rfl
    filter_upwards [hT (w c), coeFn_finsum (ν := ν) Finset.univ (fun j : s => c j • T (e j)), hsm]
      with x hx hsum hj
    rw [hlin, hsum] at hx
    simpa only [hj] using hx
  filter_upwards [(ae_ball_iff hDc).2 hD] with x hx

  have hall : ∀ c : s → ℂ, ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖ := by
    have hcl : IsClosed {c : s → ℂ | ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have hsub : closure D ⊆ {c : s → ℂ | ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖} :=
      hcl.closure_subset_iff.2 fun c hc => hx c hc
    intro c
    exact hsub (hDd.closure_eq ▸ Set.mem_univ c)

  set S := ∑ j : s, ‖T (e j) x‖ ^ 2 with hS
  have key := hall fun j => (starRingEnd ℂ) (T (e j) x)
  have hL : ‖∑ j : s, (starRingEnd ℂ) (T (e j) x) * T (e j) x‖ = S := by
    have : ∑ j : s, (starRingEnd ℂ) (T (e j) x) * T (e j) x = ((S : ℝ) : ℂ) := by
      rw [hS]; push_cast
      exact Finset.sum_congr rfl fun j _ => RCLike.conj_mul _
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hR : ‖w (fun j => (starRingEnd ℂ) (T (e j) x))‖ ^ 2 = S := by
    rw [hw2]
    exact Finset.sum_congr rfl fun j _ => by rw [RCLike.norm_conj]
  rw [hL] at key
  have hnn := norm_nonneg (w fun j => (starRingEnd ℂ) (T (e j) x))
  have hfin : S ≤ C ^ 2 := by
    nlinarith [sq_nonneg (C - ‖w fun j => (starRingEnd ℂ) (T (e j) x)‖)]
  rw [← Finset.sum_coe_sort s (fun i => ‖T (e i) x‖ ^ 2)]
  exact hfin

theorem sum_le {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type} (e : ι → H) (he : Orthonormal ℂ e) (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ)
    (hT : ∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) (s : Finset ι) :
    ∑ i ∈ s, ‖T (e i)‖ ^ 2 ≤ C ^ 2 * ν.real univ := by
  have hn : ∀ f : Lp ℂ 2 ν, ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
    intro f
    rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
    simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    rw [integral_ofReal, RCLike.ofReal_re]
  have hint : ∀ f : Lp ℂ 2 ν, Integrable (fun x => ‖f x‖ ^ 2) ν := by
    intro f
    have hm : MemLp f ((2 : ℕ) : ENNReal) ν := by simpa using Lp.memLp f
    exact hm.integrable_norm_pow (by norm_num)
  calc ∑ i ∈ s, ‖T (e i)‖ ^ 2 = ∫ x, ∑ i ∈ s, ‖T (e i) x‖ ^ 2 ∂ν := by
        rw [integral_finsetSum s fun i _ => hint (T (e i))]
        exact Finset.sum_congr rfl fun i _ => hn _
    _ ≤ ∫ _x, C ^ 2 ∂ν :=
        integral_mono_ae (integrable_finsetSum s fun i _ => hint (T (e i)))
          (integrable_const _) (pointwise e he T C hT s)
    _ = C ^ 2 * ν.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

end GlobalTheory.HSAbs


open GlobalTheory.HSAbs in
theorem GlobalTheory.isHilbertSchmidt_of_ae_bounded : ∀ {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ), (∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) → GlobalTheory.OpTrace.IsHilbertSchmidt T := by
  intro X _ ν _ H _ _ _ T C hT
  unfold GlobalTheory.OpTrace.IsHilbertSchmidt
  refine summable_of_sum_le (c := C ^ 2 * ν.real univ) (fun i => sq_nonneg _) fun u => ?_
  exact GlobalTheory.HSAbs.sum_le _ (GlobalTheory.OpTrace.stdBasis (H := H)).orthonormal T C hT u
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPureTensorBaseVectorAndLocalFactor
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalPure

variable {D : D7}

theorem wAt_add {m n : ℕ} (p : Place D) (x y : Mx D m n) : wAt p (x + y) = wAt p x + wAt p y := by
  rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

theorem wAt_two {m n : ℕ} (p : Place D) (x : Mx D m n) : wAt p (2 • x) = 2 • wAt p x := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_comm]

theorem wAt_wAt_self {m n : ℕ} (p : Place D) (x : Mx D m n) : wAt p (wAt p x) = wAt p x := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, ((_root_.GlobalTheory.PlaceTensor.idem_spec D).1 p)]

theorem wAt_wAt_ne {m n : ℕ} {p q : Place D} (h : p ≠ q) (x : Mx D m n) : wAt p (wAt q x) = 0 := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, ((_root_.GlobalTheory.PlaceTensor.idem_spec D).2.1 p q h), zero_smul]

theorem wAt_sum_of_notMem {m n : ℕ} {p : Place D} {P : Finset (Place D)} (h : p ∉ P) (x : Mx D m n) :
    wAt p (∑ r ∈ P, wAt r x) = 0 := by
  rw [wAt_eq_smul, Finset.smul_sum]
  refine Finset.sum_eq_zero fun r hr => ?_
  have hpr : p ≠ r := fun e => h (e ▸ hr)
  rw [← wAt_eq_smul]
  exact wAt_wAt_ne hpr x

theorem wAt_sum_of_mem {m n : ℕ} {p : Place D} {P : Finset (Place D)} (h : p ∈ P) (x : Mx D m n) :
    wAt p (∑ r ∈ P, wAt r x) = wAt p x := by
  rw [wAt_eq_smul, Finset.smul_sum, Finset.sum_eq_single_of_mem p h]
  · rw [← wAt_eq_smul]
    exact wAt_wAt_self p x
  · intro r _ hrp
    rw [← wAt_eq_smul]
    exact wAt_wAt_ne (Ne.symm hrp) x

theorem symplO_wAt (S T : HSp D) {p : Place D} (w : WO S T) {z : WO S T} (hz : wAt p z = 0) :
    symplO S T (wAt p w) z = 0 := by
  rw [wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (_root_.GlobalTheory.PlaceTensor.idem_spec D).2.2.1 p, ← wAt_eq_smul, hz,
    GlobalTheory.SplitScalar.symplO_zero_right]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem ip_base (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) : ipO μ 𝓕 f₀ f₀ = 1 := by
  obtain ⟨-, -, -, -, hff, -⟩ := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 (base_std h) hμ f₀ f₀ (base_theta h) (base_theta h)
  rw [hff, restrictedTensorBasePoint_norm_sq h hμ]
  simp

theorem ip_heis_wAt (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (p : Place D) (w : WO S T)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (vf : VacAt ψ θ S T sS sT ΛS ΛT p f) (vg : VacAt ψ θ S T sS sT ΛS ΛT p g) :
    ipO μ 𝓕 g (heisO ψ S T (wAt p w) f) = ipO μ 𝓕 f₀ (heisO ψ S T (wAt p w) f₀) * ipO μ 𝓕 g f := by
  have h0 := base_vacAt h p
  have hb := base_theta h
  rcases p with v | τ
  · obtain ⟨γ, hγ⟩ := _root_.GlobalTheory.PlaceCompress.compress_fin D ψ S T ΛS ΛT μ 𝓕 (base_std h) h.2.2.1 h.2.2.2.1 hμ v w
    have e0 := hγ f₀ f₀ hb hb h0 h0
    rw [ip_base h hμ, mul_one] at e0
    rw [hγ f g hf hg vf vg, e0]
  · obtain ⟨γ, hγ⟩ := _root_.GlobalTheory.VacCompress.compress D ψ θ S T μ 𝓕 (base_std h) (base_inf h) hμ τ (sS τ) (sT τ) (h.1 τ) (h.2.1 τ) w
    have e0 := hγ f₀ f₀ hb hb h0 h0
    rw [ip_base h hμ, mul_one] at e0
    rw [hγ f g hf hg vf vg, e0]

theorem ip_heis_sum (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (w z : WO S T)
    {y : WO S T → ℂ} (hy : IsThetaFunO ψ S T y) (P : Finset (Place D)) (hz : ∀ p ∈ P, wAt p z = 0)
    (vy : ∀ p ∈ P, VacAt ψ θ S T sS sT ΛS ΛT p y) :
    ipO μ 𝓕 y (heisO ψ S T (∑ p ∈ P, wAt p w + z) f₀) =
      (∏ p ∈ P, ipO μ 𝓕 f₀ (heisO ψ S T (wAt p w) f₀)) * ipO μ 𝓕 y (heisO ψ S T z f₀) := by
  classical
  have hψ := base_std h
  have hb := base_theta h
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  revert hz vy
  refine Finset.induction_on P ?_ ?_
  · intro _ _
    rw [Finset.sum_empty, zero_add, Finset.prod_empty, one_mul]
  · intro a P ha ih hz vy
    have hzP : ∀ p ∈ P, wAt p z = 0 := fun p hp => hz p (Finset.mem_insert_of_mem hp)
    have vyP : ∀ p ∈ P, VacAt ψ θ S T sS sT ΛS ΛT p y := fun p hp => vy p (Finset.mem_insert_of_mem hp)
    have hZ : wAt a (∑ p ∈ P, wAt p w + z) = 0 := by
      rw [wAt_add, wAt_sum_of_notMem ha, hz a (Finset.mem_insert_self a P), add_zero]
    have hv : VacAt ψ θ S T sS sT ΛS ΛT a (heisO ψ S T (∑ p ∈ P, wAt p w + z) f₀) :=
      (_root_.GlobalTheory.PlaceStable.heis_stable D ψ θ S T sS sT ΛS ΛT hψ (base_inf h) f₀ hb).1 a _ hZ (base_vacAt h a)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, add_assoc,
      GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (symplO_wAt S T w hZ),
      ip_heis_wAt h hμ a w (hth _ _ hb) hy hv (vy a (Finset.mem_insert_self a P)), ih hzP vyP]
    ring

private theorem isLatVac_of_isBase (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) :
    IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ := by
  have hv := h.2.2.2.2
  unfold IsVacO at hv
  obtain ⟨-, hv2⟩ := hv
  cases hv2
  assumption

theorem isPure_local (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (q : Place D)
    (x : Place D → WO S T → ℂ) (hx : IsLocal ψ θ S T sS sT ΛS ΛT q (x q)) (hq : ∀ p, p ≠ q → x p = f₀) :
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x (x q) := by
  classical
  have hfull := isLatVac_of_isBase h
  unfold IsPure IsRestricted
  refine ⟨⟨fun p => ?_, ?_⟩, hx.1, fun w => ?_⟩
  · by_cases hpq : p = q
    · subst hpq
      exact hx
    · rw [hq p hpq]
      exact base_isLocal h p
  · refine (Set.finite_singleton q).subset fun p hp => ?_
    by_contra hpq
    exact hp (hq p hpq)
  · obtain ⟨P₀, hP₀⟩ := _root_.GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul D S T ΛS ΛT h.2.2.1 h.2.2.2.1 w
    obtain ⟨u, hu, hw⟩ := hP₀ (insert q P₀) (Finset.subset_insert q P₀)
    have hqP : q ∈ insert q P₀ := Finset.mem_insert_self q P₀
    generalize insert q P₀ = P at hw hqP

    have key : ∀ p ∈ P, wAt p (2 • u) = 0 := by
      intro p hp
      have e := congrArg (wAt p) hw
      rw [wAt_add, wAt_sum_of_mem hp] at e
      calc wAt p (2 • u) = wAt p w + wAt p (2 • u) - wAt p w := by abel
        _ = wAt p w - wAt p w := by rw [← e]
        _ = 0 := sub_self _
    have hS : symplO S T (∑ p ∈ P, wAt p w) (2 • u) = 0 := by
      refine Finset.sum_induction _ (fun t => symplO S T t (2 • u) = 0) ?_
        (GlobalTheory.SplitScalar.symplO_zero_left S T _) (fun p hp => symplO_wAt S T w (key p hp))
      intro a b (ha : symplO S T a (2 • u) = 0) (hb : symplO S T b (2 • u) = 0)
      show symplO S T (a + b) (2 • u) = 0
      have e := GlobalTheory.SplitScalar.symplO_sub_left S T (a + b) b (2 • u)
      rw [show a + b - b = a by abel, ha, hb, sub_zero] at e
      exact e.symm
    have hsub : Function.mulSupport (fun p => ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)) ⊆ ↑P := by
      intro p hp
      by_contra hpP
      apply hp
      have hpq : p ≠ q := fun e => hpP (e ▸ hqP)
      have ew : wAt p w = wAt p (2 • u) := by
        conv_lhs => rw [hw]
        rw [wAt_add, wAt_sum_of_notMem hpP, zero_add]
      show ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀) = 1
      rw [hq p hpq, ew, wAt_two]
      have hh : heisO ψ S T (2 • wAt p u) f₀ = f₀ := by
        rcases p with v | τ
        · have hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f₀ := base_vacAt h (.inl v)
          exact hv.1 _ (latO_mono (fun v' hv' => Sum.inl_injective hv'.2)
            (_root_.GlobalTheory.LatticeLocal.wAt_mem_latO D S T ΛS ΛT (fun _ => True) u hu (.inl v)).1)
        · rw [(_root_.GlobalTheory.LatticeLocal.wAt_mem_latO D S T ΛS ΛT (fun _ => True) u hu (.inr τ)).2.2 (fun v _ => Sum.inl_ne_inr),
            smul_zero, GlobalTheory.SplitScalar.heisO_zero]
      rw [hh, ip_base h hμ]
    have e1 : heisO ψ S T w f₀ = heisO ψ S T (∑ p ∈ P, wAt p w) f₀ := by
      conv_lhs => rw [hw]
      rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T hS, hfull.1 u hu]
    have e2 : ipO μ 𝓕 (x q) (heisO ψ S T w f₀) =
        (∏ p ∈ P.erase q, ipO μ 𝓕 f₀ (heisO ψ S T (wAt p w) f₀)) * ipO μ 𝓕 (x q) (heisO ψ S T (wAt q w) f₀) := by
      rw [e1, ← Finset.sum_erase_add P (fun p => wAt p w) hqP]
      exact ip_heis_sum h hμ w (wAt q w) hx.1 (P.erase q) (fun p hp => wAt_wAt_ne (Finset.ne_of_mem_erase hp) w)
        (fun p hp => vacAt_of_isLocal hx (Finset.ne_of_mem_erase hp))
    refine ⟨P.finite_toSet.subset hsub, ?_⟩
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub, ← Finset.prod_erase_mul P _ hqP, e2]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [hq p (Finset.ne_of_mem_erase hp)]

end

theorem isPure_base_and_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun _ => f₀) f₀ ∧ ∀ (q : Place D) (x : Place D → WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT q (x q) → (∀ p, p ≠ q → x p = f₀) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x (x q) := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 h hμ
  refine ⟨?_, fun q x hx hq => isPure_local h hμ q x hx hq⟩
  rcases isEmpty_or_nonempty (Place D) with hE | ⟨⟨q⟩⟩
  · unfold IsPure IsRestricted
    refine ⟨⟨fun p => isEmptyElim p, Set.toFinite _⟩, base_theta h, fun w => ⟨Set.toFinite _, ?_⟩⟩
    rw [finprod_of_isEmpty]
    obtain ⟨P₀, hP₀⟩ := _root_.GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul D S T ΛS ΛT h.2.2.1 h.2.2.2.1 w
    obtain ⟨u, hu, hw⟩ := hP₀ P₀ subset_rfl
    rw [Finset.eq_empty_of_isEmpty P₀, Finset.sum_empty, zero_add] at hw
    rw [hw, (isLatVac_of_isBase h).1 u hu, ip_base h hμ]
  · exact isPure_local h hμ q (fun _ => f₀) (base_isLocal h q) (fun _ _ => rfl)

end GlobalTheory.LocalPure

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicPartRationalCharactersAdelicMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoDualChars

variable {D : D7}

theorem isoPart_add (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y y' : Mx D W.rank r) :
    isoPart V W C (y + y') = isoPart V W C y + isoPart V W C y' := by
  simp only [isoPart, Matrix.add_mul]

theorem isoPart_zero (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    isoPart V W C 0 = 0 := by
  simp only [isoPart, Matrix.zero_mul]

theorem midPart_zero (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) :
    midPart V V' W B 0 = 0 := by
  simp only [midPart, Matrix.zero_mul]

theorem continuous_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous fun y : Mx D W.rank r => isoPart V W C y := by
  unfold isoPart
  exact continuous_id.matrix_mul continuous_const

theorem symplO_smul_left' (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T (c • x) y = c * symplO S T x y := by
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, ← GlobalTheory.SplitScalar.symplOH_add_self,
    GlobalTheory.FinTranslate.symplOH_smul_left, mul_add]

theorem symplO_smul_right' (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T x (c • y) = c * symplO S T x y := by
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, ← GlobalTheory.SplitScalar.symplOH_add_self,
    GlobalTheory.FinTranslate.symplOH_smul_right, mul_add]

theorem trace_incA' (x : D.host.E) : Algebra.trace (AF D.host.F) (AE D) (incA D x) =
    algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E x) := by
  show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem exists_pair_ne_one (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (c : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (hc : c ≠ 0) :
    ∃ w : WO S T, ψ (symplO S T (c.map (incA D)) w) ≠ 1 := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, c i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (Matrix.ext h)
  obtain ⟨x₀, hx₀⟩ := hψ.1.2.2.2
  set q : D.host.F := Algebra.trace D.host.F D.host.E 1 with hq
  have hq0 : q ≠ 0 := by
    rw [hq, ← map_one (algebraMap D.host.F D.host.E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
    exact_mod_cast (Module.finrank_pos (R := D.host.F) (M := D.host.E)).ne'
  set s : AF D.host.F := x₀ * algebraMap D.host.F (AF D.host.F) q⁻¹
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.RatAnnih.exists_symplO_eq S T (s • c.map (incA D)) i j (c i j)⁻¹
  refine ⟨s • γ, ?_⟩
  have h1 : symplO S T (c.map (incA D)) (s • γ) = x₀ := by
    rw [symplO_smul_right', ← symplO_smul_left', hγ, Matrix.smul_apply, Matrix.map_apply, mul_smul_comm,
      map_smul, ← map_mul, inv_mul_cancel₀ hij, trace_incA', smul_eq_mul, ← hq, mul_assoc, ← map_mul,
      inv_mul_cancel₀ hq0, map_one, mul_one]
  rw [h1]
  exact hx₀

end GlobalTheory.IsoDualChars

namespace GlobalTheory.IsoDualChars


open GlobalTheory.LatVac in
theorem chars : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E), Continuous fun t : Mx D W.rank r => ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E) t s, ψ (symplO V W (isoPart V W C' (t + s)) (isoPart V W C (a.map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' s) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a b : Matrix (Fin W.rank) (Fin r) D.host.E) t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C ((a + b).map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' t) (isoPart V W C (b.map (incA D))))) ∧ (∀ t, (∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) ↔ t ∈ ratMx D W.rank r) ∧ ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) → a = 0 := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ
  obtain ⟨e, he, hrat⟩ := GlobalTheory.T.exists_homSpace_dual_isotropic_middle_decomposition D V V' W r C B hs C' h1 h2 h3
  obtain ⟨oII, oIM, oDM, oDD⟩ := _root_.GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hs C' h1 h2 h3
  have hdual : ∀ t, isoPart V W C' t = e (t, 0, 0) := fun t => by
    rw [he, isoPart_zero, midPart_zero, add_zero, add_zero]
  have hiso : ∀ y, isoPart V W C y = e (0, y, 0) := fun y => by
    rw [he, isoPart_zero, midPart_zero, add_zero, zero_add]
  have hmapr : ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, a.map (incA D) ∈ ratMx D W.rank r := fun a => ⟨a, rfl⟩
  refine ⟨fun a => ?_, fun a t s => ?_, fun a b t => ?_, fun t => ?_, fun a ha => ?_⟩
  · exact hψ.1.1.comp (GlobalTheory.SplitScalar.continuous_symplO V W (continuous_isoPart V W C') continuous_const)
  · rw [isoPart_add, symplO_add_left, AddChar.map_add_eq_mul]
  · rw [Matrix.map_add _ (map_add (incA D)), isoPart_add, symplO_add_right, AddChar.map_add_eq_mul]
  · constructor
    · intro h
      have hmem : isoPart V W C' t ∈ ratL W V := by
        refine (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).1 fun γ hγ => ?_
        obtain ⟨⟨t₀, y₀, x₀⟩, rfl⟩ := e.surjective γ
        obtain ⟨-, ⟨a₀, rfl⟩, -⟩ := (hrat t₀ _ x₀).1 hγ
        rw [he, symplO_add_right, symplO_add_right, oDD, oDM, zero_add, add_zero]
        exact h a₀
      rw [hdual] at hmem
      exact ((hrat t 0 0).1 hmem).1
    · intro ht a
      have hx : isoPart V W C' t ∈ ratL W V := by
        rw [hdual]; exact (hrat t 0 0).2 ⟨ht, zero_mem _, zero_mem _⟩
      have hy : isoPart V W C (a.map (incA D)) ∈ ratL W V := by
        rw [hiso]; exact (hrat 0 _ 0).2 ⟨zero_mem _, hmapr a, zero_mem _⟩
      exact (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).2 hx _ hy
  · set z := isoPart V W C (a.map (incA D)) with hz
    have hall : ∀ w : WO V W, ψ (symplO V W z w) = 1 := fun w => by
      obtain ⟨⟨t, y, x⟩, rfl⟩ := e.surjective w
      have hskew : symplO V W z (e (t, y, x)) = -symplO V W (e (t, y, x)) z := by
        exact GlobalTheory.SplitScalar.symplO_skew V W _ _
      rw [hskew, he, symplO_add_left, symplO_add_left, hz, oII, GlobalTheory.SplitScalar.symplO_skew V W _ (midPart V V' W B x),
        oIM, neg_zero, add_zero, add_zero, AddChar.map_neg_eq_inv, ha t, inv_one]
    have hzc : z = (a * (adj D C * V.gram)).map (incA D) := by
      simp only [hz, isoPart, Matrix.map_mul]
    by_contra ha0
    have hc : a * (adj D C * V.gram) ≠ 0 := by
      intro h0
      apply ha0
      calc a = a * (adj D C * V.gram * C') := by rw [h1, Matrix.mul_one]
        _ = a * (adj D C * V.gram) * C' := (Matrix.mul_assoc _ _ _).symm
        _ = 0 := by rw [h0, Matrix.zero_mul]
    obtain ⟨w, hw⟩ := exists_pair_ne_one ψ hψ V W _ hc
    rw [← hzc] at hw
    exact hw (hall w)

end GlobalTheory.IsoDualChars
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaRuleExchangePairMembersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realThetaRule_exchange_pair_members : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), (Formalism.MainNotions.SchurIrreducible.ARiiiUp X lam lam' → Formalism.MainNotions.SchurIrreducible.ARiiiDown X lam' lam) ∧ (Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam' → Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam' lam) ∧ (Formalism.MainNotions.SchurIrreducible.ARiv X (r := r) (s := s) lam → NoLow X r s lam) := by
  first | exact @GlobalTheory.SwapRule.swap_rule | exact GlobalTheory.SwapRule.swap_rule | (intros; apply GlobalTheory.SwapRule.swap_rule <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumLeOfLatticeCoordsQuadraticDecayStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_le_of_lattice_coords_quadraticDecay : ∀ {Y : Type} (n N : ℕ), 0 < N → ∀ (a : Y → ENNReal) (T : Fin n → Y → ℝ), (∀ y y', a y ≠ 0 → a y' ≠ 0 → (∀ j, T j y = T j y') → y = y') → (∀ y, a y ≠ 0 → ∀ j, ∃ c : ℤ, (N : ℝ) * T j y = c) → ∀ S : ENNReal, (∀ y, a y * ∏ j, ENNReal.ofReal (1 + T j y ^ 2) ≤ S) → ∑' y, a y ≤ S * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n) := by
  first | exact @GlobalTheory.TwBoundFour.tsum_le | exact GlobalTheory.TwBoundFour.tsum_le | (intros; apply GlobalTheory.TwBoundFour.tsum_le <;> assumption)
end

