module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabU

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfCV
section
noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology

theorem changeVar_holds : ChangeVar := by
  intro n m μ hμ f hf x0 hx0
  let A := fderiv ℝ f x0
  obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hx0)
  have hRI : Function.RightInverse B A := fun y => by
    simpa using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB
  let T := ContinuousLinearEquiv.equivOfRightInverse A B hRI
  have hT1 : ∀ x, (T x).1 = A x := fun x => rfl
  let Θ : (Fin n → ℝ) → (Fin n → ℝ) := fun x => T.symm (f x, (T x).2)
  have hΘc : ContDiff ℝ 1 Θ :=
    T.symm.contDiff.comp (hf.prodMk (contDiff_snd.comp T.contDiff))
  have hfA : ∀ x, A (Θ x) = f x := by
    intro x
    rw [← hT1]; simp [Θ]
  have hd : ∀ x, HasFDerivAt Θ (fderiv ℝ Θ x) x :=
    fun x => ((hΘc.differentiable one_ne_zero) x).hasFDerivAt
  have hid : fderiv ℝ Θ x0 = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    let P := (ContinuousLinearMap.snd ℝ (Fin m → ℝ) A.ker).comp T.toContinuousLinearMap
    have hP : HasFDerivAt (fun x => (T x).2) P x0 := P.hasFDerivAt
    have h1 : HasFDerivAt (fun x => (f x, (T x).2)) ((fderiv ℝ f x0).prod P) x0 :=
      ((hf.differentiable one_ne_zero) x0).hasFDerivAt.prodMk hP
    have h2 := T.symm.toContinuousLinearMap.hasFDerivAt.comp x0 h1
    rw [show fderiv ℝ Θ x0 = T.symm.toContinuousLinearMap.comp ((fderiv ℝ f x0).prod P) from
      h2.fderiv]
    ext1 y
    change T.symm ((fderiv ℝ f x0) y, (T y).2) = y
    have : ((fderiv ℝ f x0) y, (T y).2) = T y := Prod.ext (hT1 y).symm rfl
    rw [this, ContinuousLinearEquiv.symm_apply_apply]
  have hs : HasStrictFDerivAt Θ
      ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x0 := by
    have := hΘc.contDiffAt.hasStrictFDerivAt_fderiv (x := x0) one_ne_zero
    rw [hid] at this
    exact this
  let PH := hs.toOpenPartialHomeomorph Θ
  have hPH : ∀ x, PH x = Θ x := fun x => rfl
  let D : (Fin n → ℝ) → ℝ := fun x => (fderiv ℝ Θ x).det
  have hDc : Continuous D :=
    ContinuousLinearMap.continuous_det.comp (hΘc.continuous_fderiv one_ne_zero)
  let N := PH.source ∩ {x | D x ≠ 0}
  have hNo : IsOpen N := PH.open_source.inter (isOpen_ne_fun hDc continuous_const)
  have hx0N : x0 ∈ N := ⟨hs.mem_toOpenPartialHomeomorph_source, by
    show (fderiv ℝ Θ x0).det ≠ 0
    rw [hid, ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
    norm_num⟩
  refine ⟨N, hNo, hx0N, A, hx0, fun φ hc hsφ hφN => ?_⟩
  let C := PH '' tsupport φ
  have hNsrc : N ⊆ PH.source := Set.inter_subset_left
  have hCc : IsCompact C :=
    hsφ.image_of_continuousOn (PH.continuousOn.mono (hφN.trans hNsrc))
  let G : (Fin n → ℝ) → ℝ := PH.target.indicator fun z => φ (PH.symm z) / |D (PH.symm z)|
  have hGC : ∀ z, z ∉ C → G z = 0 := by
    intro z hz
    by_cases ht : z ∈ PH.target
    · simp only [G, Set.indicator_of_mem ht]
      have : φ (PH.symm z) = 0 := by
        by_contra h0
        exact hz ⟨PH.symm z, subset_tsupport _ h0, PH.right_inv ht⟩
      rw [this, zero_div]
    · simp [G, ht]
  have hNimg : IsOpen (PH '' N) := PH.isOpen_image_of_subset_source hNo hNsrc
  have hCN : C ⊆ PH '' N := Set.image_mono hφN
  have hGcont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ PH '' N
    · obtain ⟨x, hxN, rfl⟩ := hz
      have hxs : x ∈ PH.source := hNsrc hxN
      have hev : G =ᶠ[𝓝 (PH x)] fun z => φ (PH.symm z) / |D (PH.symm z)| := by
        filter_upwards [PH.open_target.mem_nhds (PH.map_source hxs)] with z hz
        simp [G, Set.indicator_of_mem hz]
      refine ContinuousAt.congr ?_ hev.symm
      have hsymm : ContinuousAt PH.symm (PH x) := PH.continuousAt_symm (PH.map_source hxs)
      have hD0 : D (PH.symm (PH x)) ≠ 0 := by rw [PH.left_inv hxs]; exact hxN.2
      exact (hc.continuousAt.comp hsymm).div
        ((continuous_abs.continuousAt).comp (hDc.continuousAt.comp hsymm))
        (abs_ne_zero.2 hD0)
    · have hzC : z ∉ C := fun h => hz (hCN h)
      have hev : G =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [hCc.isClosed.isOpen_compl.mem_nhds hzC] with w hw
        exact hGC w hw
      exact (continuousAt_const).congr hev.symm
  have hGs : HasCompactSupport G := HasCompactSupport.intro hCc hGC
  refine ⟨G, hGcont, hGs, fun S hS => ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hNm : MeasurableSet N := hNo.measurableSet
  have hJ := integral_image_eq_integral_abs_det_fderiv_smul μ hNm
    (fun x _ => (hd x).hasFDerivWithinAt) (PH.injOn.mono hNsrc)
    ((A ⁻¹' S).indicator G)

  have hL : ∫ x in Θ '' N, (A ⁻¹' S).indicator G x ∂μ = ∫ v in A ⁻¹' S, G v ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_indicator
      (hSm.preimage A.continuous.measurable)]
    intro z hz
    have : G z = 0 := hGC z fun h => hz (hCN h)
    simp [Set.indicator, this]

  have hR : ∫ x in N, |(fderiv ℝ Θ x).det| • (A ⁻¹' S).indicator G (Θ x) ∂μ =
      ∫ v in f ⁻¹' S, φ v ∂μ := by
    have e1 : ∀ x ∈ N, |(fderiv ℝ Θ x).det| • (A ⁻¹' S).indicator G (Θ x) =
        (f ⁻¹' S).indicator φ x := by
      intro x hxN
      have hxs : x ∈ PH.source := hNsrc hxN
      have ht : Θ x ∈ PH.target := PH.map_source hxs
      have hl : PH.symm (Θ x) = x := PH.left_inv hxs
      have hD : D x ≠ 0 := hxN.2
      by_cases hfS : f x ∈ S
      · have h1 : Θ x ∈ A ⁻¹' S := by simp [hfA, hfS]
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show x ∈ f ⁻¹' S from hfS)]
        simp only [G, Set.indicator_of_mem ht, hl, smul_eq_mul]
        change |D x| * (φ x / |D x|) = φ x
        field_simp
      · have h1 : Θ x ∉ A ⁻¹' S := by simp [hfA, hfS]
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show x ∉ f ⁻¹' S from hfS),
          smul_zero]
    rw [setIntegral_congr_fun hNm e1, setIntegral_eq_integral_of_forall_compl_eq_zero,
      integral_indicator (hSm.preimage (hf.continuous.measurable))]
    intro x hx
    have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hφN h)
    simp [Set.indicator, this]
  rw [← hR, ← hL, hJ]

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVCos
section
noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Set Filter

section Cos

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

theorem hasDens_zero : HasDens μ f ι ν (fun _ => 0) (fun _ => 0) :=
  ⟨integrable_zero _ _ _, continuous_const, fun S _ => by simp⟩

theorem HasDens.add [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v + φ₂ v) (fun b => g₁ b + g₂ b) := by
  refine ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, fun S hS => ?_⟩
  rw [integral_add h₁.1.integrableOn h₂.1.integrableOn, h₁.2.2 S hS, h₂.2.2 S hS,
    integral_add (h₁.2.1.continuousOn.integrableOn_compact hS)
      (h₂.2.1.continuousOn.integrableOn_compact hS)]

theorem hasDens_sum [IsFiniteMeasureOnCompacts ν] {κ : Type} (φ : κ → V → ℝ) (g : κ → X → ℝ) :
    ∀ T : Finset κ, (∀ i ∈ T, HasDens μ f ι ν (φ i) (g i)) →
      HasDens μ f ι ν (fun v => ∑ i ∈ T, φ i v) (fun b => ∑ i ∈ T, g i b) := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; simpa using (hasDens_zero (μ := μ) (f := f) (ι := ι) (ν := ν))
  | insert i T hi ih =>
    intro h
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

def DensCosB (B : AddSubgroup V → Prop) (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X)
    (U : Set V) : Prop :=
  ∀ x ∈ U, ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ : AddSubgroup V, B Λ → IsOpen (Λ : Set V) →
    IsCompact (Λ : Set V) → (Λ : Set V) ⊆ N → ∃ g : X → ℝ, Continuous g ∧
      ∀ S : Set X, IsCompact S →
        ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ}.indicator (fun _ => (1 : ℝ)) v ∂μ =
          ∫ b in S, g b ∂ν


omit [IsTopologicalAddGroup V] in
def IsCOBasis (B : AddSubgroup V → Prop) : Prop :=
  ∀ N ∈ 𝓝 (0 : V), ∃ Λ : AddSubgroup V, B Λ ∧ IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧
    (Λ : Set V) ⊆ N

omit [MeasurableSpace V] [OpensMeasurableSpace V] in
theorem isCompact_cos (Λ : AddSubgroup V) (hΛc : IsCompact (Λ : Set V)) (y : V) :
    IsCompact {z | z - y ∈ Λ} := by
  have : {z | z - y ∈ Λ} = (fun w => w + y) '' (Λ : Set V) := by
    ext z
    constructor
    · intro hz
      exact ⟨z - y, hz, sub_add_cancel z y⟩
    · rintro ⟨w, hw, rfl⟩
      show w + y - y ∈ Λ
      rwa [add_sub_cancel_right]
  rw [this]
  exact hΛc.image (continuous_id.add continuous_const)

theorem integrable_cos [IsFiniteMeasureOnCompacts μ] (Λ : AddSubgroup V)
    (hΛo : IsOpen (Λ : Set V)) (hΛc : IsCompact (Λ : Set V)) (y : V) :
    Integrable ({z | z - y ∈ Λ}.indicator fun _ => (1 : ℝ)) μ := by
  have hm : MeasurableSet {z : V | z - y ∈ Λ} :=
    (hΛo.preimage (continuous_id.sub continuous_const)).measurableSet
  rw [integrable_indicator_iff hm]
  exact integrableOn_const (isCompact_cos Λ hΛc y).measure_lt_top.ne

theorem densLC_of_cosB [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] (U : Set V)
    (B : AddSubgroup V → Prop) (hB : IsCOBasis B) (h : DensCosB B μ f ι ν U) :
    DensOn (IsLCcOn U) μ f ι ν := by
  classical
  rintro φ ⟨hlc, hs, hsU⟩
  have hloc : ∀ x : tsupport φ, ∃ Λx : AddSubgroup V, IsOpen (Λx : Set V) ∧
      IsCompact (Λx : Set V) ∧
      (∀ y, y - (x : V) ∈ Λx → ∀ Λ : AddSubgroup V, B Λ → IsOpen (Λ : Set V) →
        IsCompact (Λ : Set V) → Λ ≤ Λx →
          ∃ g, HasDens μ f ι ν ({z | z - y ∈ Λ}.indicator fun _ => (1 : ℝ)) g) ∧
      ∀ z ∈ Λx, φ ((x : V) + z) = φ x := by
    intro x
    obtain ⟨N, hN, hd⟩ := h x (hsU x.2)
    have hfib : {z : V | φ ((x : V) + z) = φ x} ∈ 𝓝 (0 : V) := by
      have ho : IsOpen {z : V | (φ ∘ fun z => (x : V) + z) z = φ x} :=
        (hlc.comp_continuous (continuous_const.add continuous_id)).isClopen_fiber _ |>.isOpen
      exact ho.mem_nhds (by simp)
    obtain ⟨Λx, -, ho, hc, hsub⟩ := hB _ (inter_mem hN hfib)
    refine ⟨Λx, ho, hc, fun y hy Λ hBΛ hΛo hΛc hle => ?_, fun z hz => (hsub hz).2⟩
    obtain ⟨g, hg, hS⟩ := hd y (hsub hy).1 Λ hBΛ hΛo hΛc fun z hz => (hsub (hle hz)).1
    exact ⟨g, integrable_cos Λ hΛo hΛc y, hg, hS⟩
  choose Λx hΛxo hΛxc hΛxd hΛxφ using hloc
  obtain ⟨t, ht⟩ := hs.isCompact.elim_finite_subcover
    (fun x : tsupport φ => {y : V | y - (x : V) ∈ Λx x})
    (fun x => (hΛxo x).preimage (continuous_id.sub continuous_const))
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, by simp [(Λx _).zero_mem]⟩)
  obtain ⟨Λs, -, hso, -, -⟩ := hB univ univ_mem
  set Λi : AddSubgroup V := Λs ⊓ ⨅ x ∈ t, Λx x with hΛi
  have hΛio : IsOpen (Λi : Set V) := isOpen_inf_iInf Λs hso t Λx hΛxo
  obtain ⟨Λ', hBΛ', hΛ'o, hΛ'c, hΛ'sub⟩ := hB _ (hΛio.mem_nhds Λi.zero_mem)
  have hΛ'le : ∀ x ∈ t, Λ' ≤ Λx x := fun x hx z hz =>
    AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (inf_le_right (a := Λs) (hΛ'sub hz)) x) hx
  have hK : ∀ y ∈ tsupport φ, ∃ x ∈ t, y - (x : V) ∈ Λx x := fun y hy => by
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (ht hy)
    exact ⟨x, hx, hyx⟩
  have hconst : ∀ y ∈ tsupport φ, ∀ z ∈ Λ', φ (y + z) = φ y := by
    intro y hy z hz
    obtain ⟨x, hx, hyx⟩ := hK y hy
    have h1 := hΛxφ x (y - x) hyx
    have h2 := hΛxφ x (y + z - x) (by
      have := (Λx x).add_mem hyx (hΛ'le x hx hz)
      rwa [show y - (x : V) + z = y + z - x by abel] at this)
    rw [add_sub_cancel] at h1 h2
    rw [h2, h1]
  obtain ⟨t2, ht2⟩ := hs.isCompact.elim_finite_subcover
    (fun y : tsupport φ => {z : V | z - (y : V) ∈ Λ'})
    (fun y => hΛ'o.preimage (continuous_id.sub continuous_const))
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, by simp [Λ'.zero_mem]⟩)
  set T : Finset (V ⧸ Λ') :=
    t2.image fun y : tsupport φ => (QuotientAddGroup.mk (y : V) : V ⧸ Λ') with hT
  have hrep : ∀ q ∈ T, ∃ y ∈ tsupport φ, q.out - y ∈ Λ' := by
    intro q hq
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hq
    refine ⟨y, y.2, ?_⟩
    have := Λ'.neg_mem (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (y : V) : V ⧸ Λ')))
    rwa [neg_add_rev, neg_neg, neg_add_eq_sub] at this
  have hTd : ∀ q ∈ T, ∃ g, HasDens μ f ι ν ({z | z - q.out ∈ Λ'}.indicator fun _ => (1 : ℝ)) g := by
    intro q hq
    obtain ⟨y, hy, hqy⟩ := hrep q hq
    obtain ⟨x, hx, hyx⟩ := hK y hy
    exact hΛxd x q.out (by
      have := (Λx x).add_mem hyx (hΛ'le x hx hqy)
      rwa [show y - (x : V) + (q.out - y) = q.out - x by abel] at this) Λ' hBΛ' hΛ'o hΛ'c
      (hΛ'le x hx)
  choose! gq hgq using hTd
  have hsum := hasDens_sum
    (fun q v => φ (q : V ⧸ Λ').out * {z | z - q.out ∈ Λ'}.indicator (fun _ => (1 : ℝ)) v)
    (fun q b => φ (q : V ⧸ Λ').out * gq q b) T (fun q hq => (hgq q hq).const_mul _)
  have heq : (fun v => ∑ q ∈ T,
      φ (q : V ⧸ Λ').out * {z | z - q.out ∈ Λ'}.indicator (fun _ => (1 : ℝ)) v) = φ := by
    funext x
    have hind : ∀ q : V ⧸ Λ', {z | z - q.out ∈ Λ'}.indicator (fun _ => (1 : ℝ)) x =
        if (x : V ⧸ Λ') = q then 1 else 0 := by
      intro q
      have : x - q.out ∈ Λ' ↔ (x : V ⧸ Λ') = q := by
        conv_rhs => rw [← QuotientAddGroup.out_eq' q]
        rw [eq_comm, QuotientAddGroup.eq, neg_add_eq_sub]
      by_cases hq : (x : V ⧸ Λ') = q
      · rw [if_pos hq, Set.indicator_of_mem (show x ∈ {z | z - q.out ∈ Λ'} from this.2 hq)]
      · rw [if_neg hq, Set.indicator_of_notMem (show x ∉ {z | z - q.out ∈ Λ'} from
          fun h' => hq (this.1 h'))]
    simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    split_ifs with hxT
    · obtain ⟨y, hy, hqy⟩ := hrep _ hxT
      have e1 := hconst y hy _ hqy
      rw [add_sub_cancel] at e1
      have hxo : x - (x : V ⧸ Λ').out ∈ Λ' := by
        have := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (x : V ⧸ Λ'))
        rwa [neg_add_eq_sub] at this
      have e2 := hconst y hy _ (Λ'.add_mem hxo hqy)
      rw [show y + (x - (x : V ⧸ Λ').out + ((x : V ⧸ Λ').out - y)) = x by abel] at e2
      rw [e1, e2]
    · by_contra hne
      have hxK : x ∈ tsupport φ := subset_tsupport φ (Ne.symm hne)
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht2 hxK)
      apply hxT
      refine Finset.mem_image.2 ⟨y, hy, ?_⟩
      exact QuotientAddGroup.eq.2 (by rw [neg_add_eq_sub]; exact hxy)
  rw [heq] at hsum
  exact ⟨_, hsum.2.1, hsum.2.2⟩

end Cos

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExFDStabFin
section
namespace PI.VolStabS

theorem discHF_holds : DiscHF :=
  discHF_of_discHA (PI.VolSemiDirect.W.discHA_of PI.VolSemiDirect.W.Lc.tensor_adele_topology_holds)

theorem exFDStab_holds : ExFDStab := exFDStab_of scha_holds discHF_holds

end PI.VolStabS
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabFin
section
noncomputable section

namespace PI.VolStabS

theorem exStab_of_orb (hO : OrbTup) (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_U secCtblW_holds lcscPolish_holds hO hI hF hN

end PI.VolStabS
end
end

