module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVCos
section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set Filter

section Cos

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

theorem hasDens_zero : HasDens μ f ι ν (fun _ => 0) (fun _ => 0) := by
  exact ⟨integrable_zero _ _ _, continuous_const, fun S _ => by simp⟩

theorem HasDens.add [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v + φ₂ v) (fun b => g₁ b + g₂ b) := by
  obtain ⟨hi1, hc1, he1⟩ := h₁
  obtain ⟨hi2, hc2, he2⟩ := h₂
  refine ⟨hi1.add hi2, hc1.add hc2, fun S hS => ?_⟩
  have hg1 : IntegrableOn g₁ S ν := by
    first
      | exact hc1.continuousOn.integrableOn_compact hS
      | exact ContinuousOn.integrableOn_compact hS hc1.continuousOn
  have hg2 : IntegrableOn g₂ S ν := by
    first
      | exact hc2.continuousOn.integrableOn_compact hS
      | exact ContinuousOn.integrableOn_compact hS hc2.continuousOn
  rw [integral_add hi1.integrableOn hi2.integrableOn, integral_add hg1 hg2, he1 S hS, he2 S hS]

theorem hasDens_sum [IsFiniteMeasureOnCompacts ν] {κ : Type} (φ : κ → V → ℝ) (g : κ → X → ℝ) :
    ∀ T : Finset κ, (∀ i ∈ T, HasDens μ f ι ν (φ i) (g i)) →
      HasDens μ f ι ν (fun v => ∑ i ∈ T, φ i v) (fun b => ∑ i ∈ T, g i b) := by
  intro T
  induction T using Finset.cons_induction with
  | empty =>
    intro _
    simpa using (hasDens_zero : HasDens μ f ι ν (fun _ => 0) (fun _ => 0))
  | cons a s ha ih =>
    intro hT
    have h1 := hT a (Finset.mem_cons_self a s)
    have h2 := ih (fun i hi => hT i (Finset.mem_cons_of_mem hi))
    simpa [Finset.sum_cons] using h1.add h2

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
  have he : {z | z - y ∈ Λ} = (fun w => w + y) '' (Λ : Set V) := by
    ext z
    constructor
    · intro hz
      exact ⟨z - y, hz, sub_add_cancel z y⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  rw [he]
  exact hΛc.image (continuous_add_const y)

theorem integrable_cos [IsFiniteMeasureOnCompacts μ] (Λ : AddSubgroup V)
    (hΛo : IsOpen (Λ : Set V)) (hΛc : IsCompact (Λ : Set V)) (y : V) :
    Integrable ({z | z - y ∈ Λ}.indicator fun _ => (1 : ℝ)) μ := by
  have hK := isCompact_cos Λ hΛc y
  have hO : IsOpen {z : V | z - y ∈ Λ} := hΛo.preimage (continuous_sub_right y)
  have hI : IntegrableOn (fun _ : V => (1 : ℝ)) {z : V | z - y ∈ Λ} μ := by
    first
      | exact ContinuousOn.integrableOn_compact hK continuousOn_const
      | exact integrableOn_const hK.measure_lt_top.ne
      | exact integrableOn_const.2 (Or.inr hK.measure_lt_top)
  exact hI.integrable_indicator hO.measurableSet

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

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVSec
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

theorem exists_leftInv_of_linIndep {K : Type} [CommRing K] [IsSemisimpleRing K] {a M : ℕ}
    (Z : Fin a → Fin M → K) (hZ : LinearIndependent K Z) :
    ∃ q : Fin M → Fin a → K, ∀ i i', ∑ k, Z i k * q k i' = if i = i' then 1 else 0 := by
  classical
  let f : (Fin a → K) →ₗ[K] (Fin M → K) := ∑ i, (LinearMap.proj i).smulRight (Z i)
  have hf_apply : ∀ c, f c = ∑ i, c i • Z i := by
    intro c
    simp [f, LinearMap.sum_apply]
  have hf : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    rw [hf_apply] at hc
    funext i
    exact Fintype.linearIndependent_iff.1 hZ c hc i
  obtain ⟨g, hg⟩ : ∃ g : (Fin M → K) →ₗ[K] (Fin a → K), g ∘ₗ f = LinearMap.id := by
    first
    | exact IsSemisimpleModule.extension_property f hf LinearMap.id
    | (obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.range f)
       exact ⟨(LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ
         Submodule.linearProjOfIsCompl _ _ hC, by
           ext c : 1
           simp [Submodule.linearProjOfIsCompl_apply_left]⟩)
  refine ⟨fun k i' => g (fun j => if k = j then 1 else 0) i', fun i i' => ?_⟩
  have hZi : Z i = ∑ k, Z i k • (fun j => if k = j then (1 : K) else 0) := pi_eq_sum_univ (Z i)
  have key : g (Z i) = fun j => if i = j then 1 else 0 := by
    have hZf : Z i = f (fun j => if i = j then 1 else 0) := by
      rw [hf_apply]
      simp
    rw [hZf, ← LinearMap.comp_apply, hg, LinearMap.id_apply]
  have h2 := congrFun key i'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hZi, map_sum] at h2
  simpa [Finset.sum_apply, map_smul] using h2

theorem secGram_holds : SecGram := by
  intro F E _ _ _ _ _ σ hσ M J hJ hdet R _ _ hss a x hx
  classical
  have hs2 : ∀ z : R ⊗[F] E, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hσ]
    | add z w hz hw => rw [map_add (f := _), map_add (f := _), hz, hw]
  have hsF : ∀ c : F, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (algebraMap F (R ⊗[F] E) c) = algebraMap F (R ⊗[F] E) c := by
    intro c
    simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  have hJR : ∀ k l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (JR (F := F) R J l k) = JR (F := F) R J k l := by
    intro k l
    simp [JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hJ]
  have hJunit : IsUnit (JR (F := F) R J).det := by
    have hd : (JR (F := F) R J).det = inclR (F := F) R J.det := (RingHom.map_det (inclR (F := F) R) J).symm
    rw [hd]
    exact (isUnit_iff_ne_zero.2 hdet).map _
  set s := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ with hs
  let w : Fin a → Fin M → R ⊗[F] E := fun i l => ∑ k, s (x i k) * JR (F := F) R J k l
  have hw : LinearIndependent (R ⊗[F] E) w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    set v : Fin M → R ⊗[F] E := fun k => ∑ i, c i * s (x i k) with hv
    have hvJ : Matrix.vecMul v (JR (F := F) R J) = 0 := by
      funext l
      have hl := congrFun hc l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w, Finset.mul_sum] at hl
      simp only [Matrix.vecMul, dotProduct, hv, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      simpa [mul_assoc] using hl
    have hv0 : v = 0 := by
      have h3 := congrArg (fun u => Matrix.vecMul u (JR (F := F) R J)⁻¹) hvJ
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJunit] using h3
    have hx0 : ∑ i, s (c i) • x i = 0 := by
      funext k
      have h4 := congrArg s (congrFun hv0 k)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hv, map_sum, map_mul, hs2, map_zero, Pi.zero_apply] at h4
      simpa [Finset.sum_apply, smul_eq_mul] using h4
    have h5 := Fintype.linearIndependent_iff.1 hx _ hx0 i
    rw [← hs2 (c i), h5, map_zero]
  obtain ⟨q, hq⟩ := exists_leftInv_of_linIndep w hw
  refine ⟨q, fun S hS => ?_⟩
  have hS' : ∀ i j, s (S j i) = S i j := hS
  set c : R ⊗[F] E := algebraMap F (R ⊗[F] E) (1 / 2) with hc
  set Y : Fin a → Fin M → R ⊗[F] E := fun j k => ∑ i', c * S i' j * q k i' with hY
  have hsum3 : ∀ f : Fin M → Fin M → Fin a → R ⊗[F] E,
      ∑ k, ∑ l, ∑ i', f k l i' = ∑ i', ∑ l, ∑ k, f k l i' := by
    intro f
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i' _ => Finset.sum_comm
  have h1 : ∀ i j, hR R σ J (x i) (Y j) = c * S i j := by
    intro i j
    have e1 : hR R σ J (x i) (Y j) =
        ∑ k, ∑ l, ∑ i', s (x i k) * JR (F := F) R J k l * (c * S i' j * q l i') := by
      simp only [hR, Formalism.UG.hform, hY, Finset.mul_sum, ← hs]
    have e2 : ∑ i', c * S i' j * ∑ l, w i l * q l i' =
        ∑ i', ∑ l, ∑ k, s (x i k) * JR (F := F) R J k l * (c * S i' j * q l i') := by
      refine Finset.sum_congr rfl fun i' _ => ?_
      simp only [w, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
    rw [e1, hsum3 (fun k l i' => s (x i k) * JR (F := F) R J k l * (c * S i' j * q l i')), ← e2]
    simp [hq]
  have h2 : ∀ i j, hR R σ J (Y i) (x j) = s (hR R σ J (x j) (Y i)) := by
    intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hR, Formalism.UG.hform, ← hs, map_sum, map_mul, hs2, hJR]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hsc : s c = c := hsF _
  have hcc : c + c = 1 := by
    rw [hc, ← map_add (f := _), show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
  unfold gramB
  funext i j
  show hR R σ J (x i) (Y j) + hR R σ J (Y i) (x j) = S i j
  rw [h2, h1, h1, map_mul, hsc, hS', ← add_mul, hcc, one_mul]

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolA
section
noncomputable section

namespace PI.VolStabSW

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

def CondAA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v in cofinite, ∀ t : Fv F v,
      (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) ↔ t ∈ v.adicCompletionIntegers F

section Vol

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]

end Vol

section Ann

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

end Ann

end VolAAW

end PI.VolStabSW
end
end

