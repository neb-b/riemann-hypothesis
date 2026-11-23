module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0011
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetIntegralScaledBoxPiCosetReps
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.BoxReps

def boxSubgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) (s : kˣ) : AddSubgroup (n → k) where
  carrier := box n s
  add_mem' hx hy i _ := add_mem_cball (hx i trivial) (hy i trivial)
  zero_mem' i _ := by simp [cball]
  neg_mem' hx i _ := neg_mem_cball (hx i trivial)

theorem exists_finset_box_reps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ), valuation k (r : k) ≤ valuation k (R : k) → ∃ S : Finset (n → k), (∀ b ∈ S, b ∈ box n R) ∧ ∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r := by
  intro k _ _ _ _ n _ r R _
  classical
  set H := boxSubgroup k n r
  have hH : ∀ x, x ∈ H ↔ x ∈ box n r := fun _ => Iff.rfl
  have hq : ∀ a b : n → k, (QuotientAddGroup.mk a : (n → k) ⧸ H) = QuotientAddGroup.mk b ↔ a - b ∈ box n r := by
    intro a b
    rw [QuotientAddGroup.eq, ← hH, ← H.neg_mem_iff]
    simp [neg_add_eq_sub]
  obtain ⟨T, hTsub, hTfin, hcov⟩ := (isCompact_box (n := n) R).elim_finite_subcover_image
    (b := box n R) (c := fun a => (fun x => x - a) ⁻¹' box n r)
    (fun a _ => (isOpen_box r).preimage (continuous_id.sub continuous_const))
    (fun x hx => Set.mem_biUnion hx (show x - x ∈ box n r by rw [sub_self]; exact (boxSubgroup k n r).zero_mem))
  set π : (n → k) → (n → k) ⧸ H := QuotientAddGroup.mk
  let f : (n → k) ⧸ H → (n → k) := fun q =>
    if h : ∃ a ∈ box n R, π a = q then Classical.choose h else 0
  have hf : ∀ a ∈ box n R, f (π a) ∈ box n R ∧ π (f (π a)) = π a := by
    intro a ha
    have h : ∃ b ∈ box n R, π b = π a := ⟨a, ha, rfl⟩
    simp only [f, dif_pos h]
    exact Classical.choose_spec h
  refine ⟨(hTfin.toFinset.image π).image f, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hb
    obtain ⟨q, ⟨t, ht, rfl⟩, rfl⟩ := hb
    exact (hf t (hTsub ht)).1
  · intro a ha
    obtain ⟨t, ht, hat⟩ := Set.mem_iUnion₂.mp (hcov ha)
    have hat' : π a = π t := (hq a t).mpr hat
    refine ⟨f (π a), ⟨?_, ?_⟩, ?_⟩
    · simp only [Finset.mem_image, Set.Finite.mem_toFinset]
      exact ⟨π t, ⟨t, ht, rfl⟩, by rw [hat']⟩
    · exact (hq a _).mp (hf a ha).2.symm
    · rintro b ⟨hb, hab⟩
      simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hb
      obtain ⟨q, ⟨t', ht', rfl⟩, rfl⟩ := hb
      have h1 : π a = π (f (π t')) := (hq a _).mpr hab
      rw [(hf t' (hTsub ht')).2] at h1
      rw [h1]

end GlobalTheory.BoxReps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralScaledBoxPiSupersetOfIsCompact
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

namespace GlobalTheory

theorem box_subset_box_of_valuation_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) {s t : kˣ}
    (h : valuation k (s : k) ≤ valuation k (t : k)) : box n s ⊆ box n t :=
  fun x hx i _ => show valuation k (x i) ≤ _ from le_trans (hx i trivial) h

theorem exists_box_superset_of_isCompact (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (K : Set (n → k)) :
    IsCompact K → ∀ r : kˣ, ∃ R : kˣ, valuation k (r : k) ≤ valuation k (R : k) ∧ K ⊆ box n R := by
  intro hK r
  let ι := {s : kˣ // valuation k (r : k) ≤ valuation k (s : k)}
  haveI : Nonempty ι := ⟨⟨r, le_rfl⟩⟩
  have hcov : K ⊆ ⋃ s : ι, box n (s : kˣ) := by
    intro x _
    rw [Set.mem_iUnion]
    by_cases hn : Nonempty n
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => valuation k (x i))
        Finset.univ_nonempty
      by_cases hle : valuation k (x i0) ≤ valuation k (r : k)
      · refine ⟨⟨r, le_rfl⟩, fun i _ => ?_⟩
        exact le_trans (hi0 i (Finset.mem_univ i)) hle
      · push_neg at hle
        have hx0 : x i0 ≠ 0 := by
          intro h0
          rw [h0, map_zero] at hle
          exact not_lt_zero' hle
        refine ⟨⟨Units.mk0 (x i0) hx0, by simpa using hle.le⟩, fun i _ => ?_⟩
        simpa [cball] using hi0 i (Finset.mem_univ i)
    · refine ⟨⟨r, le_rfl⟩, fun i _ => (hn ⟨i⟩).elim⟩
  have hdir : Directed (· ⊆ ·) (fun s : ι => box n (s : kˣ)) := by
    intro s t
    rcases le_total (valuation k ((s : kˣ) : k)) (valuation k ((t : kˣ) : k)) with h | h
    · exact ⟨t, box_subset_box_of_valuation_le n h, le_rfl⟩
    · exact ⟨s, le_rfl, box_subset_box_of_valuation_le n h⟩
  obtain ⟨s, hs⟩ := hK.elim_directed_cover (fun s : ι => box n (s : kˣ))
    (fun s => isOpen_box _) hcov hdir
  exact ⟨s, s.2, hs⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBoxInvariantEqMeasureRealMulSumReps
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil.FourierPi

theorem integral_eq_measureReal_box_mul_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)), (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) → ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) → (∀ y ∉ box n R, F y = 0) → ∫ y, F y ∂(Measure.pi fun _ => ν) = ((Measure.pi fun _ : n => ν).real (box n r) : ℂ) * ∑ b ∈ S, F b := by
  intro k _ _ _ _ _ _ ν hν n _ r R S hS hrep F hF hF0
  classical
  have : ν.IsAddHaarMeasure := hν
  have : SecondCountableTopology k := secondCountable k
  have : SigmaFinite ν := inferInstance
  have : (Measure.pi fun _ : n => ν).IsAddHaarMeasure := inferInstance
  set μ : Measure (n → k) := Measure.pi fun _ => ν
  have hmeas : MeasurableSet (box n r) :=
    MeasurableSet.univ_pi fun _ => (isOpen_cball r).measurableSet
  have hfin : μ (box n r) < ⊤ := (isCompact_box r).measure_lt_top

  have key : ∀ y, F y = ∑ b ∈ S, (box n r).indicator (fun _ => F b) (y - b) := by
    intro y
    by_cases hy : y ∈ box n R
    · obtain ⟨b, ⟨hbS, hb⟩, huniq⟩ := hrep y hy
      rw [Finset.sum_eq_single b]
      · rw [Set.indicator_of_mem hb]
        have h := hF (y - b) hb b
        rwa [add_sub_cancel] at h
      · intro b' hb'S hne
        have hnot : y - b' ∉ box n r := fun hmem => hne (huniq b' ⟨hb'S, hmem⟩)
        exact Set.indicator_of_notMem hnot _
      · intro hbn
        exact absurd hbS hbn
    · rw [hF0 y hy]
      symm
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hmem : y - b ∈ box n r
      · rw [Set.indicator_of_mem hmem]
        have h := hF (y - b) hmem b
        rw [add_sub_cancel] at h
        rw [← h, hF0 y hy]
      · exact Set.indicator_of_notMem hmem _
  have hint : ∀ b ∈ S, Integrable (fun y => (box n r).indicator (fun _ => F b) (y - b)) μ := by
    intro b _
    have h1 : Integrable ((box n r).indicator fun _ : n → k => F b) μ := by
      refine (integrable_indicator_iff hmeas).2 ?_
      exact integrableOn_const hfin.ne
    exact h1.comp_sub_right b
  calc ∫ y, F y ∂μ = ∫ y, ∑ b ∈ S, (box n r).indicator (fun _ => F b) (y - b) ∂μ := by
        congr 1
        funext y
        exact key y
    _ = ∑ b ∈ S, ∫ y, (box n r).indicator (fun _ => F b) (y - b) ∂μ := integral_finsetSum S hint
    _ = ∑ b ∈ S, (μ.real (box n r) : ℂ) * F b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [integral_sub_right_eq_self (fun y => (box n r).indicator (fun _ => F b) y) b,
          integral_indicator_const _ hmeas, Complex.real_smul]
    _ = _ := by rw [Finset.mul_sum]

end GlobalTheory.SplitWeil.FourierPi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralLastFactorSliceMemSchwartzBruhat
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SliceIntegral

theorem integral_slice_mem_SB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂]
    (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) :
    (fun x => ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∈ SB (I₀ → k) := by
  haveI := t2Space k
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro (IsCompact.image Φ.2.2 continuous_fst) fun x hx => ?_⟩
  · have ht : Filter.Tendsto (fun x' : I₀ → k => ((x - x', (0 : I₁ → k), (0 : I₂ → k)) :
        (I₀ → k) × (I₁ → k) × (I₂ → k))) (𝓝 x) (𝓝 0) := by
      have hc : Continuous (fun x' : I₀ → k => ((x - x', (0 : I₁ → k), (0 : I₂ → k)) :
          (I₀ → k) × (I₁ → k) × (I₂ → k))) := by fun_prop
      have := hc.tendsto x
      rwa [sub_self, ← Prod.zero_eq_mk, ← Prod.zero_eq_mk] at this
    filter_upwards [ht.eventually (GlobalTheory.SBConv.eventually_translate Φ.2)] with x' hx'
    congr 1
    funext a
    have := hx' (x, 0, a)
    simpa using this
  · have h0 : ∀ a, Φ.1 (x, 0, a) = 0 := fun a =>
      image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩
    simp [h0]

end GlobalTheory.SliceIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantOfTsupport
section
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology

namespace GlobalTheory.LocMod.Inhab

section Abstract

variable {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {N : Submodule ℂ (G → ℂ)} {K : AddSubgroup G}

theorem ind_mem (h : IsBichar χ) (hN : ∀ y, ∀ Φ ∈ N, (fun t => χ t y * Φ t) ∈ N)
    (hsep : ∀ u, u ∉ K → ∃ y, (∀ κ ∈ K, χ κ y = 1) ∧ χ u y ≠ 1) (R : Finset G) :
    ∀ Φ ∈ N, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → Φ 0 ≠ 0 → (∀ t, Φ t ≠ 0 → t ∈ K ∨ ∃ r ∈ R, t - r ∈ K) → ind K ∈ N := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro Φ hΦ h1 h2 h3
    convert N.smul_mem (Φ 0)⁻¹ hΦ using 1
    funext t
    by_cases ht : t ∈ K
    · have := h1 t ht 0
      rw [zero_add] at this
      simp [ind, ht, this, h2]
    · have : Φ t = 0 := by_contra fun hh => by simpa [ht] using h3 t hh
      simp [ind, ht, this]
  | insert r R _ ih =>
    intro Φ hΦ h1 h2 h3
    by_cases hr : r ∈ K
    · refine ih Φ hΦ h1 h2 fun t ht => ?_
      rcases h3 t ht with hh | ⟨s, hs, hh⟩
      · exact Or.inl hh
      · rcases Finset.mem_insert.1 hs with rfl | hs
        · exact Or.inl (by simpa using add_mem hh hr)
        · exact Or.inr ⟨s, hs, hh⟩
    · obtain ⟨y, hy, hne⟩ := hsep r hr
      refine ih _ (N.sub_mem (hN y Φ hΦ) (N.smul_mem (χ r y) hΦ)) (fun u hu t => ?_) ?_ fun t ht => ?_
      · simp only [Pi.sub_apply, Pi.smul_apply, h.left, hy u hu, h1 u hu, mul_one]
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h.zero_left, ← sub_mul]
        exact mul_ne_zero (sub_ne_zero.2 hne.symm) h2
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← sub_mul] at ht
        rcases h3 t (right_ne_zero_of_mul ht) with hh | ⟨s, hs, hh⟩
        · exact Or.inl hh
        · rcases Finset.mem_insert.1 hs with rfl | hs
          · refine absurd ?_ (left_ne_zero_of_mul ht)
            rw [← add_sub_cancel s t, h.left, hy _ hh, mul_one, sub_self]
          · exact Or.inr ⟨s, hs, hh⟩

theorem mem_of_ind_mem (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hK : ind K ∈ N) (R : Finset G) :
    ∀ Φ : G → ℂ, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → (∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ K) → Φ ∈ N := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro Φ _ h3
    convert N.zero_mem using 1
    funext t
    by_contra ht
    simpa using h3 t ht
  | insert s R _ ih =>
    intro Φ h2 h3
    have hm := N.smul_mem (Φ s) (hN (-s) _ hK)
    have hval : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ≠ 0 → Φ t ≠ 0 ∧ t + -s ∉ K := by
      intro t ht
      have hn : t + -s ∉ K := fun hh => ht (by
        have := h2 _ hh s
        rw [show s + (t + -s) = t by abel] at this
        simp [ind, hh, this])
      exact ⟨by simpa [ind, hn] using ht, hn⟩
    have := ih (Φ - Φ s • fun t => ind K (t + -s)) (fun u hu t => by
      simp only [Pi.sub_apply, Pi.smul_apply, h2 u hu]
      rw [add_right_comm, ind_add K _ hu]) fun t ht => by
        obtain ⟨s', hs', hu⟩ := h3 t (hval t ht).1
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · exact absurd (by rwa [← sub_eq_add_neg]) (hval _ ht).2
        · exact ⟨s', hs', hu⟩
    simpa using add_mem this hm

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem eventually_invariant {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) :
    ∀ᶠ u in 𝓝 (0 : Matrix Y Y' k), ∀ t ∈ tsupport Φ, Φ (t + u) = Φ t :=
  hΦ.2.isCompact.eventually_forall_of_forall_eventually (P := fun u t => Φ (t + u) = Φ t) fun x _ => by
    have h1 := ((continuous_snd.add continuous_fst).tendsto' ((0 : Matrix Y Y' k), x) x (add_zero x)).eventually
      (hΦ.1.eventually_eq x)
    have h2 := (continuous_snd.tendsto ((0 : Matrix Y Y' k), x)).eventually (hΦ.1.eventually_eq x)
    filter_upwards [h1, h2] with z a b using a.trans b.symm

theorem invariant_of_tsupport {Φ : Matrix Y Y' k → ℂ} {K : AddSubgroup (Matrix Y Y' k)}
    (h : ∀ u ∈ K, ∀ t ∈ tsupport Φ, Φ (t + u) = Φ t) (u : Matrix Y Y' k) (hu : u ∈ K) (t : Matrix Y Y' k) :
    Φ (t + u) = Φ t := by
  by_cases ht : t ∈ tsupport Φ
  · exact h u hu t ht
  by_cases ht' : t + u ∈ tsupport Φ
  · rw [← h _ (neg_mem hu) _ ht', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport ht, image_eq_zero_of_notMem_tsupport ht']

theorem exists_cosets {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (a : kˣ) :
    ∃ R : Finset (Matrix Y Y' k), ∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ box Y Y' a := by
  obtain ⟨R, -, hR⟩ := hΦ.2.isCompact.elim_nhds_subcover (fun r => {t | t - r ∈ box Y Y' a}) fun r _ =>
    ((isOpen_box a).preimage (continuous_sub_right r)).mem_nhds (by simp)
  exact ⟨R, fun t ht => by simpa using hR (subset_tsupport Φ ht)⟩

theorem sb_le {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {N : Submodule ℂ (Matrix Y Y' k → ℂ)}
    (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hN' : ∀ y, ∀ Φ ∈ N, (fun t => pairing ψ t y * Φ t) ∈ N)
    {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (h0 : Φ ≠ 0) (hΦN : Φ ∈ N) : SB (Matrix Y Y' k) ≤ N := by
  classical
  intro Ψ hΨ
  obtain ⟨a, ha⟩ := exists_box_subset ((eventually_invariant hΦ).and (eventually_invariant hΨ))
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  obtain ⟨R, hR⟩ := exists_cosets hΦ a
  obtain ⟨R', hR'⟩ := exists_cosets hΨ a
  refine mem_of_ind_mem hN (ind_mem (isBichar_pairing ψ) hN'
    (fun u hu => let ⟨y, hy, hne⟩ := exists_sep hd a hu; ⟨y, fun κ hκ => pairing_box hd hκ hy, hne⟩)
    (R.image (· - x)) _ (hN x Φ hΦN) (fun u hu t => ?_) (by rwa [zero_add]) fun t ht => ?_) R' Ψ
    (invariant_of_tsupport fun u hu => (ha u hu).2) hR'
  · rw [add_right_comm]
    exact invariant_of_tsupport (fun u hu => (ha u hu).1) u hu _
  · obtain ⟨r, hr, h⟩ := hR _ ht
    exact Or.inr ⟨_, Finset.mem_image_of_mem _ hr, by convert h using 1; abel⟩

end GlobalTheory.LocMod.Inhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
section
open Polynomial

namespace GlobalTheory.FixedRoots

theorem exists_ringEquiv_add_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] (k : Subfield Ω) (c : Ω)
    (hc : Transcendental k c) :
    ∃ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) ∧ σ c = c + 1 := by
  first
  | exact @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | (apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one ..)

theorem mem_of_forall_ringEquiv_fixed {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (k : Subfield Ω) (c : Ω) (hfix : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → σ c = c) : c ∈ k := by
  by_cases hc : Transcendental k c
  · exfalso
    obtain ⟨σ, hσk, hσc⟩ := exists_ringEquiv_add_one k c hc
    have := hfix σ hσk
    rw [hσc] at this
    simp at this
  · have hcA : IsAlgebraic k c := by simpa [Transcendental] using hc
    have hzA : c ∈ algebraicClosure k Ω := (mem_algebraicClosure_iff).2 hcA
    have : IsGalois k (algebraicClosure k Ω) := inferInstance
    obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (k := k) (K := algebraicClosure k Ω) ⟨c, hzA⟩).2 (by
        intro σ₀
        obtain ⟨σ, hσ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_algEquiv_extending σ₀
        apply Subtype.ext
        rw [← hσ]
        exact hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩))
    have : ((r : k) : Ω) = c := congrArg Subtype.val hr
    rw [← this]
    exact r.2

end GlobalTheory.FixedRoots
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralScaledBoxPiCosetRepsShiftInvariant
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

namespace GlobalTheory.CosetSumShift

theorem sum_shift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)),
    (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) →
    ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) →
    ∀ a ∈ box n R, ∑ b ∈ S, F (a + b) = ∑ b ∈ S, F b := by
  intro k _ _ _ _ n _ r R S hS huniq F hF a ha
  classical
  have hadd : ∀ {s : kˣ} {x y : n → k}, x ∈ box n s → y ∈ box n s → x + y ∈ box n s :=
    fun hx hy i _ => add_mem_cball (hx i trivial) (hy i trivial)
  have hneg : ∀ {s : kˣ} {x : n → k}, x ∈ box n s → -x ∈ box n s :=
    fun hx i _ => neg_mem_cball (hx i trivial)
  have hzero : (0 : n → k) ∈ box n r := fun i _ => by simp [cball]
  have hmem : ∀ b ∈ S, a + b ∈ box n R := fun b hb => hadd ha (hS b hb)
  choose! c hc using fun b (hb : b ∈ S) => (huniq (a + b) (hmem b hb)).exists
  have hF' : ∀ b ∈ S, F (a + b) = F (c b) := by
    intro b hb
    have := hF _ (hc b hb).2 (c b)
    rwa [add_sub_cancel] at this
  have hinj : ∀ x ∈ S, ∀ y ∈ S, c x = c y → x = y := by
    intro x hx y hy h
    have e : x - y = (a + x - c x) + -(a + y - c y) := by rw [h]; abel
    have h1 : x - y ∈ box n r := e ▸ hadd (hc x hx).2 (hneg (hc y hy).2)
    obtain ⟨z, -, huq⟩ := huniq x (hS x hx)
    exact (huq x ⟨hx, by simpa using hzero⟩).trans (huq y ⟨hy, h1⟩).symm
  have himg : S.image c = S := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      exact (hc b hb).1
    · rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)]
  rw [Finset.sum_congr rfl hF', ← Finset.sum_image hinj, himg]

end GlobalTheory.CosetSumShift
end

