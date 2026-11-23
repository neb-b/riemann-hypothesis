module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnfoldAbs

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HenselCountHolds
section
noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology

section Hensel

variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]

def hlev (Λ0 : AddSubgroup V) (H : AddSubgroup X) (G : V → X) (y : V) (h : X) : Set V :=
  {Z | Z ∈ Λ0 ∧ G (y + Z) - h ∈ H}

theorem hensel_main (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (G : V → X) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (h : X) (hh : h - G y ∈ H 0) (n : ℕ) :
    μ (hlev (Λ 0) (H n) G y h) * ν (H 0) = μ (Λ 0) * ν (H n) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : V → X, ∀ Z, f Z = G (y + Z) - h := ⟨_, fun _ => rfl⟩
  have memS : ∀ m Z, Z ∈ hlev (Λ 0) (H m) G y h ↔ Z ∈ Λ 0 ∧ f Z ∈ H m := by
    intro m Z; rw [hf]; rfl
  have hHa : ∀ m, H (m + 1) ≤ H m := fun m => by
    rw [← hD, ← hD]; exact AddSubgroup.map_mono (hΛa (Nat.le_succ m))
  have hΛ0 : ∀ m, Λ m ≤ Λ 0 := fun m => hΛa (Nat.zero_le m)
  have hDm : ∀ m, ∀ W ∈ Λ m, D W ∈ H m := fun m W hW => by
    rw [← hD]; exact AddSubgroup.mem_map_of_mem D hW

  have hstep : ∀ m, ∀ Z ∈ Λ 0, ∀ W ∈ Λ m, f (Z + W) - f Z - D W ∈ H (m + 1) := by
    intro m Z hZ W hW
    have e := hG m Z hZ W hW
    have : f (Z + W) - f Z - D W = G (y + Z + W) - G (y + Z) - D W := by
      rw [hf, hf, ← add_assoc]; abel
    rw [this]; exact e

  have hinv : ∀ m, ∀ Z ∈ hlev (Λ 0) (H m) G y h, ∀ W ∈ Λ m, Z + W ∈ hlev (Λ 0) (H m) G y h := by
    intro m Z hZ W hW
    rw [memS] at hZ ⊢
    refine ⟨(Λ 0).add_mem hZ.1 (hΛ0 m hW), ?_⟩
    have e := hstep m Z hZ.1 W hW
    have : f (Z + W) = (f (Z + W) - f Z - D W) + f Z + D W := by abel
    rw [this]
    exact (H m).add_mem ((H m).add_mem (hHa m e) hZ.2) (hDm m W hW)
  have hopen : ∀ m, IsOpen (hlev (Λ 0) (H m) G y h) := by
    intro m
    rw [isOpen_iff_forall_mem_open]
    intro Z hZ
    refine ⟨(fun u => -Z + u) ⁻¹' (Λ m : Set V), ?_,
      (hΛo m).preimage (continuous_const.add continuous_id), ?_⟩
    · intro u hu
      have := hinv m Z hZ _ hu
      have e : Z + (-Z + u) = u := by abel
      rw [e] at this; exact this
    · show -Z + Z ∈ Λ m
      rw [neg_add_cancel]; exact (Λ m).zero_mem
  have hsub : ∀ m, hlev (Λ 0) (H (m + 1)) G y h ⊆ hlev (Λ 0) (H m) G y h := by
    intro m Z hZ
    rw [memS] at hZ ⊢
    exact ⟨hZ.1, hHa m hZ.2⟩
  induction n with
  | zero =>
    have hS0 : hlev (Λ 0) (H 0) G y h = (Λ 0 : Set V) := by
      ext Z
      rw [memS]
      refine ⟨And.left, fun hZ => ⟨hZ, ?_⟩⟩
      have e := hstep 0 0 (Λ 0).zero_mem Z hZ
      have h0 : f 0 ∈ H 0 := by
        have : f 0 = -(h - G y) := by rw [hf, add_zero]; abel
        rw [this]; exact (H 0).neg_mem hh
      have : f Z = (f (0 + Z) - f 0 - D Z) + f 0 + D Z := by rw [zero_add]; abel
      rw [this]
      exact (H 0).add_mem ((H 0).add_mem (hHa 0 e) h0) (hDm 0 Z hZ)
    rw [hS0]
  | succ m ih =>

    haveI : DiscreteTopology (X ⧸ H (m + 1)) := QuotientAddGroup.discreteTopology (hHo (m + 1))
    set C : Set (X ⧸ H (m + 1)) := (QuotientAddGroup.mk : X → X ⧸ H (m + 1)) '' (H m : Set X)
      with hC
    have hCf : C.Finite := ((hHc m).image QuotientAddGroup.continuous_mk).finite_of_discrete
    haveI : Fintype C := hCf.fintype
    have hxc : ∀ c : C, ∃ u ∈ H m, (u : X ⧸ H (m + 1)) = c := fun c => c.2
    choose x hxm hxq using hxc
    have htc : ∀ c : C, ∃ W ∈ Λ m, D W = x c := by
      intro c
      have := hxm c
      rw [← hD] at this
      exact AddSubgroup.mem_map.1 this
    choose t htm htD using htc
    have hcov : ∀ u ∈ H m, ∃ c : C, -x c + u ∈ H (m + 1) := by
      intro u hu
      refine ⟨⟨(u : X ⧸ H (m + 1)), u, hu, rfl⟩, ?_⟩
      rw [← QuotientAddGroup.eq, hxq]
    have hinj : ∀ c d : C, -x c + x d ∈ H (m + 1) → c = d := by
      intro c d hcd
      apply Subtype.ext
      rw [← hxq c, ← hxq d]
      exact QuotientAddGroup.eq.2 hcd
    have hne : Nonempty C := ⟨(hcov 0 (H m).zero_mem).choose⟩

    have hAi : ∀ c Z, Z ∈ (fun Z => -t c + Z) ⁻¹' hlev (Λ 0) (H (m + 1)) G y h →
        -x c + f Z ∈ H (m + 1) := by
      intro c Z hZ
      have hZ' := (memS _ _).1 hZ
      have e := hstep m (-t c + Z) hZ'.1 (t c) (htm c)
      have e2 : -t c + Z + t c = Z := by abel
      rw [e2, htD] at e
      have : -x c + f Z = (f Z - f (-t c + Z) - x c) + f (-t c + Z) := by abel
      rw [this]
      exact (H (m + 1)).add_mem e hZ'.2
    have hμ : μ (hlev (Λ 0) (H m) G y h) =
        (Fintype.card C : ENNReal) * μ (hlev (Λ 0) (H (m + 1)) G y h) := by
      have hU : hlev (Λ 0) (H m) G y h =
          ⋃ c : C, (fun Z => -t c + Z) ⁻¹' hlev (Λ 0) (H (m + 1)) G y h := by
        ext Z
        simp only [Set.mem_iUnion, Set.mem_preimage]
        constructor
        · intro hZ
          have hZ' := (memS _ _).1 hZ
          obtain ⟨c, hc⟩ := hcov (f Z) hZ'.2
          refine ⟨c, (memS _ _).2 ⟨(Λ 0).add_mem ((Λ 0).neg_mem (hΛ0 m (htm c))) hZ'.1, ?_⟩⟩
          have e := hstep m (-t c + Z) ((Λ 0).add_mem ((Λ 0).neg_mem (hΛ0 m (htm c))) hZ'.1)
            (t c) (htm c)
          have e2 : -t c + Z + t c = Z := by abel
          rw [e2, htD] at e
          have : f (-t c + Z) = -(f Z - f (-t c + Z) - x c) + (-x c + f Z) := by abel
          rw [this]
          exact (H (m + 1)).add_mem ((H (m + 1)).neg_mem e) hc
        · rintro ⟨c, hc⟩
          have := hinv m _ (hsub m hc) (t c) (htm c)
          have e2 : -t c + Z + t c = Z := by abel
          rwa [e2] at this
      rw [hU, measure_iUnion, tsum_fintype]
      · simp only [measure_preimage_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      · intro c d hcd
        rw [Function.onFun, Set.disjoint_left]
        intro Z hc hd
        apply hcd
        apply hinj
        have a1 := hAi c Z hc
        have a2 := hAi d Z hd
        have : -x c + x d = (-x c + f Z) - (-x d + f Z) := by abel
        rw [this]; exact (H (m + 1)).sub_mem a1 a2
      · intro c
        exact ((hopen (m + 1)).preimage (continuous_const.add continuous_id)).measurableSet
    have hν : ν (H m) = (Fintype.card C : ENNReal) * ν (H (m + 1)) := by
      have hU : (H m : Set X) = ⋃ c : C, (fun u => -x c + u) ⁻¹' (H (m + 1) : Set X) := by
        ext u
        simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · intro hu; exact hcov u hu
        · rintro ⟨c, hc⟩
          have : u = x c + (-x c + u) := by abel
          rw [this]; exact (H m).add_mem (hxm c) (hHa m hc)
      rw [hU, measure_iUnion, tsum_fintype]
      · simp only [measure_preimage_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      · intro c d hcd
        rw [Function.onFun, Set.disjoint_left]
        intro u hc hd
        apply hcd
        apply hinj
        simp only [Set.mem_preimage, SetLike.mem_coe] at hc hd
        have : -x c + x d = (-x c + u) - (-x d + u) := by abel
        rw [this]; exact (H (m + 1)).sub_mem hc hd
      · intro c
        exact ((hHo (m + 1)).preimage (continuous_const.add continuous_id)).measurableSet
    have hc0 : (Fintype.card C : ENNReal) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card C ≠ 0)
    have hct : (Fintype.card C : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    apply (ENNReal.mul_right_inj hc0 hct).1
    calc (Fintype.card C : ENNReal) * (μ (hlev (Λ 0) (H (m + 1)) G y h) * ν (H 0))
        = μ (hlev (Λ 0) (H m) G y h) * ν (H 0) := by rw [hμ, mul_assoc]
      _ = μ (Λ 0) * ν (H m) := ih
      _ = (Fintype.card C : ENNReal) * (μ (Λ 0) * ν (H (m + 1))) := by rw [hν]; ring

end Hensel

theorem henselCount_holds : HenselCount := by
  intro V X _ _ _ _ _ _ _ _ _ _ μ ν _ _ Λ H hΛo _ hΛa hHo hHc D hD G y hG n h hh
  exact hensel_main μ ν Λ H hΛo hΛa hHo hHc D hD G y hG h hh n

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LintFibre
section
noncomputable section

namespace PI.VolStabS

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs2

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y]

theorem lint_fibre {Γ H : Subgroup G} [Countable Γ] (μ' : Measure H) [μ'.IsMulLeftInvariant]
    [μ'.IsInvInvariant] (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0) [Countable (orbS Γ y0)]
    {A : Set G} (hA : MeasurableSet A)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ')
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρi : ∀ γ ∈ Γ, ∀ g, ρ (γ * g) = ρ g) (s : G) :
    ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ' =
      ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' := by
  have : Countable ((Γ ⊓ H).subgroupOf H) := countable_subgroupOf
  have : MeasurableSMul ((Γ ⊓ H).subgroupOf H) H :=
    { measurable_const_smul := fun c => measurable_const_mul (c : H)
      measurable_smul_const := fun x => (measurable_mul_const x).comp measurable_subtype_coe }
  have : SMulInvariantMeasure ((Γ ⊓ H).subgroupOf H) H μ' :=
    ⟨fun c t _ => measure_preimage_mul μ' (c : H) t⟩
  have hg : Measurable fun k : H => s * (k : G)⁻¹ :=
    (measurable_const_mul s).comp (measurable_inv.comp measurable_subtype_coe)
  set F : H → ℝ≥0∞ := fun k =>
    cfun Γ A y0 (s * (k : G)⁻¹) * ρ ((s * (k : G)⁻¹)⁻¹) with hF
  have hFm : Measurable F := by
    rw [hF]
    exact ((meas_cfun Γ y0 hA).comp hg).mul (hρ.comp hg.inv)
  have hinv : ∫⁻ k, F k⁻¹ ∂μ' = ∫⁻ k, F k ∂μ' := by
    exact (Measure.measurePreserving_inv μ').lintegral_comp hFm
  have h1 : ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ' =
      ∫⁻ k, F k ∂μ' := by
    rw [← hinv]
    refine lintegral_congr fun k => ?_
    simp only [hF, InvMemClass.coe_inv, inv_inv]
  have hmem : ∀ δ : (Γ ⊓ H).subgroupOf H, ((δ : H) : G) ∈ Γ := fun δ =>
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 δ.2)).1
  have hcoe : ∀ (δ : (Γ ⊓ H).subgroupOf H) (k : H),
      ((δ • k : H) : G) = ((δ : H) : G) * (k : G) := fun _ _ => rfl
  have hpt : ∀ k : H, ∑' δ : (Γ ⊓ H).subgroupOf H, F (δ • k) =
      cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) := by
    intro k
    have hδ : ∀ δ : (Γ ⊓ H).subgroupOf H, F (δ • k) =
        (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
          (repO Γ y0 x * (((δ : H) : G) * ((k : G) * s⁻¹)))) * ρ ((k : G) * s⁻¹) := by
      intro δ
      rw [← hρi _ (hmem δ) ((k : G) * s⁻¹)]
      simp only [hF, hcoe, cfun, mul_inv_rev, inv_inv, mul_assoc]
    have hrep := sum_rep_eq (Γ := Γ) y0 hH
      (fun g => A.indicator (fun _ => (1 : ℝ≥0∞)) (g * ((k : G) * s⁻¹)))
    simp only [mul_assoc] at hrep
    rw [tsum_congr hδ, ENNReal.tsum_mul_right, ENNReal.tsum_comm, hrep, cntN]
  calc ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ'
      = ∫⁻ k, F k ∂μ' := h1
    _ = ∑' δ : (Γ ⊓ H).subgroupOf H, ∫⁻ k in 𝓕', F (δ • k) ∂μ' :=
      h𝓕'.lintegral_eq_tsum'' F
    _ = ∫⁻ k in 𝓕', ∑' δ : (Γ ⊓ H).subgroupOf H, F (δ • k) ∂μ' :=
      (lintegral_tsum fun δ => (hFm.comp (measurable_const_smul δ)).aemeasurable).symm
    _ = ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' :=
      lintegral_congr hpt

end Abs2

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensChLift
section
noncomputable section

open NumberField Complex

namespace PI.VolStabS

namespace ChLiftW

theorem int_valued_zero {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y] (ψ : Y → ℝ)
    (hψ : Continuous ψ) (hint : ∀ p, ∃ n : ℤ, ψ p = n) (a : Y) (ha : ψ a = 0) (p : Y) :
    ψ p = 0 := by
  obtain ⟨n, hn⟩ := hint p
  have key : ∀ t : ℝ, t ∈ Set.uIcc (0 : ℝ) (n : ℝ) → ∃ m : ℤ, t = m := by
    intro t ht
    rcases le_total (0 : ℝ) n with h | h
    · rw [Set.uIcc_of_le h] at ht
      obtain ⟨q, hq⟩ := intermediate_value_univ a p hψ (by rw [ha, hn]; exact ht)
      obtain ⟨m, hm⟩ := hint q
      exact ⟨m, by rw [← hq, hm]⟩
    · rw [Set.uIcc_of_ge h] at ht
      obtain ⟨q, hq⟩ := intermediate_value_univ p a hψ (by rw [ha, hn]; exact ht)
      obtain ⟨m, hm⟩ := hint q
      exact ⟨m, by rw [← hq, hm]⟩
  rw [hn]
  by_contra hne
  have hn0 : n ≠ 0 := fun h => hne (by simp [h])
  rcases lt_or_gt_of_ne hn0 with h | h
  · have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    obtain ⟨m, hm⟩ := key (-1 / 2) (by
      rw [Set.uIcc_of_ge (by linarith)]
      constructor <;> linarith)
    have h2 : ((2 * m : ℤ) : ℝ) = -1 := by push_cast; linarith
    have h3 : 2 * m = -1 := by exact_mod_cast h2
    omega
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    obtain ⟨m, hm⟩ := key (1 / 2) (by
      rw [Set.uIcc_of_le (by linarith)]
      constructor <;> linarith)
    have h2 : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h3 : 2 * m = 1 := by exact_mod_cast h2
    omega

theorem lift_normed {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (χ : W → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : W →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hne : ∀ x, χ x ≠ 0 := fun x h => by
    have := hadd x (-x)
    rw [add_neg_cancel, h0, h, zero_mul] at this
    exact one_ne_zero this
  let f : C(W, {z : ℂ // z ≠ 0}) := ⟨fun x => ⟨χ x, hne x⟩, hc.subtype_mk _⟩
  obtain ⟨g, ⟨hg0, hgl⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (by ext; simp [f, h0])
  have hge : ∀ x, exp (g x) = χ x := fun x => congrArg Subtype.val (congrFun hgl x)
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  let D : W × W → ℂ := fun p => g (p.1 + p.2) - g p.1 - g p.2
  have hDc : Continuous D := by
    have := g.continuous
    fun_prop
  have hDint : ∀ p, ∃ n : ℤ, D p = n * (2 * Real.pi * I) := fun p => by
    rw [← Complex.exp_eq_one_iff]
    simp only [D, Complex.exp_sub, hge, hadd]
    field_simp [hne p.1, hne p.2]
  let ψ : W × W → ℝ := fun p => (D p / (2 * Real.pi * I)).re
  have hψint : ∀ p, ∃ n : ℤ, ψ p = n := fun p => by
    obtain ⟨n, hn⟩ := hDint p
    refine ⟨n, ?_⟩
    simp only [ψ, hn, mul_div_assoc, div_self h2, mul_one]
    simp
  have hψ : ∀ p, D p = ψ p * (2 * Real.pi * I) := fun p => by
    obtain ⟨n, hn⟩ := hDint p
    have : ψ p = n := by simp only [ψ, hn, mul_div_assoc, div_self h2, mul_one]; simp
    rw [this, hn]; push_cast; ring
  have hψc : Continuous ψ := by
    simp only [ψ]
    fun_prop
  have hψ0 : ψ (0, 0) = 0 := by simp [ψ, D, hg0]
  have hD0 : ∀ p, D p = 0 := fun p => by
    rw [hψ p, int_valued_zero ψ hψc hψint (0, 0) hψ0 p]; simp
  refine ⟨{ toFun := g, map_zero' := hg0, map_add' := fun x y => ?_ }, g.continuous,
    fun x => (hge x).symm⟩
  have := hD0 (x, y)
  simp only [D] at this
  linear_combination this

theorem lift_homeo {X W : Type*} [AddCommGroup X] [TopologicalSpace X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (e : X ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (χ : X → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : X →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hes : ∀ a b, e.symm (a + b) = e.symm a + e.symm b := fun a b => by
    apply e.injective
    rw [he]; simp
  have he0 : e.symm 0 = 0 := by
    have := hes 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  obtain ⟨ℓ', hℓc, hℓ⟩ := lift_normed (χ ∘ e.symm) (hc.comp e.symm.continuous)
    (fun a b => by simp only [Function.comp, hes, hadd]) (by simp [he0, h0])
  refine ⟨ℓ'.comp (AddMonoidHom.mk' e he), hℓc.comp e.continuous, fun x => ?_⟩
  have := hℓ (e x)
  simpa using this

theorem lift_place {F : Type} [Field F] (v : InfinitePlace F) (χ : v.Completion → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  by_cases hv : v.IsReal
  · exact lift_homeo (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph
      (fun x y => (InfinitePlace.Completion.ringEquivRealOfIsReal hv).map_add x y) χ hc hadd h0
  · have hv' : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hv
    exact lift_homeo (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').toHomeomorph
      (fun x y => (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv').map_add x y) χ hc hadd h0

theorem addChar_sum {ι A : Type*} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end ChLiftW


open Classical in
def sgl {F : Type} [Field F] (v : InfinitePlace F) (t : v.Completion) : InfiniteAdeleRing F :=
  Pi.single v t

open Classical in
theorem sgl_add {F : Type} [Field F] (v : InfinitePlace F) (x y : v.Completion) :
    sgl v (x + y) = sgl v x + sgl v y :=
  Pi.single_add v x y

open Classical in
theorem sgl_zero {F : Type} [Field F] (v : InfinitePlace F) : sgl v (0 : v.Completion) = 0 :=
  Pi.single_zero v

open Classical in
theorem continuous_sgl {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) :=
  continuous_single (A := fun w : InfinitePlace F => w.Completion) v

open Classical in
theorem sum_sgl {F : Type} [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    ∑ v, sgl v (x v) = x :=
  Finset.univ_sum_single (M := fun w : InfinitePlace F => w.Completion) x

open ChLiftW in
theorem chLift_holds : ChLift := by
  intro F _ _ χ hχ
  have hloc : ∀ v : InfinitePlace F, ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧
      ∀ t, χ (sgl v t) = exp (ℓ t) := fun v =>
    lift_place v (fun t => χ (sgl v t)) (hχ.comp (continuous_sgl v))
      (fun x y => by simp only [sgl_add, AddChar.map_add_eq_mul])
      (by simp only [sgl_zero, AddChar.map_zero_eq_one])
  choose ℓv hℓc hℓ using hloc
  let ℓ : InfiniteAdeleRing F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ v, ℓv v (x v)) (fun a b => by
    show ∑ v, ℓv v (a v + b v) = _
    simp [map_add (f := _), Finset.sum_add_distrib])
  refine ⟨ℓ, ?_, fun x => ?_⟩
  · show Continuous (fun x : InfiniteAdeleRing F => ∑ v, ℓv v (x v))
    exact continuous_finsetSum _ fun v _ => (hℓc v).comp (continuous_apply v)
  · conv_lhs => rw [← sum_sgl x]
    rw [addChar_sum]
    show _ = exp (∑ v, ℓv v (x v))
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun v _ => hℓ v (x v)

end PI.VolStabS
end
end

