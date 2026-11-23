module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExtensionRepIndexTwoOfTraceInvariant
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0043
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.EqOneOrEqOfKer
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedHomogeneousComponentMemOfGLSchemeSubmodu

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqWeightsOfTraceEPowerHighestWeightValueEq
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem eq_of_hcVal_eq : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν μ : Fin N → ℕ), Antitone ν → Antitone μ → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → (∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j) → μ = ν := by
  intro p hp k _ _ N ν μ hν hμ hb hval
  have hS : PowerSeries.mk (hcVal k fun i => (μ i : k)) = PowerSeries.mk (hcVal k fun i => (ν i : k)) := by
    ext j
    simp [hval j]
  have gμ := _root_.GlobalTheory.Alc.hcVal_generating k N (fun i => (μ i : k))
  have gν := _root_.GlobalTheory.Alc.hcVal_generating k N (fun i => (ν i : k))
  rw [hS] at gμ
  have cast : ∀ (w : Fin N → ℕ) (i : Fin N),
      shift k (fun i => (w i : k)) i = ((w i + (N - 1 - i.val) : ℕ) : k) := by
    intro w i
    simp [shift]
  simp only [cast] at gμ gν
  refine _root_.GlobalTheory.Alc.eq_of_shifted_residues_eq p N hp ν μ hν hμ hb ?_
  refine _root_.GlobalTheory.Alc.multiset_eq_of_series_eq p hp k N (fun i => ν i + (N - 1 - i.val)) (fun i => μ i + (N - 1 - i.val)) ?_
  rw [← gν, ← gμ]
  ring

end GlobalTheory.Alc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDominantHighestVectorOfLtStable
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc.HighestVec

theorem weight_rowW_apply {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type, rowDeg]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp [rowW]
  · intro b _ hb
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [rowW, Ne.symm hb]
  · simp

def height (N : ℕ) (μ : Fin N → ℕ) : ℕ := ∑ a : Fin N, (N - a.val) * μ a

theorem height_add (N : ℕ) (μ ν : Fin N → ℕ) : height N (μ + ν) = height N μ + height N ν := by
  simp [height, mul_add, Finset.sum_add_distrib]

theorem height_single (N : ℕ) (a : Fin N) : height N (Pi.single a 1) = N - a.val := by
  simp [height, Pi.single_apply]

theorem height_lt_swap (N : ℕ) (μ : Fin N → ℕ) (a b : Fin N) (hab : a < b) (hμ : μ a < μ b) :
    height N μ < height N (μ ∘ Equiv.swap a b) := by
  classical
  unfold height
  have hne : a ≠ b := hab.ne
  rw [← Finset.sum_add_sum_compl {a, b}, ← Finset.sum_add_sum_compl {a, b}
    (fun c => (N - c.val) * (μ ∘ Equiv.swap a b) c)]
  have hrest : ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - c.val) * (μ ∘ Equiv.swap a b) c =
      ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - c.val) * μ c := by
    refine Finset.sum_congr rfl fun c hc => ?_
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    simp [Equiv.swap_apply_of_ne_of_ne hc.1 hc.2]
  rw [hrest, Finset.sum_pair hne, Finset.sum_pair hne]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  apply Nat.add_lt_add_right
  have hlt : N - b.val < N - a.val := by have := b.isLt; have : a.val < b.val := hab; omega
  generalize N - b.val = q at *
  generalize N - a.val = p at *
  nlinarith

theorem isWeightedHomogeneous_rename_rows {k : Type} [Field k] {N : ℕ} (σ : Equiv.Perm (Fin N))
    {v : MvPolynomial (Fin N × Fin N) k} {μ : Fin N → ℕ}
    (hv : IsWeightedHomogeneous (rowW N N) v μ) :
    IsWeightedHomogeneous (rowW N N) (rename (fun x : Fin N × Fin N => (σ x.1, x.2)) v) (μ ∘ σ.symm) := by
  classical
  have hinj : Function.Injective (fun x : Fin N × Fin N => (σ x.1, x.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (σ.injective h.1) h.2
  intro d hd
  have hmem : d ∈ (rename (fun x : Fin N × Fin N => (σ x.1, x.2)) v).support := mem_support_iff.mpr hd
  rw [support_rename_of_injective hinj, Finset.mem_image] at hmem
  obtain ⟨u, hu, rfl⟩ := hmem
  have hw := hv (mem_support_iff.mp hu)
  funext a
  rw [weight_rowW_apply, Function.comp_apply, ← hw, weight_rowW_apply]
  unfold rowDeg
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show ((a, s) : Fin N × Fin N) = (fun x : Fin N × Fin N => (σ x.1, x.2)) (σ.symm a, s) by simp]
  exact Finsupp.mapDomain_apply_of_injective hinj u _

end GlobalTheory.Alc.HighestVec


open GlobalTheory.Alc.HighestVec in
theorem GlobalTheory.Alc.exists_dominant_highest_vector_of_lt : ∀ (k : Type) [Field k] (N : ℕ)
    (M M' : Submodule k (MvPolynomial (Fin N × Fin N) k)), Good M → Good M' → M < M' →
    (∃ c : ℕ, ∀ f ∈ M', ∀ m ∈ f.support, ∑ a, rowDeg m a ≤ c) →
    ∃ (μ : Fin N → ℕ) (v : MvPolynomial (Fin N × Fin N) k), Antitone μ ∧ v ∈ M' ∧ v ∉ M ∧
      IsWeightedHomogeneous (rowW N N) v μ ∧ ∀ a b, a < b → rowE k N N a b v ∈ M := by
  open GlobalTheory.Alc.HighestVec in
  intro k _ N M M' hM hM' hlt hc
  obtain ⟨c, hc⟩ := hc
  classical
  let S : Set ℕ := {h | ∃ (μ : Fin N → ℕ) (v : MvPolynomial (Fin N × Fin N) k), v ∈ M' ∧ v ∉ M ∧
    IsWeightedHomogeneous (rowW N N) v μ ∧ height N μ = h}
  have hne : S.Nonempty := by
    obtain ⟨f, hfM', hfM⟩ := SetLike.exists_of_lt hlt
    by_contra hcon
    apply hfM
    rw [← sum_weightedHomogeneousComponent (rowW N N) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    refine Submodule.sum_mem _ fun μ _ => ?_
    by_contra hμ
    exact hcon ⟨_, μ, _, hM'.2.1 μ f hfM', hμ,
      weightedHomogeneousComponent_isWeightedHomogeneous μ f, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨N * c, ?_⟩
    rintro h ⟨μ, v, hv', hvM, hvh, rfl⟩
    have hv0 : v ≠ 0 := fun h0 => hvM (h0 ▸ M.zero_mem)
    obtain ⟨m, hm⟩ := ne_zero_iff.mp hv0
    have hw := hvh hm
    have hsum := hc v hv' m (mem_support_iff.mpr hm)
    have hμm : ∀ a, μ a = rowDeg m a := fun a => by rw [← hw, weight_rowW_apply]
    calc height N μ = ∑ a, (N - a.val) * μ a := rfl
      _ ≤ ∑ a, N * μ a := Finset.sum_le_sum fun a _ => Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = N * ∑ a, rowDeg m a := by rw [Finset.mul_sum]; simp only [hμm]
      _ ≤ N * c := Nat.mul_le_mul_left _ hsum
  obtain ⟨μ, v, hv', hvM, hvh, hH⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ (μ' : Fin N → ℕ) (v' : MvPolynomial (Fin N × Fin N) k), v' ∈ M' → v' ∉ M →
      IsWeightedHomogeneous (rowW N N) v' μ' → height N μ' ≤ height N μ := by
    intro μ' v' h1 h2 h3
    rw [hH]
    exact le_csSup hbdd ⟨μ', v', h1, h2, h3, rfl⟩
  refine ⟨μ, v, ?_, hv', hvM, hvh, ?_⟩
  · intro a b hab
    rcases hab.lt_or_eq with hab | rfl
    · by_contra hba
      push_neg at hba
      have h1 : rename (fun x : Fin N × Fin N => (Equiv.swap a b x.1, x.2)) v ∈ M' :=
        hM'.2.2 (Equiv.swap a b) v hv'
      have h2 : rename (fun x : Fin N × Fin N => (Equiv.swap a b x.1, x.2)) v ∉ M := by
        intro h
        apply hvM
        have h' := hM.2.2 (Equiv.swap a b) _ h
        rw [rename_rename] at h'
        have hid : ((fun x : Fin N × Fin N => (Equiv.swap a b x.1, x.2)) ∘
            fun x : Fin N × Fin N => (Equiv.swap a b x.1, x.2)) = id := by
          funext x; simp
        rwa [hid, rename_id_apply] at h'
      have h3 := isWeightedHomogeneous_rename_rows (Equiv.swap a b) hvh
      rw [Equiv.symm_swap] at h3
      have h4 := hmax _ _ h1 h2 h3
      have h5 := height_lt_swap N μ a b hab hba
      omega
    · exact le_rfl
  · intro a b hab
    by_contra hnot
    have hne : a ≠ b := hab.ne
    obtain ⟨_, hE⟩ := _root_.GlobalTheory.Alc.rowE_rowWeight k N N μ v hvh
    obtain ⟨hz, hw⟩ := hE a b hne
    by_cases hb : μ b = 0
    · exact hnot (by rw [hz hb]; exact M.zero_mem)
    · let μ' : Fin N → ℕ := μ + Pi.single a 1 - Pi.single b 1
      have hμ' : μ' + Pi.single b 1 = μ + Pi.single a 1 := by
        funext c
        by_cases hca : c = a
        · subst hca; simp [μ', Pi.single_apply, hne]
        · by_cases hcb : c = b
          · subst hcb; simp [μ', Pi.single_apply, hca]; omega
          · simp [μ', Pi.single_apply, hca, hcb]
      have h3 := hw μ' hμ'
      have h1 : rowE k N N a b v ∈ M' := hM'.1 a b v hv'
      have hle := hmax μ' _ h1 hnot h3
      have hh := congrArg (height N) hμ'
      rw [height_add, height_add, height_single, height_single] at hh
      have : N - b.val < N - a.val := by
        have := b.isLt; have : a.val < b.val := hab; omega
      omega
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GlMatrixUnitPowCommutatorAndTraceCentral
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem glRel_pow_comm : ∀ (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A), GlRel E → ∀ k : ℕ, (∀ a b c d, E a b * (E ^ k) c d - (E ^ k) c d * E a b = (if b = c then (E ^ k) a d else 0) - (if d = a then (E ^ k) c b else 0)) ∧ ∀ a b, E a b * (E ^ k).trace = (E ^ k).trace * E a b := by
  first
  | exact @_root_.GlobalTheory.CommutatorPowerEntry.main
  | exact _root_.GlobalTheory.CommutatorPowerEntry.main
  | (apply _root_.GlobalTheory.CommutatorPowerEntry.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommutatorPowerEntry.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommutatorPowerEntry.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommutatorPowerEntry.main ..)

end GlobalTheory.Alc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HybridLargeSieve
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.HybridLargeSieve

theorem sum_integral_le {ι : Type*} (s : Finset ι) (μ : Measure ℝ) (f : ι → ℝ → ℝ) (G : ℝ → ℝ)
    (hm : ∀ i, AEStronglyMeasurable (f i) μ) (h0 : ∀ᵐ x ∂μ, ∀ i, 0 ≤ f i x)
    (hG : Integrable G μ) (h : ∀ᵐ x ∂μ, ∑ i ∈ s, f i x ≤ G x) :
    ∑ i ∈ s, ∫ x, f i x ∂μ ≤ ∫ x, G x ∂μ := by
  have hint : ∀ i ∈ s, Integrable (f i) μ := by
    intro i hi
    refine hG.mono' (hm i) ?_
    filter_upwards [h0, h] with x hx0 hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hx0 i)]
    exact (Finset.single_le_sum (fun j _ => hx0 j) hi).trans hx
  rw [← integral_finsetSum s hint]
  exact integral_mono_ae (integrable_finsetSum s hint) hG h

theorem kernel_eq (n δ x : ℝ) :
    (if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) =
      (Set.Ico (n / Real.exp δ) n).indicator (fun x => 1 / x) x := by
  have he := Real.exp_pos δ
  by_cases hx : x < n ∧ n ≤ x * Real.exp δ
  · have hmem : x ∈ Set.Ico (n / Real.exp δ) n := ⟨(div_le_iff₀ he).2 hx.2, hx.1⟩
    rw [if_pos hx, Set.indicator_of_mem hmem]
  · have hmem : x ∉ Set.Ico (n / Real.exp δ) n := fun hm => hx ⟨hm.2, (div_le_iff₀ he).1 hm.1⟩
    rw [if_neg hx, Set.indicator_of_notMem hmem]

theorem kernel_integral (n δ : ℝ) (hn : 0 < n) (hδ : 0 ≤ δ) :
    IntegrableOn (fun x : ℝ => if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) (Set.Ioi 0) ∧
    ∫ x in Set.Ioi (0 : ℝ), (if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) = δ := by
  have he := Real.exp_pos δ
  have ha : 0 < n / Real.exp δ := div_pos hn he
  have hfun : (fun x : ℝ => if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) =
      (Set.Ico (n / Real.exp δ) n).indicator (fun x => 1 / x) := funext (kernel_eq n δ)
  have hcont : ContinuousOn (fun x : ℝ => 1 / x) (Set.Icc (n / Real.exp δ) n) :=
    continuousOn_const.div continuousOn_id (fun x hx => (ha.trans_le hx.1).ne')
  have hI : IntegrableOn (fun x : ℝ => 1 / x) (Set.Ico (n / Real.exp δ) n) :=
    hcont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  have hsub : Set.Ico (n / Real.exp δ) n ⊆ Set.Ioi 0 := fun x hx => ha.trans_le hx.1
  rw [hfun]
  refine ⟨((integrable_indicator_iff measurableSet_Ico).2 hI).integrableOn, ?_⟩
  rw [setIntegral_indicator measurableSet_Ico, Set.inter_eq_right.2 hsub,
    integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (div_le_self hn.le (Real.one_le_exp hδ)),
    integral_one_div_of_pos ha hn, div_div_cancel₀ hn.ne', Real.log_exp]

theorem window (Q N : ℕ) (a : ℕ → ℂ) (T x : ℝ) (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hx : 0 < x) :
    ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive},
      ‖∑ n ∈ (Finset.Icc 1 N).filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod (q + 1))‖ ^ 2 ≤
    ∑ n ∈ (Finset.Icc 1 N).filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)),
      ((Q : ℝ) ^ 2 + 8 * (2 * n / T + 1)) * ‖a n‖ ^ 2 := by
  set S := (Finset.Icc 1 N).filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)) with hS
  have hT0 : 0 < T := by linarith
  have hu0 : 0 ≤ 1 / T := by positivity
  have hu1 : 1 / T ≤ 1 := by rw [div_le_one hT0]; exact hT
  have hxy : x ≤ x * Real.exp (1 / T) := le_mul_of_one_le_right hx.le (Real.one_le_exp hu0)
  have hML : ⌊x⌋₊ + (⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊) = ⌊x * Real.exp (1 / T)⌋₊ :=
    Nat.add_sub_cancel' (Nat.floor_mono hxy)
  have hsub : S ⊆ Finset.Ioc ⌊x⌋₊ (⌊x⌋₊ + (⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊)) := by
    intro n hn
    have hn' := (Finset.mem_filter.1 hn).2
    rw [Finset.mem_Ioc, hML]
    exact ⟨(Nat.floor_lt hx.le).2 hn'.1, Nat.le_floor hn'.2⟩
  have hL : ((⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) ≤ 2 * x / T + 1 := by
    rw [Nat.cast_sub (Nat.floor_mono hxy)]
    have h1 := Nat.floor_le (hx.le.trans hxy)
    have h2 := Nat.sub_one_lt_floor x
    have h3 : Real.exp (1 / T) - 1 ≤ 2 * (1 / T) := by
      have := Real.abs_exp_sub_one_le (x := 1 / T) (by rw [abs_of_nonneg hu0]; exact hu1)
      rw [abs_of_nonneg hu0] at this
      exact (le_abs_self _).trans this
    have h4 : x * (Real.exp (1 / T) - 1) ≤ x * (2 * (1 / T)) := mul_le_mul_of_nonneg_left h3 hx.le
    have h5 : x * (2 * (1 / T)) = 2 * x / T := by ring
    nlinarith
  let b : ℕ → ℂ := fun n => if n ∈ S then a n else 0
  have key := _root_.GlobalTheory.multiplicative_large_sieve Q ⌊x⌋₊ (⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊) b hQ
  have hinner : ∀ (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)),
      ∑ n ∈ S, a n * χ (n : ZMod (q + 1)) =
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ (⌊x⌋₊ + (⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊)), b n * χ (n : ZMod (q + 1)) := by
    intro q χ
    calc ∑ n ∈ S, a n * χ (n : ZMod (q + 1)) = ∑ n ∈ S, b n * χ (n : ZMod (q + 1)) :=
          Finset.sum_congr rfl (fun n hn => by simp [b, hn])
      _ = _ := Finset.sum_subset hsub (fun n _ hn => by simp [b, hn])
  have hR : ∑ n ∈ Finset.Ioc ⌊x⌋₊ (⌊x⌋₊ + (⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊)), ‖b n‖ ^ 2 =
      ∑ n ∈ S, ‖a n‖ ^ 2 := by
    rw [← Finset.sum_subset hsub (fun n _ hn => by simp [b, hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp [b, hn])
  simp only [hinner]
  refine key.trans ?_
  rw [hR, Finset.mul_sum]
  refine Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right ?_ (by positivity))
  have hxn : x < n := (Finset.mem_filter.1 hn).2.1
  have h2 : 2 * x / T + 1 ≤ 2 * n / T + 1 := by gcongr
  have h3 : 0 ≤ 2 * (n : ℝ) / T + 1 := by positivity
  have h4 := Real.pi_le_four
  have h5 := Real.pi_pos
  have h6 : ((⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) ≤ 2 * n / T + 1 := hL.trans h2
  nlinarith

private theorem sum_finsum_primitive_eq_sum_sigma (Q : ℕ) (g : (q : ℕ) → DirichletCharacter ℂ (q + 1) → ℝ) :
    ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}, g q χ =
      ∑ p ∈ (Finset.range Q).sigma
        (fun q => (Set.toFinite {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}).toFinset),
        g p.1 p.2 := by
  rw [Finset.sum_sigma]
  exact Finset.sum_congr rfl (fun q _ => finsum_mem_eq_finite_toFinset_sum _ _)

private theorem measurable_sum_filter_Icc_window (N : ℕ) (c : ℕ → ℂ) (δ : ℝ) :
    Measurable (fun x : ℝ => ∑ n ∈ (Finset.Icc 1 N).filter
      (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp δ), c n) := by
  have e : (fun x : ℝ => ∑ n ∈ (Finset.Icc 1 N).filter
      (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp δ), c n) =
      fun x : ℝ => ∑ n ∈ Finset.Icc 1 N, if x < n ∧ (n : ℝ) ≤ x * Real.exp δ then c n else 0 := by
    funext x
    rw [Finset.sum_filter]
  rw [e]
  refine Finset.measurable_sum _ (fun n _ => Measurable.ite ?_ measurable_const measurable_const)
  exact (measurableSet_lt measurable_id measurable_const).inter
    (measurableSet_le measurable_const (measurable_id.mul measurable_const))

theorem hybrid_large_sieve : ∃ C : ℝ, 0 < C ∧ ∀ (Q N : ℕ) (a : ℕ → ℂ) (T : ℝ), 1 ≤ Q → 1 ≤ T →
    ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive},
      (∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod (q + 1)) * (n : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hGal⟩ := GlobalTheory.GallagherLemma.gallagher
  refine ⟨16 * C, by positivity, fun Q N a T hQ hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hδ0 : 0 ≤ 1 / T := by positivity
  let W : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) → ℝ → ℂ := fun p x =>
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)),
      a n * p.2 (n : ZMod (p.1 + 1))
  let c : ℕ → ℝ := fun n => ((Q : ℝ) ^ 2 + 8 * (2 * n / T + 1)) * ‖a n‖ ^ 2
  let K : ℕ → ℝ → ℝ := fun n x => if x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T) then 1 / x else 0
  have hKint : ∀ n ∈ Finset.Icc 1 N,
      IntegrableOn (K n) (Set.Ioi 0) ∧ ∫ x in Set.Ioi (0 : ℝ), K n x = 1 / T := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    exact kernel_integral n (1 / T) hn0 hδ0
  have hGint : Integrable (fun x => ∑ n ∈ Finset.Icc 1 N, c n * K n x)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrable_finsetSum _ (fun n hn => (hKint n hn).1.const_mul (c n))
  have hstep1 : ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive},
      (∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod (q + 1)) * (n : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * T ^ 2 * ∑ p ∈ (Finset.range Q).sigma
        (fun q => (Set.toFinite {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}).toFinset),
        ∫ x in Set.Ioi (0 : ℝ), ‖W p x‖ ^ 2 / x := by
    refine (sum_finsum_primitive_eq_sum_sigma Q _).trans_le ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p _ => hGal N (fun n => a n * p.2 (n : ZMod (p.1 + 1))) T hT)
  have hstep2 : ∑ p ∈ (Finset.range Q).sigma
        (fun q => (Set.toFinite {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}).toFinset),
        ∫ x in Set.Ioi (0 : ℝ), ‖W p x‖ ^ 2 / x ≤
      ∫ x in Set.Ioi (0 : ℝ), ∑ n ∈ Finset.Icc 1 N, c n * K n x := by
    refine sum_integral_le _ _ (fun p x => ‖W p x‖ ^ 2 / x) _
      (fun p => (((measurable_sum_filter_Icc_window N (fun n => a n * p.2 (n : ZMod (p.1 + 1))) (1 / T)).norm.pow_const
        2).div measurable_id).aestronglyMeasurable) ?_ hGint ?_
    · exact (ae_restrict_iff' measurableSet_Ioi).2
        (Filter.Eventually.of_forall (fun x hx p => div_nonneg (by positivity) (le_of_lt hx)))
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall (fun x hx => ?_))
      have hx0 : 0 < x := hx
      have e := sum_finsum_primitive_eq_sum_sigma Q (fun q (χ : DirichletCharacter ℂ (q + 1)) =>
        ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)),
          a n * χ (n : ZMod (q + 1))‖ ^ 2)
      have e2 : ∑ p ∈ (Finset.range Q).sigma
          (fun q => (Set.toFinite {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}).toFinset),
          ‖W p x‖ ^ 2 = _ := e.symm
      rw [← Finset.sum_div, e2]
      refine (div_le_div_of_nonneg_right (window Q N a T x hQ hT hx0) hx0.le).trans (le_of_eq ?_)
      rw [Finset.sum_div, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      simp only [c, K]
      split_ifs <;> ring
  have hstep3 : ∫ x in Set.Ioi (0 : ℝ), ∑ n ∈ Finset.Icc 1 N, c n * K n x =
      ∑ n ∈ Finset.Icc 1 N, c n * (1 / T) := by
    rw [integral_finsetSum _ (fun n hn => (hKint n hn).1.const_mul (c n))]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [integral_const_mul, (hKint n hn).2]
  have hstep4 : C * T ^ 2 * ∑ n ∈ Finset.Icc 1 N, c n * (1 / T) ≤
      16 * C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun n _ => ?_)
    have hQ1 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hQ)
    have e : C * T ^ 2 * (c n * (1 / T)) = C * ((T * Q ^ 2 + 16 * n + 8 * T) * ‖a n‖ ^ 2) := by
      simp only [c]
      field_simp
      ring
    rw [e]
    have h1 : T * (Q : ℝ) ^ 2 + 16 * n + 8 * T ≤ 16 * ((Q : ℝ) ^ 2 * T + n) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖a n‖)) hC.le
    linarith
  calc _ ≤ _ := hstep1
    _ ≤ C * T ^ 2 * ∫ x in Set.Ioi (0 : ℝ), ∑ n ∈ Finset.Icc 1 N, c n * K n x :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = C * T ^ 2 * ∑ n ∈ Finset.Icc 1 N, c n * (1 / T) := by rw [hstep3]
    _ ≤ _ := hstep4

end GlobalTheory.HybridLargeSieve
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsSide
section

end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedHomogeneousComponentMemOfGLSchemeSubmoduStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedHomogeneousComponent_mem_of_GLSchemeSubmodule : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) (M : Submodule k (MvPolynomial (Fin N × Fin N) k)), GlobalTheory.Published.IsGLSubmodule k N lam M → ∀ μ : Fin N → ℕ, ∀ f ∈ M, weightedHomogeneousComponent (rowW N N) μ f ∈ M := by
  first | exact @GlobalTheory.Alc.weightedHomogeneousComponent_mem_of_isGLSubmodule | exact GlobalTheory.Alc.weightedHomogeneousComponent_mem_of_isGLSubmodule | (intros; apply GlobalTheory.Alc.weightedHomogeneousComponent_mem_of_isGLSubmodule <;> assumption)
end

