module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GlueBasic
section
noncomputable section

open PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped Fin.NatCast Fin.CommRing

namespace UpperTheory.ConvolutionTheory.L1

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
  {ι : R →+* S} {s : S →+* S} {m : ℕ} (D : Split ι s m) (n : ℕ)

private theorem comp_apply (i : Fin (m + 1)) (x : GL (Fin n) S) (a b : Fin n) :
    (D.comp n i x : Matrix (Fin n) (Fin n) R) a b = D.e ((x : Matrix (Fin n) (Fin n) S) a b) i := rfl

private theorem comp_glue (g : Fin (m + 1) → GL (Fin n) R) (i : Fin (m + 1)) :
    D.comp n i (D.glue n g) = g i := by
  apply Units.ext
  ext a b
  rw [comp_apply]
  show D.e (D.e.symm fun i => (g i : Matrix (Fin n) (Fin n) R) a b) i = _
  simp

private theorem glue_comp (x : GL (Fin n) S) : D.glue n (fun i => D.comp n i x) = x := by
  apply Units.ext
  ext a b
  show D.e.symm (fun i => (D.comp n i x : Matrix (Fin n) (Fin n) R) a b) = _
  simp only [comp_apply]
  exact D.e.symm_apply_apply _

private theorem comp_inj {x y : GL (Fin n) S} (h : ∀ i, D.comp n i x = D.comp n i y) : x = y := by
  rw [← glue_comp D n x, ← glue_comp D n y]
  exact congrArg _ (funext h)

private theorem comp_diag (t : GL (Fin n) R) (i : Fin (m + 1)) : D.comp n i (mapGL n ι t) = t := by
  apply Units.ext
  ext a b
  rw [comp_apply]
  exact D.map_diag _ i

private theorem comp_shift (x : GL (Fin n) S) (i : Fin (m + 1)) :
    D.comp n i (mapGL n s x) = D.comp n (i + 1) x := by
  apply Units.ext
  ext a b
  rw [comp_apply, comp_apply]
  exact D.map_shift _ i

private theorem comp_pow (θ : Monoid.End (GL (Fin n) S)) (hθ : ∀ x, θ x = mapGL n s x) (k : ℕ)
    (x : GL (Fin n) S) (i : Fin (m + 1)) :
    D.comp n i ((θ ^ k) x) = D.comp n (i + (k : Fin (m + 1))) x := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    show D.comp n i (θ ((θ ^ k) x)) = _
    rw [hθ, comp_shift, ih]
    congr 1
    push_cast
    abel_nf

private theorem ofFn_range {G : Type} [Monoid G] (k : ℕ) (f : ℕ → G) :
    (List.ofFn fun i : Fin k => f i).prod = ((List.range k).map f).prod := by
  congr 1
  apply List.ext_getElem <;> simp

private theorem comp_twNorm (θ : Monoid.End (GL (Fin n) S)) (hθ : ∀ x, θ x = mapGL n s x)
    (δ : GL (Fin n) S) (j : Fin (m + 1)) :
    D.comp n j (twNorm θ (m + 1) δ) = (List.ofFn fun i => D.comp n (j + i) δ).prod := by
  have hh : (fun i : Fin (m + 1) => D.comp n (j + i) δ) =
      fun i : Fin (m + 1) => (fun k : ℕ => D.comp n (j + (k : Fin (m + 1))) δ) i := by
    funext i
    simp only [Fin.cast_val_eq_self]
  rw [hh, ofFn_range (m + 1) (fun k : ℕ => D.comp n (j + (k : Fin (m + 1))) δ), twNorm, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact comp_pow D n θ hθ k δ j

private theorem entry {T : Type} [CommRing T] [TopologicalSpace T] (a b : Fin n) :
    Continuous fun x : GL (Fin n) T => (x : Matrix (Fin n) (Fin n) T) a b :=
  (Units.continuous_val (M := Matrix (Fin n) (Fin n) T)).matrix_elem a b

private theorem entryInv {T : Type} [CommRing T] [TopologicalSpace T] (a b : Fin n) :
    Continuous fun x : GL (Fin n) T => ((x⁻¹ : GL (Fin n) T) : Matrix (Fin n) (Fin n) T) a b :=
  (Units.continuous_iff.mp (continuous_id (X := GL (Fin n) T))).2.matrix_elem a b

private theorem norm_shift {G : Type} [Group G] (c : Fin (m + 1) → G) (j : Fin (m + 1)) :
    (List.ofFn fun i => c (j + i)).prod * c j = c j * (List.ofFn fun i => c (j + 1 + i)).prod := by
  rw [List.ofFn_succ, List.ofFn_succ' (f := fun i => c (j + 1 + i))]
  simp only [List.prod_cons, List.concat_eq_append, List.prod_append, List.prod_nil, mul_one, List.prod_singleton,
    add_zero, Fin.zero_eta]
  have h1 : ∀ i : Fin m, j + i.succ = j + 1 + i.castSucc := fun i => by
    rw [← Fin.coeSucc_eq_succ]
    abel
  have h2 : j + 1 + Fin.last m = j := by
    rw [add_assoc, add_comm 1, Fin.last_add_one, add_zero]
  simp only [h1, h2, mul_assoc]

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.glueBasic :
    UpperTheory.ConvolutionTheory.L1.GlueBasic := by
  intro R S _ _ _ _ _ _ ι s m D n
  refine ⟨comp_glue D n, glue_comp D n, ?_, ?_, ?_, comp_diag D n, comp_shift D n, ?_⟩
  · intro g h
    apply comp_inj D n
    intro i
    rw [map_mul, comp_glue, comp_glue, comp_glue]
    rfl
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun a b => ?_
      exact D.cont_symm.comp (continuous_pi fun i => (entry n a b).comp (continuous_apply i))
    · refine continuous_matrix fun a b => ?_
      exact D.cont_symm.comp (continuous_pi fun i => (entryInv n a b).comp (continuous_apply i))
  · intro i
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun a b => ?_
      exact (continuous_apply i).comp (D.cont.comp (entry n a b))
    · refine continuous_matrix fun a b => ?_
      have : (fun x : GL (Fin n) S => (((D.comp n i x)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b) =
          fun x => D.e (((x⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) a b) i := by
        funext x
        rw [← map_inv, comp_apply]
      show Continuous (fun x : GL (Fin n) S => (((D.comp n i x)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b)
      rw [this]
      exact (continuous_apply i).comp (D.cont.comp (entryInv n a b))
  · intro δ γ
    constructor
    · intro h
      have N : ∀ j : Fin (m + 1), (List.ofFn fun i => D.comp n (j + i) δ).prod = γ := fun j => by
        rw [← comp_twNorm D n (mapGL n s) (fun _ => rfl), h, comp_diag]
      refine ⟨fun i => ?_, ?_, N⟩
      · have e := norm_shift (fun i => D.comp n i δ) i
        rw [N, N] at e
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact e.symm
      · simpa using N 0
    · rintro ⟨-, -, N⟩
      apply comp_inj D n
      intro j
      rw [comp_twNorm D n (mapGL n s) (fun _ => rfl), N, comp_diag]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatImage
section
private theorem UpperTheory.ConvolutionTheory.L1.simple_of_prime (R : Type) [Ring R] [Nontrivial R] [IsArtinianRing R]
    (h : ∀ I : Ideal R, I.IsTwoSided → ∀ r : R, (∀ x ∈ I, x * r = 0) → I = ⊥ ∨ r = 0) : IsSimpleRing R := by
  have hJ : Ring.jacobson R = ⊥ := by
    by_contra hne
    obtain ⟨n, hn⟩ : IsNilpotent (Ring.jacobson R) := IsSemiprimaryRing.isNilpotent
    have key : ∀ n : ℕ, Ring.jacobson R ^ n ≠ ⊥ := by
      intro n
      induction n with
      | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; exact top_ne_bot
      | succ k ih =>
        intro hk
        apply ih
        rw [eq_bot_iff]
        intro r hr
        rcases h (Ring.jacobson R) inferInstance r (fun x hx => by
          have : x * r ∈ Ring.jacobson R ^ (k + 1) := by
            rw [Ideal.IsTwoSided.pow_succ]
            exact Ideal.mul_mem_mul hx hr
          rw [hk] at this
          exact this) with h1 | h1
        · exact absurd h1 hne
        · exact h1
    exact key n hn
  haveI : IsSemisimpleRing R := IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr hJ
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I.asIdeal
  rcases h I.asIdeal inferInstance (1 - e) (fun x hx => by
    rw [hI, Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [mul_assoc, mul_sub, mul_one, he.eq, sub_self, mul_zero]) with h1 | h1
  · left
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ I.asIdeal := hx
    rw [h1] at this
    exact this
  · right
    have h2 : e ∈ I.asIdeal := by rw [hI]; exact Ideal.subset_span rfl
    rw [← sub_eq_zero.mp h1] at h2
    exact I.one_mem_iff.mp h2

theorem UpperTheory.ConvolutionTheory.L1.matImage :
    UpperTheory.ConvolutionTheory.L1.MatImage := by
  intro A W _ _ _ _ _ _ ρ B hB hirr
  haveI : FiniteDimensional ℂ ρ.range :=
    FiniteDimensional.of_injective ρ.range.val.toLinearMap Subtype.val_injective
  haveI : IsArtinianRing ρ.range := IsArtinianRing.of_finite ℂ _
  haveI : IsSimpleRing ρ.range := by
    refine UpperTheory.ConvolutionTheory.L1.simple_of_prime _ fun I hI r hr => ?_
    let P : Submodule ℂ W :=
      { carrier := {w | ∀ x ∈ I, (x : Module.End ℂ W) w = 0}
        add_mem' := fun {a b} ha hb x hx => by rw [map_add (f := _), ha x hx, hb x hx, add_zero]
        zero_mem' := fun x _ => map_zero _
        smul_mem' := fun c w hw x hx => by rw [map_smul, hw x hx, smul_zero] }
    rcases hirr P (fun a w hw x hx => hw (x * ⟨ρ a, a, rfl⟩) (I.mul_mem_right _ hx))
      (fun b hb w hw x hx => by
        have h0 := hw x hx
        obtain ⟨_, a, rfl⟩ := x
        have h1 : (ρ a * b) w = (b * ρ a) w := by rw [(hB a b hb).eq]
        change ρ a w = 0 at h0
        change ρ a (b w) = 0
        rw [Module.End.mul_apply, Module.End.mul_apply, h0, map_zero] at h1
        exact h1) with h1 | h1
    · right
      ext w
      have : (r : Module.End ℂ W) w ∈ P := fun x hx => by
        have := congrArg (fun y : ρ.range => (y : Module.End ℂ W) w) (hr x hx)
        simpa using this
      rw [h1] at this
      simpa using this
    · left
      rw [eq_bot_iff]
      intro x hx
      have : x = 0 := by
        ext w
        have : w ∈ P := by rw [h1]; trivial
        simpa using this x hx
      exact this
  obtain ⟨n, hn, h⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed ℂ ρ.range
  exact ⟨n, Nat.pos_of_ne_zero hn.out, h⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PushTest
section
open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

private theorem cont_prodFn {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ) :
    Continuous fun y : Fin m → G => (List.ofFn y).prod := by
  simp only [List.ofFn_eq_map]
  exact continuous_list_prod (f := fun i (y : Fin m → G) => y i) _ fun i _ => continuous_apply i

private theorem cont_fib {G : Type} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ) :
    Continuous fun p : G × (Fin m → G) => fib p.2 p.1 := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [fib, Fin.snoc_last]
    exact ((cont_prodFn m).comp continuous_snd).inv.mul continuous_fst
  · simp only [fib, Fin.snoc_castSucc]
    exact (continuous_apply j).comp continuous_snd

private theorem prod_fib {G : Type} [Group G] [MeasurableSpace G] {m : ℕ} (y : Fin m → G) (x : G) :
    (List.ofFn (fib y x)).prod = x := by
  rw [List.ofFn_succ']
  simp [fib]

private theorem integrable_fib {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : ℕ)
    (Φ : (Fin (m + 1) → G) → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    ∃ K : Set (Fin m → G), IsCompact K ∧ (∀ x y, y ∉ K → Φ (fib y x) = 0) ∧
      ∀ x, Integrable (fun y : Fin m → G => Φ (fib y x)) (Measure.pi fun _ => μ) := by
  have hK : IsCompact ((fun g : Fin (m + 1) → G => fun i : Fin m => g i.castSucc) '' tsupport Φ) :=
    hs.isCompact.image (continuous_pi fun i => continuous_apply _)
  have h0 : ∀ x y, y ∉ ((fun g : Fin (m + 1) → G => fun i : Fin m => g i.castSucc) '' tsupport Φ) →
      Φ (fib y x) = 0 := by
    intro x y hy
    by_contra h
    exact hy ⟨fib y x, subset_tsupport _ h, funext fun i => by simp [fib]⟩
  refine ⟨_, hK, h0, fun x => ?_⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK (h0 x))
  exact hc.comp ((cont_fib m).comp (Continuous.prodMk_right x))

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.pushTest :
    UpperTheory.ConvolutionTheory.L1.PushTest := by
  intro G _ _ _ _ _ _ _ _ μ _ m Φ hc hs
  obtain ⟨K, hK, h0, hint⟩ := integrable_fib μ m Φ hc hs
  have hsup : ∀ x, push μ m Φ x ≠ 0 → ∃ g, Φ g ≠ 0 ∧ (List.ofFn g).prod = x := by
    intro x hx
    by_contra h
    apply hx
    have : ∀ y : Fin m → G, Φ (fib y x) = 0 := fun y => by
      by_contra h'
      exact h ⟨_, h', prod_fib y x⟩
    simp [push, this]
  refine ⟨?_, ?_, hsup, hint, ?_, ?_⟩
  · have e : push μ m Φ = fun x => ∫ y in K, Φ (fib y x) ∂(Measure.pi fun _ => μ) := by
      funext x
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero (h0 x)).symm
    rw [e]
    exact continuous_parametric_integral_of_continuous (f := fun x y => Φ (fib y x)) (hc.comp (cont_fib m)) hK
  · refine HasCompactSupport.intro (hs.isCompact.image (cont_prodFn (m + 1))) fun x hx => ?_
    by_contra h
    obtain ⟨g, hg, rfl⟩ := hsup x h
    exact hx ⟨g, subset_tsupport _ hg, rfl⟩
  · intro c
    funext x
    simp [push, integral_const_mul]
  · intro Ψ hc' hs'
    obtain ⟨_, _, _, hint'⟩ := integrable_fib μ m Ψ hc' hs'
    funext x
    simp only [push, Pi.add_apply]
    exact integral_add (hint x) (hint' x)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.QuotAny
section
open MeasureTheory
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.L1

section QuotAnyAux

variable {X T : Type} [Group X] [MeasurableSpace X] [MeasurableMul₂ X] [Group T] [MeasurableSpace T]
  [MeasurableInv T]

private theorem lint_eq {μ : Measure X} [μ.IsMulLeftInvariant] [SFinite μ] {ν : Measure T} [SFinite ν]
    [ν.IsInvInvariant] {i : T →* X} (hi : Measurable i) {F : X → ℝ≥0∞} (hF : Measurable F)
    (hFi : ∀ t x, F (i t * x) = F x) {ρ ρ' : X → ℝ≥0∞} (hρ : Measurable ρ)
    (hρ1 : ∀ x, ∫⁻ t, ρ (i t * x) ∂ν = 1) (hρ' : Measurable ρ')
    (hρ'1 : ∀ x, ∫⁻ t, ρ' (i t * x) ∂ν = 1) :
    ∫⁻ x, F x * ρ x ∂μ = ∫⁻ x, F x * ρ' x ∂μ := by
  have hmul : Measurable fun p : T × X => i p.1 * p.2 := (hi.comp measurable_fst).mul measurable_snd
  have e1 : ∫⁻ x, F x * ρ x ∂μ = ∫⁻ t, ∫⁻ x, F x * ρ x * ρ' (i t * x) ∂μ ∂ν := by
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun x => ?_
      rw [lintegral_const_mul, hρ'1 x, mul_one]
      exact hρ'.comp (hi.mul_const x)
    · exact (((hF.comp measurable_snd).mul (hρ.comp measurable_snd)).mul (hρ'.comp hmul)).aemeasurable
  have e2 : ∀ t : T, ∫⁻ x, F x * ρ x * ρ' (i t * x) ∂μ = ∫⁻ x, F x * ρ' x * ρ (i t⁻¹ * x) ∂μ := by
    intro t
    rw [← lintegral_mul_left_eq_self (fun x => F x * ρ x * ρ' (i t * x)) (i t)⁻¹]
    refine lintegral_congr fun x => ?_
    simp only [mul_inv_cancel_left]
    rw [← map_inv, hFi]
    ring
  rw [e1, lintegral_congr e2, ← lintegral_lintegral_swap]
  · refine lintegral_congr fun x => ?_
    rw [lintegral_const_mul, lintegral_inv_eq_self (fun t : T => ρ (i t * x)), hρ1 x, mul_one]
    · exact hρ.comp ((hi.comp measurable_inv).mul_const x)

  · have hm : Measurable fun p : X × T => i p.2⁻¹ * p.1 :=
      (hi.comp (measurable_snd.inv)).mul measurable_fst
    exact (((hF.comp measurable_fst).mul (hρ'.comp measurable_fst)).mul (hρ.comp hm)).aemeasurable

end QuotAnyAux

section QuotAnyReal

variable {X : Type} [MeasurableSpace X]

private theorem nn_int {μ : Measure X} {g : X → ℝ} (hg : Measurable g) (h0 : ∀ x, 0 ≤ g x)
    {ρ : X → ℝ≥0∞} (hρ : Measurable ρ) (hfin : ∫⁻ x, ‖g x‖ₑ * ρ x ∂μ < ⊤) :
    ∫ x, g x * (ρ x).toReal ∂μ = (∫⁻ x, ‖g x‖ₑ * ρ x ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => mul_nonneg (h0 x) ENNReal.toReal_nonneg)
    (hg.mul hρ.ennreal_toReal).aestronglyMeasurable]
  congr 1
  apply lintegral_congr_ae
  have hae := ae_lt_top (hg.enorm.mul hρ) hfin.ne
  filter_upwards [hae] with x hx
  rw [ENNReal.ofReal_mul (h0 x), ← Real.enorm_of_nonneg (h0 x)]
  by_cases h : ρ x = ⊤
  · have hz : ‖g x‖ₑ = 0 := by
      by_contra hne
      simp only [Pi.mul_apply] at hx
      rw [h, ENNReal.mul_top hne] at hx
      exact lt_irrefl _ hx
    simp [hz]
  · rw [ENNReal.ofReal_toReal h]

private theorem int_of {μ : Measure X} {g : X → ℝ} (hg : Measurable g) {ρ : X → ℝ≥0∞}
    (hρ : Measurable ρ) (hfin : ∫⁻ x, ‖g x‖ₑ * ρ x ∂μ < ⊤) :
    Integrable (fun x => g x * (ρ x).toReal) μ := by
  refine ⟨(hg.mul hρ.ennreal_toReal).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
  rw [enorm_mul, Real.enorm_of_nonneg ENNReal.toReal_nonneg]
  gcongr
  exact ENNReal.ofReal_toReal_le

end QuotAnyReal

section QuotAnyMain

variable {X T : Type} [Group X] [MeasurableSpace X] [MeasurableMul₂ X] [Group T] [MeasurableSpace T]
  [MeasurableInv T]

private theorem real_eq {μ : Measure X} [μ.IsMulLeftInvariant] [SFinite μ] {ν : Measure T} [SFinite ν]
    [ν.IsInvInvariant] {i : T →* X} (hi : Measurable i) {g : X → ℝ} (hg : Measurable g)
    (hgi : ∀ t x, g (i t * x) = g x) {ρ ρ' : X → ℝ≥0∞} (hρ : Measurable ρ)
    (hρ1 : ∀ x, ∫⁻ t, ρ (i t * x) ∂ν = 1) (hρ' : Measurable ρ')
    (hρ'1 : ∀ x, ∫⁻ t, ρ' (i t * x) ∂ν = 1) (hfin : ∫⁻ x, ‖g x‖ₑ * ρ x ∂μ < ⊤) :
    ∫ x, g x * (ρ x).toReal ∂μ = ∫ x, g x * (ρ' x).toReal ∂μ := by
  have hpm : Measurable fun x => max (g x) 0 := hg.max measurable_const
  have hnm : Measurable fun x => max (-g x) 0 := hg.neg.max measurable_const
  have hpi : ∀ t x, max (g (i t * x)) 0 = max (g x) 0 := fun t x => by rw [hgi]
  have hni : ∀ t x, max (-g (i t * x)) 0 = max (-g x) 0 := fun t x => by rw [hgi]
  have hple : ∀ x, ‖max (g x) 0‖ₑ ≤ ‖g x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _))
  have hnle : ∀ x, ‖max (-g x) 0‖ₑ ≤ ‖g x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (neg_le_abs _) (abs_nonneg _))
  have hfin' : ∫⁻ x, ‖g x‖ₑ * ρ' x ∂μ < ⊤ := by
    rw [← lint_eq hi hg.enorm (fun t x => by rw [hgi]) hρ hρ1 hρ' hρ'1]
    exact hfin
  have split : ∀ r : X → ℝ≥0∞, Measurable r → ∫⁻ x, ‖g x‖ₑ * r x ∂μ < ⊤ →
      ∫ x, g x * (r x).toReal ∂μ =
        (∫⁻ x, ‖max (g x) 0‖ₑ * r x ∂μ).toReal - (∫⁻ x, ‖max (-g x) 0‖ₑ * r x ∂μ).toReal := by
    intro r hr hf
    have fp : ∫⁻ x, ‖max (g x) 0‖ₑ * r x ∂μ < ⊤ :=
      lt_of_le_of_lt (lintegral_mono fun x => by gcongr; exact hple x) hf
    have fn : ∫⁻ x, ‖max (-g x) 0‖ₑ * r x ∂μ < ⊤ :=
      lt_of_le_of_lt (lintegral_mono fun x => by gcongr; exact hnle x) hf
    rw [← nn_int hpm (fun x => le_max_right _ _) hr fp, ← nn_int hnm (fun x => le_max_right _ _) hr fn,
      ← integral_sub (int_of hpm hr fp) (int_of hnm hr fn)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show g x * (r x).toReal = max (g x) 0 * (r x).toReal - max (-g x) 0 * (r x).toReal
    rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
  rw [split ρ hρ hfin, split ρ' hρ' hfin',
    lint_eq hi hpm.enorm (fun t x => by rw [hpi]) hρ hρ1 hρ' hρ'1,
    lint_eq hi hnm.enorm (fun t x => by rw [hni]) hρ hρ1 hρ' hρ'1]

private theorem cpx_int {μ : Measure X} {Φ : X → ℂ} (hΦ : Measurable Φ) {ρ : X → ℝ≥0∞}
    (hρ : Measurable ρ) (hfin : ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤) :
    Integrable (fun x => Φ x * ((ρ x).toReal : ℂ)) μ := by
  have h := int_of (μ := μ) (g := fun x => ‖Φ x‖) hΦ.norm hρ (by simpa [enorm_norm] using hfin)
  refine h.mono (hΦ.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simp [abs_of_nonneg ENNReal.toReal_nonneg]

private theorem cpx_eq {μ : Measure X} [μ.IsMulLeftInvariant] [SFinite μ] {ν : Measure T} [SFinite ν]
    [ν.IsInvInvariant] {i : T →* X} (hi : Measurable i) {Φ : X → ℂ} (hΦ : Measurable Φ)
    (hΦi : ∀ t x, Φ (i t * x) = Φ x) {ρ ρ' : X → ℝ≥0∞} (hρ : Measurable ρ)
    (hρ1 : ∀ x, ∫⁻ t, ρ (i t * x) ∂ν = 1) (hρ' : Measurable ρ')
    (hρ'1 : ∀ x, ∫⁻ t, ρ' (i t * x) ∂ν = 1) (hfin : ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤) :
    ∫ x, Φ x * ((ρ x).toReal : ℂ) ∂μ = ∫ x, Φ x * ((ρ' x).toReal : ℂ) ∂μ := by
  have hfin' : ∫⁻ x, ‖Φ x‖ₑ * ρ' x ∂μ < ⊤ := by
    rw [← lint_eq hi hΦ.enorm (fun t x => by rw [hΦi]) hρ hρ1 hρ' hρ'1]
    exact hfin
  have h1 := cpx_int hΦ hρ hfin
  have h2 := cpx_int hΦ hρ' hfin'
  have bre : ∫⁻ x, ‖(Φ x).re‖ₑ * ρ x ∂μ < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun x => by
      gcongr
      exact enorm_le_iff_norm_le.2 (Complex.abs_re_le_norm _)) hfin
  have bim : ∫⁻ x, ‖(Φ x).im‖ₑ * ρ x ∂μ < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun x => by
      gcongr
      exact enorm_le_iff_norm_le.2 (Complex.abs_im_le_norm _)) hfin
  apply Complex.ext
  · have a := Complex.reCLM.integral_comp_comm h1
    have b := Complex.reCLM.integral_comp_comm h2
    simp only [Complex.reCLM_apply, Complex.re_mul_ofReal] at a b
    rw [← a, ← b]
    exact real_eq hi (Complex.measurable_re.comp hΦ) (fun t x => by simp [hΦi]) hρ hρ1 hρ' hρ'1 bre
  · have a := Complex.imCLM.integral_comp_comm h1
    have b := Complex.imCLM.integral_comp_comm h2
    simp only [Complex.imCLM_apply, Complex.im_mul_ofReal] at a b
    rw [← a, ← b]
    exact real_eq hi (Complex.measurable_im.comp hΦ) (fun t x => by simp [hΦi]) hρ hρ1 hρ' hρ'1 bim

end QuotAnyMain

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.quotAny :
    UpperTheory.ConvolutionTheory.L1.QuotAny := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ i hi Φ ρ hΦ hinv hρ hfin
  have hex : ∃ ρ, PositivityTheory.Rg.Tf.Geo.IsNormAlong id i ν ρ := ⟨ρ, hρ⟩
  rw [PositivityTheory.Rg.Tf.Geo.quotInt, dite_eq_left hex]
  have hc := hex.choose_spec
  exact (UpperTheory.ConvolutionTheory.L1.cpx_eq hi hΦ hinv hρ.1 hρ.2 hc.1 hc.2 hfin).symm
end

