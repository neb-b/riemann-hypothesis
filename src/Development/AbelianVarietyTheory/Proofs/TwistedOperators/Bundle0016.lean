module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeExistsPairGroupSmulMemShearedDomain
section
open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

theorem ae_exists_pairGroup_smul_mem_shear : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → ∀ᵐ p ∂((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)), ∃ g : GlobalTheory.UnfoldNormal.pairGroup Γ N hN, g • p ∈ GlobalTheory.UnfoldNormal.shear N '' (𝓝 ×ˢ 𝓕) := by
  intro H _ _ _ _ _ _ _ _ ν _ Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hconj 𝓕 h𝓕
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : SigmaFinite κ := inferInstance
  have hgoodn : ∀ᵐ n : N ∂κ, ∀ v : Γ, ∃ δ : Γ.subgroupOf N,
      δ • (⟨(v : H) * n * (v : H)⁻¹, hN v v.2 n n.2⟩ : N) ∈ 𝓝 := by
    rw [ae_all_iff]
    intro v
    have hc : Continuous (fun n : N => (⟨(v : H) * n * (v : H)⁻¹, hN v v.2 n n.2⟩ : N)) :=
      Continuous.subtype_mk (by fun_prop) _
    have hmp : MeasurePreserving (fun n : N => (⟨(v : H) * n * (v : H)⁻¹, hN v v.2 n n.2⟩ : N)) κ κ :=
      ⟨hc.measurable, hconj v v.2⟩
    exact hmp.quasiMeasurePreserving.ae h𝓝.ae_covers
  have hboth : ∀ᵐ p ∂(κ.prod ν), (∀ v : Γ, ∃ δ : Γ.subgroupOf N,
      δ • (⟨(v : H) * p.1 * (v : H)⁻¹, hN v v.2 p.1 p.1.2⟩ : N) ∈ 𝓝) ∧
      ∃ v : Γ, v • p.2 ∈ 𝓕 :=
    (Measure.quasiMeasurePreserving_fst.ae hgoodn).and
      (Measure.quasiMeasurePreserving_snd.ae h𝓕.ae_covers)
  rw [(measurableEmbedding_shear hNc).ae_map_iff]
  filter_upwards [hboth] with p hp
  obtain ⟨n, h⟩ := p
  obtain ⟨hn, v, hv⟩ := hp
  obtain ⟨δ, hδ⟩ := hn v
  have hδN : ((δ : N) : H) ∈ N := (δ : N).2
  have hδΓ : ((δ : N) : H) ∈ Γ := δ.2
  refine ⟨⟨(((δ : N) : H) * v, (v : H)), Γ.mul_mem hδΓ v.2, v.2, ?_⟩, ?_⟩
  · simpa using hδN
  · refine ⟨(_, v • h), ⟨hδ, hv⟩, ?_⟩
    ext
    · simp [shear, Subgroup.smul_def, Submonoid.smul_def, mul_assoc]
    · simp [shear, Subgroup.smul_def, Submonoid.smul_def]

end GlobalTheory.UnfoldNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AedisjointPairGroupSmulShearedDomain
section
open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

theorem aedisjoint_pairGroup_smul_shear_image : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → Pairwise (AEDisjoint ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)) on fun g : GlobalTheory.UnfoldNormal.pairGroup Γ N hN => g • (GlobalTheory.UnfoldNormal.shear N '' (𝓝 ×ˢ 𝓕))) := by
  intro H _ _ _ _ _ _ _ _ ν _ Γ N _ hNc hN κ 𝓝 _ h𝓝 hconj 𝓕 h𝓕
  have key : ∀ (g : pairGroup Γ N hN) (x : N × H), shear N x ∈ g • (shear N '' (𝓝 ×ˢ 𝓕)) →
      ∃ n ∈ 𝓝, ∃ h ∈ 𝓕, (x.1 : H) * x.2 = g.1.1 * n * h ∧ x.2 = g.1.2 * h := by
    rintro g ⟨a, b⟩ hx
    obtain ⟨_, ⟨⟨n, h⟩, ⟨hn, hh⟩, rfl⟩, he⟩ := Set.mem_smul_set.1 hx
    refine ⟨n, hn, h, hh, ?_⟩
    have := Prod.ext_iff.1 he
    simp only [Subgroup.smul_def, shear, smul_eq_mul, Prod.fst_mul, Prod.snd_mul] at this
    exact ⟨by rw [← this.1, mul_assoc], this.2.symm⟩
  rintro ⟨⟨u, v⟩, hg⟩ ⟨⟨u', v'⟩, hg'⟩ hne
  obtain ⟨hu, hv, huv⟩ := hg
  obtain ⟨hu', hv', huv'⟩ := hg'
  change ((κ.prod ν).map (shear N)) (_ ∩ _) = 0
  rw [(measurableEmbedding_shear hNc).map_apply]
  by_cases hvv : v = v'
  · subst hvv
    have huu : u ≠ u' := by
      rintro rfl
      exact hne rfl
    have memN : ∀ w, w ∈ Γ → w * v⁻¹ ∈ N → v⁻¹ * w ∈ N := by
      intro w _ hw
      have := hN v⁻¹ (Γ.inv_mem hv) (w * v⁻¹) hw
      have e : v⁻¹ * (w * v⁻¹) * v⁻¹⁻¹ = v⁻¹ * w := by group
      rwa [e] at this
    let δ : Γ.subgroupOf N := ⟨⟨v⁻¹ * u, memN u hu huv⟩, Subgroup.mem_subgroupOf.2 (Γ.mul_mem (Γ.inv_mem hv) hu)⟩
    let δ' : Γ.subgroupOf N := ⟨⟨v⁻¹ * u', memN u' hu' huv'⟩, Subgroup.mem_subgroupOf.2 (Γ.mul_mem (Γ.inv_mem hv) hu')⟩
    have hδ : δ ≠ δ' := by
      intro h
      have := congrArg (fun d : Γ.subgroupOf N => ((d : N) : H)) h
      simp only [δ, δ', mul_right_inj] at this
      exact huu this
    have hW : κ (δ • 𝓝 ∩ δ' • 𝓝) = 0 := h𝓝.aedisjoint hδ
    let c : N → N := fun n : N => (⟨v⁻¹ * n * v⁻¹⁻¹, hN v⁻¹ (Γ.inv_mem hv) n n.2⟩ : N)
    have hc : Continuous c :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
    have hcW : κ (c ⁻¹' (δ • 𝓝 ∩ δ' • 𝓝)) = 0 := by
      have h1 := Measure.le_map_apply hc.measurable.aemeasurable (μ := κ) (δ • 𝓝 ∩ δ' • 𝓝)
      have h2 : κ.map c = κ := hconj v⁻¹ (Γ.inv_mem hv)
      rw [h2, hW] at h1
      exact le_antisymm h1 bot_le
    refine measure_mono_null (t := (c ⁻¹' (δ • 𝓝 ∩ δ' • 𝓝)) ×ˢ Set.univ) ?_ ?_
    · rintro ⟨a, b⟩ ⟨h1, h2⟩
      obtain ⟨n, hn, h, hh, e1, e2⟩ := key _ _ h1
      obtain ⟨n', hn', h', hh', e1', e2'⟩ := key _ _ h2
      have av : ∀ (w : H) (m : N) (k : H), (a : H) * b = w * m * k → b = v * k → (a : H) * v = w * m := by
        intro w m k e e'
        rw [e'] at e
        have := congrArg (· * k⁻¹) e
        simpa [mul_assoc] using this
      refine ⟨⟨Set.mem_smul_set.2 ⟨n, hn, ?_⟩, Set.mem_smul_set.2 ⟨n', hn', ?_⟩⟩, Set.mem_univ _⟩
      · apply Subtype.ext
        show v⁻¹ * u * (n : H) = v⁻¹ * a * v⁻¹⁻¹
        rw [inv_inv, mul_assoc v⁻¹ (a : H), av _ _ _ e1 e2, mul_assoc]
      · apply Subtype.ext
        show v⁻¹ * u' * (n' : H) = v⁻¹ * a * v⁻¹⁻¹
        rw [inv_inv, mul_assoc v⁻¹ (a : H), av _ _ _ e1' e2', mul_assoc]
    · rw [Measure.prod_prod, hcW, zero_mul]
  · have hZ : ν ((⟨v, hv⟩ : Γ) • 𝓕 ∩ (⟨v', hv'⟩ : Γ) • 𝓕) = 0 :=
      h𝓕.aedisjoint (fun h => hvv (congrArg Subtype.val h))
    refine measure_mono_null (t := Set.univ ×ˢ ((⟨v, hv⟩ : Γ) • 𝓕 ∩ (⟨v', hv'⟩ : Γ) • 𝓕)) ?_ ?_
    · rintro ⟨a, b⟩ ⟨h1, h2⟩
      obtain ⟨n, hn, h, hh, e1, e2⟩ := key _ _ h1
      obtain ⟨n', hn', h', hh', e1', e2'⟩ := key _ _ h2
      exact ⟨Set.mem_univ _, Set.mem_smul_set.2 ⟨h, hh, by rw [e2]; rfl⟩,
        Set.mem_smul_set.2 ⟨h', hh', by rw [e2']; rfl⟩⟩
    · rw [Measure.prod_prod, hZ, mul_zero]

end GlobalTheory.UnfoldNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMatrixOneParameterGroupEqExp
section
open scoped Matrix
open Filter Topology

namespace GlobalTheory

theorem banach_oneParamGroup_eq_exp {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1)
    (hm : ∀ s t, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t, NormedSpace.exp (t • X) = M t := by
  first
  | exact @_root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq
  | exact _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq
  | (apply _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq ..)

theorem matrix_oneParamGroup_eq_exp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : ℝ → Matrix ι ι ℝ), Continuous M → M 0 = 1 → (∀ s t, M (s + t) = M s * M t) →
    ∃ X : Matrix ι ι ℝ, ∀ t, M t = NormedSpace.exp (t • X) := by
  intro ι _ _ M hc h0 hm
  letI : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  obtain ⟨X, hX⟩ := banach_oneParamGroup_eq_exp M hc h0 hm
  exact ⟨X, fun t => (hX t).symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRightConvolutionBoundedIntegrableStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_right_convolution_bounded_integrable : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (m : Measure H) (α : H → ℂ), Integrable α m → ∀ (φ : G → ℂ), Continuous φ → ∀ B : ℝ, (∀ g, ‖φ g‖ ≤ B) → Continuous (fun x => ∫ h, α h * φ (x * (h : G)) ∂m) := by
  first | exact @GlobalTheory.conv_right_continuous | exact GlobalTheory.conv_right_continuous | (intros; apply GlobalTheory.conv_right_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CountBindWordShuffleByPositions
section
open GlobalTheory

namespace GlobalTheory
namespace ShufflePositions

variable {A : Type} [DecidableEq A]

theorem count_cons_map (a b : A) (x : List A) (s : Multiset (List A)) :
    (s.map (List.cons b)).count (a :: x) = if a = b then s.count x else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    exact Multiset.count_map_eq_count' (List.cons a) s List.cons_injective x
  · rw [if_neg hab, Multiset.count_eq_zero]
    intro hmem
    obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 hmem
    exact hab (List.cons.inj hy).1.symm

omit [DecidableEq A] in
theorem pos_cons {n : ℕ} (w : Fin (n + 1) → A) (p : Fin (n + 1) → Bool) :
    ((List.finRange (n + 1)).filter p).map w =
      (if p 0 then [w 0] else []) ++
        ((List.finRange n).filter fun j => p j.succ).map (fun j => w j.succ) := by
  rw [List.finRange_succ, List.filter_cons, List.filter_map]
  cases h0 : p 0
  · simp [List.map_map, Function.comp_def]
  · simp [List.map_map, Function.comp_def]

private theorem sum_filter_sub_sum_filter_and_not_eq_sum {M : Type} [AddCommMonoid M] (n : ℕ) (f : (Fin (n + 1) → Bool) → M) :
    ∑ ε, f ε = ∑ ε : Fin n → Bool, (f (Fin.cons true ε) + f (Fin.cons false ε)) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  rfl

private theorem count_cons_singleton_cons (c a : A) (x u : List A) :
    ({a :: u} : Multiset (List A)).count (c :: x) =
      if c = a then ({u} : Multiset (List A)).count x else 0 := by
  rw [← Multiset.map_singleton (List.cons a) u]
  exact count_cons_map c a x {u}

private theorem count_cons_singleton_nil (c : A) (x : List A) :
    ({[]} : Multiset (List A)).count (c :: x) = 0 := by
  simp

theorem count_single (n : ℕ) : ∀ (w : Fin n → A) (u v : List A),
    (Shuffle.shuffle u v).count (List.ofFn w) =
      ∑ ε : Fin n → Bool,
        ({u} : Multiset (List A)).count (((List.finRange n).filter fun j => !ε j).map w) *
        ({v} : Multiset (List A)).count (((List.finRange n).filter ε).map w) := by
  induction n with
  | zero =>
    intro w u v
    simp only [List.ofFn_zero, List.finRange_zero, List.filter_nil, List.map_nil,
      Finset.univ_unique, Finset.sum_singleton]
    rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩
    · simp
    · simp
    · simp [Shuffle.shuffle_nil_right]
    · rw [Shuffle.shuffle_cons_cons]
      simp [Multiset.mem_map]
  | succ n ih =>
    intro w u v
    rw [sum_filter_sub_sum_filter_and_not_eq_sum, List.ofFn_succ]
    simp only [pos_cons, Fin.cons_zero, Fin.cons_succ, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, if_true, if_false, List.nil_append, List.singleton_append]
    set w' : Fin n → A := fun j => w j.succ with hw'
    rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩
    · simp
    · have h := ih w' [] v
      rw [Shuffle.shuffle_nil_left] at h
      rw [Shuffle.shuffle_nil_left, count_cons_singleton_cons]
      simp only [count_cons_singleton_cons, count_cons_singleton_nil, zero_mul, add_zero]
      by_cases hc : w 0 = b
      · simp only [if_pos hc, h]
      · simp [if_neg hc]
    · have h := ih w' u []
      rw [Shuffle.shuffle_nil_right] at h
      rw [Shuffle.shuffle_nil_right, count_cons_singleton_cons]
      simp only [count_cons_singleton_cons, count_cons_singleton_nil, mul_zero, zero_add]
      by_cases hc : w 0 = a
      · simp only [if_pos hc, h]
      · simp [if_neg hc]
    · have h1 := ih w' u (b :: v)
      have h2 := ih w' (a :: u) v
      rw [Shuffle.shuffle_cons_cons, Multiset.count_add, count_cons_map, count_cons_map]
      simp only [count_cons_singleton_cons, Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      · by_cases hc : w 0 = b
        · simp only [if_pos hc, h2]
        · simp [if_neg hc]
      · by_cases hc : w 0 = a
        · simp only [if_pos hc, h1]
        · simp [if_neg hc]

private theorem sum_map_count_singleton (X : List A) (s : Multiset (List A)) :
    (s.map fun v => ({v} : Multiset (List A)).count X).sum = s.count X := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons, Multiset.count_singleton,
      add_comm]

theorem count_bind_shuffle (A : Type) [DecidableEq A] (n : ℕ) (w : Fin n → A)
    (s₁ s₂ : Multiset (List A)) :
    (s₁.bind fun u => s₂.bind fun v => Shuffle.shuffle u v).count (List.ofFn w) =
      ∑ ε : Fin n → Bool, s₁.count (((List.finRange n).filter fun j => !ε j).map w) *
        s₂.count (((List.finRange n).filter ε).map w) := by
  simp only [Multiset.count_bind, count_single n w, Multiset.sum_map_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp only [Multiset.sum_map_mul_left, Multiset.sum_map_mul_right, sum_map_count_singleton]

end ShufflePositions
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseSpanTensorOfDenseSubspacesStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_span_tensor_of_dense_subspaces' : ∀ {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (u : (∀ i, H i) → Hs) (W : ∀ i, Submodule ℂ (H i)), (∀ x y, ⟪u x, u y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) → Dense (Submodule.span ℂ (Set.range u) : Set Hs) → (∀ i, Dense (W i : Set (H i))) → Dense (Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i)))) : Set Hs) := by
  first | exact @GlobalTheory.dense_span_tensor_of_dense_subspaces | exact GlobalTheory.dense_span_tensor_of_dense_subspaces | (intros; apply GlobalTheory.dense_span_tensor_of_dense_subspaces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfPureTensorsOfFactorGenerators
section
open scoped TensorProduct

namespace GlobalTheory.TensHead

open scoped TensorProduct in
private lemma piOp_tprod {ι : Type} [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i))
    (y : ∀ j, M j) :
    _root_.GlobalTheory.TensHead.piOp i g (PiTensorProduct.tprod ℂ y) =
      PiTensorProduct.tprod ℂ (Function.update y i (g (y i))) := by
  unfold _root_.GlobalTheory.TensHead.piOp
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

open scoped TensorProduct in
lemma _root_.GlobalTheory.TensHead.piOp_tprod_update {ι : Type} [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i))
    (y : ∀ j, M j) (x : M i) :
    _root_.GlobalTheory.TensHead.piOp i g (PiTensorProduct.tprod ℂ (Function.update y i x)) =
      PiTensorProduct.tprod ℂ (Function.update y i (g x)) := by
  rw [piOp_tprod]
  simp

open scoped TensorProduct in
private lemma apply_tmul_mem_of_stab_left {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀]
    [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    {Op₀ : Set (Module.End ℂ M₀)} {Op : ∀ i, Set (Module.End ℂ (M i))}
    {N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))}
    (hN : _root_.GlobalTheory.TensHead.Stab
      (_root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op)) N)
    {g : Module.End ℂ M₀} (hg : g ∈ Op₀) {a : M₀} {t : ⨂[ℂ] i, M i} (h : a ⊗ₜ[ℂ] t ∈ N) :
    g a ⊗ₜ[ℂ] t ∈ N := by
  have hmem : TensorProduct.map g LinearMap.id ∈
      _root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op) := by
    unfold _root_.GlobalTheory.TensHead.tensOps
    exact Or.inl ⟨g, hg, rfl⟩
  unfold _root_.GlobalTheory.TensHead.Stab at hN
  simpa using hN _ hmem _ h

open scoped TensorProduct in
private lemma tmul_tprod_update_apply_mem_of_stab {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀]
    [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    {Op₀ : Set (Module.End ℂ M₀)} {Op : ∀ i, Set (Module.End ℂ (M i))}
    {N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))}
    (hN : _root_.GlobalTheory.TensHead.Stab
      (_root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op)) N)
    (i : ι) {g : Module.End ℂ (M i)} (hg : g ∈ Op i) {a : M₀} {y : ∀ j, M j} {x : M i}
    (h : a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) :
    a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i (g x)) ∈ N := by
  have hmem : TensorProduct.map LinearMap.id (_root_.GlobalTheory.TensHead.piOp i g) ∈
      _root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op) := by
    unfold _root_.GlobalTheory.TensHead.tensOps _root_.GlobalTheory.TensHead.piOps
    exact Or.inr ⟨_, ⟨i, g, hg, rfl⟩, rfl⟩
  unfold _root_.GlobalTheory.TensHead.Stab at hN
  have := hN _ hmem _ h
  rwa [TensorProduct.map_tmul, LinearMap.id_apply, _root_.GlobalTheory.TensHead.piOp_tprod_update] at this


open scoped TensorProduct in
theorem _root_.GlobalTheory.TensHead.eq_top_of_pure_generators :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (F₀ : Finset M₀) (F : ∀ i, Finset (M i)),
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → _root_.GlobalTheory.TensHead.Stab Op₀ N → (↑F₀ : Set M₀) ⊆ ↑N → N = ⊤) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → _root_.GlobalTheory.TensHead.Stab (Op i) N →
      (↑(F i) : Set (M i)) ⊆ ↑N → N = ⊤) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      _root_.GlobalTheory.TensHead.Stab (_root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op)) N →
      (∀ x₀ ∈ F₀, ∀ y : ∀ i, M i, (∀ i, y i ∈ F i) → x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y ∈ N) →
      N = ⊤ := by
  intro ι _ _ M₀ _ _ M _ _ Op₀ Op Rel₀ Rel F₀ F h₀ hF N hRel₀ hRel hN hgen
  have key : ∀ s : Finset ι, ∀ y : ∀ j, M j, (∀ j, j ∉ s → y j ∈ F j) →
      ∀ a : M₀, a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y hy a
      have hT := h₀ (N.comap ((TensorProduct.mk ℂ M₀ (⨂[ℂ] i, M i)).flip
        (PiTensorProduct.tprod ℂ y))) ?_ ?_ ?_
      · have ha : a ∈ (⊤ : Submodule ℂ M₀) := trivial
        rw [← hT] at ha
        simpa using ha
      · intro x hx
        simpa using hRel₀ x hx _
      · unfold _root_.GlobalTheory.TensHead.Stab
        intro g hg x hx
        simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply] at hx ⊢
        exact apply_tmul_mem_of_stab_left hN hg hx
      · intro x hx
        simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.flip_apply,
          TensorProduct.mk_apply]
        exact hgen x hx y (fun j => hy j (by simp))
    | insert i s hi ih =>
      intro y hy a
      let S : Submodule ℂ (M i) := ⨅ (b : M₀)
        (z : {z : ∀ j, M j // ∀ j, j ∉ s → j ≠ i → z j ∈ F j}),
        N.comap ((TensorProduct.mk ℂ M₀ (⨂[ℂ] j, M j) b) ∘ₗ
          (PiTensorProduct.tprod ℂ).toLinearMap z.1 i)
      have hS : ∀ x, x ∈ S ↔ ∀ (b : M₀) (z : ∀ j, M j), (∀ j, j ∉ s → j ≠ i → z j ∈ F j) →
          b ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update z i x) ∈ N := by
        intro x
        simp only [S, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply,
          MultilinearMap.toLinearMap_apply, TensorProduct.mk_apply, Subtype.forall]
      have hT := hF i S ?_ ?_ ?_
      · have hx : y i ∈ S := by
          rw [hT]
          trivial
        have := (hS _).1 hx a y (fun j hj hji => hy j (by simp [hji, hj]))
        simpa using this
      · intro x hx
        rw [hS]
        intro b z _
        exact hRel i x hx b z
      · unfold _root_.GlobalTheory.TensHead.Stab
        intro g hg x hx
        rw [hS] at hx ⊢
        intro b z hz
        exact tmul_tprod_update_apply_mem_of_stab hN i hg (hx b z hz)
      · intro x hx
        rw [SetLike.mem_coe, hS]
        intro b z hz
        apply ih
        intro j hj
        by_cases hji : j = i
        · subst hji
          simpa using hx
        · rw [Function.update_of_ne hji]
          exact hz j hj hji
  have hall : ∀ v, v ∈ N := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => exact N.zero_mem
    | tmul a t =>
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r y =>
        rw [TensorProduct.tmul_smul]
        exact N.smul_mem r (key Finset.univ y (fun j hj => absurd (Finset.mem_univ j) hj) a)
      | add p q hp hq =>
        rw [TensorProduct.tmul_add]
        exact N.add_mem hp hq
    | add p q hp hq => exact N.add_mem hp hq
  exact eq_top_iff.2 fun v _ => hall v

end GlobalTheory.TensHead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroAtOneOfIteratedDerivsVanishOfGrowthStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_at_one_of_iteratedDerivs_vanish_of_growth : ∀ (φ : ℕ → ℝ → ℂ) (a b : ℝ), (∀ k t, HasDerivAt (φ k) (φ (k + 1) t) t) → (∀ k, φ k 0 = 0) → (∀ k t, ‖φ k t‖ ^ 2 ≤ b * a ^ k * k.factorial) → φ 0 1 = 0 := by
  first | exact @GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth | exact GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth | (intros; apply GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfAeFundamentalDomainOfLeftInvariantStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_ae_zero_on_fundamentalDomain : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ F : G → ℂ, Continuous F → (∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) → (∀ᵐ x ∂(μ.restrict 𝓕), F x = 0) → ∀ x, F x = 0 := by
  first | exact @GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant | exact GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant | (intros; apply GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant <;> assumption)
end

