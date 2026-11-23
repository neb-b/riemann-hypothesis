module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmOfGramEqSmul
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_clm_of_gram_eq_smul {α Hs E : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : α → Hs) (f : α → E)
    (K : ℝ) (hK : ∀ a b, ⟪f a, f b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range u) : Set Hs)) :
    ∃ A : Hs →L[ℂ] E, ∀ a, A (u a) = f a := by
  classical
  let Φ : (α →₀ ℂ) →ₗ[ℂ] Hs := Finsupp.linearCombination ℂ u
  let Ψ : (α →₀ ℂ) →ₗ[ℂ] E := Finsupp.linearCombination ℂ f
  have hinner : ∀ z w : α →₀ ℂ, ⟪Ψ z, Ψ w⟫_ℂ = (K : ℂ) * ⟪Φ z, Φ w⟫_ℂ := by
    intro z w
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => simp only [map_add (f := _), inner_add_left, h₁, h₂]; ring
    | single a c =>
      induction w using Finsupp.induction_linear with
      | zero => simp
      | add w₁ w₂ h₁ h₂ => simp only [map_add (f := _), inner_add_right, h₁, h₂]; ring
      | single b d =>
        simp only [Φ, Ψ, Finsupp.linearCombination_single, inner_smul_left, inner_smul_right, hK]
        ring
  have hnorm : ∀ z, ‖Ψ z‖ ^ 2 = K * ‖Φ z‖ ^ 2 := by
    intro z
    have h := hinner z z
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    apply Complex.ofReal_injective
    push_cast
    simpa using h
  have hbound : ∀ z, ‖Ψ z‖ ≤ Real.sqrt (max K 0) * ‖Φ z‖ := by
    intro z
    have hs : Real.sqrt (max K 0) ^ 2 = max K 0 := Real.sq_sqrt (le_max_right _ _)
    have h0 : 0 ≤ Real.sqrt (max K 0) := Real.sqrt_nonneg _
    have h1 : ‖Ψ z‖ ^ 2 ≤ (Real.sqrt (max K 0) * ‖Φ z‖) ^ 2 := by
      rw [mul_pow, hs, hnorm]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg h0 (norm_nonneg _)) two_ne_zero).1 h1
  have hdense : DenseRange Φ := by
    have hr : Set.range Φ = (Submodule.span ℂ (Set.range u) : Set Hs) := by
      rw [← LinearMap.coe_range]
      exact congrArg _ (Finsupp.range_linearCombination ℂ)
    rw [DenseRange, hr]
    exact hd
  refine ⟨Ψ.extendOfNorm Φ, fun a => ?_⟩
  have h := LinearMap.extendOfNorm_eq hdense ⟨_, hbound⟩ (Finsupp.single a 1)
  simpa [Φ, Ψ, Finsupp.linearCombination_single] using h
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonDenominator
section
namespace GlobalTheory.CommonDenominatorLemma

open NumberField

theorem exists_common_denominator {E : Type} [inst : Field E] [NumberField E] [StarRing E] {N : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) (hL : Submodule.FG L) :
    ∃ (b : NumberField.RingOfIntegers E), b ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∀ x ∈ L, ∀ (i : Fin N), ∃ (u : NumberField.RingOfIntegers E), (↑u : E) = (↑b : E) * x i := by
  obtain ⟨s, rfl⟩ := hL
  choose z hz using fun p : (Fin N → E) × Fin N =>
    IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) (p.1 p.2)
  let b : NumberField.RingOfIntegers E :=
    ∏ p ∈ s ×ˢ (Finset.univ : Finset (Fin N)), ((z p).2 : NumberField.RingOfIntegers E)
  refine ⟨b, Finset.prod_ne_zero_iff.mpr fun p _ => nonZeroDivisors.ne_zero (z p).2.2, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    intro i
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun p => ((z p).2 : NumberField.RingOfIntegers E))
      (show (g, i) ∈ s ×ˢ (Finset.univ : Finset (Fin N)) from
        Finset.mem_product.mpr ⟨hg, Finset.mem_univ i⟩)
    refine ⟨e * (z (g, i)).1, ?_⟩
    have h := hz (g, i)
    simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap] at h
    rw [show b = ((z (g, i)).2 : NumberField.RingOfIntegers E) * e from he]
    push_cast
    linear_combination (-(e : E)) * h
  | zero =>
    intro i
    exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨c1, h1⟩ := hx i
    obtain ⟨c2, h2⟩ := hy i
    refine ⟨c1 + c2, ?_⟩
    rw [Pi.add_apply, mul_add, ← h1, ← h2]
    push_cast
    ring
  | smul t x _ hx =>
    intro i
    obtain ⟨c1, h1⟩ := hx i
    refine ⟨t * c1, ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← NumberField.RingOfIntegers.coe_eq_algebraMap]
    push_cast
    linear_combination (t : E) * h1

end GlobalTheory.CommonDenominatorLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualFrameSpanUnitaryRepresentation
section
open Module

namespace GlobalTheory.DualFrameSpan

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

lemma sum_comp' {ι : Type} (s : Finset ι) (f : ι → (H →ₗ[ℂ] H)) (g : H →ₗ[ℂ] H) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by
  ext x; simp [LinearMap.sum_apply]

lemma comp_sum' {ι : Type} (s : Finset ι) (f : ι → (H →ₗ[ℂ] H)) (g : H →ₗ[ℂ] H) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  ext x; simp [LinearMap.sum_apply]

lemma eq_zero_of_trace_adjoint_comp_self (B : H →ₗ[ℂ] H)
    (h : LinearMap.trace ℂ H (LinearMap.adjoint B ∘ₗ B) = 0) : B = 0 := by
  set b := stdOrthonormalBasis ℂ H
  rw [LinearMap.trace_eq_sum_inner _ b] at h
  have h' : ∀ i, (inner ℂ (b i) ((LinearMap.adjoint B ∘ₗ B) (b i)) : ℂ)
      = ((‖B (b i)‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast; first | rfl | simp | norm_cast
  simp_rw [h'] at h
  have h2 : (∑ i, ‖B (b i)‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h2
  apply b.toBasis.ext
  intro i
  have := h3 i (Finset.mem_univ _)
  simpa using this

noncomputable def pairing (W : Submodule ℂ (H →ₗ[ℂ] H)) : LinearMap.BilinForm ℂ W :=
  LinearMap.mk₂ ℂ (fun X Y : W => LinearMap.trace ℂ H ((X : H →ₗ[ℂ] H) ∘ₗ (Y : H →ₗ[ℂ] H)))
    (fun x y z => by simp [LinearMap.add_comp]) (fun c x y => by simp [LinearMap.smul_comp])
    (fun x y z => by simp [LinearMap.comp_add]) (fun c x y => by simp [LinearMap.comp_smul])

lemma pairing_apply (W : Submodule ℂ (H →ₗ[ℂ] H)) (X Y : W) :
    pairing W X Y = LinearMap.trace ℂ H ((X : H →ₗ[ℂ] H) ∘ₗ (Y : H →ₗ[ℂ] H)) := rfl

lemma pairing_nondegenerate (W : Submodule ℂ (H →ₗ[ℂ] H))
    (hW : ∀ X ∈ W, LinearMap.adjoint X ∈ W) : (pairing W).Nondegenerate := by
  have key : ∀ y : W, (∀ x : W, pairing W x y = 0) → y = 0 := by
    intro y hy
    have := hy ⟨LinearMap.adjoint (y : H →ₗ[ℂ] H), hW _ y.2⟩
    rw [pairing_apply] at this
    exact Subtype.ext (eq_zero_of_trace_adjoint_comp_self _ this)
  refine ⟨fun x hx => key x (fun y => ?_), fun y hy => key y hy⟩
  rw [pairing_apply, LinearMap.trace_comp_comm']
  exact hx y

section span

variable {G : Type} [Mul G] (K : Set G) (ρ : G → (H →ₗ[ℂ] H))

lemma adjoint_mem_span (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g')
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    LinearMap.adjoint X ∈ Submodule.span ℂ (ρ '' K) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨g', hg', he⟩ := hadj g hg
    rw [he]; exact Submodule.subset_span ⟨g', hg', rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

lemma comp_mem_span (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h) {h : G} (hh : h ∈ K)
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    X ∘ₗ ρ h ∈ Submodule.span ℂ (ρ '' K) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [← hρ g hg h hh]; exact Submodule.subset_span ⟨_, hmul g hg h hh, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [LinearMap.add_comp]; exact add_mem hx hy
  | smul a x _ hx => rw [LinearMap.smul_comp]; exact Submodule.smul_mem _ _ hx

end span

theorem dual_frame : ∀ {G H : Type} [Mul G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g'), ∃ (m : ℕ) (k : Fin m → G) (B : Fin m → (H →ₗ[ℂ] H)), (∀ j, k j ∈ K) ∧
      (∀ A : H →ₗ[ℂ] H, ∀ g ∈ K, LinearMap.trace ℂ H (ρ g ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) * LinearMap.trace ℂ H (ρ g ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j) := by
  intro G H _ _ _ _ K ρ hmul hρ hadj
  classical
  obtain ⟨t, hts, hsp, hli⟩ := exists_linearIndependent ℂ (ρ '' K)
  set W := Submodule.span ℂ (ρ '' K) with hWdef
  have hWt : Submodule.span ℂ (Set.range ((↑) : t → (H →ₗ[ℂ] H))) = W := by
    rw [Subtype.range_coe]; exact hsp
  haveI : Finite t := hli.finite
  letI : Fintype t := Fintype.ofFinite t
  let b0 : Basis t ℂ W := (Basis.span hli).map (LinearEquiv.ofEq _ _ hWt)
  let e := Fintype.equivFin t
  let b : Basis (Fin (Fintype.card t)) ℂ W := b0.reindex e
  have hb : ∀ j, ((b j : W) : H →ₗ[ℂ] H) = ((e.symm j : t) : H →ₗ[ℂ] H) := by
    intro j; simp [b, b0, Basis.span_apply]
  have hbK : ∀ j, ∃ g ∈ K, ρ g = (b j : H →ₗ[ℂ] H) := fun j => by
    rw [hb]; exact hts (e.symm j).2
  choose k hkK hk using hbK
  have hnd := pairing_nondegenerate W (fun X hX => adjoint_mem_span K ρ hadj hX)
  let D := (pairing W).dualBasis hnd b
  have expand : ∀ X ∈ W, X = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ X) • (D j : H →ₗ[ℂ] H) := by
    intro X hX
    have h1 := congrArg Subtype.val (D.sum_repr ⟨X, hX⟩)
    rw [Submodule.coe_sum] at h1
    change _ = X at h1
    conv_lhs => rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, LinearMap.BilinForm.dualBasis_repr_apply, pairing_apply, hk,
      LinearMap.trace_comp_comm' (b j : H →ₗ[ℂ] H) X]
  have hdual : ∀ i j, LinearMap.trace ℂ H (ρ (k i) ∘ₗ (D j : H →ₗ[ℂ] H)) = if i = j then 1 else 0 := by
    intro i j
    rw [hk, LinearMap.trace_comp_comm']
    exact LinearMap.BilinForm.apply_dualBasis_left hnd b j i
  refine ⟨Fintype.card t, k, fun j => (D j : H →ₗ[ℂ] H), hkK, ?_, ?_⟩
  · intro A g hg
    set A' := ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) • (D j : H →ₗ[ℂ] H) with hA'
    have hbi : ∀ i, LinearMap.trace ℂ H (ρ (k i) ∘ₗ A') = LinearMap.trace ℂ H (ρ (k i) ∘ₗ A) := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [A', comp_sum', LinearMap.comp_smul, map_sum, map_smul, hdual, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hvan : ∀ C ∈ W, LinearMap.trace ℂ H (C ∘ₗ A') = LinearMap.trace ℂ H (C ∘ₗ A) := by
      intro C hC
      have h1 := congrArg Subtype.val (b.sum_repr ⟨C, hC⟩)
      rw [Submodule.coe_sum] at h1
      change _ = C at h1
      rw [← h1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Submodule.coe_smul, sum_comp', LinearMap.smul_comp, map_sum, map_smul, ← hk, hbi]
    rw [← hvan (ρ g) (Submodule.subset_span ⟨g, hg, rfl⟩)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [A', comp_sum', LinearMap.comp_smul, map_sum, map_smul, smul_eq_mul]
  · intro i h hh
    exact expand _ (comp_mem_span K ρ hmul hρ hh (D i).2)

end GlobalTheory.DualFrameSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualPairIsUnitDetBlocks
section
open scoped Matrix

namespace GlobalTheory

theorem exists_det_add_mul_ne_zero_of_ker_inf {k : Type} [Field k] {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) k)
    (h : ∀ v : Fin n → k, A *ᵥ v = 0 → C *ᵥ v = 0 → v = 0) :
    ∃ X : Matrix (Fin n) (Fin n) k, (A + X * C).det ≠ 0 := by
  classical
  set a := Matrix.toLin' A with ha
  set c := Matrix.toLin' C with hc
  obtain ⟨L', hL'⟩ := Submodule.exists_isCompl (LinearMap.ker c)
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl ((LinearMap.ker c).map a)

  have hkey : ∀ x ∈ LinearMap.ker c, a x = 0 → x = 0 := by
    intro x hx hax
    rw [LinearMap.mem_ker] at hx
    exact h x (by simpa [ha] using hax) (by simpa [hc] using hx)
  have hinj : Function.Injective (a.domRestrict (LinearMap.ker c)) := by
    intro x y hxy
    have hxy' : a ((x : Fin n → k) - y) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr (by simpa using hxy)
    have := hkey _ (Submodule.sub_mem _ x.2 y.2) hxy'
    exact Subtype.ext (sub_eq_zero.mp this)
  have hrank : Module.finrank k L' = Module.finrank k U := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hL'
    have h2 := Submodule.finrank_add_eq_of_isCompl hU
    have h3 : Module.finrank k ((LinearMap.ker c).map a) = Module.finrank k (LinearMap.ker c) := by
      rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
    omega
  let e : L' ≃ₗ[k] U := LinearEquiv.ofFinrankEq L' U hrank
  let g : (Fin n → k) →ₗ[k] (Fin n → k) :=
    LinearMap.ofIsCompl hL' (a.domRestrict (LinearMap.ker c)) (U.subtype ∘ₗ e.toLinearMap)
  have hgL : ∀ x (hx : x ∈ LinearMap.ker c), g x = a x := fun x hx =>
    LinearMap.ofIsCompl_apply_left hL' ⟨x, hx⟩
  have hgL' : ∀ y (hy : y ∈ L'), g y = (e ⟨y, hy⟩ : Fin n → k) := fun y hy =>
    LinearMap.ofIsCompl_apply_right hL' ⟨y, hy⟩

  have hg_inj : ∀ v, g v = 0 → v = 0 := by
    intro v hv
    have hvmem : v ∈ LinearMap.ker c ⊔ L' := by rw [hL'.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hvmem
    rw [map_add (f := _), hgL x hx, hgL' y hy] at hv
    have hax : a x ∈ (LinearMap.ker c).map a ⊓ U := by
      refine ⟨Submodule.mem_map_of_mem hx, ?_⟩
      rw [eq_neg_of_add_eq_zero_left hv]
      exact U.neg_mem (e ⟨y, hy⟩).2
    rw [hU.inf_eq_bot, Submodule.mem_bot] at hax
    have hx0 := hkey x hx hax
    rw [hax, zero_add] at hv
    have hy0 : e ⟨y, hy⟩ = 0 := Subtype.ext hv
    rw [LinearEquiv.map_eq_zero_iff] at hy0
    rw [hx0, zero_add]
    exact congrArg Subtype.val hy0

  have hle : LinearMap.ker c ≤ LinearMap.ker (g - a) := fun x hx => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hgL x hx, sub_self]
  let f0 : LinearMap.range c →ₗ[k] (Fin n → k) :=
    ((LinearMap.ker c).liftQ (g - a) hle) ∘ₗ (c.quotKerEquivRange.symm.toLinearMap)
  obtain ⟨Y, hY⟩ := LinearMap.exists_extend f0
  have hfac : ∀ v, Y (c v) = g v - a v := by
    intro v
    have h0 := LinearMap.congr_fun hY ⟨c v, LinearMap.mem_range_self c v⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h0
    rw [h0]
    simp only [f0, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.sub_apply]
  refine ⟨LinearMap.toMatrix' Y, fun hdet => ?_⟩
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  apply hg_inj
  have hmv : (A + LinearMap.toMatrix' Y * C) *ᵥ v = g v := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    have hcv : C *ᵥ v = c v := by rw [hc, Matrix.toLin'_apply]
    have hav : A *ᵥ v = a v := by rw [ha, Matrix.toLin'_apply]
    rw [hcv, hfac, hav]
    abel
  rw [← hmv, hv]

theorem exists_isUnit_det_toBlocks_add_mul {R : Type} [CommRing R] [IsLocalRing R] {n : ℕ}
    (H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (hH : IsUnit H.det) :
    ∃ X : Matrix (Fin n) (Fin n) R, IsUnit (H.toBlocks₁₁ + X * H.toBlocks₂₁).det := by
  classical
  set Hb := H.map (IsLocalRing.residue R) with hHb_def
  have hHb : Hb.det ≠ 0 := by
    rw [hHb_def, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hH.map (IsLocalRing.residue R)).ne_zero
  obtain ⟨Xb, hXb⟩ := exists_det_add_mul_ne_zero_of_ker_inf Hb.toBlocks₁₁ Hb.toBlocks₂₁ (by
    intro v h1 h2
    by_contra hv
    apply hHb
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Sum.elim v 0, ?_, ?_⟩
    · intro h0
      apply hv
      funext i
      simpa using congrFun h0 (Sum.inl i)
    · funext i
      cases i with
      | inl i =>
        simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁] using congrFun h1 i
      | inr i =>
        simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁] using congrFun h2 i)
  choose X hX using fun i j => IsLocalRing.residue_surjective (R := R) (Xb i j)
  refine ⟨Matrix.of X, ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hm : (IsLocalRing.residue R).mapMatrix (H.toBlocks₁₁ + Matrix.of X * H.toBlocks₂₁) =
      Hb.toBlocks₁₁ + Xb * Hb.toBlocks₂₁ := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [RingHom.mapMatrix_apply, Matrix.mul_apply, map_sum, hX, hHb_def, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁]
  rw [hm]
  exact hXb

theorem isUnit_det_of_dual_blocks {R : Type} [CommRing R] {n : ℕ}
    (S A B C D A' C' : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det)
    (h1 : Aᵀ * (S * C') + Cᵀ * (S * A') = 0)
    (h2 : IsUnit (Bᵀ * (S * C') + Dᵀ * (S * A')).det) : IsUnit A'.det := by
  have hAt : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
  have hSC : S * C' = -(Aᵀ⁻¹ * (Cᵀ * (S * A'))) := by
    have h1' : Aᵀ * (S * C') = -(Cᵀ * (S * A')) := eq_neg_of_add_eq_zero_left h1
    calc S * C' = Aᵀ⁻¹ * (Aᵀ * (S * C')) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAt, Matrix.one_mul]
      _ = -(Aᵀ⁻¹ * (Cᵀ * (S * A'))) := by rw [h1', Matrix.mul_neg]
  have key : Bᵀ * (S * C') + Dᵀ * (S * A') = (Dᵀ - Bᵀ * Aᵀ⁻¹ * Cᵀ) * (S * A') := by
    rw [hSC]
    generalize Aᵀ⁻¹ = M
    noncomm_ring
  rw [key, Matrix.det_mul, Matrix.det_mul] at h2
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right h2)

private lemma blocks_conj_eq_fromBlocks_sums {R : Type} [CommRing R] {n : ℕ}
    (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix.fromBlocks 1 1 1 (-1) * G * Matrix.fromBlocks 1 1 1 (-1) =
      Matrix.fromBlocks (G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂)
        (G.toBlocks₁₁ - G.toBlocks₁₂ + G.toBlocks₂₁ - G.toBlocks₂₂)
        (G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂)
        (G.toBlocks₁₁ - G.toBlocks₁₂ - G.toBlocks₂₁ + G.toBlocks₂₂) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks G]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1 <;> noncomm_ring

private lemma H_affine_combination_eq_of_quadratic_relation {R : Type} [CommRing R] {n : ℕ}
    (S a11 a12 a21 a22 b11 b12 b21 b22 X₁ X₂ : Matrix (Fin n) (Fin n) R)
    (E11 : a11ᵀ * S * b11 - a21ᵀ * S * b21 = S) (E12 : a11ᵀ * S * b12 - a21ᵀ * S * b22 = 0)
    (E21 : a12ᵀ * S * b11 - a22ᵀ * S * b21 = 0) (E22 : a12ᵀ * S * b12 - a22ᵀ * S * b22 = -S)
    (hX : X₁ᵀ * S + S * X₂ = 0) :
    (a11 + a12 + a21 + a22 + X₁ * (a11 + a12 - a21 - a22))ᵀ * (S * (b11 + b12 - b21 - b22)) +
        (a11 + a12 - a21 - a22)ᵀ *
          (S * (b11 + b12 + b21 + b22 + X₂ * (b11 + b12 - b21 - b22))) = 0 ∧
      (a11 - a12 + a21 - a22 + X₁ * (a11 - a12 - a21 + a22))ᵀ * (S * (b11 + b12 - b21 - b22)) +
        (a11 - a12 - a21 + a22)ᵀ *
          (S * (b11 + b12 + b21 + b22 + X₂ * (b11 + b12 - b21 - b22))) = S + S + S + S := by
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul]
  constructor
  · calc _ = ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) +
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) + (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) +
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) + (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          (a11ᵀ + a12ᵀ - a21ᵀ - a22ᵀ) * (X₁ᵀ * S + S * X₂) * (b11 + b12 - b21 - b22) := by
          noncomm_ring
      _ = 0 := by rw [E11, E12, E21, E22, hX]; noncomm_ring
  · calc _ = ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) -
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) - (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) -
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) - (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          (a11ᵀ - a12ᵀ - a21ᵀ + a22ᵀ) * (X₁ᵀ * S + S * X₂) * (b11 + b12 - b21 - b22) +
          (S + S + S + S) := by
          noncomm_ring
      _ = S + S + S + S := by rw [E11, E12, E21, E22, hX]; noncomm_ring

theorem exists_dual_pair_isUnit_det_blocks :
    ∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det := by
  intro R _ _ h2 n S hS G₁ G₂ hG₁ hG
  classical
  have hKdet : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R)
      (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R)).det := by
    rw [Matrix.det_fromBlocks_one₁₁]
    have e : (-1 - 1 * 1 : Matrix (Fin n) (Fin n) R) = (-2 : R) • (1 : Matrix (Fin n) (Fin n) R) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply]
      split_ifs <;> ring
    rw [e, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact h2.neg.pow n
  obtain ⟨X₁, hX₁⟩ := exists_isUnit_det_toBlocks_add_mul
    (Matrix.fromBlocks 1 1 1 (-1) * G₁ * Matrix.fromBlocks 1 1 1 (-1))
    (by rw [Matrix.det_mul, Matrix.det_mul]; exact (hKdet.mul hG₁).mul hKdet)
  rw [blocks_conj_eq_fromBlocks_sums, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁] at hX₁
  have hsum : X₁ᵀ * S + S * -(S⁻¹ * X₁ᵀ * S) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS,
      Matrix.one_mul, add_neg_cancel]
  refine ⟨X₁, -(S⁻¹ * X₁ᵀ * S), hsum, hX₁, ?_⟩
  have hG' := hG
  rw [← Matrix.fromBlocks_toBlocks G₁, ← Matrix.fromBlocks_toBlocks G₂, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hG'
  obtain ⟨e11, e12, e21, e22⟩ := Matrix.fromBlocks_inj.mp hG'
  have E11 : G₁.toBlocks₁₁ᵀ * S * G₂.toBlocks₁₁ - G₁.toBlocks₂₁ᵀ * S * G₂.toBlocks₂₁ = S := by
    convert e11 using 1; noncomm_ring
  have E12 : G₁.toBlocks₁₁ᵀ * S * G₂.toBlocks₁₂ - G₁.toBlocks₂₁ᵀ * S * G₂.toBlocks₂₂ = 0 := by
    convert e12 using 1; noncomm_ring
  have E21 : G₁.toBlocks₁₂ᵀ * S * G₂.toBlocks₁₁ - G₁.toBlocks₂₂ᵀ * S * G₂.toBlocks₂₁ = 0 := by
    convert e21 using 1; noncomm_ring
  have E22 : G₁.toBlocks₁₂ᵀ * S * G₂.toBlocks₁₂ - G₁.toBlocks₂₂ᵀ * S * G₂.toBlocks₂₂ = -S := by
    convert e22 using 1; noncomm_ring
  obtain ⟨c1, c2⟩ := H_affine_combination_eq_of_quadratic_relation S _ _ _ _ _ _ _ _ X₁ _ E11 E12 E21 E22 hsum
  have h4 : IsUnit (4 : R) := by
    have := h2.mul h2
    norm_num at this
    exact this
  have hU4 : IsUnit (S + S + S + S).det := by
    have e : S + S + S + S = (4 : R) • S := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [e, Matrix.det_smul]
    exact (h4.pow _).mul hS
  rw [← c2] at hU4
  exact isUnit_det_of_dual_blocks S _ _ _ _ _ _ hX₁ c1 hU4

end GlobalTheory
end

