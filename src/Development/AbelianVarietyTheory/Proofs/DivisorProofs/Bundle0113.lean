module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFourReorder
section
namespace GlobalTheory.FourTermSumReorder

theorem sum_four_reorder {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ b : β, ∑ a : α, ∑ c : α, ∑ e : β, f a b c e := Finset.sum_comm
    _ = ∑ p : β × α, ∑ q : α × β, f p.2 p.1 q.1 q.2 := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ q : α × β, ∑ p : β × α, f p.2 p.1 q.1 q.2 := Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
        simp only [Fintype.sum_prod_type]

end GlobalTheory.FourTermSumReorder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFourSwap
section
namespace GlobalTheory.FourTermSumSwap

theorem sum_four_swap : ∀ {R α β : Type} [inst : AddCommMonoid R] [inst_1 : Fintype α] [inst_2 : Fintype β]
    (f : α → β → α → β → R),
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e := by
  intro R α β _ _ _ f
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ a : α, ∑ c : α, ∑ b : β, ∑ e : β, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ b : β, ∑ e : β, f a b c e := Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ e : β, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

end GlobalTheory.FourTermSumSwap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHadamardPosDefPosSemidef
section
namespace GlobalTheory


open Matrix in
theorem sum_hadamard_posDef_posSemidef :
    ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef →
      0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by
  intro r S G hS hG
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hG
  have key : ∑ i, ∑ j, S i j * (∑ k, vecMulVec (v k) (star (v k))) i j
      = ∑ k, star (v k) ⬝ᵥ (S *ᵥ v k) := by
    simp only [Matrix.sum_apply, Finset.sum_apply, vecMulVec_apply, Pi.star_apply, star_trivial, dotProduct,
      mulVec, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have term : ∀ k, 0 ≤ star (v k) ⬝ᵥ (S *ᵥ v k) := fun k =>
    hS.posSemidef.dotProduct_mulVec_nonneg _
  rw [key]
  refine ⟨Finset.sum_nonneg fun k _ => term k, fun hne => ?_⟩
  have : ∃ k, v k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    simp [h]
  obtain ⟨k, hk⟩ := this
  exact Finset.sum_pos' (fun k _ => term k) ⟨k, Finset.mem_univ _, hS.dotProduct_mulVec_pos hk⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumInnerMulInnerProj
section
noncomputable section

open scoped InnerProductSpace

namespace GlobalTheory.Pc3

section
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (L : Submodule ℂ U)
  [FiniteDimensional ℂ L]

theorem sum_inner_mul_inner_proj [L.HasOrthogonalProjection] (a c : U) :
    ∑ j, ⟪a, (stdOrthonormalBasis ℂ L j : U)⟫_ℂ * ⟪(stdOrthonormalBasis ℂ L j : U), c⟫_ℂ =
      ⟪a, c⟫_ℂ - ⟪a - L.starProjection a, c - L.starProjection c⟫_ℂ := by
  set e := stdOrthonormalBasis ℂ L
  have h1 : ∀ j, ⟪a, (e j : U)⟫_ℂ = ⟪(⟨L.starProjection a, L.starProjection_apply_mem a⟩ : L), e j⟫_ℂ := by
    intro j
    rw [Submodule.coe_inner]
    have := L.inner_starProjection_left_eq_right a (e j : U)
    rw [this, L.starProjection_eq_self_iff.2 (e j).2]
  have h2 : ∀ j, ⟪(e j : U), c⟫_ℂ = ⟪e j, (⟨L.starProjection c, L.starProjection_apply_mem c⟩ : L)⟫_ℂ := by
    intro j
    rw [Submodule.coe_inner]
    have := L.inner_starProjection_left_eq_right (e j : U) c
    rw [← this, L.starProjection_eq_self_iff.2 (e j).2]
  simp_rw [h1, h2]
  rw [e.sum_inner_mul_inner, Submodule.coe_inner]
  simp only
  have ha := L.sub_starProjection_mem_orthogonal a
  have hc := L.sub_starProjection_mem_orthogonal c
  have o1 : ⟪L.starProjection a, c - L.starProjection c⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (L.starProjection_apply_mem a) hc
  have o2 : ⟪a - L.starProjection a, L.starProjection c⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (L.starProjection_apply_mem c) ha
  have e1 : ⟪a, c⟫_ℂ = ⟪L.starProjection a + (a - L.starProjection a),
      L.starProjection c + (c - L.starProjection c)⟫_ℂ := by simp
  rw [e1, inner_add_left, inner_add_right, inner_add_right, o1, o2]
  ring

end

theorem conjDeriv : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (L : Submodule ℂ U) [FiniteDimensional ℂ L] (x y : ℝ → U →L[ℂ] U) (A : U →L[ℂ] U), x 0 = 1 → (∀ t v w, inner ℂ (x t v) (x t w) = inner ℂ v w) → (∀ t v w, inner ℂ v (y t w) = inner ℂ (x t v) w) → (∀ v ∈ L, ∃ w, HasDerivAt (fun t => x t v) w 0) → (∀ u, A u ∈ L) → (∀ u, ContinuousLinearMap.adjoint A u ∈ L) → HasDerivAt (fun t => ∑ j, inner ℂ (stdOrthonormalBasis ℂ L j : U) (x t (A (y t (stdOrthonormalBasis ℂ L j : U))))) 0 0 := by
  intro U _ _ _ L _ x y A hx0 hxi hy hxd hA hAd
  set e := stdOrthonormalBasis ℂ L
  set E : Fin (Module.finrank ℂ L) → U := fun j => (e j : U)
  set b : Fin (Module.finrank ℂ L) → U := fun k => ContinuousLinearMap.adjoint A (E k)

  have hexp : ∀ u, A u = ∑ k, ⟪E k, A u⟫_ℂ • E k := by
    intro u
    have := e.sum_repr' (⟨A u, hA u⟩ : L)
    have h := congrArg (fun z : L => (z : U)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    exact h.symm
  have hterm : ∀ t, (∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) =
      ∑ k, (⟪x t (b k), x t (E k)⟫_ℂ - ⟪x t (b k) - L.starProjection (x t (b k)),
        x t (E k) - L.starProjection (x t (E k))⟫_ℂ) := by
    intro t
    have h1 : ∀ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ = ∑ k, ⟪x t (b k), E j⟫_ℂ * ⟪E j, x t (E k)⟫_ℂ := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hexp (y t (E j)), map_sum, inner_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, inner_smul_right, ← ContinuousLinearMap.adjoint_inner_left, hy]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact sum_inner_mul_inner_proj L _ _
  have hconst : ∀ t k, ⟪x t (b k), x t (E k)⟫_ℂ = ⟪b k, E k⟫_ℂ := fun t k => hxi t _ _
  simp_rw [hconst] at hterm
  have hfun : (fun t => ∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) = fun t =>
      (∑ k, ⟪b k, E k⟫_ℂ) - ∑ k, ⟪x t (b k) - L.starProjection (x t (b k)),
        x t (E k) - L.starProjection (x t (E k))⟫_ℂ := by
    funext t; rw [hterm t, Finset.sum_sub_distrib]
  show HasDerivAt (fun t => ∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) 0 0
  rw [hfun]
  have hbL : ∀ k, b k ∈ L := fun k => hAd _
  have hEL : ∀ k, E k ∈ L := fun k => (e k).2
  have hd : ∀ v ∈ L, ∃ w, HasDerivAt (fun t => x t v - L.starProjection (x t v)) w 0 ∧
      x 0 v - L.starProjection (x 0 v) = 0 := by
    intro v hv
    obtain ⟨w, hw⟩ := hxd v hv
    have hP : HasDerivAt (fun t => L.starProjection (x t v)) (L.starProjection w) 0 :=
      (L.starProjection.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hw
    refine ⟨w - L.starProjection w, hw.sub hP, ?_⟩
    rw [hx0, ContinuousLinearMap.one_apply, L.starProjection_eq_self_iff.2 hv, sub_self]
  have hsum : HasDerivAt (fun t => ∑ k, ⟪x t (b k) - L.starProjection (x t (b k)),
      x t (E k) - L.starProjection (x t (E k))⟫_ℂ) 0 0 := by
    have : (0 : ℂ) = ∑ _k : Fin (Module.finrank ℂ L), (0 : ℂ) := by simp
    rw [this]
    refine HasDerivAt.fun_sum fun k _ => ?_
    obtain ⟨w1, h1, z1⟩ := hd _ (hbL k)
    obtain ⟨w2, h2, z2⟩ := hd _ (hEL k)
    have := h1.inner ℂ h2
    rw [z1, z2, inner_zero_left, inner_zero_right, add_zero] at this
    exact this
  have := hsum.const_sub (∑ k, ⟪b k, E k⟫_ℂ)
  rwa [neg_zero] at this

end GlobalTheory.Pc3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormEntriesMulLe
section
namespace GlobalTheory.EntryNormProductBound

theorem sum_norm_entries_mul_le {n : ℕ} {α : Type} [NormedRing α]
    (a b : Matrix (Fin n) (Fin n) α) :
    ∑ i : Fin n, ∑ j : Fin n, ‖(a * b) i j‖ ≤
      (∑ i : Fin n, ∑ j : Fin n, ‖a i j‖) * ∑ i : Fin n, ∑ j : Fin n, ‖b i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j : Fin n, ‖(a * b) i j‖
      ≤ ∑ j : Fin n, ∑ k : Fin n, ‖a i k‖ * ‖b k j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ k : Fin n, ‖a i k‖ * ∑ j : Fin n, ‖b k j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ k : Fin n, ‖a i k‖ * ∑ l : Fin n, ∑ j : Fin n, ‖b l j‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun l => ∑ j : Fin n, ‖b l j‖)
          (fun l _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)
    _ = (∑ k : Fin n, ‖a i k‖) * ∑ l : Fin n, ∑ j : Fin n, ‖b l j‖ :=
        (Finset.sum_mul _ _ _).symm

end GlobalTheory.EntryNormProductBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTracePowMulSubMulPowTelescope
section
namespace GlobalTheory.ChernCalc

theorem sum_trace_pow_mul_sub_mul_pow (R : Type) [CommRing R] (r : Type) [Fintype r]
    [DecidableEq r] (P Q : Matrix r r R) (k : ℕ) :
    ∑ i ∈ Finset.range k, (P ^ i * (P - Q) * Q ^ (k - 1 - i)).trace
      = (P ^ k).trace - (Q ^ k).trace := by
  have h : ∀ i ∈ Finset.range k, (P ^ i * (P - Q) * Q ^ (k - 1 - i)).trace
      = (P ^ (i + 1) * Q ^ (k - (i + 1))).trace - (P ^ i * Q ^ (k - i)).trace := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have e1 : k - 1 - i = k - (i + 1) := by omega
    have e2 : k - i = (k - (i + 1)) + 1 := by omega
    rw [e1, e2, ← Matrix.trace_sub, mul_sub, sub_mul, ← pow_succ, pow_succ' Q, mul_assoc]
  rw [Finset.sum_congr rfl h,
    Finset.sum_range_sub (fun i => (P ^ i * Q ^ (k - i)).trace)]
  simp

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTranslatesEqDoubleCosetAverage
section
namespace GlobalTheory
namespace CosetAvg

open MulAction

theorem orbit_sum {H X M : Type*} [Group H] [Fintype H] [MulAction H X] [AddCommGroup M]
    [Module ℂ M] (y : X) [Fintype (orbit H y)] (F : X → M) :
    (Fintype.card (orbit H y) : ℂ) • ∑ h : H, F (h • y) =
      (Fintype.card H : ℂ) • ∑ z : orbit H y, F z := by
  have h1 : ∀ z : orbit H y, ∑ h : H, F (h • (z : X)) = ∑ h : H, F (h • y) := by
    rintro ⟨z, g, rfl⟩
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => by simp [mul_smul])
  have h2 : ∀ h : H, ∑ z : orbit H y, F (h • (z : X)) = ∑ z : orbit H y, F z := by
    intro h
    exact Fintype.sum_equiv (MulAction.toPerm h) _ _ (fun z => rfl)
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.card_univ,
    ← Finset.sum_const, ← Finset.sum_const]
  calc ∑ _z : orbit H y, ∑ h : H, F (h • y) = ∑ z : orbit H y, ∑ h : H, F (h • (z : X)) :=
        Finset.sum_congr rfl (fun z _ => (h1 z).symm)
    _ = ∑ h : H, ∑ z : orbit H y, F (h • (z : X)) := Finset.sum_comm
    _ = ∑ _h : H, ∑ z : orbit H y, F z := Finset.sum_congr rfl (fun h _ => h2 h)

theorem avg_of_invariant {H X M ι : Type*} [Group H] [Fintype H] [MulAction H X]
    [AddCommGroup M] [Module ℂ M] (s : Finset ι) (y : ι → X) [∀ i, Fintype (orbit H (y i))]
    (F : ι → X → M) (hinv : ∀ h : H, ∑ i ∈ s, F i (h • y i) = ∑ i ∈ s, F i (y i)) :
    ∑ i ∈ s, F i (y i) =
      ∑ i ∈ s, ((Fintype.card (orbit H (y i)) : ℂ)⁻¹ • ∑ z : orbit H (y i), F i z) := by
  have hH : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hO : ∀ i, (Fintype.card (orbit H (y i)) : ℂ) ≠ 0 := fun i => by
    haveI : Nonempty (orbit H (y i)) := ⟨⟨y i, mem_orbit_self _⟩⟩
    exact_mod_cast Fintype.card_ne_zero
  have key : ∀ i, ∑ h : H, F i (h • y i) = (Fintype.card H : ℂ) •
      ((Fintype.card (orbit H (y i)) : ℂ)⁻¹ • ∑ z : orbit H (y i), F i z) := by
    intro i
    rw [smul_comm (Fintype.card H : ℂ), ← orbit_sum, smul_smul, inv_mul_cancel₀ (hO i), one_smul]
  apply smul_right_injective M hH
  simp only
  calc (Fintype.card H : ℂ) • ∑ i ∈ s, F i (y i) = ∑ _h : H, ∑ i ∈ s, F i (y i) := by
        rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    _ = ∑ h : H, ∑ i ∈ s, F i (h • y i) := Finset.sum_congr rfl (fun h _ => (hinv h).symm)
    _ = ∑ i ∈ s, ∑ h : H, F i (h • y i) := Finset.sum_comm
    _ = _ := by rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _ => key i)

end CosetAvg
end GlobalTheory

namespace GlobalTheory
namespace CosetAvg

open MulAction

theorem sum_translates_eq_avg : ∀ {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : G →* Module.End ℂ M) (K : Subgroup G) {ι : Type} (s : Finset ι) (a : ι → G) (R : ι → Finset G) (w : ι → M), (∀ i ∈ s, (∀ γ ∈ R i, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * a i * k₂) ∧ ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a i * k₂) → ∃! γ, γ ∈ R i ∧ γ⁻¹ * x ∈ K) → (∀ i ∈ s, ∀ k ∈ K, ρ k (w i) = w i) → (∀ k ∈ K, ρ k (∑ i ∈ s, ρ (a i) (w i)) = ∑ i ∈ s, ρ (a i) (w i)) → ∑ i ∈ s, ρ (a i) (w i) = ∑ i ∈ s, ((R i).card : ℂ)⁻¹ • ∑ γ ∈ R i, ρ γ (w i) := by
  intro G M _ _ _ ρ K ι s a R w hR hw hm
  classical
  have hsm : ∀ (k : K) (g : G), k • ((g : G) : G ⧸ K) = ((k * g : G) : G ⧸ K) := fun k g => rfl
  let Y : SubMulAction K (G ⧸ K) :=
    { carrier := {q | ∃ i ∈ s, ∃ k : K, q = k • ((a i : G) : G ⧸ K)}
      smul_mem' := by
        rintro c q ⟨i, hi, k, rfl⟩
        exact ⟨i, hi, c * k, (mul_smul c k _).symm⟩ }
  have hYsub : (Y : Set (G ⧸ K)) ⊆
      ((s.biUnion fun i => (R i).image (QuotientGroup.mk : G → G ⧸ K) : Finset (G ⧸ K)) :
        Set (G ⧸ K)) := by
    rintro q ⟨i, hi, k, rfl⟩
    obtain ⟨γ, ⟨hγ, hγk⟩, -⟩ := (hR i hi).2 (k * a i) ⟨k, k.2, 1, K.one_mem, by simp⟩
    refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨γ, hγ, ?_⟩⟩)
    rw [hsm, QuotientGroup.eq]
    exact hγk
  haveI : Finite Y := (Set.Finite.subset (Finset.finite_toSet _) hYsub).to_subtype
  letI : Fintype Y := Fintype.ofFinite Y
  let φ := MulAction.toPermHom K Y
  let H := φ.range
  letI : Fintype H := Fintype.ofFinite H
  have hy : ∀ i ∈ s, ((a i : G) : G ⧸ K) ∈ Y := fun i hi => ⟨i, hi, 1, by simp⟩
  let y : s → Y := fun i => ⟨((a i : G) : G ⧸ K), hy i i.2⟩
  letI : ∀ i, Fintype (orbit H (y i)) := fun i => Fintype.ofFinite _
  let F : s → Y → M := fun i q => ρ (q : G ⧸ K).out (w i)
  have hF : ∀ (i : s) (q : Y) (g : G), (q : G ⧸ K) = (g : G ⧸ K) → F i q = ρ g (w i) := by
    intro i q g hq
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    simp only [F, hq, hk, map_mul, Module.End.mul_apply, hw i i.2 k k.2]
  have hval : ∀ (k : K) (i : s),
      ((((⟨φ k, k, rfl⟩ : H) • y i : Y)) : G ⧸ K) = ((k * a i : G) : G ⧸ K) := fun k i => rfl
  have hinv : ∀ h : H, ∑ i ∈ Finset.univ, F i (h • y i) = ∑ i ∈ Finset.univ, F i (y i) := by
    rintro ⟨_, k, rfl⟩
    rw [Finset.sum_congr rfl (fun i _ => hF i _ _ (hval k i)),
      Finset.sum_congr rfl (fun i _ => hF i (y i) (a i) rfl)]
    simp only [map_mul, Module.End.mul_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, Finset.sum_coe_sort s (fun i => ρ (a i) (w i)), hm k k.2]
  have hmain := avg_of_invariant (H := H) Finset.univ y F hinv

  have horb : ∀ i : s, ∃ e : (R i) ≃ orbit H (y i),
      ∀ γ : R i, ((e γ : Y) : G ⧸ K) = ((γ : G) : G ⧸ K) := by
    intro i
    have hmemY : ∀ γ ∈ R i, ((γ : G) : G ⧸ K) ∈ Y := by
      intro γ hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (hR i i.2).1 γ hγ
      exact ⟨i, i.2, ⟨k₁, hk₁⟩, by rw [hsm, QuotientGroup.mk_mul_of_mem _ hk₂]⟩
    have hmemO : ∀ (γ : G) (hγ : γ ∈ R i), (⟨(γ : G ⧸ K), hmemY γ hγ⟩ : Y) ∈ orbit H (y i) := by
      intro γ hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, hγe⟩ := (hR i i.2).1 γ hγ
      refine ⟨⟨φ ⟨k₁, hk₁⟩, ⟨k₁, hk₁⟩, rfl⟩, Subtype.ext ?_⟩
      exact (hval _ _).trans ((QuotientGroup.mk_mul_of_mem _ hk₂).symm.trans (congrArg _ hγe.symm))
    let f : R i → orbit H (y i) := fun γ => ⟨⟨(γ : G ⧸ K), hmemY γ γ.2⟩, hmemO γ γ.2⟩
    have hbij : Function.Bijective f := by
      constructor
      · rintro ⟨γ, hγ⟩ ⟨γ', hγ'⟩ he
        have he' : ((γ : G) : G ⧸ K) = ((γ' : G) : G ⧸ K) :=
          congrArg (fun z : orbit H (y i) => ((z : Y) : G ⧸ K)) he
        rw [QuotientGroup.eq] at he'
        have hu := (hR i i.2).2 γ' ((hR i i.2).1 γ' hγ')
        exact Subtype.ext (hu.unique ⟨hγ, he'⟩ ⟨hγ', by simp⟩)
      · rintro ⟨z, ⟨⟨_, k, rfl⟩, hz⟩⟩
        obtain ⟨γ, ⟨hγ, hγk⟩, -⟩ := (hR i i.2).2 (k * a i) ⟨k, k.2, 1, K.one_mem, by simp⟩
        refine ⟨⟨γ, hγ⟩, Subtype.ext (Subtype.ext ?_)⟩
        exact (QuotientGroup.eq.mpr hγk).trans ((hval k i).symm.trans (congrArg Subtype.val hz))
    exact ⟨Equiv.ofBijective f hbij, fun γ => rfl⟩
  rw [← Finset.sum_coe_sort s, ← Finset.sum_coe_sort s, Finset.sum_congr rfl
    (fun i _ => (hF i (y i) (a i) rfl).symm), hmain]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  obtain ⟨e, he⟩ := horb i
  rw [← Fintype.card_congr e, Fintype.card_coe]
  congr 1
  rw [← Finset.sum_coe_sort (R i)]
  exact (Fintype.sum_equiv e _ _ (fun γ => (hF i _ _ (he γ)).symm)).symm

end CosetAvg
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransversalLeftTranslateInvariant
section
namespace GlobalTheory

theorem sum_transversal_left_translate_invariant :
    ∀ {G X : Type} [Group G] [AddCommMonoid X] (H K : Subgroup G) (R : Finset G) (f : G → X),
      (∀ r ∈ R, r ∈ H) → (∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K) →
      (∀ r ∈ H, ∀ c ∈ K, f (r * c) = f r) → ∀ k ∈ H, ∑ r ∈ R, f (k * r) = ∑ r ∈ R, f r := by
  intro G X _ _ H K R f hR hU hf k hk
  have hkH : ∀ a ∈ R, k * a ∈ H := fun a ha => H.mul_mem hk (hR a ha)
  refine Finset.sum_bij (fun a ha => Classical.choose (hU (k * a) (hkH a ha)).exists)
    (fun a ha => (Classical.choose_spec (hU (k * a) (hkH a ha)).exists).1) ?_ ?_ ?_
  · intro a₁ ha₁ a₂ ha₂ heq
    have h1 := (Classical.choose_spec (hU (k * a₁) (hkH a₁ ha₁)).exists).2
    have h2 := (Classical.choose_spec (hU (k * a₂) (hkH a₂ ha₂)).exists).2
    rw [heq] at h1
    set r' := Classical.choose (hU (k * a₂) (hkH a₂ ha₂)).exists
    have hm : a₁⁻¹ * a₂ ∈ K := by
      have := K.mul_mem (K.inv_mem h1) h2
      simpa [mul_assoc] using this
    have hu := (hU a₂ (hR a₂ ha₂)).unique (y₁ := a₁) (y₂ := a₂) ⟨ha₁, hm⟩ ⟨ha₂, by simpa using K.one_mem⟩
    exact hu
  · intro b hb
    have hb' : k⁻¹ * b ∈ H := H.mul_mem (H.inv_mem hk) (hR b hb)
    obtain ⟨a, ⟨ha, haK⟩, -⟩ := hU (k⁻¹ * b) hb'
    refine ⟨a, ha, ?_⟩
    have hs := Classical.choose_spec (hU (k * a) (hkH a ha)).exists
    have hbK : b⁻¹ * (k * a) ∈ K := by
      have := K.inv_mem haK
      simpa [mul_assoc] using this
    exact (hU (k * a) (hkH a ha)).unique hs ⟨hb, hbK⟩
  · intro a ha
    have hs := Classical.choose_spec (hU (k * a) (hkH a ha)).exists
    set r' := Classical.choose (hU (k * a) (hkH a ha)).exists
    have := hf r' (hR r' hs.1) (r'⁻¹ * (k * a)) hs.2
    rw [mul_inv_cancel_left] at this
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleSumPowMul
section
namespace GlobalTheory.TwoCocycle

theorem interchange {Γ D : Type} [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D)
    (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (a b x y : Γ) :
    c (a * b) (x * y) + c x y + c a b = c a x + c b y + c (a * x) (b * y) := by
  have h1 := hc a b (x * y)
  have h2 := hc b y x
  have h3 := hc a x (b * y)
  rw [mul_comm y x, hs y x, hs (b * y) x] at h2
  rw [mul_left_comm x b y] at h3
  linear_combination (norm := abel) h2 + h3 - h1

theorem sum_pow_mul (Γ D : Type) [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D)
    (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (n : ℕ) (x y : Γ) :
    ∑ i ∈ Finset.range n, c ((x * y) ^ i) (x * y) + n • c x y =
      ∑ i ∈ Finset.range n, c (x ^ i) x + ∑ i ∈ Finset.range n, c (y ^ i) y
        + c (x ^ n) (y ^ n) - c 1 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := interchange c hs hc (x ^ n) (y ^ n) x y
    rw [← mul_pow] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, succ_nsmul,
      pow_succ x, pow_succ y]
    linear_combination (norm := abel) ih + h

end GlobalTheory.TwoCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorInvolutionAlgebraProperties
section
namespace GlobalTheory

open IsLocalization in
theorem localFlat_dvd_descends : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D] (Q : Ideal D) [Q.IsPrime] (f b : B), algebraMap B (Localization.AtPrime Q) b ∈ Ideal.span {algebraMap B (Localization.AtPrime Q) f} → ∃ s : B, s ∉ Q.comap (algebraMap B D) ∧ s * b ∈ Ideal.span {f} := by
  intro B D _ _ _ _ Q _ f b h
  set P : Ideal B := Q.comap (algebraMap B D) with hP
  let φ : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (algebraMap B D) rfl
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) := φ.toAlgebra
  have hφ : ∀ x : B, φ (algebraMap B (Localization.AtPrime P) x) = algebraMap B (Localization.AtPrime Q) x := by
    intro x
    simp [φ, Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply B D (Localization.AtPrime Q)]
  have hfl : φ.Flat := RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) Q P rfl
  haveI : Module.Flat (Localization.AtPrime P) (Localization.AtPrime Q) := hfl
  haveI : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) :=
    (inferInstance : IsLocalHom φ)
  haveI : Module.FaithfullyFlat (Localization.AtPrime P) (Localization.AtPrime Q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have key : algebraMap B (Localization.AtPrime P) b ∈
      (Ideal.span {f}).map (algebraMap B (Localization.AtPrime P)) := by
    rw [Ideal.map_span, Set.image_singleton,
      ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Localization.AtPrime Q)
        (Ideal.span {algebraMap B (Localization.AtPrime P) f}), Ideal.mem_comap,
      Ideal.map_span, Set.image_singleton]
    change φ _ ∈ Ideal.span {φ _}
    rw [hφ, hφ]; exact h
  obtain ⟨s, hs, h2⟩ := (algebraMap_mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P) _ b).1 key
  exact ⟨s, hs, h2⟩

end GlobalTheory
end

