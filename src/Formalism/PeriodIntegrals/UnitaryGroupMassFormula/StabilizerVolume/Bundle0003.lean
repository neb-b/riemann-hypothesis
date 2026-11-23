module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensCntQ
section
noncomputable section

namespace PI.VolStabS

open Polynomial

private theorem bijective_algebraMap_add_mul_of_finrank_two {k K : Type} [Field k] [CommRing K]
    [Algebra k K] [Module.Finite k K] (hK : Module.finrank k K = 2) (r : K)
    (h0 : ∀ a b : k, algebraMap k K a + algebraMap k K b * r = 0 → a = 0 ∧ b = 0) :
    Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  let L : (k × k) →ₗ[k] K :=
    (LinearMap.fst k k k).smulRight (1 : K) + (LinearMap.snd k k k).smulRight r
  have hL : ∀ p : k × k, L p = algebraMap k K p.1 + algebraMap k K p.2 * r := by
    intro p
    simp [L, Algebra.smul_def]
  have hfun : (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) = ⇑L :=
    funext fun p => (hL p).symm
  rw [hfun]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hL] at hp
    obtain ⟨h1, h2⟩ := h0 p.1 p.2 hp
    exact Prod.ext h1 h2
  have H : Module.finrank k (k × k) = Module.finrank k K := by
    rw [hK]
    simp
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank H).mp hinj⟩

private theorem exists_algEquiv_prod_swap (k : Type) [Field k] :
    ∃ σ : (k × k) ≃ₐ[k] (k × k), ∀ x, σ x = x.swap :=
  ⟨{ toFun := Prod.swap
     invFun := Prod.swap
     left_inv := fun x => Prod.swap_swap x
     right_inv := fun x => Prod.swap_swap x
     map_mul' := fun x y => rfl
     map_add' := fun x y => rfl
     commutes' := fun c => rfl }, fun x => rfl⟩

private theorem isQuadInv_and_bijective_of_not_isSquare (k K : Type) [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) (hsq : ¬ IsSquare D)
    (hK : Module.finrank k K = 2) (r : K) (hr : r * r = algebraMap k K D)
    (σ' : K ≃ₐ[k] K) (hσ : σ' r = -r) (hinv : ∀ x, σ' (σ' x) = x) :
    IsQuadInv k K σ' ∧
      Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have h11 : algebraMap k K (1 + 1) = 0 := by
      rw [map_add (f := _), map_one]
      linear_combination h
    have h11' : (1 + 1 : k) = 0 := (algebraMap k K).injective (h11.trans (map_zero _).symm)
    exact h2 (by linear_combination h11')
  refine ⟨⟨hinv, Or.inl ⟨Field.toIsField K, hK, ?_⟩⟩, ?_⟩
  · intro hσr
    have h1 : r = -r := by
      simpa [hσr] using hσ
    have hr0 : r = 0 := by
      have h2r : (2 : K) * r = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2r).resolve_left h2K
    apply hD
    apply (algebraMap k K).injective
    rw [← hr, hr0, mul_zero, map_zero]
  · apply bijective_algebraMap_add_mul_of_finrank_two hK r
    intro a b h
    by_cases hb : b = 0
    · subst hb
      simp only [map_zero, zero_mul, add_zero] at h
      refine ⟨?_, rfl⟩
      apply (algebraMap k K).injective
      rw [h, map_zero]
    · exfalso
      apply hsq
      refine ⟨-a / b, ?_⟩
      apply (algebraMap k K).injective
      have hbK : algebraMap k K b ≠ 0 := (_root_.map_ne_zero _).mpr hb
      have hrc : r = algebraMap k K (-a / b) := by
        rw [map_div₀, map_neg, eq_div_iff hbK]
        linear_combination h
      rw [← hr, hrc, map_mul]

theorem exists_quadAlg (k : Type) [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) :
    ∃ (K : Type) (_ : CommRing K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K) (r : K),
      IsQuadInv k K σ' ∧ r * r = algebraMap k K D ∧ σ' r = -r ∧
      Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  by_cases hsq : IsSquare D
  · obtain ⟨s, hs⟩ := hsq
    have hs0 : s ≠ 0 := fun h => hD (by rw [hs, h, mul_zero])
    obtain ⟨σ, hσ⟩ := exists_algEquiv_prod_swap k
    refine ⟨k × k, inferInstance, inferInstance, σ, (s, -s), ?_, ?_, ?_, ?_⟩
    · refine ⟨fun x => by rw [hσ, hσ, Prod.swap_swap], Or.inr ⟨AlgEquiv.refl, fun x => ?_⟩⟩
      rw [hσ]
      rfl
    · ext <;> simp [hs]
    · rw [hσ]
      ext <;> simp
    · apply bijective_algebraMap_add_mul_of_finrank_two
      · simp
      · intro a b h
        have e1 : a + b * s = 0 := by
          exact congrArg Prod.fst h
        have e2 : a + b * -s = 0 := by
          exact congrArg Prod.snd h
        have hb : (2 * s) * b = 0 := by linear_combination e1 - e2
        have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_left (mul_ne_zero h2 hs0)
        refine ⟨?_, hb0⟩
        linear_combination e1 - s * hb0
  · have hroot : ∀ b : k, b ^ 2 ≠ D := fun b hb => hsq ⟨b, by rw [← hb, sq]⟩
    have hirr : Irreducible (X ^ 2 - C D : k[X]) := by
      exact X_pow_sub_C_irreducible_of_prime Nat.prime_two hroot
    have : Fact (Irreducible (X ^ 2 - C D : k[X])) := ⟨hirr⟩
    have hf0 : (X ^ 2 - C D : k[X]) ≠ 0 := hirr.ne_zero
    have hfin : Module.finrank k (AdjoinRoot (X ^ 2 - C D : k[X])) = 2 := by
      rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C _]
    have : Module.Finite k (AdjoinRoot (X ^ 2 - C D : k[X])) := (AdjoinRoot.powerBasis hf0).finite
    have hr : AdjoinRoot.root (X ^ 2 - C D : k[X]) * AdjoinRoot.root (X ^ 2 - C D : k[X]) =
        algebraMap k (AdjoinRoot (X ^ 2 - C D : k[X])) D := by
      have h0 : aeval (AdjoinRoot.root (X ^ 2 - C D : k[X])) (X ^ 2 - C D : k[X]) = 0 := by
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      simp only [map_sub, aeval_X_pow, aeval_C] at h0
      linear_combination h0
    have hneg : aeval (-AdjoinRoot.root (X ^ 2 - C D : k[X])) (X ^ 2 - C D : k[X]) = 0 := by
      simp only [map_sub, aeval_X_pow, aeval_C]
      linear_combination hr
    have hneg' : eval₂ (algebraMap k (AdjoinRoot (X ^ 2 - C D : k[X])))
        (-AdjoinRoot.root (X ^ 2 - C D : k[X])) (X ^ 2 - C D : k[X]) = 0 := by
      rw [← aeval_def]
      exact hneg
    obtain ⟨τ, hτr⟩ : ∃ τ : AdjoinRoot (X ^ 2 - C D : k[X]) →ₐ[k] AdjoinRoot (X ^ 2 - C D : k[X]),
        τ (AdjoinRoot.root _) = -AdjoinRoot.root (X ^ 2 - C D : k[X]) := by
      exact ⟨{ AdjoinRoot.lift (algebraMap k _) (-AdjoinRoot.root _) hneg' with
          commutes' := fun c => by simp [AdjoinRoot.algebraMap_eq] }, AdjoinRoot.lift_root hneg'⟩
    have hττ : τ.comp τ = AlgHom.id k _ := by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, hτr, map_neg, hτr, neg_neg, AlgHom.id_apply]
    let σ' := AlgEquiv.ofAlgHom τ τ hττ hττ
    have hσ : σ' (AdjoinRoot.root (X ^ 2 - C D : k[X])) = -AdjoinRoot.root (X ^ 2 - C D : k[X]) :=
      hτr
    have hinv : ∀ x, σ' (σ' x) = x := fun x => DFunLike.congr_fun hττ x
    obtain ⟨hq, hbij⟩ := isQuadInv_and_bijective_of_not_isSquare k (AdjoinRoot (X ^ 2 - C D : k[X])) h2 D hD hsq hfin
      (AdjoinRoot.root _) hr σ' hσ hinv
    exact ⟨AdjoinRoot (X ^ 2 - C D : k[X]), inferInstance, inferInstance, σ',
      AdjoinRoot.root _, hq, hr, hσ, hbij⟩

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFHS
section
noncomputable section

namespace PI.VolStabS.FFHS

open Module

variable {K : Type} [Field K] {σ : K →+* K}

structure IsSq {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) :
    Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (c : K) x y, h x (c • y) = c * h x y
  herm : ∀ x y, h y x = σ (h x y)

structure IsHS {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) : Prop
    extends IsSq σ h where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0

section basic

variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

def IsSq.lin (hs : IsSq σ h) (x : V) : V →ₗ[K] K where
  toFun := h x
  map_add' := hs.add_right x
  map_smul' c y := by simp [hs.smul_right]

theorem IsSq.lin_apply (hs : IsSq σ h) (x y : V) : hs.lin x y = h x y := rfl

theorem IsSq.add_left (hs : IsSq σ h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hs.herm z (x + y), hs.add_right, map_add (f := _), ← hs.herm z x, ← hs.herm z y]

theorem IsSq.smul_left (hs : IsSq σ h) (c : K) (x y : V) : h (c • x) y = σ c * h x y := by
  rw [hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm y x]

theorem IsSq.zero_right (hs : IsSq σ h) (x : V) : h x 0 = 0 := by
  simpa using hs.add_right x 0 0

theorem IsSq.zero_left (hs : IsSq σ h) (y : V) : h 0 y = 0 := by
  rw [hs.herm y 0, hs.zero_right, map_zero]

theorem IsSq.sub_right (hs : IsSq σ h) (x y z : V) : h x (y - z) = h x y - h x z :=
  (hs.lin x).map_sub y z

theorem IsSq.self_fixed (hs : IsSq σ h) (x : V) : σ (h x x) = h x x := (hs.herm x x).symm

theorem IsSq.ext_basis {h' : V → V → K} (hs : IsSq σ h) (hs' : IsSq σ h') {ι : Type}
    (b : Basis ι K V) (hb : ∀ i j, h (b i) (b j) = h' (b i) (b j)) (x y : V) : h x y = h' x y := by
  have step1 : ∀ i y, h (b i) y = h' (b i) y := fun i y => by
    have : hs.lin (b i) = hs'.lin (b i) := b.ext (fun j => hb i j)
    exact LinearMap.congr_fun this y
  have step2 : ∀ x, hs.lin x = hs'.lin x := fun x => b.ext (fun i => by
    simp only [IsSq.lin_apply]
    rw [hs.herm (b i) x, hs'.herm (b i) x, step1])
  exact LinearMap.congr_fun (step2 x) y

theorem exists_aniso (h2 : (2 : K) ≠ 0) (hs : IsHS σ h) (x : V) (hx : x ≠ 0) :
    ∃ e, h e e ≠ 0 := by
  have hq := hs.toIsSq
  by_contra H
  push_neg at H
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra H'
    push_neg at H'
    exact hx (hs.nondeg x H')
  have key := H (x + (h x y)⁻¹ • y)
  simp only [hq.add_right, hq.add_left, hq.smul_right, hq.smul_left, H x, H y,
    hq.herm x y] at key
  have e1 : σ (h x y)⁻¹ * σ (h x y) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hy, map_one]
  have e2 : (h x y)⁻¹ * h x y = 1 := inv_mul_cancel₀ hy
  exact h2 (by linear_combination key - e1 - e2)

def perp (hs : IsSq σ h) (e : V) : Submodule K V := LinearMap.ker (hs.lin e)

theorem mem_perp (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := LinearMap.mem_ker

theorem perp_isHS (hs : IsHS σ h) (e : V) (he : h e e ≠ 0) :
    IsHS σ (fun w w' : perp hs.toIsSq e => h w w') where
  add_right x y z := hs.add_right x y z
  smul_right c x y := hs.smul_right c x y
  herm x y := hs.herm x y
  nondeg w hw := by
    have hq := hs.toIsSq
    apply Subtype.ext
    apply hs.nondeg
    intro y
    have hm : y - ((h e e)⁻¹ * h e y) • e ∈ perp hq e := by
      have : (h e e)⁻¹ * h e y * h e e = h e y := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
      rw [mem_perp, hq.sub_right, hq.smul_right, this, sub_self]
    have h1 := hw ⟨_, hm⟩
    have hwe : h w e = 0 := by rw [hq.herm e w, (mem_perp hq e w).1 w.2, map_zero]
    calc h w y = h w (((h e e)⁻¹ * h e y) • e + (y - ((h e e)⁻¹ * h e y) • e)) := by
          rw [add_sub_cancel]
      _ = ((h e e)⁻¹ * h e y) * h w e + h w (y - ((h e e)⁻¹ * h e y) • e) := by
          rw [hq.add_right, hq.smul_right]
      _ = 0 := by rw [hwe, h1]; ring

theorem finrank_perp [FiniteDimensional K V] (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) :
    finrank K (perp hs e) + 1 = finrank K V := by
  have hsurj : Function.Surjective (hs.lin e) := fun c =>
    ⟨(c * (h e e)⁻¹) • e, by rw [IsSq.lin_apply, hs.smul_right, mul_assoc, inv_mul_cancel₀ he,
      mul_one]⟩
  have := LinearMap.finrank_range_add_finrank_ker (hs.lin e)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_self] at this
  unfold perp
  omega

theorem linIndep_orth (hs : IsSq σ h) {n : ℕ} (f : Fin n → V)
    (h1 : ∀ i j, i ≠ j → h (f i) (f j) = 0) (h2 : ∀ i, h (f i) (f i) ≠ 0) :
    LinearIndependent K f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have := congrArg (hs.lin (f i)) hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero, Finset.sum_eq_single i] at this
  · rw [map_smul, IsSq.lin_apply, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (h2 i)
  · intro j _ hji
    rw [map_smul, IsSq.lin_apply, h1 i j (Ne.symm hji), smul_zero]
  · simp

theorem decomp_val (hs : IsSq σ h) (e w : V) (hw : h e w = 0) (s : K) :
    h (s • e + w) (s • e + w) = σ s * s * h e e + h w w := by
  simp only [hs.add_right, hs.add_left, hs.smul_right, hs.smul_left, hw, hs.herm e w, map_zero]
  ring

end basic

theorem exists_orth (h2 : (2 : K) ≠ 0) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V → V → K), IsHS σ h → finrank K V = m →
    ∃ f : Fin m → V, (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, h (f i) (f i) ≠ 0 := by
  intro m
  induction m with
  | zero => intro V _ _ _ h _ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro V _ _ _ h hs hm
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hm
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hs x hx
    have hq := hs.toIsSq
    have hfr : finrank K (perp hq e) = m := by have := finrank_perp hq e he; omega
    obtain ⟨g, hg1, hg2⟩ := ih (perp hq e) (fun w w' => h w w') (perp_isHS hs e he) hfr
    refine ⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using (mem_perp hq e (g j)).1 (g j).2
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hq.herm e, (mem_perp hq e (g i)).1 (g i).2, map_zero]
        | succ j =>
          simp only [Fin.cons_succ]
          exact hg1 i j (fun hh => hij (by rw [hh]))
    · intro i
      induction i using Fin.cases with
      | zero => simpa using he
      | succ i => simpa using hg2 i

end PI.VolStabS.FFHS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensSAInt
section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace PI.VolStabS

private theorem exists_trace_mul_eq_linearMap (F : Type) [Field F] [NumberField F] (f : F →ₗ[ℚ] ℚ) :
    ∃ β : F, ∀ y : F, f y = Algebra.trace ℚ F (β * y) := by
  have hnd := traceForm_nondegenerate ℚ F
  obtain ⟨β, hβ⟩ : ∃ β, (LinearMap.BilinForm.toDual (Algebra.traceForm ℚ F) hnd) β = f :=
    ⟨_, LinearEquiv.apply_symm_apply _ f⟩
  refine ⟨β, fun y => ?_⟩
  rw [← hβ, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply]

theorem addIntF_holds : AddIntF := by
  intro F _ _ Λ ⟨c0, hc0, hc0Λ⟩ hnot g hg
  have hmul : ∀ (r : 𝓞 F) (x : F), x ∈ Λ → algebraMap (𝓞 F) F r * x ∈ Λ := by
    intro r x hx
    have h1 := Λ.smul_mem r hx
    rw [Algebra.smul_def] at h1
    exact h1
  obtain ⟨bb, hbb⟩ : ∃ bb, bb = NumberField.integralBasis F := ⟨_, rfl⟩
  have hmem : ∀ i, c0 * bb i ∈ Λ := by
    intro i
    rw [hbb, NumberField.integralBasis_apply, mul_comm]
    exact hmul _ _ hc0Λ
  choose n hn using fun i => hg _ (hmem i)
  let h0 : F →ₗ[ℚ] ℚ := bb.constr ℚ (fun i => (n i : ℚ))
  have hh0 : ∀ y : F, g (c0 * y) = ((h0 y : ℚ) : ℂ) := by
    let L1 : F →+ ℂ := g.comp (AddMonoidHom.mulLeft c0)
    let L2 : F →+ ℂ := (Rat.castHom ℂ).toAddMonoidHom.comp h0.toAddMonoidHom
    have hL : L1.toRatLinearMap = L2.toRatLinearMap := by
      refine bb.ext (fun i => ?_)
      simp [L1, L2, h0, hn i]
    intro y
    have h1 := congrArg (fun L : F →ₗ[ℚ] ℂ => L y) hL
    simpa [L1, L2] using h1
  obtain ⟨β, hβ⟩ := exists_trace_mul_eq_linearMap F h0
  have hgx : ∀ x : F, g x = ((Algebra.trace ℚ F (β * c0⁻¹ * x) : ℚ) : ℂ) := by
    intro x
    have h1 := hh0 (c0⁻¹ * x)
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at h1
    rw [h1, hβ, mul_assoc]
  intro a
  by_contra ha
  have hβ0 : β * c0⁻¹ ≠ 0 := by
    intro h0'
    apply ha
    rw [hgx, h0', zero_mul, map_zero, Rat.cast_zero]
  have h10 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    intro h
    have h1 : (1 : F) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨1, map_one _⟩
    rw [h, FractionalIdeal.mem_zero_iff] at h1
    exact one_ne_zero h1
  have hdual : ∀ x ∈ Λ,
      β * c0⁻¹ * x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    intro x hx
    rw [FractionalIdeal.mem_dual h10]
    intro b hb
    rw [FractionalIdeal.mem_one_iff] at hb
    obtain ⟨r, rfl⟩ := hb
    obtain ⟨m, hm⟩ := hg _ (hmul r x hx)
    rw [RingHom.mem_range]
    refine ⟨m, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast]
    have h1 := hgx (algebraMap (𝓞 F) F r * x)
    have h2 : ((Algebra.trace ℚ F (β * c0⁻¹ * (algebraMap (𝓞 F) F r * x)) : ℚ) : ℂ)
        = ((m : ℚ) : ℂ) := by
      rw [← h1, hm, Rat.cast_intCast]
    rw [Rat.cast_inj] at h2
    rw [← h2]
    congr 1
    ring
  obtain ⟨d, hd, hdint⟩ :=
    (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).isFractional
  have hd0 : algebraMap (𝓞 F) F d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  apply hnot ((algebraMap (𝓞 F) F d * (β * c0⁻¹))⁻¹) (inv_ne_zero (mul_ne_zero hd0 hβ0))
  intro x hx
  obtain ⟨r, hr⟩ := hdint _ (hdual x hx)
  refine ⟨r, ?_⟩
  rw [Algebra.smul_def] at hr
  have hr' : (r : F) = algebraMap (𝓞 F) F r := rfl
  rw [hr', hr, show algebraMap (𝓞 F) F d * (β * c0⁻¹ * x)
      = algebraMap (𝓞 F) F d * (β * c0⁻¹) * x by ring,
    inv_mul_cancel_left₀ (mul_ne_zero hd0 hβ0)]

theorem chInf_of_lift (hL : ChLift) : ChInf :=
  chInf_of hL addIntF_holds

end PI.VolStabS
end
end

