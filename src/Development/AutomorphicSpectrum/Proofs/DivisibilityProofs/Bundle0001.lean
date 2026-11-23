module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MemSmulOfTmulEqZero
section
open CategoryTheory TensorProduct ChangeOfRings

namespace GlobalTheory.CompanionTheory.ModuleReduction

theorem mem_smul_of_tmul_eq_zero {A Q N : Type} [CommRing A] [AddCommGroup Q] [Module A Q]
    [AddCommGroup N] [Module A N] (g : A →ₗ[A] Q) (hg : Function.Surjective g) (ξ : A)
    (hk : ∀ a, g a = 0 ↔ ∃ b, a = ξ * b) (m : N) (h : g 1 ⊗ₜ[A] m = 0) :
    ∃ n : N, m = ξ • n := by
  have hex : Function.Exact (LinearMap.mulLeft A ξ) g := by
    intro a
    rw [hk a]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
  have hex' := rTensor_exact N hex hg
  have h1 : (LinearMap.rTensor N g) ((1 : A) ⊗ₜ[A] m) = 0 := by
    simpa using h
  obtain ⟨t, ht⟩ := (hex' _).1 h1
  have key : ∀ t : A ⊗[A] N, TensorProduct.lid A N (LinearMap.rTensor N (LinearMap.mulLeft A ξ) t)
      = ξ • TensorProduct.lid A N t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a n => simp [mul_smul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
  refine ⟨TensorProduct.lid A N t, ?_⟩
  rw [← key, ht]
  simp

theorem exists_reduction (A O : Type) [CommRing A] [CommRing O] (θ : A →+* O)
    (hθ : Function.Surjective θ) (ξ : A) (hker : RingHom.ker θ = Ideal.span {ξ})
    (𝒞 : Type 1) [CategoryTheory.Category.{0} 𝒞] (M : CategoryTheory.Functor 𝒞 (ModuleCat.{0} A)) :
    ∃ (D : CategoryTheory.Functor 𝒞 (ModuleCat.{0} O)) (r : ∀ X : 𝒞, M.obj X →ₛₗ[θ] D.obj X),
      (∀ X, Function.Surjective (r X) ∧ ∀ m, r X m = 0 ↔ ∃ n, m = ξ • n) ∧
      ∀ (X Y : 𝒞) (f : X ⟶ Y) (m : M.obj X), D.map f (r X m) = r Y (M.map f m) := by
  let Q := (ModuleCat.restrictScalars θ).obj (ModuleCat.of O O)
  let one : Q := (1 : O)
  let g : A →ₗ[A] Q := LinearMap.toSpanSingleton A Q one
  have hgθ : ∀ a, (g a : O) = θ a := fun a => mul_one (θ a)
  have hsm : ∀ (X : 𝒞) (a : A) (m : M.obj X),
      (1 : O) ⊗ₜ[A,θ] (a • m) = (θ a) ⊗ₜ[A,θ] m := by
    intro X a m
    have h := TensorProduct.smul_tmul (R := A) (R' := A) a one m
    have e : a • one = (θ a : O) := hgθ a
    rw [e] at h
    exact h.symm
  let r : ∀ X : 𝒞, M.obj X →ₛₗ[θ] (M ⋙ ModuleCat.extendScalars θ).obj X := fun X =>
    { toFun := fun m => (1 : O) ⊗ₜ[A,θ] m
      map_add' := fun a b => TensorProduct.tmul_add _ _ _
      map_smul' := fun a m => by
        refine (hsm X a m).trans ?_
        have := ModuleCat.ExtendScalars.smul_tmul θ (M := M.obj X) (θ a) (1 : O) m
        rw [mul_one] at this
        exact this.symm }
  refine ⟨M ⋙ ModuleCat.extendScalars θ, r, fun X => ⟨?_, fun m => ⟨?_, ?_⟩⟩, ?_⟩
  · intro y
    change Q ⊗[A] (M.obj X) at y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul o n =>
      obtain ⟨a, ha⟩ := hθ o
      refine ⟨a • n, ?_⟩
      refine (hsm X a n).trans ?_
      rw [ha]
      rfl
    | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨u + v, ?_⟩
      rw [map_add (f := _), hu, hv]
      rfl
  · intro h
    refine mem_smul_of_tmul_eq_zero g ?_ ξ ?_ m ?_
    · intro q
      obtain ⟨a, ha⟩ := hθ q
      exact ⟨a, (hgθ a).trans ha⟩
    · intro a
      have : g a = 0 ↔ θ a = 0 := by
        rw [← hgθ a]
        rfl
      rw [this, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton']
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨b, mul_comm _ _⟩
      · rintro ⟨b, rfl⟩
        exact ⟨b, mul_comm _ _⟩
    · have e : g 1 = one := one_smul A one
      rw [e]
      exact h
  · rintro ⟨n, rfl⟩
    have : θ ξ = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact Ideal.mem_span_singleton_self ξ
    change (1 : O) ⊗ₜ[A,θ] (ξ • n) = 0
    rw [hsm X ξ n, this]
    exact TensorProduct.zero_tmul (R := A) Q n
  · intro X Y f m
    rfl

end GlobalTheory.CompanionTheory.ModuleReduction
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SemilinearFactorsThroughReduction
section
namespace GlobalTheory.CompanionTheory.Div

theorem semilinear_factors_through_reduction :
    ∀ (A O : Type) [CommRing A] [CommRing O] (θ : A →+* O), Function.Surjective θ →
      ∀ (ξ : A), θ ξ = 0 →
      ∀ (M D L : Type) [AddCommGroup M] [Module A M] [AddCommGroup D] [Module O D]
        [AddCommGroup L] [Module O L] (r : M →ₛₗ[θ] D) (q : M →ₛₗ[θ] L),
        Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = ξ • n) →
        ∃ π : D →ₗ[O] L, ∀ m, π (r m) = q m := by
  intro A O _ _ θ hθ ξ hξ M D L _ _ _ _ _ _ r q hr hker
  have hq : ∀ m m', r m = r m' → q m = q m' := by
    intro m m' h
    obtain ⟨n, hn⟩ := (hker (m - m')).1 (by rw [map_sub, h, sub_self])
    have h0 : q (m - m') = 0 := by rw [hn, map_smulₛₗ, hξ, zero_smul]
    rwa [map_sub, sub_eq_zero] at h0
  let s := Function.surjInv hr
  have hs : ∀ d, r (s d) = d := Function.surjInv_eq hr
  refine ⟨{ toFun := fun d => q (s d), map_add' := ?_, map_smul' := ?_ }, fun m => hq _ _ (hs _)⟩
  · intro d d'
    rw [← map_add (f := _)]
    exact hq _ _ (by rw [map_add (f := _), hs, hs, hs])
  · intro o d
    obtain ⟨a, rfl⟩ := hθ o
    simp only [RingHom.id_apply]
    rw [← map_smulₛₗ]
    exact hq _ _ (by rw [map_smulₛₗ, hs, hs])

end GlobalTheory.CompanionTheory.Div
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogDivNSqLeTwo
section
namespace GlobalTheory.CompanionTheory.Ar.Small

theorem log_tail_step (x : ℝ) (hx : 1 ≤ x) :
    Real.log (x + 1) / ((x + 1) * x) ≤
      (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hL : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    have he : (x + 1) / x - 1 = 1 / x := by
      field_simp
      ring
    linarith
  have hK : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ 2 := by
    have h1 : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ (x + 1) * (1 / x) :=
      mul_le_mul_of_nonneg_left hL (by linarith)
    have h2 : (x + 1) * (1 / x) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hx0]
      linarith
    linarith
  have hE : (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) - Real.log (x + 1) / ((x + 1) * x) =
      (2 - (x + 1) * (Real.log (x + 1) - Real.log x)) / ((x + 1) * x) := by
    field_simp
    ring
  have hpos : 0 ≤ (2 - (x + 1) * (Real.log (x + 1) - Real.log x)) / ((x + 1) * x) :=
    div_nonneg (by linarith) (by positivity)
  linarith

theorem log_tail_Icc (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤
      2 - (Real.log N + 2) / N := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by norm_num)]
    simp
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hstep := log_tail_step (k : ℝ) (by exact_mod_cast hk)
    have hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hc]
    have hc2 : (k : ℝ) + 1 - 1 = k := by ring
    rw [hc2]
    linarith

theorem log_tail :
    ∀ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) →
      ∑ n ∈ S, Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 := by
  intro S hS
  have hN : 1 ≤ max 1 (S.sup id) := le_max_left _ _
  have hsub : S ⊆ Finset.Icc 2 (max 1 (S.sup id)) := by
    intro n hn
    rw [Finset.mem_Icc]
    exact ⟨hS n hn, le_trans (Finset.le_sup (f := id) hn) (le_max_right _ _)⟩
  have hnn : ∀ n ∈ Finset.Icc 2 (max 1 (S.sup id)), 0 ≤ Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith
  have h1 : (1 : ℝ) ≤ ((max 1 (S.sup id) : ℕ) : ℝ) := by exact_mod_cast hN
  have hq : 0 ≤ (Real.log ((max 1 (S.sup id) : ℕ) : ℝ) + 2) / ((max 1 (S.sup id) : ℕ) : ℝ) :=
    div_nonneg (by linarith [Real.log_nonneg h1]) (by linarith)
  calc ∑ n ∈ S, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
      ≤ ∑ n ∈ Finset.Icc 2 (max 1 (S.sup id)), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hnn n hn)
    _ ≤ 2 - (Real.log ((max 1 (S.sup id) : ℕ) : ℝ) + 2) / ((max 1 (S.sup id) : ℕ) : ℝ) :=
        log_tail_Icc _ hN
    _ ≤ 2 := by linarith

end GlobalTheory.CompanionTheory.Ar.Small
end

