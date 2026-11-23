module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.GeneralizedVermaModulePolynomial
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.Bundle0002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MemFiltOfWords
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SgMulSelf

@[expose] public section

open Finset
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.RealMult.CovR

open GlobalTheory.CompanionTheory.RealMult
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos)
open GlobalTheory.CompanionTheory.DSICKoszul (homotopy_ring filt mem_filt_succ euler_filt)

variable {n : ℕ}

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure FiltR (R a d : Ix n → Module.End ℂ V) (Fil : ℕ → Submodule ℂ V) : Prop where
  a_comm : ∀ i j, Commute (a i) (a j)
  d_comm : ∀ i j, Commute (d i) (d j)
  da : ∀ i j, d i * a j - a j * d i = if i = j then 1 else 0
  mono : Monotone Fil
  exh : ∀ z, ∃ k, z ∈ Fil k
  a_mem : ∀ i k, ∀ z ∈ Fil k, a i z ∈ Fil (k + 1)
  r_mem : ∀ i k, ∀ z ∈ Fil k, R i z - a i z ∈ Fil k
  d_mem : ∀ i k, ∀ z ∈ Fil (k + 1), d i z ∈ Fil k
  d_zero : ∀ i, ∀ z ∈ Fil 0, d i z = 0

section Tens

variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

def FW (Fil : ℕ → Submodule ℂ Z) (k : ℕ) : Submodule ℂ (Z ⊗[ℂ] Z) :=
  Submodule.span ℂ {t | ∃ k₁ k₂ z w, z ∈ Fil k₁ ∧ w ∈ Fil k₂ ∧ k₁ + k₂ ≤ k ∧ t = z ⊗ₜ[ℂ] w}

theorem tmul_mem_FW (Fil : ℕ → Submodule ℂ Z) {k k₁ k₂ : ℕ} {z w : Z} (hz : z ∈ Fil k₁) (hw : w ∈ Fil k₂)
    (h : k₁ + k₂ ≤ k) : z ⊗ₜ[ℂ] w ∈ FW Fil k :=
  Submodule.subset_span ⟨k₁, k₂, z, w, hz, hw, h, rfl⟩

theorem FW_map (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ (Z ⊗[ℂ] Z)) (k : ℕ) (Q : Submodule ℂ (Z ⊗[ℂ] Z))
    (h : ∀ k₁ k₂ z w, z ∈ Fil k₁ → w ∈ Fil k₂ → k₁ + k₂ ≤ k → T (z ⊗ₜ[ℂ] w) ∈ Q) : ∀ t ∈ FW Fil k, T t ∈ Q := by
  refine fun t ht => (Submodule.span_le (p := Q.comap T)).2 ?_ ht
  rintro _ ⟨k₁, k₂, z, w, hz, hw, hk, rfl⟩
  exact h k₁ k₂ z w hz hw hk

theorem FW_mono (Fil : ℕ → Submodule ℂ Z) : Monotone (FW Fil) := fun k l hkl =>
  Submodule.span_mono (by
    rintro _ ⟨k₁, k₂, z, w, hz, hw, hk, rfl⟩
    exact ⟨k₁, k₂, z, w, hz, hw, hk.trans hkl, rfl⟩)

theorem FW_exh (Fil : ℕ → Submodule ℂ Z) (hm : Monotone Fil) (he : ∀ z, ∃ k, z ∈ Fil k) (t : Z ⊗[ℂ] Z) :
    ∃ k, t ∈ FW Fil k := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul z w =>
    obtain ⟨k, hk⟩ := he z
    obtain ⟨l, hl⟩ := he w
    exact ⟨k + l, tmul_mem_FW Fil hk hl le_rfl⟩
  | add p q hp hq =>
    obtain ⟨k, hk⟩ := hp
    obtain ⟨l, hl⟩ := hq
    exact ⟨max k l, Submodule.add_mem _ (FW_mono Fil (le_max_left _ _) hk) (FW_mono Fil (le_max_right _ _) hl)⟩

theorem rT_mem (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ Z) (s : ℕ) (h : ∀ l, ∀ z ∈ Fil l, T z ∈ Fil (l + s))
    (k : ℕ) : ∀ t ∈ FW Fil k, (T.rTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) t ∈ FW Fil (k + s) :=
  FW_map Fil _ k _ fun k₁ k₂ z w hz hw hk => by
    rw [LinearMap.rTensor_tmul]
    exact tmul_mem_FW Fil (h _ _ hz) hw (by omega)

theorem lT_mem (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ Z) (s : ℕ) (h : ∀ l, ∀ z ∈ Fil l, T z ∈ Fil (l + s))
    (k : ℕ) : ∀ t ∈ FW Fil k, (T.lTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) t ∈ FW Fil (k + s) :=
  FW_map Fil _ k _ fun k₁ k₂ z w hz hw hk => by
    rw [LinearMap.lTensor_tmul]
    exact tmul_mem_FW Fil hz (h _ _ hw) (by omega)

theorem rT_low (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ Z) (h : ∀ l, ∀ z ∈ Fil (l + 1), T z ∈ Fil l)
    (h0 : ∀ z ∈ Fil 0, T z = 0) (k : ℕ) :
    ∀ t ∈ FW Fil (k + 1), (T.rTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) t ∈ FW Fil k :=
  FW_map Fil _ _ _ fun k₁ k₂ z w hz hw hk => by
    rw [LinearMap.rTensor_tmul]
    cases k₁ with
    | zero => rw [h0 z hz, TensorProduct.zero_tmul]; exact Submodule.zero_mem _
    | succ k₁ => exact tmul_mem_FW Fil (h _ _ hz) hw (by omega)

theorem lT_low (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ Z) (h : ∀ l, ∀ z ∈ Fil (l + 1), T z ∈ Fil l)
    (h0 : ∀ z ∈ Fil 0, T z = 0) (k : ℕ) :
    ∀ t ∈ FW Fil (k + 1), (T.lTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) t ∈ FW Fil k :=
  FW_map Fil _ _ _ fun k₁ k₂ z w hz hw hk => by
    rw [LinearMap.lTensor_tmul]
    cases k₂ with
    | zero => rw [h0 w hw, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | succ k₂ => exact tmul_mem_FW Fil hz (h _ _ hw) (by omega)

theorem rT_zero (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ Z) (h0 : ∀ z ∈ Fil 0, T z = 0) :
    ∀ t ∈ FW Fil 0, (T.rTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) t = 0 := fun t ht => by
  have := FW_map Fil (T.rTensor Z) 0 ⊥ (fun k₁ k₂ z w hz hw hk => by
    obtain rfl : k₁ = 0 := by omega
    rw [LinearMap.rTensor_tmul, h0 z hz, TensorProduct.zero_tmul]; exact Submodule.zero_mem _) t ht
  simpa using this

theorem lT_zero (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ Z) (h0 : ∀ z ∈ Fil 0, T z = 0) :
    ∀ t ∈ FW Fil 0, (T.lTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) t = 0 := fun t ht => by
  have := FW_map Fil (T.lTensor Z) 0 ⊥ (fun k₁ k₂ z w hz hw hk => by
    obtain rfl : k₂ = 0 := by omega
    rw [LinearMap.lTensor_tmul, h0 w hw, TensorProduct.tmul_zero]; exact Submodule.zero_mem _) t ht
  simpa using this

theorem rT_lT_comm (S T : Module.End ℂ Z) :
    Commute (S.rTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) (T.lTensor Z) := by
  show _ * _ = _ * _
  apply TensorProduct.ext'
  intro z w
  simp

theorem rT_mul (S T : Module.End ℂ Z) :
    ((S * T).rTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) = S.rTensor Z * T.rTensor Z := by
  apply TensorProduct.ext'
  intro z w
  simp

theorem lT_mul (S T : Module.End ℂ Z) :
    ((S * T).lTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) = S.lTensor Z * T.lTensor Z := by
  apply TensorProduct.ext'
  intro z w
  simp

end Tens

theorem freeR (n : ℕ) : ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (P1 P2 : Fin n → Fin n → Module.End ℂ W)
    (χ : W →ₗ[ℂ] ℂ) (w₀ : W) (a d : Ix n → Module.End ℂ W) (Fil : ℕ → Submodule ℂ W),
    Pair2 P1 P2 ∧ χ w₀ = 1 ∧ (∀ c e w, χ (P1 c e w) = 0) ∧ (∀ c e w, χ (P2 c e w) = 0) ∧
      FiltR (rl P1 P2) a d Fil := by
  obtain ⟨Z, _, _, M, χ, z₀, a, d, Fil, hM, h1, h0, hF⟩ := CompanionTheory.D.LK.free_all n n
  let R : Module.End ℂ Z → Module.End ℂ (Z ⊗[ℂ] Z) := fun T => T.rTensor Z
  let L : Module.End ℂ Z → Module.End ℂ (Z ⊗[ℂ] Z) := fun T => T.lTensor Z
  have hRL : ∀ S T, R S * L T = L T * R S := fun S T => (rT_lT_comm S T).eq
  have hR1 : R 1 = 1 := LinearMap.rTensor_id _ _
  have hL1 : L 1 = 1 := LinearMap.lTensor_id _ _
  have hR0 : R 0 = 0 := LinearMap.rTensor_zero _
  have hL0 : L 0 = 0 := LinearMap.lTensor_zero _
  have hRm : ∀ S T, R (S * T) = R S * R T := rT_mul
  have hLm : ∀ S T, L (S * T) = L S * L T := lT_mul
  have hRs : ∀ S T, R (S - T) = R S - R T := fun S T => LinearMap.rTensor_sub _ _
  have hLs : ∀ S T, L (S - T) = L S - L T := fun S T => LinearMap.lTensor_sub _ _
  let χ' : Z ⊗[ℂ] Z →ₗ[ℂ] ℂ := LinearMap.mul' ℂ ℂ ∘ₗ TensorProduct.map χ χ
  have hχ : ∀ z w, χ' (z ⊗ₜ w) = χ z * χ w := fun z w => by simp [χ']
  let aR : Ix n → Module.End ℂ (Z ⊗[ℂ] Z) := fun i => if i.1 then R (a i.2) + L (a i.2) else L (a i.2)
  let dR : Ix n → Module.End ℂ (Z ⊗[ℂ] Z) := fun i => if i.1 then R (d i.2) else L (d i.2) - R (d i.2)
  have hda : ∀ p q : Pos n, d p * a q = a q * d p + if p = q then 1 else 0 := fun p q => by
    rw [← hF.da p q p.1.1.2]; abel
  have hr : ∀ p q : Pos n, R (d p) * R (a q) = R (a q) * R (d p) + if p = q then 1 else 0 := fun p q => by
    have := congrArg R (hda p q)
    by_cases h : p = q
    · simpa [h, hRm, ← hR1, R, LinearMap.rTensor_add] using this
    · simpa [h, hRm, hR0, R, LinearMap.rTensor_add] using this
  have hl : ∀ p q : Pos n, L (d p) * L (a q) = L (a q) * L (d p) + if p = q then 1 else 0 := fun p q => by
    have := congrArg L (hda p q)
    by_cases h : p = q
    · simpa [h, hLm, ← hL1, L, LinearMap.lTensor_add] using this
    · simpa [h, hLm, hL0, L, LinearMap.lTensor_add] using this
  have hcomR : ∀ {S T : Module.End ℂ Z}, Commute S T → Commute (R S) (R T) := fun h => by
    show _ * _ = _ * _
    rw [← hRm, ← hRm, h.eq]
  have hcomL : ∀ {S T : Module.End ℂ Z}, Commute S T → Commute (L S) (L T) := fun h => by
    show _ * _ = _ * _
    rw [← hLm, ← hLm, h.eq]
  have hRLc : ∀ S T, Commute (R S) (L T) := fun S T => rT_lT_comm S T
  refine ⟨Z ⊗[ℂ] Z, inferInstance, inferInstance, fun c e => R (M c e), fun c e => L (M c e), χ', z₀ ⊗ₜ z₀, aR, dR,
    FW Fil, ⟨?_, ?_, ?_⟩, by simp [hχ, h1], ?_, ?_, ⟨?_, ?_, ?_, FW_mono Fil, FW_exh Fil hF.mono hF.exh, ?_, ?_, ?_, ?_⟩⟩
  · intro a' b c e
    have := congrArg R (hM a' b c e)
    rw [hRs, hRm, hRm, hRs] at this
    rw [this]
    split_ifs <;> simp [hR0]
  · intro a' b c e
    have := congrArg L (hM a' b c e)
    rw [hLs, hLm, hLm, hLs] at this
    rw [this]
    split_ifs <;> simp [hL0]
  · exact fun a' b c e => hRL _ _
  · intro c e t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z w => simp [R, hχ, h0]
    | add p q hp hq => simp only [map_add (f := _), hp, hq, add_zero]
  · intro c e t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z w => simp [L, hχ, h0]
    | add p q hp hq => simp only [map_add (f := _), hp, hq, add_zero]
  · rintro ⟨s, p⟩ ⟨t, q⟩
    have c1 := hF.a_comm p q
    cases s <;> cases t <;> simp only [aR, Bool.false_eq_true, if_false, if_true]
    · exact hcomL c1
    · exact (hRLc _ _).symm.add_right (hcomL c1) |>.symm.symm
    · exact (hRLc _ _).add_left (hcomL c1)
    · exact ((hcomR c1).add_right (hRLc _ _)).add_left ((hRLc _ _).symm.add_right (hcomL c1))
  · rintro ⟨s, p⟩ ⟨t, q⟩
    have c1 := hF.d_comm p q
    cases s <;> cases t <;> simp only [dR, Bool.false_eq_true, if_false, if_true]
    · exact ((hcomL c1).sub_right (hRLc _ _).symm).sub_left ((hRLc _ _).sub_right (hcomR c1))
    · exact (hRLc _ _).symm.sub_left (hcomR c1)
    · exact (hRLc _ _).sub_right (hcomR c1)
    · exact hcomR c1
  · rintro ⟨s, p⟩ ⟨t, q⟩
    have c1 := hRL (d p) (a q)
    have c2 := hRL (a q) (d p)
    have r1 := hr p q
    have l1 := hl p q
    cases s <;> cases t <;> simp only [aR, dR, Bool.false_eq_true, if_false, if_true, sub_mul, mul_sub, add_mul, mul_add,
      r1, l1, c1, ← c2, Prod.mk.injEq, reduceCtorEq, false_and, true_and, and_true] <;> by_cases h : p = q <;> simp [h] <;> abel
  · rintro ⟨s, p⟩ k t ht
    cases s
    · exact lT_mem Fil (a p) 1 (fun l z hz => hF.a_mem p l z hz) k t ht
    · exact Submodule.add_mem _ (rT_mem Fil (a p) 1 (fun l z hz => hF.a_mem p l z hz) k t ht)
        (lT_mem Fil (a p) 1 (fun l z hz => hF.a_mem p l z hz) k t ht)
  · rintro ⟨s, p⟩ k t ht
    have h3 : ∀ l, ∀ z ∈ Fil l, (M p.1.1 p.1.2 - a p) z ∈ Fil (l + 0) := fun l z hz => hF.r_mem p l z hz
    cases s
    · have := lT_mem Fil _ 0 h3 k t ht
      simpa [rl, aR, L, LinearMap.lTensor_sub] using this
    · have e1 := rT_mem Fil _ 0 h3 k t ht
      have e2 := lT_mem Fil _ 0 h3 k t ht
      have e3 := Submodule.add_mem _ e1 e2
      show (R (M p.1.1 p.1.2) + L (M p.1.1 p.1.2)) t - (R (a p) + L (a p)) t ∈ FW Fil k
      have e4 : (R (M p.1.1 p.1.2) + L (M p.1.1 p.1.2)) t - (R (a p) + L (a p)) t =
          R (M p.1.1 p.1.2 - a p) t + L (M p.1.1 p.1.2 - a p) t := by
        rw [hRs, hLs]
        simp only [LinearMap.add_apply, LinearMap.sub_apply]
        abel
      rw [e4]
      exact e3
  · rintro ⟨s, p⟩ k t ht
    have e1 := rT_low Fil (d p) (fun l z hz => ?_) (hF.d_zero p) k t ht
    have e2 := lT_low Fil (d p) (fun l z hz => ?_) (hF.d_zero p) k t ht
    · cases s
      · exact Submodule.sub_mem _ e2 e1
      · exact e1
    · exact hF.d_mem p l z hz
    · exact hF.d_mem p l z hz
  · rintro ⟨s, p⟩ t ht
    have e1 := rT_zero Fil (d p) (hF.d_zero p) t ht
    have e2 := lT_zero Fil (d p) (hF.d_zero p) t ht
    cases s
    · simp only [dR, Bool.false_eq_true, if_false, LinearMap.sub_apply]
      rw [show R (d p) t = 0 from e1, show L (d p) t = 0 from e2, sub_zero]
    · simpa [dR, R] using e1

end GlobalTheory.CompanionTheory.RealMult.CovR
