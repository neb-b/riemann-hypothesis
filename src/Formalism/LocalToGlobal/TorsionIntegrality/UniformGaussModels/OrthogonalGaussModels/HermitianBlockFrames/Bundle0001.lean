module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.IsUnitaryK
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP

def cmTheta (b : ℤ) (d : ℕ) : ℂ := ((b : ℂ) + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2

def cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) : PeriodPair where
  ω₁ := (a : ℂ)
  ω₂ := cmTheta b d
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [cmTheta] at him hre
    have ht : t = 0 := by
      rcases him with h1 | h1
      · exact h1
      · exact absurd h1 (by positivity)
    subst ht
    simp at hre
    refine ⟨?_, rfl⟩
    rcases hre with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)

def scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have h := L.indep
    rw [LinearIndependent.pair_iff] at h ⊢
    intro s t hst
    apply h s t
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.mp this).resolve_left hc

def area (L : PeriodPair) : ℝ := |(conj L.ω₁ * L.ω₂).im|

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

abbrev Sesq (V : Type*) [AddCommGroup V] [Module ℂ V] := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ

def altE (H : Sesq V) (x y : V) : ℝ := (H x y).im

def dualLat (H : Sesq V) (Λ : AddSubgroup V) : AddSubgroup V where
  carrier := {x | ∀ y ∈ Λ, ∃ m : ℤ, altE H x y = (m : ℝ)}
  zero_mem' := fun y _ => ⟨0, by simp [altE]⟩
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨m, hm⟩ := ha y hy
    obtain ⟨k, hk⟩ := hb y hy
    exact ⟨m + k, by simp only [altE] at hm hk ⊢; simp [hm, hk]⟩
  neg_mem' := by
    intro a ha y hy
    obtain ⟨m, hm⟩ := ha y hy
    exact ⟨-m, by simp only [altE] at hm ⊢; simp [hm]⟩

def IsSelfDual (H : Sesq V) (Λ : AddSubgroup V) : Prop := dualLat H Λ = Λ

def relIdx (Λ₁ Λ₂ : AddSubgroup V) : ℕ := Λ₁.relIndex Λ₂

def IsIsom {W : Type*} [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W) (g : V →ₗ[ℂ] W) : Prop :=
  ∀ x y, H' (g x) (g y) = H x y

def imgLat {W : Type*} [AddCommGroup W] [Module ℂ W] (g : V →ₗ[ℂ] W) (Λ : AddSubgroup V) : AddSubgroup W :=
  Λ.map g.toAddMonoidHom

end General

section Coordinates

variable {n : Type*} [Fintype n]

def matH (h : Matrix n n ℂ) : Sesq (n → ℂ) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => ∑ i, ∑ j, z i * h i j * conj (w j))
    (by intro a b c; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (by intro c a b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc])
    (by intro a b c; simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)

def stdH (L : PeriodPair) (n : Type*) [Fintype n] [DecidableEq n] : Sesq (n → ℂ) :=
  matH (((area L : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ))

def stdLat (L : PeriodPair) (n : Type*) : AddSubgroup (n → ℂ) :=
  AddSubgroup.pi Set.univ fun _ => L.lattice.toAddSubgroup

def slice (a : Fin 4) (z : Fin 4 × n → ℂ) : n → ℂ := fun i => z (a, i)

def blk4 (h : Matrix n n ℂ) : Matrix (Fin 4 × n) (Fin 4 × n) ℂ :=
  fun w w' => if w.1 = w'.1 then h w.2 w'.2 else 0

def pow4 (Λ : AddSubgroup (n → ℂ)) : AddSubgroup (Fin 4 × n → ℂ) where
  carrier := {z | ∀ a, slice a z ∈ Λ}
  zero_mem' := fun _ => Λ.zero_mem
  add_mem' := fun hx hy a => Λ.add_mem (hx a) (hy a)
  neg_mem' := fun hx a => Λ.neg_mem (hx a)

end Coordinates

def cmL (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) : PeriodPair :=
  scalePair (cmPair a b d ha hd) lam hlam

def CmOK (a : ℕ) (b c : ℤ) (d : ℕ) : Prop := 4 * (a : ℤ) * c = b ^ 2 + d ∧ Odd a ∧ d % 8 = 7 ∧ d.Prime


open Classical in
def MaximalUnramifiedExtension (l : ℕ) [Fact l.Prime] : Subfield ℂ_[l] :=
  (Subfield.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}).topologicalClosure

def UnrOK (K : Type) [NormedField K] (p : ℕ) (σ : K →+* K) : Prop :=
  p.Prime ∧ 2 < p ∧ ‖(p : K)‖ = (p : ℝ)⁻¹ ∧ (∀ a : K, a ≠ 0 → ∃ k : ℤ, ‖a‖ = (p : ℝ) ^ k) ∧
    ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹

def IsUnitaryK {K : Type} [NormedField K] (σ : K →+* K) {m : Type} [Fintype m] [DecidableEq m]
    (γ : Matrix m m K) : Prop :=
  (∀ a b, ‖γ a b‖ ≤ 1 ∧ σ (σ (γ a b)) = γ a b) ∧
  (∀ a b, ∑ k, σ (γ k a) * γ k b = if a = b then 1 else 0)

def IsLatH (L : PeriodPair) (b : ℤ) (d : ℕ) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : Prop :=
  IsIsom (matH (blk4 h)) (stdH L (Fin 4 × n)) (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
  IsSelfDual (matH h) Λ ∧ (∀ x ∈ Λ, cmTheta b d • x ∈ Λ) ∧
  relIdx (stdLat L (Fin 4 × n)) (imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 ∧
  relIdx (imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) (stdLat L (Fin 4 × n)) ≠ 0

def IsFrameH {l : ℕ} [Fact l.Prime] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (ι : ℂ ≃+* ℂ_[l]) {n : Type} [Fintype n]
    [DecidableEq n] (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]) : Prop :=
  IsUnitaryK σ γ ∧ ∀ (i' : Fin 4) (i : n) (w : Fin 4 × n),
    ∑ j, B' i j * ((γ (i', j) w : MaximalUnramifiedExtension l) : ℂ_[l]) = ι (g.symm (Pi.single w 1) (i', i))

def HermFrame : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ (ι : ℂ ≃+* ℂ_[l]) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l), UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (g₀ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∃ (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]), IsFrameH σ ι g₁ γ B'

end Formalism.L2.Th1.Top.FrP
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.LocAbs
section
noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac

structure JSetup (K : Type*) [Field K] where
  σ : K →+* K
  O : Subring K
  p : K
  hp0 : p ≠ 0
  hpO : p ∈ O
  hσp : σ p = p
  hσO : ∀ x ∈ O, σ x ∈ O
  hσσ : ∀ x ∈ O, σ (σ x) = x
  hinv : ∀ x ∈ O, (¬ ∃ y ∈ O, x = p * y) → x⁻¹ ∈ O
  hone : ¬ ∃ y ∈ O, (1 : K) = p * y
  htwo : (2 : K)⁻¹ ∈ O
  h2 : (2 : K) ≠ 0
  hnorm : ∀ u ∈ O, σ u = u → (¬ ∃ y ∈ O, u = p * y) → ∃ w ∈ O, σ w * w = u
  hsep : ∀ x ∈ O, x ≠ 0 → ∃ N : ℕ, ¬ ∃ y ∈ O, x = p ^ N * y

variable {K : Type*} [Field K] (S : JSetup K)

namespace JSetup

def NU (x : K) : Prop := ∃ y ∈ S.O, x = S.p * y

theorem NU_zero : S.NU 0 := ⟨0, S.O.zero_mem, by rw [mul_zero]⟩

theorem NU_add {x y : K} (hx : S.NU x) (hy : S.NU y) : S.NU (x + y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a + b, S.O.add_mem ha hb, by rw [mul_add]⟩

theorem NU_neg {x : K} (hx : S.NU x) : S.NU (-x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨-a, S.O.neg_mem ha, by rw [mul_neg]⟩

theorem NU_mul {x z : K} (hz : z ∈ S.O) (hx : S.NU x) : S.NU (z * x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨z * a, S.O.mul_mem hz ha, by ring⟩

theorem NU_sum {ι : Type*} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, S.NU (f i)) : S.NU (∑ i ∈ s, f i) := by
  exact Finset.sum_induction _ S.NU (fun _ _ => S.NU_add) S.NU_zero h

theorem ne_zero_of_not_NU {x : K} (hx : ¬ S.NU x) : x ≠ 0 := by
  rintro rfl
  exact hx S.NU_zero

theorem NU_σ {x : K} (hx : S.NU x) : S.NU (S.σ x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨S.σ a, S.hσO a ha, by rw [map_mul, S.hσp]⟩

theorem not_NU_σ {x : K} (hxO : x ∈ S.O) (hx : ¬ S.NU x) : ¬ S.NU (S.σ x) := by
  intro h
  apply hx
  have h2 := S.NU_σ h
  rwa [S.hσσ x hxO] at h2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IntV (x : ι → K) : Prop := ∀ i, x i ∈ S.O

def IntM (Γ : Matrix ι ι K) : Prop := ∀ i j, Γ i j ∈ S.O

def cv (x : ι → K) : ι → K := fun i => S.σ (x i)

def Herm (Γ : Matrix ι ι K) : Prop := ∀ i j, S.σ (Γ i j) = Γ j i

def hf (Γ : Matrix ι ι K) (x y : ι → K) : K := S.cv x ⬝ᵥ (Γ *ᵥ y)

def UM (Γ : Matrix ι ι K) : Prop :=
  ∀ x : ι → K, S.IntV x → (∀ i, S.NU ((Γ *ᵥ x) i)) → ∃ x', S.IntV x' ∧ Γ *ᵥ x = S.p • (Γ *ᵥ x')

theorem IntV_mulVec {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) {x : ι → K} (hx : S.IntV x) : S.IntV (Γ *ᵥ x) := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact S.O.sum_mem fun j _ => S.O.mul_mem (hΓ i j) (hx j)

theorem IntV_cv {x : ι → K} (hx : S.IntV x) : S.IntV (S.cv x) := fun i => S.hσO (x i) (hx i)

theorem hf_mem {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) {x y : ι → K} (hx : S.IntV x) (hy : S.IntV y) :
    S.hf Γ x y ∈ S.O := by
  unfold hf
  simp only [dotProduct]
  exact S.O.sum_mem fun i _ => S.O.mul_mem (S.IntV_cv hx i) (S.IntV_mulVec hΓ hy i)

theorem hf_swap {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) (hH : S.Herm Γ) {x y : ι → K} (hx : S.IntV x)
    (hy : S.IntV y) : S.hf Γ y x = S.σ (S.hf Γ x y) := by
  unfold hf cv
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [S.hσσ _ (hx _), hH]
  ring

theorem σ_mulVec {Γ : Matrix ι ι K} (hH : S.Herm Γ) (a : ι → K) (i : ι) :
    S.σ ((Γ *ᵥ a) i) = (S.cv a ᵥ* Γ) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, cv, hH i]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem σ_vecMul {Γ : Matrix ι ι K} (hH : S.Herm Γ) {a : ι → K} (ha : S.IntV a) (j : ι) :
    S.σ ((S.cv a ᵥ* Γ) j) = (Γ *ᵥ a) j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, cv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [S.hσσ _ (ha i), hH i j, mul_comm]

end JSetup

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
end
end

