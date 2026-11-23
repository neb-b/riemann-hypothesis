module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0007

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BoxFundX
section
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem box_fundX {ι P : Type} [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (A : P → AddSubgroup (ι → ℂ)) (F : P → Set (ι → ℂ)) (hFd : ∀ p (v : ι → ℂ), ∃! a : A p, (a : ι → ℂ) + v ∈ F p)
    (x : ι → P → ℂ) :
    ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ A p) ∧
      lawX BX γ x ∈ {y : ι → P → ℂ | ∀ p, (fun v => y v p) ∈ F p} := by
  classical
  let w : P → (ι → P → ℂ) → (ι → ℂ) := fun p γ => τ p γ + fun v => x v p + BX p (γ v) (x v)
  let c : P → (ι → P → ℂ) → (ι → ℂ) := fun p γ =>
    ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ
  have hloc : ∀ p (γ γ' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, γ v q = γ' v q) → c p γ = c p γ' := by
    intro p γ γ' hg
    have h1 : τ p γ = τ p γ' := hτ p γ γ' hg
    have h2 : w p γ = w p γ' := by
      show (τ p γ + fun v => x v p + BX p (γ v) (x v)) = τ p γ' + fun v => x v p + BX p (γ' v) (x v)
      rw [h1]
      congr 1
      funext v
      rw [hBd p (γ v) (γ' v) (x v) (x v) (fun q hq => ⟨hg q hq v, rfl⟩)]
    have hch : ∀ u u' : ι → ℂ, u = u' →
        ((hFd p u).exists.choose : ι → ℂ) = ((hFd p u').exists.choose : ι → ℂ) := by
      rintro u _ rfl
      rfl
    show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = ((hFd p (w p γ')).exists.choose : ι → ℂ) + τ p γ'
    rw [h1, hch _ _ h2]
  have key : ∀ p (γ : ι → P → ℂ), ((fun v => γ v p) - τ p γ ∈ A p ∧ (fun v => lawX BX γ x v p) ∈ F p) ↔
      (fun v => γ v p) = c p γ := by
    intro p γ
    obtain ⟨a, ha, huniq⟩ := hFd p (w p γ)
    have hc : c p γ = (a : ι → ℂ) + τ p γ := by
      show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = (a : ι → ℂ) + τ p γ
      rw [huniq _ (hFd p (w p γ)).exists.choose_spec]
    have hlaw : (fun v => lawX BX γ x v p) = ((fun v => γ v p) - τ p γ) + w p γ := by
      funext v
      simp only [lawX, w, Pi.add_apply, Pi.sub_apply]
      ring
    rw [hc, hlaw]
    constructor
    · rintro ⟨hA, hF⟩
      have e := congrArg Subtype.val (huniq ⟨_, hA⟩ hF)
      simp only at e
      rw [← e]
      abel
    · intro hg
      rw [hg, add_sub_cancel_right]
      exact ⟨a.2, ha⟩
  let Φ : (ι → P → ℂ) → (ι → P → ℂ) := fun γ v p => c p γ v
  have hit : ∀ k (γ γ' : ι → P → ℂ), ∀ p, h p < k → ∀ v, (Φ^[k] γ) v p = (Φ^[k] γ') v p := by
    intro k
    induction k with
    | zero => intro γ γ' p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ k ih =>
      intro γ γ' p hp v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show c p (Φ^[k] γ) v = c p (Φ^[k] γ') v
      rw [hloc p _ _ (fun q hq v => ih γ γ' q (by omega) v)]
  have hN : ∀ p, h p < Finset.univ.sup h + 1 := fun p =>
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p))
  have hcond : ∀ γ : ι → P → ℂ, ((∀ p, (fun v => γ v p) - τ p γ ∈ A p) ∧
      lawX BX γ x ∈ {y : ι → P → ℂ | ∀ p, (fun v => y v p) ∈ F p}) ↔ Φ γ = γ := by
    intro γ
    rw [Set.mem_setOf_eq, ← forall_and, forall_congr' (fun p => key p γ)]
    constructor
    · intro H
      funext v p
      exact (congrFun (H p) v).symm
    · intro H p
      funext v
      exact (congrFun (congrFun H v) p).symm
  refine ⟨Φ^[Finset.univ.sup h + 1] 0, (hcond _).2 ?_, fun γ hγ => ?_⟩
  · rw [← Function.iterate_succ_apply' Φ _ 0, Function.iterate_succ_apply]
    funext v p
    exact hit _ (Φ 0) 0 p (hN p) v
  · have e1 : Φ^[Finset.univ.sup h + 1] γ = γ := Function.iterate_fixed ((hcond γ).1 hγ) _
    funext v p
    calc γ v p = (Φ^[Finset.univ.sup h + 1] γ) v p := by rw [e1]
      _ = _ := hit _ γ 0 p (hN p) v

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxClose
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Proj

variable {A : Type*} [CommRing A] {n : ℕ}

theorem entIn_transpose {J : AddSubgroup A} {X : Matrix (Fin n) (Fin n) A} (h : EntIn J X) : EntIn J X.transpose :=
  fun i j => h j i

theorem entIn_smul {J : AddSubgroup A} (e : A) (hJ : ∀ x ∈ J, e * x ∈ J) {X : Matrix (Fin n) (Fin n) A}
    (h : EntIn J X) : EntIn J (e • X) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact hJ _ (h i j)

theorem proj_inv (f : Fin n → ℕ) (hf : ∀ i, f i < n) {J : AddSubgroup A} (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J)
    (e : A) (he : e * e = e) (x : GL (Fin n) A)
    (hlow : ∀ i j, f i ≤ f j → ((x : Matrix (Fin n) (Fin n) A) - 1) i j = 0)
    (hx : EntIn J (e • ((x : Matrix (Fin n) (Fin n) A) - 1))) :
    EntIn J (e • (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1)) := by
  set X := (x : Matrix (Fin n) (Fin n) A) - 1 with hXd
  set Y := ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1 with hYd
  have hx1 : (x : Matrix (Fin n) (Fin n) A) = 1 + X := by rw [hXd]; abel
  have hy1 : ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 + Y := by rw [hYd]; abel
  have hXY : X + Y + X * Y = 0 := by
    have h1 : (x : Matrix (Fin n) (Fin n) A) * ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hx1, hy1] at h1
    have h2 : (1 + X) * (1 + Y) = (1 : Matrix (Fin n) (Fin n) A) + (X + Y + X * Y) := by
      simp only [add_mul, mul_add, one_mul, mul_one]; abel
    rw [h2] at h1
    simpa using h1
  have hYX : Y + X + Y * X = 0 := by
    have h1 : ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * (x : Matrix (Fin n) (Fin n) A) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hx1, hy1] at h1
    have h2 : (1 + Y) * (1 + X) = (1 : Matrix (Fin n) (Fin n) A) + (Y + X + Y * X) := by
      simp only [add_mul, mul_add, one_mul, mul_one]; abel
    rw [h2] at h1
    simpa using h1
  have hv : (1 + e • X) * (1 + e • Y) = 1 := by
    rw [add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]
    have : e • Y + (e • X + e • (X * Y)) = e • (X + Y + X * Y) := by rw [smul_add, smul_add]; abel
    rw [add_assoc, this, hXY, smul_zero, add_zero]
  have hv' : (1 + e • Y) * (1 + e • X) = 1 := by
    rw [add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]
    have : e • X + (e • Y + e • (Y * X)) = e • (Y + X + Y * X) := by rw [smul_add, smul_add]; abel
    rw [add_assoc, this, hYX, smul_zero, add_zero]
  let y : GL (Fin n) A := ⟨1 + e • X, 1 + e • Y, hv, hv'⟩
  have hyv : (y : Matrix (Fin n) (Fin n) A) - 1 = e • X := by simp [y]
  have hyi : ((y⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1 = e • Y := by
    show (1 + e • Y) - 1 = e • Y
    simp
  have key := inv_sub_one f hf hJ y (fun i j h => by
      rw [hyv, Matrix.smul_apply, hlow i j h, smul_zero]) (by rw [hyv]; exact hx)
  rw [hyi] at key
  exact key.1

end Proj

section Close

open Formalism.MainNotions.S.Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {p : HeightOneSpectrum (𝓞 F)} {L : LocAt F E sig p} {n : ℕ}

theorem latS_of_eq {c c' t : L.Fp} (h : c' = c * t) (ht : t ∈ 𝒪[L.Fp]) {x : L.Ep} (hx : x ∈ latS L c') :
    x ∈ latS L c := by
  rw [h] at hx; exact latS_mono ht hx

theorem entIn_latS_of_eq {c c' t : L.Fp} (h : c' = c * t) (ht : t ∈ 𝒪[L.Fp]) {X : Matrix (Fin n) (Fin n) L.Ep}
    (hX : EntIn (latS L c') X) : EntIn (latS L c) X := fun i j => latS_of_eq h ht (hX i j)

end Close

end Formalism.L2.SG.Pf.ProdEApprox
end
end

