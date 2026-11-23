module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.Bundle0001
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.PullMulRight

@[expose] public section

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.CharSingle
section
noncomputable section
open scoped BigOperators ComplexConjugate
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

variable {ι : Type} [Fintype ι] {V V₁ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁]

theorem idx_coord (e : V ≃ₗ[ℂ] (ι → V₁)) (i₀ : ι) {M P : AddSubgroup V} {M₁ P₁ : AddSubgroup V₁}
    (hM : ∀ x, x ∈ M ↔ ∀ i, e x i ∈ M₁) (hP : ∀ x, x ∈ P ↔ ∀ i, e x i ∈ P₁) (h : relIdx M P ≠ 0) :
    relIdx M₁ P₁ ≠ 0 := by
  let f : V₁ →+ V := AddMonoidHom.mk' (fun x => e.symm (Pi.single i₀ x)) (fun x y => by
    rw [Pi.single_add, map_add (f := _)])
  have hcomap : ∀ (N : AddSubgroup V) (N₁ : AddSubgroup V₁), (∀ x, x ∈ N ↔ ∀ i, e x i ∈ N₁) →
      N₁ = N.comap f := by
    intro N N₁ hN
    ext x
    rw [AddSubgroup.mem_comap, hN]
    show x ∈ N₁ ↔ ∀ i, e (e.symm (Pi.single i₀ x)) i ∈ N₁
    simp only [LinearEquiv.apply_symm_apply]
    constructor
    · intro hx i
      by_cases hi : i = i₀
      · subst hi
        simpa using hx
      · rw [Pi.single_eq_of_ne hi]
        exact N₁.zero_mem
    · intro h
      simpa using h i₀
  unfold relIdx at *
  rw [hcomap M M₁ hM, hcomap P P₁ hP]
  exact AddSubgroup.relIndex_comap_ne_zero f h

variable {e : V ≃ₗ[ℂ] (ι → V₁)} {H : Sesq V} {H₁ : Sesq V₁} {α : V → ℂ} {α₁ : V₁ → ℂ}
  {Λ : AddSubgroup V} {Λ₁ : AddSubgroup V₁} {δ Ae : V ≃ₗ[ℂ] V} {δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁}

theorem Copies.mem_img (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (x : V) :
    x ∈ imgLat (δ : V →ₗ[ℂ] V) Λ ↔ ∀ i, e x i ∈ imgLat (δ₁ : V₁ →ₗ[ℂ] V₁) Λ₁ := by
  have key : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (d : W ≃ₗ[ℂ] W) (L : AddSubgroup W) (z : W),
      z ∈ imgLat (d : W →ₗ[ℂ] W) L ↔ d.symm z ∈ L := by
    intro W _ _ d L z
    simp only [imgLat, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      exact ⟨d.symm z, hz, by simp⟩
  rw [key, c.lat]
  apply forall_congr'
  intro i
  rw [key]
  have hmap := c.map (δ.symm x) i
  rw [LinearEquiv.apply_symm_apply] at hmap
  rw [hmap, LinearEquiv.symm_apply_apply]

theorem Copies.form_single (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (i₀ : ι) (x : V₁) (y : V) :
    H (e.symm (Pi.single i₀ x)) y = H₁ x (e y i₀) := by
  rw [c.form, LinearEquiv.apply_symm_apply, Finset.sum_eq_single i₀]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem Copies.single_mem (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (i₀ : ι) {x : V₁} (hx : x ∈ Λ₁) :
    e.symm (Pi.single i₀ x) ∈ Λ := by
  rw [c.lat]
  intro i
  rw [LinearEquiv.apply_symm_apply]
  by_cases hi : i = i₀
  · subst hi
    simpa using hx
  · rw [Pi.single_eq_of_ne hi]
    exact Λ₁.zero_mem

theorem Copies.char_single (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (h0 : α₁ 0 = 1) (i₀ : ι) {x : V₁} (hx : x ∈ Λ₁) :
    α (e.symm (Pi.single i₀ x)) = α₁ x := by
  rw [c.char _ (c.single_mem i₀ hx), LinearEquiv.apply_symm_apply, Finset.prod_eq_single i₀]
  · simp
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, h0]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem Copies.unitaryData₁ (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (i₀ : ι) (hU : UnitaryData H Λ α δ Ae)
    (hH₁ : IsHerm H₁) (hP₁ : IsPosDef H₁) (hI₁ : IsIsom H₁ H₁ (δ₁ : V₁ →ₗ[ℂ] V₁)) (hA₁ : ∀ x, Ae₁ x = x - δ₁.symm x)
    (h0 : α₁ 0 = 1) (hαδ : ∀ x, α₁ (δ₁ x) = α₁ x) : UnitaryData H₁ Λ₁ α₁ δ₁ Ae₁ := by
  have hs : ∀ x : V₁, e (e.symm (Pi.single i₀ x)) i₀ = x := fun x => by simp
  have hform : ∀ x y : V₁, H (e.symm (Pi.single i₀ x)) (e.symm (Pi.single i₀ y)) = H₁ x y := by
    intro x y
    rw [c.form_single, hs]
  have hadd : ∀ x y : V₁, e.symm (Pi.single i₀ (x + y)) = e.symm (Pi.single i₀ x) + e.symm (Pi.single i₀ y) := by
    intro x y
    rw [Pi.single_add, map_add (f := _)]
  have hδs : ∀ y : V₁, δ (e.symm (Pi.single i₀ y)) = e.symm (Pi.single i₀ (δ₁ y)) := by
    intro y
    apply e.injective
    funext i
    rw [c.map, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    by_cases hi : i = i₀
    · subst hi
      simp
    · simp [Pi.single_eq_of_ne hi]
  have himg_single : ∀ x : V₁, x ∈ imgLat (δ₁ : V₁ →ₗ[ℂ] V₁) Λ₁ →
      e.symm (Pi.single i₀ x) ∈ imgLat (δ : V →ₗ[ℂ] V) Λ := by
    intro x hx
    rw [c.mem_img]
    intro i
    rw [LinearEquiv.apply_symm_apply]
    by_cases hi : i = i₀
    · subst hi
      simpa using hx
    · rw [Pi.single_eq_of_ne hi]
      exact (imgLat _ Λ₁).zero_mem
  have hαimg : ∀ x : V₁, x ∈ imgLat (δ₁ : V₁ →ₗ[ℂ] V₁) Λ₁ → α (e.symm (Pi.single i₀ x)) = α₁ x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    show α (e.symm (Pi.single i₀ (δ₁ y))) = α₁ (δ₁ y)
    rw [← hδs, hU.inv _ (c.single_mem i₀ hy), c.char_single h0 i₀ hy, hαδ]
  refine ⟨hH₁, hP₁, ?_, ⟨?_, ?_⟩, hI₁, ⟨?_, ?_⟩, fun x _ => hαδ x, ?_, ?_, hA₁⟩
  · ext x
    constructor
    · intro hx
      have hv : e.symm (Pi.single i₀ x) ∈ Λ := by
        rw [← hU.selfDual]
        intro y hy
        obtain ⟨m, hm⟩ := hx (e y i₀) ((c.lat y).1 hy i₀)
        refine ⟨m, ?_⟩
        simp only [altE] at hm ⊢
        rw [c.form_single]
        exact hm
      have h1 := (c.lat _).1 hv i₀
      rwa [hs] at h1
    · intro hx y hy
      have h1 : e.symm (Pi.single i₀ x) ∈ dualLat H Λ := by
        rw [hU.selfDual]
        exact c.single_mem i₀ hx
      obtain ⟨m, hm⟩ := h1 _ (c.single_mem i₀ hy)
      refine ⟨m, ?_⟩
      simp only [altE] at hm ⊢
      rw [hform] at hm
      exact hm
  · intro x hx
    rw [← c.char_single h0 i₀ hx]
    exact hU.semi.1 _ (c.single_mem i₀ hx)
  · intro x hx y hy
    rw [← c.char_single h0 i₀ hx, ← c.char_single h0 i₀ hy, ← c.char_single h0 i₀ (Λ₁.add_mem hx hy), hadd,
      hU.semi.2 _ (c.single_mem i₀ hx) _ (c.single_mem i₀ hy)]
    simp only [altE, hform]
  · intro x hx
    rw [← hαimg x hx]
    exact hU.semi'.1 _ (himg_single x hx)
  · intro x hx y hy
    rw [← hαimg x hx, ← hαimg y hy, ← hαimg (x + y) ((imgLat _ Λ₁).add_mem hx hy), hadd,
      hU.semi'.2 _ (himg_single x hx) _ (himg_single y hy)]
    simp only [altE, hform]
  · exact idx_coord e i₀ c.mem_img c.lat hU.idx₁
  · exact idx_coord e i₀ c.lat c.mem_img hU.idx₂

theorem alpha_mult {H : Sesq V} {Λ : AddSubgroup V} {δ : V ≃ₗ[ℂ] V} {ℓ ℓ' σ : V →ₗ[ℂ] V} {n : ℕ}
    (hM : Multipliers H Λ δ ℓ ℓ' σ n) (c : ℝ) (α : V → ℂ) (hα : ∀ x, α x = (-1 : ℂ) ^ round (c * (H x x).re))
    (hq : ∀ x ∈ Λ, ∃ m : ℤ, c * (H x x).re = (m : ℝ)) {x : V} (hx : x ∈ Λ) : α (ℓ x) = α x := by
  obtain ⟨m1, hm1⟩ := hq x hx
  obtain ⟨m2, hm2⟩ := hq (σ x) (hM.sΛ x hx)
  obtain ⟨m3, hm3⟩ := hq (x + σ x) (Λ.add_mem hx (hM.sΛ x hx))
  have hexp : H (x + σ x) (x + σ x) = H x x + H x (σ x) + H x (σ x) + H (σ x) (σ x) := by
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [hM.sadj x x]
    ring
  have hk : c * (H x (σ x)).re * 2 = ((m3 - m1 - m2 : ℤ) : ℝ) := by
    rw [hexp] at hm3
    simp only [Complex.add_re] at hm3
    push_cast
    linarith
  have hl : H (ℓ x) (ℓ x) = -H x x + ((4 * n : ℕ) : ℂ) * H x (σ x) := by
    rw [hM.adj, hM.rel, map_add (f := _), map_neg, map_nsmul, nsmul_eq_mul]
  have hq' : c * (H (ℓ x) (ℓ x)).re = ((m1 + 2 * (-m1 + (n : ℤ) * (m3 - m1 - m2)) : ℤ) : ℝ) := by
    rw [hl]
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    push_cast
    push_cast at hk
    nlinarith [hm1, hk]
  rw [hα, hα, hq', hm1, round_intCast, round_intCast, zpow_add₀ (by norm_num), zpow_mul]
  simp

end Formalism.L2.PairingIndexBounds.Eq.J
end
end

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.FinrankRow
section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def phiU {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) :
    TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' :=
  phiL (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (Matrix.mem_unitaryGroup_iff'.mp γ.2) (Matrix.mem_unitaryGroup_iff.mp γ.2)
    (Matrix.mem_unitaryGroup_iff'.mp γ'.2) (Matrix.mem_unitaryGroup_iff.mp γ'.2)

def cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix.unitaryGroup (Fin n) D.host.E :=
  ⟨(star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff]
    have h : star ((star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ) = (γ : Matrix (Fin n) (Fin n) D.host.E)ᵀ := by
      ext i j
      simp [Matrix.star_apply, Matrix.transpose_apply]
    rw [h, ← Matrix.transpose_mul, Matrix.mem_unitaryGroup_iff.mp γ.2, Matrix.transpose_one]⟩

theorem map_row {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) (x : TaylorLogMetric.VC D N N') (i : Fin N') :
    rowE D N N' (phiU γ 1 x) i = phiU γ 1 (rowE D N N' x i) := by
  funext τ a j
  show (gM (1 : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) * (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j =
    (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (rowE D N N' x i τ) *
      (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) a j
  rw [gM_one, gM_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_apply, Matrix.mul_apply]
  rfl

theorem map_col {N N' : ℕ} (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (x : TaylorLogMetric.VC D N N') (j : Fin N) :
    colE D N N' (phiU 1 γ' x) j = phiU (cjU γ') 1 (colE D N N' x j) := by
  funext τ a i
  show (gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) * (gM (1 : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j =
    (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (colE D N N' x j τ) *
      (gM ((star (γ' : Matrix (Fin N') (Fin N') D.host.E))ᵀ) τ)ᴴ) a i
  rw [gM_one, gM_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  show TaylorLogMetric.embT D τ ((γ' : Matrix (Fin N') (Fin N') D.host.E) i k) * x τ k j =
    x τ k j * star (TaylorLogMetric.embT D τ (star ((γ' : Matrix (Fin N') (Fin N') D.host.E) i k)))
  rw [embT_star', star_star, mul_comm]

theorem det_gM {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : (gM M τ).det = TaylorLogMetric.embT D τ M.det :=
  ((TaylorLogMetric.embT D τ).map_det M).symm

theorem gM_sub {n : ℕ} (A C : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : gM (A - C) τ = gM A τ - gM C τ := by
  ext i j
  simp [gM]

theorem nofix {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (hγ : (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)).det ≠ 0) (y : TaylorLogMetric.VC D N N') (h : (phiU γ 1).symm y = y) : y = 0 := by
  funext τ
  have h1 : (gM (1 : Matrix (Fin N') (Fin N') D.host.E) τ)ᴴ * Matrix.of (y τ) * gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ =
      Matrix.of (y τ) := congrFun h τ
  rw [gM_one, Matrix.conjTranspose_one, Matrix.one_mul] at h1
  have h2 : Matrix.of (y τ) * gM (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)) τ = 0 := by
    rw [gM_sub, gM_one, Matrix.mul_sub, Matrix.mul_one, h1, sub_self]
  have hu : IsUnit (gM (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)) τ).det := by
    rw [det_gM]
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero _).mpr hγ)
  have h3 := Matrix.mul_nonsing_inv_cancel_right _ (Matrix.of (y τ)) hu
  rw [h2, Matrix.zero_mul] at h3
  exact h3.symm

theorem det_cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E) :
    ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).det =
      star (γ : Matrix (Fin n) (Fin n) D.host.E).det := by
  show ((star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ).det = _
  rw [Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]

theorem ne_cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E)
    (hγ : (1 - (γ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0) :
    (1 - ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 := by
  have h : (1 - ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) =
      (star (1 - (γ : Matrix (Fin n) (Fin n) D.host.E)))ᵀ := by
    rw [star_sub, star_one, Matrix.transpose_sub, Matrix.transpose_one]
    rfl
  rw [h, Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
  exact star_ne_zero.mpr hγ

theorem det_row {N : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) :
    LinearMap.det ((phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1) : TaylorLogMetric.VC D N 1 →ₗ[ℂ] TaylorLogMetric.VC D N 1) =
      ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det) := by
  let g : D.what₂.Tau → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) := fun τ =>
    Matrix.toLin' (((gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ)ᵀ)
  let f : D.what₂.Tau → (Fin 1 → Fin N → ℂ) →ₗ[ℂ] (Fin 1 → Fin N → ℂ) := fun τ =>
    LinearMap.pi fun a => (g τ).comp (LinearMap.proj a)
  have e : ((phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1) : TaylorLogMetric.VC D N 1 →ₗ[ℂ] TaylorLogMetric.VC D N 1) =
      LinearMap.pi fun τ => (f τ).comp (LinearMap.proj τ) := by
    refine LinearMap.ext fun x => ?_
    funext τ a j
    show (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (x τ) * (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) a j =
      (((gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ)ᵀ *ᵥ (x τ a)) j
    rw [gM_one, Matrix.one_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [e, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun τ _ => ?_
  show LinearMap.det (LinearMap.pi fun a => (g τ).comp (LinearMap.proj a)) = _
  rw [LinearMap.det_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, LinearMap.det_toLin',
    Matrix.det_transpose, Matrix.det_conjTranspose, det_gM, embT_star']

theorem finrank_row (N : ℕ) : Module.finrank ℂ (TaylorLogMetric.VC D N 1) = Fintype.card D.what₂.Tau * N := by
  simp [Module.finrank_pi_fintype]

end Formalism.L2.PairingIndexBounds.Eq.J
end
end

