module

public import Development.EtaleCohomology.DivisorCycles.OpenCoset

@[expose] public section

-- bundled from Development.EtaleCohomology.DivisorCycles.UnipotentPartTrivial
section
open Matrix
namespace LateralTheory.DivDb.UnipotentPartTrivial
open LateralTheory.DivDb

theorem pow_vanish {C : Type} [Field C] {N : ℕ} (E : Mat C N) (h : E * E = 0) (k : ℕ) (hk : 2 ≤ k) :
    E ^ k = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, sq, h, zero_mul]

theorem series_eq {C : Type} [Field C] {N : ℕ} (E : Mat C N) (h : E * E = 0) (p : Fin N × Fin N) :
    PowerSeries.mk (fun k => ((k.factorial : C)⁻¹ • E ^ k) p.1 p.2)
      = ((Polynomial.C ((1 : Mat C N) p.1 p.2) + Polynomial.X * Polynomial.C (E p.1 p.2) : Polynomial C) :
          PowerSeries C) := by
  ext k
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe]
  rcases k with _ | _ | k
  · simp
  · simp
  · rw [pow_vanish E h _ (by omega)]
    simp

theorem Unip_of (h : ExpVan) : Unip := by
  intro C _ _ N S E hE hEE f hf
  have h0 := h C N S E hE f hf
  let g : Fin N × Fin N → Polynomial C := fun p =>
    Polynomial.C ((1 : Mat C N) p.1 p.2) + Polynomial.X * Polynomial.C (E p.1 p.2)
  have h1 : MvPolynomial.aeval g f = 0 := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_zero]
    have hc := congrArg (fun φ => φ f)
      (MvPolynomial.comp_aeval (R := C) g (Polynomial.coeToPowerSeries.algHom C))
    simp only [AlgHom.comp_apply] at hc
    simp only [Polynomial.coeToPowerSeries.algHom_apply, PowerSeries.map_id, Algebra.algebraMap_self] at hc
    simp only [id] at hc
    have hs : (fun p : Fin N × Fin N => PowerSeries.mk (fun k => ((k.factorial : C)⁻¹ • E ^ k) p.1 p.2))
        = fun i => ((g i : Polynomial C) : PowerSeries C) := funext (series_eq E hEE)
    rw [hs] at h0
    exact hc.trans h0
  have h2 := congrArg (fun q => Polynomial.aeval (1 : C) q) h1
  simp only [map_zero] at h2
  have hc := congrArg (fun φ => φ f) (MvPolynomial.comp_aeval (R := C) g (Polynomial.aeval (1 : C)))
  simp only [AlgHom.comp_apply] at hc
  rw [hc] at h2
  have h3 : (fun p : Fin N × Fin N => Polynomial.aeval (1 : C) (g p)) = fun p => (1 + E) p.1 p.2 := by
    funext p; simp [g]
  rw [h3] at h2
  unfold ev
  exact h2

end LateralTheory.DivDb.UnipotentPartTrivial
end

-- bundled from Development.EtaleCohomology.DivisorCycles.ZclMulPf
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.ZclMulPf
open LateralTheory.DivDb

theorem left_mem (hC : Chain) {C : Type} [Field C] {N : ℕ} (S : Submonoid (Mat C N))
    (s : Mat C N) (hs : s ∈ S) (y : Mat C N) (hy : y ∈ Zcl (S : Set (Mat C N))) :
    s * y ∈ Zcl (S : Set (Mat C N)) := by
  intro f hf
  obtain ⟨f', hf', -⟩ := hC C N N (LinearMap.mulLeft C s) f
  have hv : f' ∈ Van (S : Set (Mat C N)) := by
    intro t ht
    rw [hf']
    exact hf _ (S.mul_mem hs ht)
  have := hy f' hv
  rw [hf'] at this
  simpa using this

theorem mul_mem (hC : Chain) {C : Type} [Field C] {N : ℕ} (S : Submonoid (Mat C N))
    (x : Mat C N) (hx : x ∈ Zcl (S : Set (Mat C N))) (y : Mat C N) (hy : y ∈ Zcl (S : Set (Mat C N))) :
    x * y ∈ Zcl (S : Set (Mat C N)) := by
  intro f hf
  obtain ⟨f', hf', -⟩ := hC C N N (LinearMap.mulRight C y) f
  have hv : f' ∈ Van (S : Set (Mat C N)) := by
    intro t ht
    rw [hf']
    exact left_mem hC S t ht y hy f hf
  have := hx f' hv
  rw [hf'] at this
  simpa using this

end LateralTheory.DivDb.ZclMulPf

namespace LateralTheory.DivDb

theorem ZclMul_of (hC : Chain) : ZclMul := fun _C _ _N S x hx y hy =>
  LateralTheory.DivDb.ZclMulPf.mul_mem hC S x hx y hy

end LateralTheory.DivDb
end

