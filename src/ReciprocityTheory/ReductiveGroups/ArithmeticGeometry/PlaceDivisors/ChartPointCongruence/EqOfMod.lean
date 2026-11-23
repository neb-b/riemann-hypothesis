module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ChartPointCongruence.InChartSt

@[expose] public section

set_option autoImplicit false

noncomputable section

open IsLocalRing MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.Chart (jetLift jetLift_zR jet_ext)

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt

theorem smod_iff {O : Type} [CommRing O] (p : O) (n : ℕ) (u w : O) :
    u ≡ w [SMOD ((Ideal.span {p}) ^ n • ⊤ : Submodule O O)] ↔
      Ideal.Quotient.mk (Ideal.span {p ^ n}) u = Ideal.Quotient.mk _ w := by
  have h : ((Ideal.span {p}) ^ n • ⊤ : Submodule O O) = Ideal.span {p ^ n} := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  rw [SModEq.sub_mem, Ideal.Quotient.eq, h]

theorem eq_of_mod {O : Type} [CommRing O] (p : O) (hH : IsHausdorff (Ideal.span {p}) O) (u w : O)
    (h : ∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {p ^ n}) u = Ideal.Quotient.mk _ w) : u = w := by
  refine sub_eq_zero.mp (hH.haus (u - w) fun n => (smod_iff p n (u - w) 0).mpr ?_)
  rw [map_sub, map_zero, h n, sub_self]

theorem algLimSt : AlgLimSt := by
  intro T A O _ _ _ _ _ p hC a hc
  have hdown : ∀ z : A, ∀ m n : ℕ, m ≤ n → ∀ y : O,
      Ideal.Quotient.mk (Ideal.span {p ^ n}) y = a n z →
        Ideal.Quotient.mk (Ideal.span {p ^ m}) y = a m z := by
    intro z m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact fun y hy => hy
    | succ n _ ih => exact fun y hy => ih y (hc n z y hy)
  have hlim : ∀ z : A, ∃ L : O, ∀ n, Ideal.Quotient.mk (Ideal.span {p ^ n}) L = a n z := by
    intro z
    have hs : ∀ n, ∃ y : O, Ideal.Quotient.mk (Ideal.span {p ^ n}) y = a n z :=
      fun n => Ideal.Quotient.mk_surjective (a n z)
    choose y hy using hs
    obtain ⟨L, hL⟩ := hC.toIsPrecomplete.prec' y (fun {m n} hmn =>
      (smod_iff p m (y m) (y n)).mpr (by rw [hy m, hdown z m n hmn (y n) (hy n)]))
    exact ⟨L, fun n => by rw [← (smod_iff p n (y n) L).mp (hL n), hy n]⟩
  choose L hL using hlim
  have huniq : ∀ x y : O, (∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {p ^ n}) x =
      Ideal.Quotient.mk (Ideal.span {p ^ n}) y) → x = y :=
    fun x y H => eq_of_mod p hC.toIsHausdorff x y H
  refine ⟨
    { toFun := L
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_
      commutes' := ?_ }, ?_⟩
  · exact huniq _ _ fun n => by simp only [hL, map_one]
  · intro x y
    exact huniq _ _ fun n => by simp only [hL, map_mul]
  · exact huniq _ _ fun n => by simp only [hL, map_zero]
  · intro x y
    exact huniq _ _ fun n => by simp only [hL, map_add (f := _)]
  · intro t
    refine huniq _ _ fun n => ?_
    rw [hL, AlgHom.commutes]
    exact ((Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).commutes t).symm
  · intro n
    ext z
    exact hL z n

end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
