module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
namespace GlobalTheory.Ex.TwNest
section
variable {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (u : Oˣ)

def Mult (t : N.X → Oˣ) (g : N.Gt) (g' : (N.twist β u).Gt) : Prop :=
  g'.b = g.b ∧ ∀ z : N.X, g'.s z = g.s z * t z

variable {β u}

theorem Mult.mul {t t' : N.X → Oˣ} {g h : N.Gt} {g' h' : (N.twist β u).Gt} (a : Mult β u t g g')
    (b : Mult β u t' h h') : Mult β u (fun z => t z * t' z) (g * h) (g' * h') := by
  refine ⟨congrArg₂ (fun x y : N.A => x * y) a.1 b.1, fun z => ?_⟩
  change g'.s z * h'.s z / N.θ (N.c z) g'.b h'.b = g.s z * h.s z / N.θ (N.c z) g.b h.b * (t z * t' z)
  rw [a.1, b.1, a.2, b.2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem Mult.pow {t : N.X → Oˣ} {g : N.Gt} {g' : (N.twist β u).Gt} (a : Mult β u t g g') (n : ℕ) :
    Mult β u (fun z => t z ^ n) (g ^ n) (g' ^ n) := by
  induction n with
  | zero => exact ⟨rfl, fun z => by simp only [pow_zero, _root_.mul_one]; rfl⟩
  | succ n ih => simp only [pow_succ]; exact ih.mul a

theorem qEq_of_twRel {s : Oˣ} {j : ℕ} (hs : s ^ j = u) {p p' : N.QT j} {P P' : (N.twist β u).QT j}
    (a : TwRel β u s p P) (b : TwRel β u s p' P') (h : N.QEq p p') : (N.twist β u).QEq P P' := by
  obtain ⟨z, h1, h2⟩ := h
  refine ⟨z, ?_, ?_⟩
  · rw [a.1, b.1]; exact h1
  · have c : Mult β u (fun w => u ^ β.be z w) (N.io z) ((N.twist β u).io z) := ⟨rfl, fun w => N.twist_τ β u z w⟩
    have d := (show Mult β u (fun w => s ^ β.be p.1.1.toAdd w) p.1.2 P.1.2 from a.2).mul c
    refine NumD.Gt.ext (b.2.1.trans ((congrArg NumD.Gt.b h2).trans d.1.symm)) (funext fun (w : N.X) => ?_)
    refine (b.2.2 w).trans (Eq.trans ?_ (d.2 w).symm)
    rw [h2, h1, map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, zpow_add, zpow_mul,
      zpow_natCast, hs]
end

theorem tx_of_qEq {O : Type} [CommRing O] [TopologicalSpace O] (N : NumD O) {m : ℕ} (hm : Odd m) {p p' : N.QT (m ^ 2)}
    (h : N.QEq p p') : N.tx m p' = N.tx m p := by
  obtain ⟨z, h1, h2⟩ := h
  exact (tsum_congr fun χ => (_root_.GlobalTheory.Ex.txT_shift O N m hm p p' χ).1 z h1 h2).trans
    ((Equiv.addRight (m • z)).tsum_eq fun χ => N.txT m p χ)

theorem qEq_pow {O : Type} [CommRing O] (N : NumD O) {La : Type} [AddCommGroup La] {j : ℕ} (q : La → N.QT j)
    (hq : ∀ a b, N.QEq (q a * q b) (q (a + b))) (x : La) (n : ℕ) : N.QEq (q x ^ (n + 1)) (q ((n + 1) • x)) := by
  have E : Equivalence (N.QEq (k := j)) := by
    constructor
    · intro p
      exact ⟨0, by simp, by simp⟩
    · rintro p p' ⟨z, h, h'⟩
      exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
    · rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
      exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, _root_.mul_assoc]⟩
  have qmul : ∀ {p p' q q' : N.QT j}, N.QEq p p' → N.QEq q q' → N.QEq (p * q) (p' * q') := by
    intro p p' q q' ⟨z, h1, h2⟩ ⟨w, h3, h4⟩
    refine ⟨z + w, ?_, ?_⟩
    · change p'.1.1.toAdd + q'.1.1.toAdd = p.1.1.toAdd + q.1.1.toAdd + _
      rw [h1, h3, smul_add]; abel
    · change p'.1.2 * q'.1.2 = p.1.2 * q.1.2 * _
      rw [h2, h4, N.io_add]; exact mul_mul_mul_comm _ _ _ _
  induction n with
  | zero => rw [zero_add, pow_one, one_smul]; exact E.refl _
  | succ n ih =>
    rw [pow_succ, succ_nsmul x (n + 1)]
    exact E.trans (qmul ih (E.refl _)) (hq _ _)
end GlobalTheory.Ex.TwNest

namespace GlobalTheory.Ex

open TwNest in
theorem twist_tx_nest : ∀ (C : Type) [NormedField C] (N : NumD C) (La : Type) [AddCommGroup La] (q : ∀ n : ℕ, La → N.QT n), (∀ n, 0 < n → ∀ a b, N.QEq (q n a * q n b) (q n (a + b))) → (∀ n m, 0 < n → 0 < m → ∀ a (p : N.QT n), p.1.1 = (q (n * m) a).1.1 → p.1.2 = (q (n * m) a).1.2 ^ m → N.QEq p (q n a)) → ∀ (k : ℕ) (β : N.Form k) (u : Cˣ) (r : ℕ → Cˣ), Roots u r → ∀ (n m : ℕ), Odd n → Odd m → ∀ (x : La) (p'' : (N.twist β u).QT ((n * m) ^ 2)) (p : (N.twist β u).QT (m ^ 2)), TwRel β u (r ((n * m) ^ 2)) (q _ (n • x)) p'' → TwRel β u (r (m ^ 2)) (q _ x) p → (N.twist β u).tx (n * m) p'' = (N.twist β u).tx m p := by
  intro C _ N La _ q hadd htow k β u r hr n m hn hm x p'' p h'' h
  have hK : (n * m) ^ 2 = m ^ 2 * n ^ 2 := by ring
  have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
  have hn2 : 0 < n ^ 2 := pow_pos hn.pos 2
  have hK0 : 0 < (n * m) ^ 2 := pow_pos (hn.mul hm).pos 2
  have hρ : r ((n * m) ^ 2) ^ (n ^ 2) = r (m ^ 2) := by rw [hK]; exact hr.2 _ _ hm2 hn2
  have htow' : ∀ K, K = m ^ 2 * n ^ 2 → ∀ p : N.QT (m ^ 2), p.1.1 = (q K x).1.1 → p.1.2 = (q K x).1.2 ^ (n ^ 2) →
      N.QEq p (q (m ^ 2) x) := by
    rintro _ rfl; exact htow _ _ hm2 hn2 x
  set Y := q ((n * m) ^ 2) x with hY
  obtain ⟨P, hP, -⟩ := existsUnique_twRel β u _ (hr.pow hK0) Y
  have hPm : Mult β u (fun w => r ((n * m) ^ 2) ^ β.be Y.1.1.toAdd w) Y.1.2 P.1.2 := hP.2
  let Y' : N.QT (m ^ 2) := ⟨(Y.1.1, Y.1.2 ^ (n ^ 2)), by
    change (Y.1.2 ^ (n ^ 2)) ^ (m ^ 2) = _
    rw [← pow_mul, ← mul_pow n m 2]; exact Y.2⟩
  let P' : (N.twist β u).QT (m ^ 2) := ⟨(P.1.1, P.1.2 ^ (n ^ 2)), by
    change (P.1.2 ^ (n ^ 2)) ^ (m ^ 2) = _
    rw [← pow_mul, ← mul_pow n m 2]; exact P.2⟩
  have t1 : TwRel β u (r (m ^ 2)) Y' P' := ⟨hP.1, (hPm.pow (n ^ 2)).1, fun w => ((hPm.pow (n ^ 2)).2 w).trans (by
    change (Y.1.2 ^ (n ^ 2)).s w * (_ ^ β.be Y.1.1.toAdd w) ^ (n ^ 2) = (Y.1.2 ^ (n ^ 2)).s w * _ ^ β.be Y.1.1.toAdd w
    rw [← hρ, ← zpow_natCast (_ ^ β.be _ _), ← zpow_natCast (r _), ← zpow_mul, ← zpow_mul, mul_comm (β.be _ _)])⟩
  have t2 : TwRel β u (r ((n * m) ^ 2)) (Y ^ n) (P ^ n) := ⟨congrArg (fun y : Multiplicative N.X => y ^ n) hP.1,
    (hPm.pow n).1, fun w => ((hPm.pow n).2 w).trans (by
      change _ = (Y.1.2 ^ n).s w * _ ^ β.be (n • Y.1.1.toAdd) w
      rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, mul_comm (n : ℤ), zpow_mul, zpow_natCast])⟩
  have e1 : N.QEq Y' (q (m ^ 2) x) := htow' _ hK Y' rfl rfl
  have e2 : N.QEq (Y ^ n) (q ((n * m) ^ 2) (n • x)) := by
    have := qEq_pow N (q ((n * m) ^ 2)) (hadd _ hK0) x (n - 1)
    rwa [Nat.sub_add_cancel hn.pos] at this
  rw [tx_of_qEq _ (hn.mul hm) (qEq_of_twRel (hr.pow hK0) t2 h'' e2), tx_of_qEq _ hm (qEq_of_twRel (hr.pow hm2) t1 h e1)]
  refine tsum_congr fun χ => _root_.GlobalTheory.Ex.Nest.txT_nest C _ n m hn hm (P ^ n) P' rfl ?_ χ
  change P.1.2 ^ (n ^ 2) = (P.1.2 ^ n) ^ n
  rw [← pow_mul, sq n]
end GlobalTheory.Ex
