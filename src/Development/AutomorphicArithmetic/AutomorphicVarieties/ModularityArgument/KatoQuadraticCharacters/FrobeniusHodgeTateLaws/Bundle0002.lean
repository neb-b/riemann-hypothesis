module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ExistsFiniteExtEisensteinUnitFunctionalMem
section
noncomputable section

open Formalism.ConjugateSelfDual UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.EisM

namespace UpperTheory.V.Z.Kato.Joint.M3

variable {l : ℕ} [Fact l.Prime]

omit [Fact l.Prime] in
theorem iter_uo (r : ℕ) (a : ℕ → ℂ) (n : ℕ) : (Uo l)^[r] a n = a (l ^ r * n) := by
  induction r generalizing a with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [Uo]
    rw [pow_succ', mul_assoc]

omit [Fact l.Prime] in
theorem mes_lin (k : ℕ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (m : ℕ) (a : ℂ) (f f' : ZMod (l ^ m) → ℂ) :
    mesMu k l u w α B c m (fun y => a * f y + f' y) = a * mesMu k l u w α B c m f + mesMu k l u w α B c m f' := by
  have h : ∀ n, Zm k l u w (fun A d => a * f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹) + f' ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n
      = a * Zm k l u w (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n +
        Zm k l u w (fun A d => f' ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n := by
    intro n
    simp only [Zm, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  simp only [mesMu, val, lam, iter_uo, h, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

omit [Fact l.Prime] in
theorem mes_smul (k : ℕ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (m : ℕ) (a : ℂ) (f : ZMod (l ^ m) → ℂ) :
    mesMu k l u w α B c m (fun y => a * f y) = a * mesMu k l u w α B c m f := by
  have key : ∀ n, Zm k l u w (fun A d => (fun y => a * f y) ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n =
      a * Zm k l u w (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n := by
    intro n
    simp only [Zm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  simp only [mesMu, val, lam, iter_uo]
  simp only [key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring


open Classical in
def sym (ι : Qbar l ≃+* ℂ) (s : ℂ) {N : ℕ} (g : ZMod N → Qbar l) : ZMod N → ℂ :=
  fun y => if IsUnit y then (ι (g y⁻¹) + s * ι (g (-y)⁻¹)) / 2 else 0

def nu0 (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (M : ℕ) :
    (ZMod (l ^ M) → Qbar l) →ₗ[Qbar l] Qbar l where
  toFun g := ι.symm (mesMu (2 * e + 1) l u w α B c M (sym ι s g))
  map_add' g g' := by
    have : sym ι s (g + g') = fun y => 1 * sym ι s g y + sym ι s g' y := by
      funext y; simp only [sym, Pi.add_apply, map_add (f := _)]; split_ifs <;> ring
    rw [this, mes_lin, one_mul, map_add (f := _)]
  map_smul' a g := by
    have : sym ι s (a • g) = fun y => ι a * sym ι s g y := by
      funext y; simp only [sym, Pi.smul_apply, smul_eq_mul, map_mul]; split_ifs <;> ring
    rw [this, mes_smul, map_mul]; simp

theorem eisensteinUnitFunctional_apply (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (M : ℕ)
    (g : ZMod (l ^ M) → Qbar l) : nu0 ι e s u w α B c M g = ι.symm (mesMu (2 * e + 1) l u w α B c M (sym ι s g)) := rfl

theorem inv_unit {N : ℕ} {y : ZMod N} (h : IsUnit y) : IsUnit y⁻¹ := IsUnit.of_mul_eq_one y (ZMod.inv_mul_of_unit y h)

theorem neg_inv_unit {N : ℕ} {y : ZMod N} (h : IsUnit y) : (-y)⁻¹ = -y⁻¹ := by
  obtain ⟨u, rfl⟩ := h
  rw [← Units.val_neg, ZMod.inv_coe_unit, ZMod.inv_coe_unit, inv_neg, Units.val_neg]

theorem sym_par (ι : Qbar l ≃+* ℂ) {s : ℂ} (hs : s * s = 1) {N : ℕ} (g : ZMod N → Qbar l) (y : ZMod N) :
    sym ι s g (-y) = s * sym ι s g y := by
  by_cases hy : IsUnit y
  · simp only [sym, if_pos hy, if_pos hy.neg, neg_neg]
    linear_combination (-ι (g (-y)⁻¹) / 2) * hs
  · simp [sym, hy]

theorem eisensteinUnitFunctional_congr_on_units (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (M : ℕ)
    (g g' : ZMod (l ^ M) → Qbar l) (h : ∀ x, IsUnit x → g x = g' x) : nu0 ι e s u w α B c M g = nu0 ι e s u w α B c M g' := by
  have hs : sym ι s g = sym ι s g' := by
    funext y
    unfold sym
    split_ifs with hy
    · rw [h _ (inv_unit hy), h _ (inv_unit hy.neg)]
    · rfl
  rw [eisensteinUnitFunctional_apply, eisensteinUnitFunctional_apply, hs]

theorem unit_iff {M : ℕ} (hM : 1 ≤ M) (y : ℕ) : IsUnit (y : ZMod (l ^ M)) ↔ ¬ l ∣ y := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hM, Nat.coprime_comm, (Fact.out : l.Prime).coprime_iff_not_dvd]

theorem eisensteinUnitFunctional_compat_succ {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ} {v : ℂ}
    (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) (M : ℕ) (hM : 1 ≤ M) (g : ZMod (l ^ M) → Qbar l)
    (g' : ZMod (l ^ (M + 1)) → Qbar l) (h : ∀ y : ℕ, g' y = g y) :
    nu0 ι e s u w α B c (M + 1) g' = nu0 ι e s u w α B c M g := by
  have hdvd : l ^ M ∣ l ^ (M + 1) := pow_dvd_pow l (Nat.le_succ M)
  haveI : NeZero (l ^ (M + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set φ := ZMod.castHom hdvd (ZMod (l ^ M))
  have hg : ∀ x, g' x = g (φ x) := by
    intro x
    rw [← ZMod.natCast_zmod_val x, h, map_natCast]
  have hinv : ∀ x : ZMod (l ^ (M + 1)), IsUnit x → φ x⁻¹ = (φ x)⁻¹ := by
    intro x hx
    symm
    apply ZMod.inv_eq_of_mul_eq_one
    rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]
  have hsym : ∀ y : ℕ, sym ι s g' (y : ZMod (l ^ (M + 1))) = sym ι s g y := by
    intro y
    unfold sym
    by_cases hy : l ∣ y
    · rw [if_neg (by rw [unit_iff (M := M + 1) (by omega)]; exact not_not.2 hy),
        if_neg (by rw [unit_iff hM]; exact not_not.2 hy)]
    · have h1 : IsUnit (y : ZMod (l ^ (M + 1))) := (unit_iff (M := M + 1) (by omega) y).2 hy
      rw [if_pos h1, if_pos ((unit_iff hM y).2 hy), hg, hg, hinv _ h1, hinv _ h1.neg, map_neg, map_natCast]
  rw [eisensteinUnitFunctional_apply, eisensteinUnitFunctional_apply, H.compat M hM (sym ι s g) (sym ι s g') (sym_par ι hs g) hsym]

theorem norm_nat {a : ℕ} (ha : ¬ l ∣ a) : ‖(a : Qbar l)‖ = 1 := by
  have h1 : algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) = (a : Qbar l) := map_natCast _ a
  have h2 : ((a : ℚ) : ℚ_[l]) = (a : ℚ_[l]) := by push_cast; rfl
  rw [← h1, PadicAlgCl.norm_extends l (a : ℚ_[l])]
  rw [← h2, Padic.eq_padicNorm, (padicNorm.nat_eq_one_iff a).2 ha]
  simp

theorem norm_half (hl : l ≠ 2) {a b : Qbar l} {δ : ℝ} (ha : ‖a‖ ≤ δ) (hb : ‖b‖ ≤ δ) : ‖(a + b) / 2‖ ≤ δ := by
  have h2 : ‖(2 : Qbar l)‖ = 1 := by
    simpa using norm_nat (l := l) (a := 2) fun h => hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  rw [norm_div, h2, div_one]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem sgn_cases {s : ℂ} (hs : s * s = 1) : s = 1 ∨ s = -1 := mul_self_eq_one_iff.1 hs

theorem symm_sym (ι : Qbar l ≃+* ℂ) (s : ℂ) {N : ℕ} (g : ZMod N → Qbar l) {y : ZMod N} (hy : IsUnit y) :
    ι.symm (sym ι s g y) = (g y⁻¹ + ι.symm s * g (-y⁻¹)) / 2 := by
  unfold sym
  rw [if_pos hy, neg_inv_unit hy, map_div₀, map_add (f := _), map_mul, RingEquiv.symm_apply_apply,
    RingEquiv.symm_apply_apply, map_ofNat]

theorem eisensteinUnitFunctional_bounded {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ} {v : ℂ}
    (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) (hl : l ≠ 2) :
    ∃ C : ℝ, ∀ (M : ℕ) (g : ZMod (l ^ M) → Qbar l), (∀ y, ‖g y‖ ≤ 1) → ‖nu0 ι e s u w α B c M g‖ ≤ C := by
  obtain ⟨C, hC⟩ := H.bound
  refine ⟨C * 1, fun M g hg => ?_⟩
  rw [eisensteinUnitFunctional_apply]
  apply hC M _ 1 zero_le_one
  intro y
  by_cases hy : IsUnit y
  · rw [symm_sym ι s g hy]
    apply norm_half hl (hg _)
    rw [norm_mul]
    have hn : ‖ι.symm s‖ = 1 := by
      rcases sgn_cases hs with rfl | rfl <;> simp
    rw [hn, one_mul]
    exact hg _
  · simp [sym, hy]

theorem exists_finiteExt_eisensteinUnitFunctional_mem {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ} {v : ℂ}
    (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) :
    ∃ E : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] E ∧
      ∀ (M : ℕ) (g : ZMod (l ^ M) → Qbar l), (∀ y, g y ∈ E) → nu0 ι e s u w α B c M g ∈ E := by
  obtain ⟨E, hE, hf⟩ := H.field
  refine ⟨E, hE, fun M g hg => ?_⟩
  rw [eisensteinUnitFunctional_apply]
  apply hf M _ E le_rfl
  intro y
  by_cases hy : IsUnit y
  · rw [symm_sym ι s g hy]
    have hs' : ι.symm s ∈ E := by
      rcases sgn_cases hs with rfl | rfl
      · rw [map_one]
        exact E.one_mem
      · rw [map_neg, map_one]
        exact E.neg_mem E.one_mem
    have h2 : (2 : Qbar l) ∈ E := by
      rw [← one_add_one_eq_two]
      exact E.add_mem E.one_mem E.one_mem
    exact E.div_mem (E.add_mem (hg _) (E.mul_mem hs' (hg _))) h2
  · simp only [sym, if_neg hy, map_zero]
    exact E.zero_mem

theorem sym_char (ι : Qbar l ≃+* ℂ) (s : ℂ) {N : ℕ} (χ : DirichletCharacter (Qbar l) N) (y : ZMod N) :
    sym ι s (fun x => χ⁻¹ x) y = (1 + s * ι (χ (-1))) / 2 * ι (χ y) := by
  unfold sym
  split_ifs with hy
  · have key : ∀ z : ZMod N, IsUnit z → χ⁻¹ z⁻¹ = χ z := by
      intro z hz
      rw [MulChar.inv_apply_eq_inv']
      have hm : χ z⁻¹ * χ z = 1 := by rw [← map_mul, ZMod.inv_mul_of_unit z hz, map_one]
      exact inv_eq_of_mul_eq_one_right hm
    dsimp only
    rw [key y hy, key (-y) hy.neg]
    have hn : χ (-y) = χ (-1) * χ y := by rw [← map_mul, neg_one_mul]
    rw [hn, map_mul ι]
    ring
  · rw [MulChar.map_nonunit χ hy, map_zero, mul_zero]

theorem eisensteinUnitFunctional_dirichletChar (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (M : ℕ)
    (χ : DirichletCharacter (Qbar l) (l ^ M)) :
    nu0 ι e s u w α B c M (fun x => χ⁻¹ x) =
      (1 + ι.symm s * χ (-1)) / 2 * ι.symm (mesMu (2 * e + 1) l u w α B c M (fun y => ι (χ y))) := by
  rw [eisensteinUnitFunctional_apply]
  have hs : sym ι s (fun x => χ⁻¹ x) = fun y => (1 + s * ι (χ (-1))) / 2 * ι (χ y) := funext (sym_char ι s χ)
  rw [hs, mes_smul, map_mul]
  congr 1
  rw [map_div₀, map_add (f := _), map_one, map_mul, RingEquiv.symm_apply_apply, map_ofNat]

theorem eisensteinUnitFunctional_interpolation {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ} {v : ℂ}
    (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) (hl : l ≠ 2) :
    ∃ C : ℝ, ∀ (M : ℕ), 1 ≤ M → ∀ (g : ZMod (l ^ M) → Qbar l) (δ : ℝ), 0 ≤ δ →
      (∀ a d : ℕ, ¬ l ∣ a → ¬ l ∣ d → ∀ y : ZMod (l ^ M), y * a = d →
        ‖g y - ι.symm (ψ a * ψ⁻¹ d * ((d : ℂ) / a) ^ e)‖ ≤ δ ∧ ‖ι.symm s * g (-y) - ι.symm (ψ a * ψ⁻¹ d * ((d : ℂ) / a) ^ e)‖ ≤ δ) →
      ‖nu0 ι e s u w α B c M g - ι.symm v‖ ≤ C * δ := by
  obtain ⟨C, hC⟩ := H.interp
  refine ⟨C, fun M hM g δ hδ hg => ?_⟩
  rw [eisensteinUnitFunctional_apply, ← map_sub]
  apply hC M hM _ δ hδ (sym_par ι hs g)
  intro a d ha hd
  have hua : IsUnit (a : ZMod (l ^ M)) := (unit_iff hM a).2 ha
  have hud : IsUnit (d : ZMod (l ^ M)) := (unit_iff hM d).2 hd
  set x : ZMod (l ^ M) := (a : ZMod (l ^ M)) * (d : ZMod (l ^ M))⁻¹ with hxdef
  have hx : IsUnit x := hua.mul (inv_unit hud)
  have hxd : x * d = a := by rw [hxdef, mul_assoc, ZMod.inv_mul_of_unit _ hud, mul_one]
  have hy : x⁻¹ * a = d := by rw [← hxd, ← mul_assoc, ZMod.inv_mul_of_unit _ hx, one_mul]
  obtain ⟨h1, h2⟩ := hg a d ha hd x⁻¹ hy
  rw [map_sub, symm_sym ι s g hx]
  set T := ι.symm (ψ a * ψ⁻¹ d * ((d : ℂ) / a) ^ e)
  have hT : (g x⁻¹ + ι.symm s * g (-x⁻¹)) / 2 - T = ((g x⁻¹ - T) + (ι.symm s * g (-x⁻¹) - T)) / 2 := by ring
  rw [hT]
  exact norm_half hl h1 h2

end UpperTheory.V.Z.Kato.Joint.M3

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.NormLeOfPow
section
open UpperTheory.V.Z.Kato.Joint

private theorem norm_le_of_pow {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (z : ℂ) (n : ℕ) (hn : n ≠ 0)
    (h : z ^ n = 1) : ‖ι.symm z‖ ≤ 1 := by
  have h1 : ‖ι.symm z‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h1).le

private theorem hat_std {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) (d : ℤ) :
    GlobalTheory.EisM.hat φ d = ∑ y : ZMod N, φ y * ZMod.stdAddChar (y * (d : ZMod N)) := by
  unfold GlobalTheory.EisM.hat
  refine Finset.sum_nbij' (fun i => (i : ZMod N)) (fun y => y.val) (fun _ _ => Finset.mem_univ _)
    (fun y _ => Finset.mem_range.mpr (ZMod.val_lt y)) (fun i hi => ZMod.val_cast_of_lt (Finset.mem_range.mp hi))
    (fun y _ => ZMod.natCast_zmod_val y) (fun i _ => ?_)
  have h : ((i : ZMod N)) * (d : ZMod N) = (((i : ℤ) * d : ℤ) : ZMod N) := by push_cast; rfl
  rw [h, ZMod.stdAddChar_coe]
  push_cast
  rfl

private theorem norm_two' {l : ℕ} [hl : Fact l.Prime] (h : l ≠ 2) : ‖(2 : PadicAlgCl l)‖ = 1 := by
  have h1 : (2 : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l]) := by
    rw [map_natCast]; rfl
  rw [h1, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes hl.out Nat.prime_two).mpr h)

theorem UpperTheory.V.Z.Kato.Joint.hatW :
    UpperTheory.V.Z.Kato.Joint.HatW := by
  intro l _ ι N _ θ hl
  refine ⟨?_, fun d => ?_, fun d => ?_⟩
  · by_contra hc
    push Not at hc
    have h0 : ZMod.dft (fun y : ZMod N => θ y) = 0 := by
      funext k
      have := hc (-k)
      rw [hat_std] at this
      rw [ZMod.dft_apply, Pi.zero_apply, ← this]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [mul_comm]
    have h1 := congrFun ((LinearEquiv.map_eq_zero_iff _).mp h0) 1
    simp at h1
  · have h2 : ι.symm 2 = 2 := map_ofNat _ 2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_div₀, norm_div, h2, norm_two' hl, div_one, hat_std, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun y _ => ?_
    rw [map_mul, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · by_cases hy : IsUnit y
      · obtain ⟨u, rfl⟩ := hy
        refine norm_le_of_pow ι _ (Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_
        rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
      · rw [MulChar.map_nonunit _ hy]; simp
    · refine norm_le_of_pow ι _ N (NeZero.ne N) ?_
      rw [← AddChar.map_nsmul_eq_pow]
      simp
  · rw [hat_std, hat_std]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.PsiEx
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open UpperTheory.V.Z.Kato.Joint

private theorem apply_eq_pow_cycMod_of_pow_eq_one (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (s : G ℚ Ω) (ζ : Ω) (hζ : ζ ^ l = 1) :
    s ζ = ζ ^ ((cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).1 inferInstance
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : Nat.Prime l).ne_zero⟩
  exact cyclotomicCharacter.spec l (n := 1) (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ
    (by rwa [pow_one])

private theorem cyc1_surjective (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (u : (ZMod l)ˣ) : ∃ s : G ℚ Ω, cyc1 l s = u := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).1 inferInstance
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : Nat.Prime l).ne_zero⟩
  haveI : NeZero l := ⟨(Fact.out : Nat.Prime l).ne_zero⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  set K := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hK
  haveI : IsCyclotomicExtension {l} ℚ K := by
    convert hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
    exact Subsingleton.elim _ _
  haveI : NumberField K := IsCyclotomicExtension.numberField {l} ℚ K
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq (fun x => by simp)
  let σ := (IsCyclotomicExtension.Rat.galEquivZMod l K).symm u
  let ζK : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hζK : ζK ^ l = 1 := Subtype.ext (by simpa using hζ.pow_eq_one)
  refine ⟨σ.liftNormal Ω, ?_⟩
  have h1 : (σ.liftNormal Ω) ζ = ζ ^ (u : ZMod l).val := by
    have h2 := σ.liftNormal_commutes Ω ζK
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq l K σ hζK,
      show IsCyclotomicExtension.Rat.galEquivZMod l K σ = u from MulEquiv.apply_symm_apply _ u] at h2
    simpa [ζK] using h2
  have h3 := apply_eq_pow_cycMod_of_pow_eq_one l Ω (σ.liftNormal Ω) ζ hζ.pow_eq_one
  rw [h1] at h3
  have hc : (cycMod ℚ Ω l 1 (σ.liftNormal Ω) : ZMod (l ^ 1)).val < l := by
    simpa [pow_one] using ZMod.val_lt (cycMod ℚ Ω l 1 (σ.liftNormal Ω) : ZMod (l ^ 1))
  have h4 := hζ.pow_inj (ZMod.val_lt (u : ZMod l)) hc h3
  unfold cyc1
  rw [← h4, ZMod.natCast_zmod_val]

theorem UpperTheory.V.Z.Kato.Joint.psiEx :
    UpperTheory.V.Z.Kato.Joint.PsiEx := by
  intro l _ Ω _ _ _ ι χ hχ
  have key : ∀ s t : G ℚ Ω, cyc1 l s = cyc1 l t → χ s = χ t := by
    intro s t hst
    have hv : (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val = (cycMod ℚ Ω l 1 t : ZMod (l ^ 1)).val := by
      have h1 := congrArg ZMod.val hst
      unfold cyc1 at h1
      have hs : (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val < l := by
        simpa [pow_one] using ZMod.val_lt (cycMod ℚ Ω l 1 s : ZMod (l ^ 1))
      have ht : (cycMod ℚ Ω l 1 t : ZMod (l ^ 1)).val < l := by
        simpa [pow_one] using ZMod.val_lt (cycMod ℚ Ω l 1 t : ZMod (l ^ 1))
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] at h1
      exact h1
    have hfix : ∀ ζ : Ω, ζ ^ l = 1 → (t⁻¹ * s) ζ = ζ := by
      intro ζ hζ
      rw [AlgEquiv.mul_apply, apply_eq_pow_cycMod_of_pow_eq_one l Ω s ζ hζ, hv, ← apply_eq_pow_cycMod_of_pow_eq_one l Ω t ζ hζ]
      exact t.symm_apply_apply ζ
    have h1 := hχ (t⁻¹ * s) hfix
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  have hd : l ∣ l ^ 1 := by rw [pow_one]
  have hcast : ∀ s : G ℚ Ω, cyc1 l s = ZMod.cast (cycMod ℚ Ω l 1 s : ZMod (l ^ 1)) := by
    intro s
    unfold cyc1
    rw [ZMod.cast_eq_val]
  have hone : cyc1 l (1 : G ℚ Ω) = 1 := by
    rw [hcast, map_one, Units.val_one, ZMod.cast_one hd]
  have hmul : ∀ s t : G ℚ Ω, cyc1 l (s * t) = cyc1 l s * cyc1 l t := by
    intro s t
    rw [hcast, hcast, hcast, map_mul, Units.val_mul, ZMod.cast_mul hd]
  let sec : (ZMod l)ˣ → G ℚ Ω := fun u => (cyc1_surjective l Ω u).choose
  have hsec : ∀ u, cyc1 l (sec u) = u := fun u => (cyc1_surjective l Ω u).choose_spec
  let f : (ZMod l)ˣ →* ℂˣ :=
    { toFun := fun u => Units.map ι.toMonoidHom (χ (sec u))
      map_one' := by
        rw [key (sec 1) 1 (by rw [hsec, hone, Units.val_one]), map_one, map_one]
      map_mul' := by
        intro u v
        rw [key (sec (u * v)) (sec u * sec v) (by rw [hsec, hmul, hsec, hsec, Units.val_mul]),
          map_mul, map_mul] }
  refine ⟨MulChar.ofUnitHom f, fun s => ?_⟩
  let w : (ZMod l)ˣ := Units.map (ZMod.castHom hd (ZMod l)).toMonoidHom (cycMod ℚ Ω l 1 s)
  have hw : (w : ZMod l) = cyc1 l s := by
    rw [hcast]
    rfl
  rw [← hw, MulChar.ofUnitHom_coe]
  show (χ s : Formalism.ConjugateSelfDual.Qbar l) = ι.symm (ι (χ (sec w) : Formalism.ConjugateSelfDual.Qbar l))
  rw [RingEquiv.symm_apply_apply, key s (sec w) (by rw [hsec, hw])]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SerVal
section
noncomputable section

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.EisM GlobalTheory.KummerEisensteinGalois

namespace UpperTheory.V.Z.Kato.Joint

def ser {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (a b : ℤ) : ℕ → PadicAlgCl l :=
  up (l ^ m) fun i => ∑ x : ZMod N, ι.symm (hat θ (x.val : ℤ) / 2) * coPtMu N l m k ψ ((x.val : ℤ) * a) b i

def frm (l N m k : ℕ) (θ ν : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ) : ℕ → ℂ :=
  (Uo l)^[m] (Zm k l (hat θ) (ch ν) fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))

def AvgEq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ χ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (a b : ℤ), l ≠ 2 → 1 ≤ m → 3 ≤ k → Odd k → χ (-1) = -1 → IsCoprime a N → IsCoprime b N →
    (ι (ψ (-1)) ≠ θ (-1) → ser ι N θ m k ψ a b = 0) ∧
    (∀ a' b' : ℤ, a ≡ a' [ZMOD N] → b ≡ b' [ZMOD N] → ser ι N θ m k ψ a b = ser ι N θ m k ψ a' b') ∧
    (ι (ψ (-1)) = θ (-1) → ∀ i, ∑ u : (ZMod N)ˣ, χ u * ι (ser ι N θ m k ψ (((u : ZMod N).val : ℤ) * a) (((u : ZMod N).val : ℤ) * b) i) =
      2 * θ (a : ZMod N) * (θ * χ)⁻¹ (b : ZMod N) * frm l N m k θ (θ * χ) (fun y => ι (ψ y)) i)

def AvgMF : Prop :=
  ∀ (k l N m : ℕ) (θ χ : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ), l.Prime → 3 ≤ k → Odd k →
    0 < N → ¬ l ∣ N → 1 ≤ m → χ (-1) = -1 → (∀ y, f (-y) = θ (-1) * f y) → α ≠ 0 → EigAll k N l χ t α B c →
    MF k (N * l) (ch χ) (frm l N m k θ (θ * χ) f) ∧
      2 * lam B c (frm l N m k θ (θ * χ) f) = (N.totient : ℂ) * α ^ m * mesMu k l (hat θ) (tw2 N (θ (-1))) α B c m f

end UpperTheory.V.Z.Kato.Joint

end
end

