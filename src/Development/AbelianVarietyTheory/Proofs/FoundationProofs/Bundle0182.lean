module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostGaloisCoordinates
section
open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.KumDlog.AlmostGal

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def Rep (C : Subalgebra (O0 p) Ω) (H : Subgroup (Gal p Ω)) (F : Gal p Ω → Ω) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (u v : ι → Ω), (∀ k, u k ∈ C) ∧ (∀ k, v k ∈ C) ∧
    ∀ h ∈ H, F h = ∑ k, u k * h (v k)

variable {C : Subalgebra (O0 p) Ω} {H : Subgroup (Gal p Ω)}

theorem rep_congr {F G : Gal p Ω → Ω} (hF : Rep C H F) (e : ∀ h ∈ H, G h = F h) : Rep C H G := by
  obtain ⟨ι, hι, u, v, hu, hv, hF⟩ := hF
  exact ⟨ι, hι, u, v, hu, hv, fun h hh => (e h hh).trans (hF h hh)⟩

theorem rep_const {c : Ω} (hc : c ∈ C) : Rep C H (fun _ => c) :=
  ⟨Unit, inferInstance, fun _ => c, fun _ => 1, fun _ => hc, fun _ => C.one_mem,
    fun h _ => by simp⟩

theorem rep_eval {x : Ω} (hx : x ∈ C) : Rep C H (fun h => h x) :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => x, fun _ => C.one_mem, fun _ => hx,
    fun h _ => by simp⟩

theorem rep_add {F G : Gal p Ω → Ω} (hF : Rep C H F) (hG : Rep C H G) :
    Rep C H (fun h => F h + G h) := by
  obtain ⟨ι, _, u, v, hu, hv, hF⟩ := hF
  obtain ⟨ι', _, u', v', hu', hv', hG⟩ := hG
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim u u', Sum.elim v v', ?_, ?_, fun h hh => ?_⟩
  · rintro (k | k)
    · exact hu k
    · exact hu' k
  · rintro (k | k)
    · exact hv k
    · exact hv' k
  · show F h + G h = _
    rw [Fintype.sum_sum_type, hF h hh, hG h hh]
    simp

theorem rep_mul {F G : Gal p Ω → Ω} (hF : Rep C H F) (hG : Rep C H G) :
    Rep C H (fun h => F h * G h) := by
  obtain ⟨ι, _, u, v, hu, hv, hF⟩ := hF
  obtain ⟨ι', _, u', v', hu', hv', hG⟩ := hG
  refine ⟨ι × ι', inferInstance, fun k => u k.1 * u' k.2, fun k => v k.1 * v' k.2,
    fun k => C.mul_mem (hu _) (hu' _), fun k => C.mul_mem (hv _) (hv' _), fun h hh => ?_⟩
  show F h * G h = ∑ k : ι × ι', u k.1 * u' k.2 * h (v k.1 * v' k.2)
  rw [hF h hh, hG h hh, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul]; ring

theorem rep_prod {α : Type*} (s : Finset α) (F : α → Gal p Ω → Ω)
    (hF : ∀ a ∈ s, Rep C H (F a)) : Rep C H (fun h => ∏ a ∈ s, F a h) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rep_const (H := H) C.one_mem)
  | insert a s ha ih =>
    refine rep_congr (rep_mul (hF a (by simp)) (ih fun b hb => hF b (by simp [hb])))
      fun h _ => ?_
    rw [Finset.prod_insert ha]

theorem gal_mem_C {T : Tower p Ω} {n : ℕ} {r : Ω}
    (hH : ∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) {g : Gal p Ω} (hg : g ∈ Hinf T)
    {x : Ω} (hx : x ∈ FixI (Hfix T r)) : g x ∈ FixI (Hfix T r) := by
  refine ⟨int_gal g hx.1, fun h hh => ?_⟩
  obtain ⟨hhinf, hhr⟩ := mem_Hfix.1 hh
  have hgr : h (g r) = g r := by
    obtain ⟨i, hi⟩ := hH g hg
    rw [hi, map_mul, map_pow, (mem_Hinf.1 hhinf n).1, hhr]
  have hk : g⁻¹ * h * g ∈ Hfix T r := by
    refine mem_Hfix.2 ⟨(Hinf T).mul_mem ((Hinf T).mul_mem ((Hinf T).inv_mem hg) hhinf) hg, ?_⟩
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hgr, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have e := hx.2 _ hk
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at e
  exact e

theorem eq_on_C {T : Tower p Ω} {r : Ω} {g h : Gal p Ω} (hg : g ∈ Hinf T) (hh : h ∈ Hinf T)
    (hr : h r = g r) {x : Ω} (hx : x ∈ FixI (Hfix T r)) : h x = g x := by
  have hk : g⁻¹ * h ∈ Hfix T r := by
    refine mem_Hfix.2 ⟨(Hinf T).mul_mem ((Hinf T).inv_mem hg) hh, ?_⟩
    rw [AlgEquiv.mul_apply, hr, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have e := hx.2 _ hk
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at e
  exact e

theorem rep_of_span {T : Tower p Ω} {n : ℕ} {r : Ω}
    (hH : ∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) {g : Gal p Ω} (hg : g ∈ Hinf T) {y : Ω}
    (hy : y ∈ Submodule.span (FixI (Hfix T r)) {y : Ω | ∃ x ∈ FixI (Hfix T r), y = g x - x}) :
    ∃ F : Gal p Ω → Ω, Rep (FixI (Hfix T r)) (Hinf T) F ∧ F 1 = y ∧
      ∀ h ∈ Hinf T, h r = g r → F h = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨fun h => g x + (-1) * h x, rep_add (rep_const (gal_mem_C hH hg hx))
      (rep_mul (rep_const (neg_mem (Subalgebra.one_mem _))) (rep_eval hx)), ?_, ?_⟩
    · simp only [AlgEquiv.one_apply]; ring
    · intro h hh hr
      simp only [eq_on_C hg hh hr hx]; ring
  | zero => exact ⟨fun _ => 0, rep_const (Subalgebra.zero_mem _), rfl, fun _ _ _ => rfl⟩
  | add y z _ _ ihy ihz =>
    obtain ⟨F, hF, hF1, hF0⟩ := ihy
    obtain ⟨G, hG, hG1, hG0⟩ := ihz
    exact ⟨fun h => F h + G h, rep_add hF hG, by simp [hF1, hG1],
      fun h hh hr => by simp [hF0 h hh hr, hG0 h hh hr]⟩
  | smul a y _ ih =>
    obtain ⟨F, hF, hF1, hF0⟩ := ih
    exact ⟨fun h => (a : Ω) * F h, rep_mul (rep_const a.2) hF,
      by simp [hF1, Subalgebra.smul_def], fun h hh hr => by simp [hF0 h hh hr]⟩

end GlobalTheory.KumDlog.AlmostGal


open GlobalTheory.KumDlog.AlmostGal in
theorem GlobalTheory.KumDlog.almostGal_coord : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω]
    [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r →
    (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∃ (ι : Type) (_ : Fintype ι) (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) ∧
    (∀ k, v k ∈ FixI (Hfix T r)) ∧
  ∑ k, u k * v k = (p : Ω) ∧ ∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0 := by
  intro p _ hp2 Ω _ _ hclo T n r hr hH
  classical
  have hp : p.Prime := Fact.out
  set τ : Ω := T.ζ (n + 1) - 1 with hτ
  have hτ0 : τ ≠ 0 :=
    sub_ne_zero.2 ((T.prim (n + 1)).ne_one (Nat.one_lt_pow (by omega) hp.one_lt))

  set W : Finset Ω := ((Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r)).filter
    (fun w => w ≠ r ∧ ∃ g ∈ Hinf T, g r = w) with hW
  have hF : ∀ w ∈ W, ∃ F : Gal p Ω → Ω, Rep (FixI (Hfix T r)) (Hinf T) F ∧ F 1 = τ ∧
      ∀ h ∈ Hinf T, h r = w → F h = 0 := by
    intro w hw
    obtain ⟨hwr, g, hg, hgw⟩ := (Finset.mem_filter.1 hw).2
    obtain ⟨F, hF, hF1, hF0⟩ := rep_of_span hH hg
      (GlobalTheory.T.zeta_sub_one_mem_span_galois_differences p hp2 Ω hclo T n r hr hH (n + 1) (by omega) g hg (hgw ▸ hwr))
    exact ⟨F, hF, hF1, fun h hh e => hF0 h hh (e.trans hgw.symm)⟩
  choose! F hFr hF1 hF0 using hF
  set s := W.card with hs
  have hsle : s ≤ Nat.totient (p ^ (n + 1)) := by
    rw [Nat.totient_prime_pow hp (by omega), Nat.add_sub_cancel]
    calc s ≤ ((Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r)).card :=
          Finset.card_filter_le _ _
      _ ≤ (Finset.range (p ^ n)).card := Finset.card_image_le
      _ = p ^ n := Finset.card_range _
      _ ≤ p ^ n * (p - 1) := Nat.le_mul_of_pos_right _ (by have := hp.two_le; omega)
  set c : Ω := (p : Ω) / τ ^ s with hc
  have hcC : c ∈ FixI (Hfix T r) := by
    refine ⟨GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T (n + 1) s (by omega) hsle, fun g hg => ?_⟩
    have hz : g (T.ζ (n + 1)) = T.ζ (n + 1) := (mem_Hinf.1 (mem_Hfix.1 hg).1 (n + 1)).1
    rw [hc, map_div₀, map_pow, hτ, map_sub, map_one, hz, map_natCast]
  have hrep : Rep (FixI (Hfix T r)) (Hinf T) (fun h => c * ∏ w ∈ W, F w h) :=
    rep_mul (rep_const hcC) (rep_prod W F hFr)
  obtain ⟨ι, hι, u, v, hu, hv, he⟩ := hrep
  refine ⟨ι, hι, u, v, hu, hv, ?_, fun h hh hhr => ?_⟩
  · have e := he 1 (Hinf T).one_mem
    simp only [AlgEquiv.one_apply] at e
    rw [← e, Finset.prod_congr rfl hF1, Finset.prod_const, ← hs, hc,
      div_mul_cancel₀ _ (pow_ne_zero _ hτ0)]
  · rw [← he h hh]
    obtain ⟨i, hi⟩ := hH h hh
    have hmod : h r = T.ζ n ^ (i % p ^ n) * r := by
      rw [hi]
      conv_lhs => rw [← Nat.div_add_mod i (p ^ n), pow_add, pow_mul, (T.prim n).pow_eq_one,
        one_pow, one_mul]
    have hmem : h r ∈ W := by
      refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨i % p ^ n, Finset.mem_range.2
        (Nat.mod_lt _ (ppow_pos n)), hmod.symm⟩, hhr, h, hh, rfl⟩
    show c * ∏ w ∈ W, F w h = 0
    rw [Finset.prod_eq_zero hmem (hF0 _ hmem h hh rfl), mul_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalHermitianOfDiagPosIsSquare
section
open NumberField
open scoped Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.SqDet

section
variable {K : Type} [Field K] [NumberField K] {d : ℕ} {θ : K}

end

open NumberField in
open scoped Matrix ComplexConjugate in
private theorem exists_rat_sum_norm_forms_eq_one {a b d : ℚ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    ∃ p₁ q₁ p₂ q₂ : ℚ, a * (p₁ ^ 2 + d * q₁ ^ 2) + b * (p₂ ^ 2 + d * q₂ ^ 2) = 1 := by
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.LocalQuad.isotropic_of_indefinite _root_.GlobalTheory.QNorm.hasseNormSt ℚ
    (![a, a * d, b, b * d, -1] : Fin 5 → ℚ) (by simp)
    (by
      intro i
      fin_cases i <;> simp [ha.ne', hb.ne', hd.ne'])
    (by
      intro τ
      refine ⟨4, 0, ?_, ?_⟩
      · simp
      · simp only [Matrix.cons_val_zero, eq_ratCast]
        exact_mod_cast ha)
  have hx' : a * x 0 ^ 2 + a * d * x 1 ^ 2 + b * x 2 ^ 2 + b * d * x 3 ^ 2 = x 4 ^ 2 := by
    simp [Fin.sum_univ_five] at hx
    linarith
  have t0 : 0 ≤ a * x 0 ^ 2 := by positivity
  have t1 : 0 ≤ a * d * x 1 ^ 2 := by positivity
  have t2 : 0 ≤ b * x 2 ^ 2 := by positivity
  have t3 : 0 ≤ b * d * x 3 ^ 2 := by positivity
  have h4 : x 4 ≠ 0 := by
    intro h4
    rw [h4] at hx'
    have e0 : a * x 0 ^ 2 = 0 := by linarith
    have e1 : a * d * x 1 ^ 2 = 0 := by linarith
    have e2 : b * x 2 ^ 2 = 0 := by linarith
    have e3 : b * d * x 3 ^ 2 = 0 := by linarith
    apply hx0
    funext i
    fin_cases i
    · simpa [ha.ne'] using e0
    · simpa [ha.ne', hd.ne'] using e1
    · simpa [hb.ne'] using e2
    · simpa [hb.ne', hd.ne'] using e3
    · exact h4
  refine ⟨x 0 / x 4, x 1 / x 4, x 2 / x 4, x 3 / x 4, ?_⟩
  field_simp
  linarith

open NumberField in
open scoped Matrix ComplexConjugate in
private theorem sesq_apply_eq_zero_and_of_mem_span_of_forall_mem {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {σ : K →+* K} (h : V →ₗ[K] V →ₛₗ[σ] K) {s : Set V} {w : V}
    (hs : ∀ u ∈ s, h u w = 0 ∧ h w u = 0) {u : V} (hu : u ∈ Submodule.span K s) :
    h u w = 0 ∧ h w u = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx.1, hy.1, hx.2, hy.2]
  | smul c x _ hx => simp [hx.1, hx.2]

open NumberField in
open scoped Matrix ComplexConjugate in
private theorem exists_orthonormal_mem_span_of_diagonal_square_prod {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) {d : ℕ} {θ : K}
    (hd : 0 < d) (hθ2 : θ ^ 2 = -(d : K)) (hθ : σ θ = -θ) :
    ∀ (r : ℕ) (v : Fin r → V) (a : Fin r → ℚ), (∀ i, 0 < a i) →
      (∀ i j, h (v i) (v j) = if i = j then (a i : K) else 0) → IsSquare (∏ i, a i) →
      ∃ e : Fin r → V, (∀ i j, h (e i) (e j) = if i = j then 1 else 0) ∧
        ∀ i, e i ∈ Submodule.span K (Set.range v) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro v a ha hv hsq
  rcases r with _ | _ | r
  · exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  · obtain ⟨s, hs⟩ := hsq
    rw [Fin.prod_univ_one] at hs
    have hs0 : (s : K) ≠ 0 := by
      have : s ≠ 0 := by
        rintro rfl
        have := ha 0
        rw [hs] at this
        simp at this
      exact_mod_cast this
    refine ⟨fun _ => ((s⁻¹ : ℚ) : K) • v 0, ?_, fun _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨0, rfl⟩)⟩
    intro i j
    have hij : i = j := Fin.ext (by have := i.2; have := j.2; omega)
    subst hij
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hv, if_true, map_ratCast,
      hs]
    push_cast
    field_simp
  · have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    obtain ⟨p₁, q₁, p₂, q₂, hq⟩ := exists_rat_sum_norm_forms_eq_one (ha 0) (ha 1) hdq
    have hqK : (a 0 : K) * ((p₁ : K) ^ 2 + (d : K) * (q₁ : K) ^ 2) +
        (a 1 : K) * ((p₂ : K) ^ 2 + (d : K) * (q₂ : K) ^ 2) = 1 := by
      exact_mod_cast hq
    have h01 : (0 : Fin (r + 2)) ≠ 1 := by simp
    have hss : ∀ i : Fin r, (i.succ.succ : Fin (r + 2)) ≠ 0 ∧ (i.succ.succ : Fin (r + 2)) ≠ 1 := by
      intro i
      refine ⟨Fin.succ_ne_zero _, ?_⟩
      rw [← Fin.succ_zero_eq_one, Ne, Fin.succ_inj]
      exact Fin.succ_ne_zero _
    have hv00 := hv 0 0
    have hv11 := hv 1 1
    have hv01 := hv 0 1
    have hv10 := hv 1 0
    simp only [if_true, h01, h01.symm, if_false] at hv00 hv11 hv01 hv10
    have hvs : ∀ (i : Fin r) (j : Fin (r + 2)), j = 0 ∨ j = 1 →
        h (v i.succ.succ) (v j) = 0 ∧ h (v j) (v i.succ.succ) = 0 := by
      intro i j hj
      rw [hv, hv]
      rcases hj with rfl | rfl
      · simp [(hss i).1, (hss i).1.symm]
      · simp [(hss i).2, (hss i).2.symm]
    set w : V := ((p₁ : K) + (q₁ : K) * θ) • v 0 + ((p₂ : K) + (q₂ : K) * θ) • v 1 with hw
    set w' : V := ((a 1 : K) * ((p₂ : K) - (q₂ : K) * θ)) • v 0 -
      ((a 0 : K) * ((p₁ : K) - (q₁ : K) * θ)) • v 1 with hw'
    have hww : h w w = 1 := by
      simp only [hw, map_add (f := _), map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, hv00, hv11, hv01, hv10, map_mul, map_ratCast, hθ]
      linear_combination hqK - ((a 0 : K) * (q₁ : K) ^ 2 + (a 1 : K) * (q₂ : K) ^ 2) * hθ2
    have hww' : h w w' = 0 := by
      simp only [hw, hw', map_add (f := _), map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hv00, hv11, hv01, hv10, map_mul,
        map_ratCast, hθ]
      ring
    have hw'w : h w' w = 0 := by
      simp only [hw, hw', map_add (f := _), map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hv00, hv11, hv01, hv10, map_mul,
        map_ratCast, hθ]
      ring
    have hw'w' : h w' w' = ((a 0 * a 1 : ℚ) : K) := by
      simp only [hw', map_sub, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, hv00, hv11, hv01, hv10, map_mul, map_ratCast, hθ, map_neg]
      push_cast
      linear_combination (a 0 : K) * (a 1 : K) * hqK -
        (a 0 : K) * (a 1 : K) * ((a 0 : K) * (q₁ : K) ^ 2 + (a 1 : K) * (q₂ : K) ^ 2) * hθ2
    have hwv : ∀ i : Fin r, h (v i.succ.succ) w = 0 ∧ h w (v i.succ.succ) = 0 := by
      intro i
      obtain ⟨h1, h1'⟩ := hvs i 0 (Or.inl rfl)
      obtain ⟨h2, h2'⟩ := hvs i 1 (Or.inr rfl)
      constructor
      · simp [hw, h1, h2]
      · simp [hw, h1', h2']
    have hw'v : ∀ i : Fin r, h (v i.succ.succ) w' = 0 ∧ h w' (v i.succ.succ) = 0 := by
      intro i
      obtain ⟨h1, h1'⟩ := hvs i 0 (Or.inl rfl)
      obtain ⟨h2, h2'⟩ := hvs i 1 (Or.inr rfl)
      constructor
      · simp [hw', h1, h2]
      · simp [hw', h1', h2']
    have hwspan : w ∈ Submodule.span K (Set.range v) :=
      add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    have hw'span : w' ∈ Submodule.span K (Set.range v) :=
      sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    let v' : Fin (r + 1) → V := Fin.cons w' (fun i => v i.succ.succ)
    let a' : Fin (r + 1) → ℚ := Fin.cons (a 0 * a 1) (fun i => a i.succ.succ)
    have ha' : ∀ i, 0 < a' i := by
      intro i
      cases i using Fin.cases with
      | zero => exact mul_pos (ha 0) (ha 1)
      | succ i => exact ha _
    have hv' : ∀ i j, h (v' i) (v' j) = if i = j then (a' i : K) else 0 := by
      intro i j
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => simpa [v', a'] using hw'w'
        | succ j => simpa [v', a', (Fin.succ_ne_zero j).symm] using (hw'v j).2
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa [v', a', Fin.succ_ne_zero i] using (hw'v i).1
        | succ j =>
          simp only [v', a', Fin.cons_succ, hv, Fin.succ_inj]
    have hsq' : IsSquare (∏ i, a' i) := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ] at hsq
      rw [Fin.prod_univ_succ]
      simp only [a', Fin.cons_zero, Fin.cons_succ]
      convert hsq using 1
      simp only [Fin.succ_zero_eq_one]
      ring
    obtain ⟨e', he', hspan'⟩ := ih (r + 1) (by omega) v' a' ha' hv' hsq'
    have hwe' : ∀ j, h (e' j) w = 0 ∧ h w (e' j) = 0 := by
      intro j
      refine sesq_apply_eq_zero_and_of_mem_span_of_forall_mem h ?_ (hspan' j)
      rintro _ ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero => exact ⟨by simpa [v'] using hw'w, by simpa [v'] using hww'⟩
      | succ i => simpa [v'] using hwv i
    have hle : Submodule.span K (Set.range v') ≤ Submodule.span K (Set.range v) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero => simpa [v'] using hw'span
      | succ i => exact Submodule.subset_span ⟨i.succ.succ, rfl⟩
    refine ⟨Fin.cons w e', ?_, ?_⟩
    · intro i j
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => simpa using hww
        | succ j => simpa [(Fin.succ_ne_zero j).symm] using (hwe' j).2
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa [Fin.succ_ne_zero i] using (hwe' i).1
        | succ j => simpa [Fin.succ_inj] using he' i j
    · intro i
      cases i using Fin.cases with
      | zero => simpa using hwspan
      | succ i => simpa using hle (hspan' i)


open NumberField in
open scoped Matrix ComplexConjugate in
theorem _root_.GlobalTheory.SqDet.exists_orthonormal_of_diag_pos_isSquare :
    ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (d : ℕ) (θ : K), 0 < d → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → ∀ (r : ℕ) (v : Fin r → V) (a : Fin r → ℚ), (∀ i, 0 < a i) → (∀ i j, h (v i) (v j) = if i = j then (a i : K) else 0) → IsSquare (∏ i, a i) → ∃ e : Fin r → V, ∀ i j, h (e i) (e j) = if i = j then 1 else 0 := by
  intro K V _ _ _ _ σ h d θ hd hθ2 hθ _ r v a ha hv hsq
  obtain ⟨e, he, -⟩ := exists_orthonormal_mem_span_of_diagonal_square_prod σ h hd hθ2 hθ r v a ha hv hsq
  exact ⟨e, he⟩

end GlobalTheory.SqDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeUAdjoint
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem adjoint_U : ∀ (k L N l : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → l.Prime → l ∣ L → ¬ l ∣ N → Wt L ρ → CF k L (ch ε) h → MF k L (ch ε) a → pet k ρ (qs h) (qs (Uo l a)) = pet k ρ (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) (qs a) := by
  intro k L N l ε ρ h a hk hL hNL hl hlL hlN hW hh ha
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNL hL
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
  have hpos : 0 < l := hl.pos
  obtain ⟨-, hUa⟩ := _root_.GlobalTheory.EisM.Uo_qs_sum_slz k l a hk hpos ha.1
  have hcontH : Continuous (qs h) := (_root_.GlobalTheory.EisM.qs_summable_continuous h hh.1.1).2
  have hcontA : Continuous (qs a) := (_root_.GlobalTheory.EisM.qs_summable_continuous a ha.1).2
  have hModA : Mod (qs a) := _root_.GlobalTheory.EisM.mod_qs_of_polyB a ha.1
  have hdet : ∀ j : Fin l, (repU l j).det = l := by
    intro j; simp [repU, Matrix.det_fin_two]
  have hint : ∀ i : Fin l, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * slz k (repU l i) (qs a) τ * (τ.im : ℂ) ^ k)) := by
    intro i
    have hd : 0 < (repU l i).det := by rw [hdet]; exact_mod_cast hpos
    exact _root_.GlobalTheory.EisM.integrable_pet_integrand k L L N ε h ρ _ hk hL hNL hW hh
      (((_root_.GlobalTheory.EisM.slz_props k (qs a) hk).2.2.2.1 _ hd hcontA).aestronglyMeasurable)
      ((_root_.GlobalTheory.EisM.mod_algebra).2.2 (qs a) k _ hd (by simp [repU]) hModA)
  have key := _root_.GlobalTheory.EisM.pet_hsum_adjoint k L N l ε ρ (DU L l) (Fin l) (Fin l) (repU l)
    (fun j => (repL L l (some j)).adjugate) (qs h) (qs a) hk hN hNL hpos hcop hW
    (by
      intro δ hδ
      obtain ⟨h1, h2, -⟩ := hδ
      exact ⟨h1, (Int.natCast_dvd_natCast.2 hNL).trans h2⟩)
    ((_root_.GlobalTheory.EisM.zrepU L l hl).1 hlL) (GlobalTheory.T.isRightGamma0CosetDecomposition_heckeU L l hL hl hlL) hh.1.2 ha.2 hcontH hcontA hint
  have e1 : qs (Uo l a) = hsum k (ch ε) (repU l) (qs a) := by
    funext τ
    rw [hUa τ]
    simp [hsum, repU, ch]
  have e2 : (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) =
      (fun τ => ∑ j, ch ε⁻¹ ((fun j => (repL L l (some j)).adjugate) j 0 0) *
        slz k ((fun j => (repL L l (some j)).adjugate) j).adjugate (qs h) τ) := by
    funext τ
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [repL, ch, Matrix.adjugate_fin_two_of]
  rw [e1, e2]
  exact key

end GlobalTheory
end

