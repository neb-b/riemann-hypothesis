module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorApproxCriticalRadius
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem kummer_approx_critical : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → v (p : L) < 1 → ∀ α : L, α ^ p ∈ F → 0 < v (p : L) →
    ∀ s : ℝ≥0, 1 < s → ∃ y ∈ F, v (α - y) ^ (p - 1) ≤ s * v (p : L) * v α ^ (p - 1) := by
  intro L _ v p hp F hF hvp α hα hvp0 s hs
  obtain ⟨θ, hθ, hθF⟩ := hF
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : p - 1 ≠ 0 := by omega
  by_cases hα0 : α = 0
  · refine ⟨0, F.zero_mem, ?_⟩
    simp [hα0, zero_pow hp1]
  by_contra hcon
  push_neg at hcon
  have hs0 : (0 : ℝ≥0) < s := zero_lt_one.trans hs
  have ha : 0 < v α := (Valuation.pos_iff v).2 hα0
  set a := v α with ha_def
  set c := s * v (p : L) * a ^ (p - 1) with hc_def
  have hc : 0 < c := by positivity
  set η : ℝ≥0 := max s⁻¹ (max θ (v (p : L))) with hη_def
  have hη : η < 1 := by
    simp only [hη_def, max_lt_iff]
    exact ⟨inv_lt_one_of_one_lt₀ hs, hθ, hvp⟩
  have step : ∀ y ∈ F, v (α - y) ≤ a → ∃ y' ∈ F, v (α - y') ^ p ≤ η * v (α - y) ^ p := by
    intro y hy hya
    obtain ⟨y', hy', h⟩ := _root_.GlobalTheory.AlmostEt.exists_approxRoot_step L v p hp F θ hθ.le hvp.le hθF α y hα hy hya
    refine ⟨y', hy', h.trans ?_⟩
    have hcb := hcon y hy
    set b := v (α - y)
    apply max_le
    · have h0 : s * (v (p : L) * a ^ (p - 1)) ≤ b ^ (p - 1) := by
        calc s * (v (p : L) * a ^ (p - 1)) = c := by rw [hc_def]; ring
          _ ≤ _ := hcb.le
      have h2 : v (p : L) * a ^ (p - 1) ≤ s⁻¹ * b ^ (p - 1) := by
        calc v (p : L) * a ^ (p - 1) = s⁻¹ * (s * (v (p : L) * a ^ (p - 1))) := (inv_mul_cancel_left₀ hs0.ne' _).symm
          _ ≤ s⁻¹ * b ^ (p - 1) := by gcongr
      have h1 : v (p : L) * b * a ^ (p - 1) ≤ s⁻¹ * b ^ p := by
        calc v (p : L) * b * a ^ (p - 1) = b * (v (p : L) * a ^ (p - 1)) := by ring
          _ ≤ b * (s⁻¹ * b ^ (p - 1)) := by gcongr
          _ = s⁻¹ * (b ^ (p - 1) * b) := by ring
          _ = s⁻¹ * b ^ p := by rw [← pow_succ]; congr 2; omega
      exact h1.trans (by gcongr; exact le_max_left _ _)
    · gcongr; exact le_max_right _ _
  have iter : ∀ k : ℕ, ∃ y ∈ F, v (α - y) ≤ a ∧ v (α - y) ^ p ≤ η ^ k * a ^ p := by
    intro k
    induction k with
    | zero => exact ⟨0, F.zero_mem, by simp [ha_def], by simp [ha_def]⟩
    | succ k ih =>
      obtain ⟨y, hy, hya, hyk⟩ := ih
      obtain ⟨y', hy', h'⟩ := step y hy hya
      have hle : v (α - y') ^ p ≤ v (α - y) ^ p :=
        h'.trans (mul_le_of_le_one_left (by positivity) hη.le)
      refine ⟨y', hy', ?_, ?_⟩
      · exact ((pow_le_pow_iff_left₀ (by positivity) (by positivity) hp.ne_zero).1 hle).trans hya
      · calc v (α - y') ^ p ≤ η * v (α - y) ^ p := h'
          _ ≤ η * (η ^ k * a ^ p) := by gcongr
          _ = η ^ (k + 1) * a ^ p := by ring
  have hA : 0 < (a ^ p) ^ (p - 1) := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos (pow_pos hc p) hA) hη
  obtain ⟨y, hy, -, hyk⟩ := iter k
  have hcb := hcon y hy
  have e1 : c ^ p < (v (α - y) ^ p) ^ (p - 1) := by
    calc c ^ p < (v (α - y) ^ (p - 1)) ^ p := pow_lt_pow_left₀ hcb (by positivity) hp.ne_zero
      _ = _ := by rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : (v (α - y) ^ p) ^ (p - 1) ≤ η ^ k * (a ^ p) ^ (p - 1) := by
    calc (v (α - y) ^ p) ^ (p - 1) ≤ (η ^ k * a ^ p) ^ (p - 1) := pow_le_pow_left₀ (by positivity) hyk _
      _ = (η ^ k) ^ (p - 1) * (a ^ p) ^ (p - 1) := mul_pow _ _ _
      _ ≤ η ^ k * (a ^ p) ^ (p - 1) :=
          mul_le_mul_of_nonneg_right (pow_le_of_le_one (by positivity) (pow_le_one₀ (by positivity) hη.le) hp1) (by positivity)
  have e3 : η ^ k * (a ^ p) ^ (p - 1) < c ^ p := (lt_div_iff₀ hA).1 hk
  exact lt_irrefl _ ((e1.trans_le e2).trans e3)

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerRootMem
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem kummer_root_mem : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ), 0 < m → ∀ (f : X.Kˣ) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → ∃ g : X.Kˣ, f = g ^ m := by
  intro Ω _ _ _ ε X _ _ m hm f a b M hM ha hb hb0 hfab hinv
  have hHs_open : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hHs_conn : IsPreconnected Hs :=
    (convex_halfSpace_gt Complex.imLm.isLinear (0 : ℝ)).isPreconnected
  have hbne : ∀ᶠ z in Filter.codiscreteWithin Hs, b z ≠ 0 := by
    rcases (hb.analyticOnNhd hHs_open).eqOn_zero_or_eventually_ne_zero_of_preconnected hHs_conn with h | h
    · exfalso; apply hb0
      exact Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) (fun z hz => h hz))
    · exact h
  have hrep : ∀ x : Mero, ∃ φ : ℂ → ℂ, x = (φ : Mero) := fun x =>
    Filter.Germ.inductionOn x (fun φ => ⟨φ, rfl⟩)
  obtain ⟨φ, hφ⟩ := hrep (X.an (f : X.K))
  rw [hφ, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul] at hfab
  have h1 : ∀ᶠ z in Filter.codiscreteWithin Hs, φ z * b z ^ m = a z ^ m :=
    (Filter.Germ.coe_eq.1 hfab).mono fun z hz => by simpa using hz
  have h2 : ∀ᶠ z in Filter.codiscreteWithin Hs, (a z / b z) ^ m = φ z := by
    filter_upwards [h1, hbne] with z hz hbz
    rw [div_pow, div_eq_iff (pow_ne_zero _ hbz), hz]
  have hpoly : ∃ P : Polynomial X.K, P ≠ 0 ∧ P.eval₂ X.an (((a / b : ℂ → ℂ)) : Mero) = 0 := by
    refine ⟨Polynomial.X ^ m - Polynomial.C (f : X.K), Polynomial.X_pow_sub_C_ne_zero hm _, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hφ, ← Filter.Germ.coe_pow, sub_eq_zero]
    exact Filter.Germ.coe_eq.2 (h2.mono fun z hz => by simpa using hz)
  obtain ⟨g0, hg0⟩ := X.sat a b M hM ha hb hb0 hinv hpoly
  obtain ⟨ψ, hψ⟩ := hrep (X.an g0)
  rw [hψ, ← Filter.Germ.coe_mul] at hg0
  have h3 : ∀ᶠ z in Filter.codiscreteWithin Hs, ψ z * b z = a z :=
    (Filter.Germ.coe_eq.1 hg0).mono fun z hz => by simpa using hz
  haveI : Nontrivial Mero := ⟨⟨_, _, hb0⟩⟩
  have hpow : g0 ^ m = (f : X.K) := by
    apply X.an.injective
    rw [map_pow, hψ, hφ, ← Filter.Germ.coe_pow]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [h2, h3, hbne] with z hz2 hz3 hbz
    have : ψ z = a z / b z := by rw [eq_div_iff hbz, hz3]
    simp only [Pi.pow_apply]
    rw [this, hz2]
  have hg0ne : g0 ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hpow
    exact f.ne_zero hpow.symm
  refine ⟨Units.mk0 g0 hg0ne, ?_⟩
  ext
  simp [hpow]

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingPrincipalMinorMulModConductor
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

namespace GlobalTheory.PsType.MinorMul

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_of_val_le {χ : kˣ →* ℂˣ} {x y : k} (h : valuation k y ≤ valuation k x) (hx : Triv χ x) : Triv χ y :=
  fun u hu hle => hx u hu (hle.trans h)

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ (0 : k) := by
  intro u _ hle
  rw [map_zero, le_zero_iff, map_eq_zero, sub_eq_zero] at hle
  have : u = 1 := Units.ext hle
  simp [this]

def trivIdeal (χ : kˣ →* ℂˣ) : Ideal 𝒪[k] where
  carrier := {x | Triv χ (x : k)}
  zero_mem' := triv_zero χ
  add_mem' {x y} hx hy := by
    show Triv χ ((x : k) + y)
    rcases le_max_iff.1 (Valuation.map_add (valuation k) (x : k) y) with h | h
    · exact triv_of_val_le h hx
    · exact triv_of_val_le h hy
  smul_mem' c x hx := by
    show Triv χ ((c : k) * x)
    refine triv_of_val_le ?_ hx
    rw [map_mul]
    exact mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 c.2)

theorem mem_trivIdeal {χ : kˣ →* ℂˣ} {x : 𝒪[k]} : x ∈ trivIdeal χ ↔ Triv χ (x : k) := Iff.rfl

theorem isUnit_of_isUnit_mk {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤) {x : R}
    (hx : IsUnit (Ideal.Quotient.mk I x)) : IsUnit x := by
  by_contra hn
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : x * y - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hy, map_one, sub_self]
  have hm : x * y ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal x).2 hn)
  have h2 := (IsLocalRing.le_maximalIdeal hI) h1
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ hm h2
    rwa [sub_sub_cancel] at this
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem toSquareBlockProp_mul {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (M N : Matrix ι ι R) (h : ∀ i, p i → ∀ j, ¬ p j → M i j = 0) :
    (M * N).toSquareBlockProp p = M.toSquareBlockProp p * N.toSquareBlockProp p := by
  have h0 : (M.toBlock p fun i => ¬ p i) = 0 := by
    ext i j; exact h i i.2 j j.2
  unfold toSquareBlockProp
  rw [toBlock_mul_eq_add p p p M N, h0, Matrix.zero_mul, add_zero]

theorem minor_map {n : ℕ} (u : GL (Fin n) 𝒪[k]) (m : Fin n) :
    minor (GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) m =
      algebraMap 𝒪[k] k ((u.val.toSquareBlockProp fun i => i ≤ m).det) := by
  rw [RingHom.map_det]; rfl

end GlobalTheory.PsType.MinorMul

open GlobalTheory.PsType.MinorMul in
theorem GlobalTheory.PsType.minor_mul_mod : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ m : Fin n, ¬ Triv (ψ m / nxt ψ m) 1 → (∀ a ∈ grp ψ, valuation k (minor a m) = 1) ∧ ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, Triv (ψ m / nxt ψ m) (minor (a * b) m - minor a m * minor b m) := by
  intro k _ _ _ _ n ψ hψ m hm
  set χ := ψ m / nxt ψ m with hχ
  set I := trivIdeal χ with hIdef
  have hI : I ≠ ⊤ := by
    intro h
    have : (1 : 𝒪[k]) ∈ I := h ▸ Submodule.mem_top
    exact hm (by have h2 := (mem_trivIdeal (χ := χ) (x := 1)).1 this; simpa using h2)

  have hent : ∀ a ∈ grp ψ, ∀ i j : Fin n, i ≤ m → ¬ j ≤ m → Triv χ (a.val i j) := by
    intro a ha i j hi hj
    have hj' : m < j := not_le.1 hj
    have hlt : (m : ℕ) + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt (Fin.lt_def.1 hj')) j.2
    have hnx : nxt ψ m = ψ ⟨(m : ℕ) + 1, hlt⟩ := dif_pos hlt
    have h1 := ha.2 i j (lt_of_le_of_lt hi hj')
    rw [hχ, hnx]
    exact hψ i m ⟨(m : ℕ) + 1, hlt⟩ j hi (Fin.le_def.2 (Nat.le_succ _))
      (Fin.le_def.2 (Nat.succ_le_of_lt (Fin.lt_def.1 hj'))) _ h1

  have hzero : ∀ u : GL (Fin n) 𝒪[k], GeneralLinearGroup.map (algebraMap 𝒪[k] k) u ∈ grp ψ →
      ∀ i, i ≤ m → ∀ j, ¬ j ≤ m → (Ideal.Quotient.mk I).mapMatrix u.val i j = 0 := by
    intro u hu i hi j hj
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hent _ hu i j hi hj)
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨u, rfl⟩ := ha.1
    rw [minor_map]
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 ?_
    refine isUnit_of_isUnit_mk hI ?_
    have hdet : IsUnit ((Ideal.Quotient.mk I).mapMatrix u.val).det := by
      rw [← RingHom.map_det]
      exact (Matrix.isUnits_det_units u).map _
    rw [twoBlockTriangular_det' _ (fun i => i ≤ m) (hzero u ha)] at hdet
    have := isUnit_of_mul_isUnit_left hdet
    rwa [show (((Ideal.Quotient.mk I).mapMatrix u.val).toSquareBlockProp fun i => i ≤ m) =
      (Ideal.Quotient.mk I).mapMatrix (u.val.toSquareBlockProp fun i => i ≤ m) from rfl, ← RingHom.map_det] at this
  · intro a ha b hb
    obtain ⟨u, rfl⟩ := ha.1
    obtain ⟨w, rfl⟩ := hb.1
    rw [← map_mul, minor_map, minor_map, minor_map, ← map_mul, ← map_sub]
    suffices hs : (((u * w).val.toSquareBlockProp fun i => i ≤ m).det -
        (u.val.toSquareBlockProp fun i => i ≤ m).det * (w.val.toSquareBlockProp fun i => i ≤ m).det) ∈ I from hs
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, RingHom.map_det, RingHom.map_det, RingHom.map_det, sub_eq_zero,
      ← det_mul]
    congr 1
    rw [Units.val_mul]
    show ((Ideal.Quotient.mk I).mapMatrix (u.val * w.val)).toSquareBlockProp (fun i => i ≤ m) = _
    rw [map_mul, toSquareBlockProp_mul _ _ _ (hzero u ha)]
    rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumSubgroupCharacterProperties
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.LevGroup

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

theorem isUp_one : IsUp g N 1 :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne']⟩

theorem isUp_mul {u v : GG g N} (hu : IsUp g N u) (hv : IsUp g N v) : IsUp g N (u * v) := by
  refine ⟨fun a => ?_, fun a c h => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hu.1, hv.1, mul_one]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hu.2 a b h, zero_mul]
      · rw [hv.2 b a h, mul_zero]
    · simp
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases lt_or_ge b a with h' | h'
    · rw [hu.2 a b h', zero_mul]
    · rw [hv.2 b c (lt_of_lt_of_le h h'), mul_zero]

theorem mul_entry {u v : GG g N} (hu : IsUp g N u) (hv : IsUp g N v) {a c : Fin N} (hac : a < c)
    (h : ∀ b, a < b → b < c → u.val a b * v.val b c = 0) : (u * v).val a c = u.val a c + v.val a c := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a c (Finset.mem_univ _) (Finset.mem_univ _) hac.ne]
  · rw [hu.1, hv.1, one_mul, mul_one, add_comm]
  · rintro b _ ⟨h1, h2⟩
    rcases lt_or_gt_of_ne h1 with h1 | h1
    · rw [hu.2 a b h1, zero_mul]
    rcases lt_or_gt_of_ne h2 with h2 | h2
    · exact h b h1 h2
    · rw [hv.2 b c h2, mul_zero]

theorem isNilpotent_of_isUp {u : GG g N} (hu : IsUp g N u) : IsNilpotent (u.val - 1) := by
  have ht : (u.val - 1).BlockTriangular id := by
    intro a b h
    have h' : b < a := h
    simp [Matrix.sub_apply, hu.2 a b h', Matrix.one_apply_ne h'.ne']
  have hc := Matrix.aeval_self_charpoly (u.val - 1)
  rw [Matrix.charpoly_of_upperTriangular _ ht] at hc
  refine ⟨N, ?_⟩
  simpa [Matrix.sub_apply, hu.1] using hc

theorem edge_lt (L : Lev g N) {a b : Fin N} (h : L.Edge a b) : a < b := by
  unfold Lev.Edge at h
  rw [Fin.lt_def]
  split_ifs at h <;> omega

theorem mem_one (L : Lev g N) : L.Mem 1 := by
  refine ⟨isUp_one, fun _ a b _ h2 h3 => ?_⟩
  have : a ≠ b := fun h => by subst h; omega
  simp [Matrix.one_apply_ne this]

theorem mem_mul (L : Lev g N) {u v : GG g N} (hu : L.Mem u) (hv : L.Mem v) : L.Mem (u * v) := by
  refine ⟨isUp_mul hu.1 hv.1, fun hs a c h1 h2 h3 => ?_⟩
  rw [mul_entry hu.1 hv.1 (by rw [Fin.lt_def]; omega), hu.2 hs a c h1 h2 h3, hv.2 hs a c h1 h2 h3, add_zero]
  intro b hb hc
  rw [Fin.lt_def] at hb hc
  rw [hv.2 hs b c (by omega) (by omega) h3, mul_zero]

theorem edge_mul (L : Lev g N) {u v : GG g N} (hu : L.Mem u) (hv : L.Mem v) {a c : Fin N} (h : L.Edge a c) :
    (u * v).val a c = u.val a c + v.val a c := by
  refine mul_entry hu.1 hv.1 (edge_lt L h) fun b hb hc => ?_
  rw [Fin.lt_def] at hb hc
  unfold Lev.Edge at h
  split_ifs at h with hs
  · rcases h with h | h
    · omega
    · rw [hv.2 hs b c (by omega) (by omega) h.2, mul_zero]
  · omega

theorem chi_one (L : Lev g N) : L.chi 1 = 1 := by
  unfold Lev.chi
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one]
  refine fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with h
  · simp [Matrix.one_apply_ne (edge_lt L h).ne]
  · rfl

theorem chi_mul (L : Lev g N) {u v : GG g N} (hu : L.Mem u) (hv : L.Mem v) : L.chi (u * v) = L.chi u * L.chi v := by
  unfold Lev.chi
  rw [← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [edge_mul L hu hv h, mul_add]
  · simp

theorem lev_group : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, L.Mem 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.Mem (u * v)) ∧ L.chi 1 = 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.chi (u * v) = L.chi u * L.chi v) ∧ ∀ u, L.Mem u → IsNilpotent (u.val - 1) :=
  fun _ _ _ L => ⟨mem_one L, fun _ _ => mem_mul L, chi_one L, fun _ _ => chi_mul L, fun _ hu => isNilpotent_of_isUp hu.1⟩

end GlobalTheory.BadShare.LevGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPowerUnitsTowerClosureProperties
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.UnClosure

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem one_mem (X : Tower Ω ε) (m : ℕ) : 1 ∈ X.Un m := by
  intro W _
  exact ⟨1, by simp⟩

theorem mul_mem (X : Tower Ω ε) (m : ℕ) (f g : X.Kˣ) (hf : f ∈ X.Un m) (hg : g ∈ X.Un m) :
    f * g ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  obtain ⟨b, hb⟩ := hg W hW
  refine ⟨a * b, ?_⟩
  have e : ((f * g : X.Kˣ) : X.K) / ((a * b : X.Kˣ) : X.K) ^ m
      = ((f : X.K) / (a : X.K) ^ m) * ((g : X.K) / (b : X.K) ^ m) := by
    push_cast; rw [mul_pow]; field_simp
  rw [e, map_mul, ha, hb, one_mul]

theorem inv_mem (X : Tower Ω ε) (m : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un m) : f⁻¹ ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  refine ⟨a⁻¹, ?_⟩
  have e : ((f⁻¹ : X.Kˣ) : X.K) / ((a⁻¹ : X.Kˣ) : X.K) ^ m = ((f : X.K) / (a : X.K) ^ m)⁻¹ := by
    push_cast; rw [inv_pow]; field_simp
  rw [e, map_inv₀, ha, inv_one]

theorem pow_mem_self (X : Tower Ω ε) (m : ℕ) (g : X.Kˣ) : g ^ m ∈ X.Un m := by
  intro W _
  refine ⟨g, ?_⟩
  have e : ((g ^ m : X.Kˣ) : X.K) / (g : X.K) ^ m = 1 := by
    push_cast; exact div_self (pow_ne_zero _ g.ne_zero)
  rw [e, map_one]

theorem mem_of_mem_mul (X : Tower Ω ε) (m k : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un (m * k)) : f ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  refine ⟨a ^ k, ?_⟩
  have e : ((a ^ k : X.Kˣ) : X.K) ^ m = (a : X.K) ^ (m * k) := by
    push_cast; rw [← pow_mul, mul_comm]
  rw [e]; exact ha

theorem pow_mem (X : Tower Ω ε) (m k : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un m) : f ^ k ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  refine ⟨a ^ k, ?_⟩
  have e : ((f ^ k : X.Kˣ) : X.K) / ((a ^ k : X.Kˣ) : X.K) ^ m = ((f : X.K) / (a : X.K) ^ m) ^ k := by
    push_cast; rw [div_pow, ← pow_mul, ← pow_mul, mul_comm m k]
  rw [e, map_pow, ha, one_pow]

theorem val_eq_one_of_pow {K : Type} [Field K] (W : ValuationSubring K) (x : K) (m : ℕ) (hm : 0 < m)
    (h : W.valuation (x ^ m) = 1) : W.valuation x = 1 := by
  rw [map_pow] at h
  exact (pow_eq_one_iff.1 h).resolve_right hm.ne'

theorem mem_of_pow_mem (X : Tower Ω ε) (m k : ℕ) (g : X.Kˣ) (hm : 0 < m) (hg : g ^ m ∈ X.Un (m * k)) :
    g ∈ X.Un k := by
  intro W hW
  obtain ⟨a, ha⟩ := hg W hW
  refine ⟨a, val_eq_one_of_pow W _ m hm ?_⟩
  have e : ((g : X.K) / (a : X.K) ^ k) ^ m = ((g ^ m : X.Kˣ) : X.K) / (a : X.K) ^ (m * k) := by
    push_cast; rw [div_pow, ← pow_mul, mul_comm k m]
  rw [e]; exact ha

end GlobalTheory.KZ.UnClosure

namespace GlobalTheory.KZ.UnClosure

theorem un_closure : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (m : ℕ), 1 ∈ X.Un m ∧ (∀ f g, f ∈ X.Un m → g ∈ X.Un m → f * g ∈ X.Un m) ∧ (∀ f, f ∈ X.Un m → f⁻¹ ∈ X.Un m) ∧
      (∀ g : X.Kˣ, g ^ m ∈ X.Un m) ∧ (∀ (k : ℕ) f, f ∈ X.Un (m * k) → f ∈ X.Un m) ∧
      (∀ (k : ℕ) f, f ∈ X.Un m → f ^ k ∈ X.Un m) ∧
      ∀ (k : ℕ) (g : X.Kˣ), 0 < m → g ^ m ∈ X.Un (m * k) → g ∈ X.Un k := by
  intro Ω _ _ _ ε X _ _ m
  exact ⟨one_mem X m, mul_mem X m, inv_mem X m, pow_mem_self X m, fun k f hf => mem_of_mem_mul X m k f hf,
    fun k f hf => pow_mem X m k f hf, fun k g hm hg => mem_of_pow_mem X m k g hm hg⟩

end GlobalTheory.KZ.UnClosure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem specialLinearGroup_map_intCast_zmod_surjective :
    ∀ (M : ℕ), Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) :
      SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod M)) :=
  fun M => GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) M

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.XMulMemSpanOfColemanLevelsStatement
section
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_mul_mem_span_of_colemanLevels : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime], IsDomain R → Prime (p : R) → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (h : PowerSeries R) (k c : ℕ), (∀ r, 1 ≤ r → r ≤ k → ∃ y : PowerSeries R, ev R p r h = ev R p r ((p : PowerSeries R) ^ c * y)) → ∀ j, j ≤ k → j ≤ c → X * h ∈ Ideal.span {(p : PowerSeries R) ^ (c - j), (1 + X) ^ (p ^ j) - 1} := by
  first | exact @GlobalTheory.Col.X_mul_mem_span_of_levels | exact GlobalTheory.Col.X_mul_mem_span_of_levels | (intros; apply GlobalTheory.Col.X_mul_mem_span_of_levels <;> assumption)
end

