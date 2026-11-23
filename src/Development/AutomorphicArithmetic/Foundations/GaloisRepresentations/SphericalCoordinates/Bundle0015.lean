module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2740

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPlaceLoc
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

private theorem formB_add_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (a b c : VQ D) : formB L β (a + b) c = formB L β a c + formB L β b c := by
  simp only [formB, map_add (f := _), LinearMap.add_apply]

private theorem formB_nsmul_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℕ) (a c : VQ D) : formB L β (n • a) c = n * formB L β a c := by
  simp only [formB, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]

private theorem formB_add_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (a b c : VQ D) : formB L β a (b + c) = formB L β a b + formB L β a c := by
  simp only [formB, map_add (f := _)]

private theorem formB_nsmul_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℕ) (a c : VQ D) : formB L β a (n • c) = n * formB L β a c := by
  simp only [formB, map_nsmul, nsmul_eq_mul]

private theorem formB_zsmul_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℤ) (a c : VQ D) : formB L β a (n • c) = n * formB L β a c := by
  simp only [formB, map_zsmul, zsmul_eq_mul]

private theorem den_dvd_of_mul_eq_int (q : ℚ) (n : ℕ) (z : ℤ) (h : (n : ℚ) * q = z) : q.den ∣ n := by
  have h1 : (n : ℤ) * q.num = z * q.den := by
    have h2 : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
    have h3 : (((n : ℤ) * q.num : ℤ) : ℚ) = ((z * q.den : ℤ) : ℚ) := by
      push_cast
      rw [h2, ← _root_.mul_assoc, h]
    exact_mod_cast h3
  have h3 : (q.den : ℤ) ∣ n * q.num := ⟨z, by rw [h1]; ring⟩
  have h4 : IsCoprime (q.den : ℤ) q.num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact q.reduced
  exact Int.natCast_dvd_natCast.1 (h4.dvd_of_dvd_mul_right h3)

theorem placeLoc_of : PlaceLoc := by
  intro p _ D G L β D' j hP hH
  obtain ⟨-, hact, hspan, s0, hs0, hform⟩ := hP
  obtain ⟨E₁, hE, e, he, hperf⟩ := hH
  have hE1 : ∀ u u', (E₁ u u' : ℚ) = (s0 / 2) * formB L β (j u) (j u') := by
    intro u u'
    have h := hform u u'
    rw [hE] at h
    simp only [LinearMap.smul_apply, smul_eq_mul] at h
    push_cast at h
    linarith
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ D'.La).FG)
  have hcl0 : AddSubgroup.closure (S : Set D'.La) = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have hu : u ∈ Submodule.span ℤ (S : Set D'.La) := hS ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem (hx trivial) (hy trivial)
    | smul a x _ hx => exact zsmul_mem (hx trivial) a
  have hcl : AddSubgroup.closure ((S.image j : Finset (VQ D)) : Set (VQ D)) = j.range := by
    rw [Finset.coe_image, ← AddMonoidHom.map_closure, hcl0, AddMonoidHom.range_eq_map]
  let M : AddSubgroup (VQ D) :=
    { carrier := {w | ∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u}
      add_mem' := by
        rintro a b ⟨m, u, hm, hu⟩ ⟨m', u', hm', hu'⟩
        refine ⟨m * m', m' • u + m • u', hm.mul_left hm', ?_⟩
        rw [map_add (f := _), map_nsmul, map_nsmul, ← hu, ← hu', smul_add, smul_smul, smul_smul, mul_comm m' m]
      zero_mem' := ⟨1, 0, Nat.coprime_one_left p, by simp⟩
      neg_mem' := by
        rintro a ⟨m, u, hm, hu⟩
        exact ⟨m, -u, hm, by rw [map_neg, ← hu, smul_neg]⟩ }
  have hM : ∀ w, w ∈ M ↔ ∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u := fun w => Iff.rfl
  refine ⟨M, ⟨?_, S.image j, ?_, ?_⟩, ⟨s0 / 2, by positivity, ?_⟩, fun w => (hM w).symm⟩
  · rintro c w ⟨m, u, hm, h⟩
    exact ⟨m, c • u, hm, by rw [hact, ← h, map_nsmul]⟩
  · rw [eq_top_iff]
    intro w _
    obtain ⟨m, u, hm, h⟩ := hspan w
    have hu : j u ∈ AddSubgroup.closure ((S.image j : Finset (VQ D)) : Set (VQ D)) := hcl ▸ ⟨u, rfl⟩
    have hu' : j u ∈ Submodule.span ℚ ((S.image j : Finset (VQ D)) : Set (VQ D)) :=
      (AddSubgroup.closure_le (Submodule.span ℚ ((S.image j : Finset (VQ D)) : Set (VQ D))).toAddSubgroup).2
        Submodule.subset_span hu
    have hw : w = (m : ℚ)⁻¹ • j u := by
      rw [← h, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm), one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ hu'
  · intro w
    rw [hcl]
    constructor
    · rintro ⟨m, u, hm, h⟩
      exact ⟨m, hm, ⟨u, h.symm⟩⟩
    · rintro ⟨m, hm, u, h⟩
      exact ⟨m, u, hm, h.symm⟩
  · intro w
    constructor
    · rintro ⟨m, a, hm, ha⟩ u ⟨m', b, hm', hb⟩
      have key : ((m * m' : ℕ) : ℚ) * (s0 / 2 * formB L β w u) = (E₁ a b : ℤ) := by
        rw [hE1, ← ha, ← hb, formB_nsmul_left, formB_nsmul_right]
        push_cast
        ring
      exact Nat.Coprime.coprime_dvd_left (den_dvd_of_mul_eq_int _ _ _ key) (hm.mul_left hm')
    · intro h
      have hden : ∀ x : D'.La, (s0 / 2 * formB L β w (j x)).den.Coprime p := fun x =>
        h (j x) ⟨1, x, Nat.coprime_one_left p, one_smul _ _⟩
      let m : ℕ := ∏ x ∈ S, (s0 / 2 * formB L β w (j x)).den
      have hm : m.Coprime p := Nat.Coprime.prod_left fun x _ => hden x
      have hint : ∀ u : D'.La, ∃ z : ℤ, (z : ℚ) = m * (s0 / 2 * formB L β w (j u)) := by
        intro u
        have hu : u ∈ Submodule.span ℤ (S : Set D'.La) := hS ▸ Submodule.mem_top
        induction hu using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun x => (s0 / 2 * formB L β w (j x)).den) hx
          refine ⟨r * (s0 / 2 * formB L β w (j x)).num, ?_⟩
          have h2 := Rat.mul_den_eq_num (s0 / 2 * formB L β w (j x))
          change (((r : ℤ) * (s0 / 2 * formB L β w (j x)).num : ℤ) : ℚ) = ((∏ x ∈ S, (s0 / 2 * formB L β w (j x)).den : ℕ) : ℚ) * _
          rw [hr]
          push_cast
          rw [← h2]
          ring
        | zero =>
          refine ⟨0, ?_⟩
          have h0 : formB L β w (j 0) = 0 := by
            have := formB_nsmul_right L β 0 w (0 : VQ D)
            simpa using this
          rw [h0]
          simp
        | add x y _ _ hx hy =>
          obtain ⟨a, ha⟩ := hx
          obtain ⟨b, hb⟩ := hy
          refine ⟨a + b, ?_⟩
          rw [map_add (f := _), formB_add_right]
          push_cast
          rw [ha, hb]
          ring
        | smul a x _ hx =>
          obtain ⟨b, hb⟩ := hx
          refine ⟨a * b, ?_⟩
          rw [map_zsmul, formB_zsmul_right]
          push_cast
          rw [hb]
          ring
      choose c hc using hint
      let f : D'.La →ₗ[ℤ] ℤ := AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' c (fun a b => by
        have h3 : ((c (a + b) : ℤ) : ℚ) = ((c a + c b : ℤ) : ℚ) := by
          push_cast
          rw [hc, hc, hc, map_add (f := _), formB_add_right]
          ring
        exact_mod_cast h3))
      obtain ⟨x, hx⟩ := hperf f
      obtain ⟨z, hz⟩ : ∃ z, z + j x = (e * m) • w := ⟨(e * m) • w - j x, sub_add_cancel _ _⟩
      have hs : s0 / 2 ≠ 0 := by positivity
      have hzero : ∀ u, formB L β z (j u) = 0 := by
        intro u
        have h1 : E₁ x u = e • c u := by
          have := LinearMap.congr_fun hx u
          simpa [f] using this
        have h2 : (E₁ x u : ℚ) = e * (m * (s0 / 2 * formB L β w (j u))) := by
          rw [h1, ← hc]
          push_cast
          simp
        rw [hE1] at h2
        have h3 : formB L β (z + j x) (j u) = ((e * m : ℕ) : ℚ) * formB L β w (j u) := by
          rw [hz, formB_nsmul_left]
        rw [formB_add_left] at h3
        have h4 : s0 / 2 * formB L β z (j u) = 0 := by
          have h5 : s0 / 2 * (formB L β z (j u) + formB L β (j x) (j u)) =
              s0 / 2 * (((e * m : ℕ) : ℚ) * formB L β w (j u)) := by rw [h3]
          push_cast at h5
          linarith
        exact (mul_eq_zero.1 h4).resolve_left hs
      obtain ⟨k, u₁, hk, hu₁⟩ := hspan z
      have hEF : ∀ u, D'.EF u₁ u = 0 := by
        intro u
        have h1 := hform u₁ u
        rw [← hu₁, formB_nsmul_left, hzero u] at h1
        simpa using h1
      have hu₀ : u₁ = 0 := D'.nondeg _ hEF
      have hz0 : z = 0 := by
        rw [hu₀, map_zero, ← Nat.cast_smul_eq_nsmul ℚ] at hu₁
        exact (smul_eq_zero.1 hu₁).resolve_left (by exact_mod_cast hk)
      refine ⟨e * m, x, he.mul_left hm, ?_⟩
      rw [← hz, hz0, zero_add]

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPlacePer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_extend {M V E : Type} [AddCommGroup M] [AddCommGroup V] [AddCommGroup E] [Module ℚ E]
    (j : M →+ V) (hj : Function.Injective j) (hd : ∀ w, ∃ (m : ℕ) (u : M), m ≠ 0 ∧ m • w = j u) (P : M →+ E) :
    ∃ Q : V →+ E, ∀ u, Q (j u) = P u := by
  choose m u hm h using hd
  have key : ∀ w (n : ℕ) (v : M), n ≠ 0 → n • w = j v →
      ((m w : ℚ)⁻¹) • P (u w) = ((n : ℚ)⁻¹) • P v := by
    intro w n v hn hv
    have h1 : n • u w = m w • v := hj (by
      rw [map_nsmul, map_nsmul, ← h w, ← hv, smul_comm])
    have h2 : n • P (u w) = m w • P v := by rw [← map_nsmul, ← map_nsmul, h1]
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hm' : (m w : ℚ) ≠ 0 := by exact_mod_cast hm w
    have h3 : (n : ℚ) • P (u w) = (m w : ℚ) • P v := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, h2]
    calc ((m w : ℚ)⁻¹) • P (u w) = ((m w : ℚ)⁻¹ * (n : ℚ)⁻¹) • ((n : ℚ) • P (u w)) := by
          rw [smul_smul]; congr 1; field_simp
      _ = ((n : ℚ)⁻¹) • P v := by rw [h3, smul_smul]; congr 1; field_simp
  refine ⟨AddMonoidHom.mk' (fun w => ((m w : ℚ)⁻¹) • P (u w)) ?_, ?_⟩
  · intro a b
    have hab : (m a * m b) • (a + b) = j (m b • u a + m a • u b) := by
      rw [map_add (f := _), map_nsmul, map_nsmul, ← h a, ← h b, smul_add, mul_smul, mul_smul,
        smul_comm (m a) (m b) a]
    have hk := key (a + b) (m a * m b) _ (mul_ne_zero (hm a) (hm b)) hab
    have hma : (m a : ℚ) ≠ 0 := by exact_mod_cast hm a
    have hmb : (m b : ℚ) ≠ 0 := by exact_mod_cast hm b
    rw [hk, map_add (f := _), map_nsmul, map_nsmul, smul_add, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, smul_smul]
    push_cast
    congr 2 <;> field_simp
  · intro v
    have hk := key (j v) 1 v one_ne_zero (by simp)
    simpa using hk

private theorem finrank_eq_of_place {M V : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    [AddCommGroup V] [Module ℚ V] (j : M →+ V) (hj : Function.Injective j)
    (hd : ∀ w, ∃ (m : ℕ) (u : M), m ≠ 0 ∧ m • w = j u) :
    Module.finrank ℤ M = Module.finrank ℚ V :=
  _root_.UpperTheory.Reformulated.B.FinrankIntEqFinrankRat.finrank_eq_of_place j hj hd

private theorem period_of_basis {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] {g : ℕ}
    (P : M →+ (Fin g → ℂ)) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (hc : Module.finrank ℤ M = 2 * g) :
    Function.Injective P ∧ DiscreteTopology P.range := by
  let b := Module.finBasis ℤ M
  let v : Fin (Module.finrank ℤ M) → (Fin g → ℂ) := fun i => P (b i)
  have hPx : ∀ x, P x = ∑ i, (b.repr x i) • v i := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul _ _ _
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hs]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    rw [hPx]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  have hfr : Fintype.card (Fin (Module.finrank ℤ M)) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Fintype.card_fin, hc, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have li : LinearIndependent ℝ v := linearIndependent_of_top_le_span_of_card_eq_finrank hsp hfr
  refine ⟨(injective_iff_map_eq_zero P).mpr fun x hx => ?_, ?_⟩
  · have h0 : ∑ i, ((b.repr x i : ℤ) : ℝ) • v i = 0 := by
      rw [← hx, hPx]
      exact Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul ℝ _ _
    have h1 := Fintype.linearIndependent_iff.mp li _ h0
    apply b.repr.injective
    ext i
    simpa using h1 i
  · let bb : Module.Basis (Fin (Module.finrank ℤ M)) ℝ (Fin g → ℂ) := Module.Basis.mk li hsp
    have hset : (P.range : Set (Fin g → ℂ)) = (Submodule.span ℤ (Set.range bb) : Set (Fin g → ℂ)) := by
      have hb : Set.range bb = Set.range v := by
        rw [Module.Basis.coe_mk]
      rw [hb]
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        show P x ∈ Submodule.span ℤ (Set.range v)
        rw [hPx]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · intro hy
        have hy' : y ∈ Submodule.span ℤ (Set.range v) := hy
        induction hy' using Submodule.span_induction with
        | mem a ha => obtain ⟨i, rfl⟩ := ha; exact ⟨b i, rfl⟩
        | zero => exact zero_mem P.range
        | add a c _ _ h1 h2 => exact add_mem (h1 (by assumption)) (h2 (by assumption))
        | smul r a _ h1 => exact zsmul_mem (h1 (by assumption)) r
    have hd : DiscreteTopology (Submodule.span ℤ (Set.range bb)) := inferInstance
    have hd' : DiscreteTopology ((Submodule.span ℤ (Set.range bb) : Set (Fin g → ℂ))) := hd
    rw [← hset] at hd'
    exact hd'

private theorem herm_smul_mat {g : ℕ} (r : ℂ) (H : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    hermForm (r • H) x y = r * hermForm H x y := by
  simp [hermForm, Matrix.smul_mulVec, dotProduct_smul]

private theorem herm_nsmul {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (m n : ℕ) (x y : Fin g → ℂ) :
    hermForm H (m • x) (n • y) = ((m : ℂ) * n) * hermForm H x y := by
  simp only [hermForm]
  rw [← Nat.cast_smul_eq_nsmul ℂ m x, ← Nat.cast_smul_eq_nsmul ℂ n y, star_smul, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, star_natCast]
  ring

private theorem herm_scale {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) {r : ℝ} (hr : 0 < r) :
    ((r : ℂ) • Hm).IsHermitian ∧ ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm ((r : ℂ) • Hm) z z).re := by
  refine ⟨?_, fun z hz => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH.eq]
    simp
  · rw [herm_smul_mat, Complex.re_ofReal_mul]
    exact mul_pos hr (hpos z hz)

theorem UpperTheory.Gal.W2.placePer_of :
    UpperTheory.Gal.W2.PlacePer := by
  intro p _ D G L β ρ D' j hpl
  obtain ⟨hinj, hact, hden, s, hs, hEF⟩ := hpl
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hform : ∀ (m n : ℕ) (u w : VQ D),
      formB L β (m • u) (n • w) = (m : ℚ) * n * formB L β u w := by
    intro m n u w
    simp only [formB, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  refine ⟨fun P hP => ?_, fun Q hQ hrk => ?_⟩
  · obtain ⟨hPa, -, -, hPs, Hm, hH, hpos, hIm⟩ := hP
    obtain ⟨Q, hQ⟩ := exists_extend j hinj hden P
    have hsc := herm_scale hH hpos (inv_pos.mpr hsR)
    refine ⟨Q, ⟨fun c w => ?_, ?_, ((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm, hsc.1, hsc.2, fun u w => ?_⟩, hQ⟩
    · obtain ⟨m, a, hm, h⟩ := hden w
      refine nsmul_right_injective hm ?_
      show m • Q (actQ D c w) = m • (ρ c *ᵥ Q w)
      have e1 : m • Q (actQ D c w) = P (c • a) := by
        rw [← map_nsmul, ← map_nsmul (actQ D c), h, ← hact, hQ]
      have e2 : m • (ρ c *ᵥ Q w) = ρ c *ᵥ P a := by
        rw [← hQ, ← h, map_nsmul, Matrix.mulVec_smul]
      rw [e1, e2, hPa]
    · rw [eq_top_iff, ← hPs]
      apply Submodule.span_mono
      rintro _ ⟨x, rfl⟩
      exact ⟨j x, hQ x⟩
    · obtain ⟨m, a, hm, ha⟩ := hden u
      obtain ⟨n, b, hn, hb⟩ := hden w
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have h1 : hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q (j a)) (Q (j b)) =
          (((m : ℝ) * n : ℝ) : ℂ) * hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q u) (Q w) := by
        rw [← ha, ← hb, map_nsmul, map_nsmul, herm_nsmul]
        push_cast
        rfl
      have h2 : (hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q (j a)) (Q (j b))).im =
          ((s : ℝ))⁻¹ * (D'.EF a b : ℝ) := by
        rw [herm_smul_mat, hQ, hQ, Complex.im_ofReal_mul, hIm]
      have h3 : (D'.EF a b : ℝ) = (s : ℝ) * ((m : ℝ) * n * (formB L β u w : ℚ)) := by
        have h4 := hEF a b
        rw [← ha, ← hb, hform] at h4
        exact_mod_cast h4
      rw [h1, Complex.im_ofReal_mul, h3] at h2
      have hs0 : (s : ℝ) ≠ 0 := hsR.ne'
      have h5 : ((m : ℝ) * n) * (hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q u) (Q w)).im =
          ((m : ℝ) * n) * (formB L β u w : ℚ) := by
        rw [h2]
        field_simp
      exact mul_left_cancel₀ (mul_ne_zero hmR hnR) h5
  · obtain ⟨hQa, hQs, Hm, hH, hpos, hIm⟩ := hQ
    have hc : Module.finrank ℤ D'.La = 2 * D.g := by
      rw [finrank_eq_of_place j hinj hden, hrk]
      haveI : Module.Free ℤ D.La := D.freeLa
      exact Module.finrank_baseChange
    have hs' : Submodule.span ℝ (Set.range (Q.comp j)) = ⊤ := by
      rw [eq_top_iff, ← hQs]
      apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      obtain ⟨m, a, hm, h⟩ := hden w
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have e : Q w = (m : ℝ)⁻¹ • Q (j a) := by
        rw [← h, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm', one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨hi, hdisc⟩ := period_of_basis (Q.comp j) hs' hc
    have hsc := herm_scale hH hpos hsR
    refine ⟨fun c u => ?_, hi, hdisc, hs', ((s : ℝ) : ℂ) • Hm, hsc.1, hsc.2, fun x y => ?_⟩
    · simp only [AddMonoidHom.comp_apply]
      rw [hact, hQa]
    · simp only [AddMonoidHom.comp_apply]
      rw [herm_smul_mat, Complex.im_ofReal_mul, hIm]
      have h4 := hEF x y
      exact_mod_cast h4.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PSheetOf
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU
open scoped Matrix

namespace UpperTheory.Gal.W2

variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}

private theorem refl_marked {Λ : Type} (N : ℕ) (D : PLat O bar) (t : Λ → D.La) :
    IsMarkedIsom N D D t t (LinearEquiv.refl O D.La) :=
  ⟨fun _ _ => rfl, fun a => ⟨0, by simp⟩⟩

private theorem commutes_rho {D : PLat O bar} {P P' : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ρ P) (hP' : IsPeriod D ρ P') (w : D.La ≃ₗ[O] D.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hw : ∀ x, P' (w x) = h (P x)) (a : O) (z : Fin g → ℂ) :
    h (ρ a *ᵥ z) = ρ a *ᵥ h z := by
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by
    rw [hP.2.2.2.1]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    rw [← hP.1, ← hw, ← hw, map_smul, hP'.1]
  | zero => simp
  | add x y _ _ hx hy => simp only [Matrix.mulVec_add, map_add (f := _), hx, hy]
  | smul c x _ hx =>
    have e : ∀ v : Fin g → ℂ, h (c • v) = c • h v := fun v =>
      (h.toLinearMap.restrictScalars ℝ).map_smul c v
    rw [Matrix.mulVec_smul, e, e, hx, Matrix.mulVec_smul]

theorem sheetOf_of : SheetOf := by
  intro O _ bar g ρ Λ F N Cl U i hN hfull
  have hN0 : 0 < N := by omega
  have key : ∀ (P P' : (U.Di i).La →+ (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      IsPeriod (U.Di i) ρ P' → (∀ x, P' x = h (P x)) →
      ∀ (y y' : Sp ℂ ⟶ F.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ F.A))
        (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F.A)), y = y' →
      UnifAt F (RingHom.id ℂ) ρ N (U.Di i) (U.t i) P y e →
      UnifAt F (RingHom.id ℂ) ρ N (U.Di i) (U.t i) P' y' e' →
      ∀ z, (e' (h z)).left = (e z).left := by
    intro P P' h hP' hx y y' e e' hy a b z
    subst hy
    have h2 := _root_.GlobalTheory.PELU.unifAt_transport O bar g ρ ℂ (RingHom.id ℂ) Λ F N (U.Di i) (U.Di i) (U.t i) (U.t i) P P' y e
      (LinearEquiv.refl O _) h hN0 a (refl_marked N _ _) (fun x => hx x) hP'
    have h3 := congrFun (_root_.GlobalTheory.PELU.unifAt_exp_unique O bar g ρ ℂ (RingHom.id ℂ) Λ F N (U.Di i) (U.t i) P' y _ _ hN hfull h2 b) (h z)
    simp only [LinearEquiv.symm_apply_apply] at h3
    rw [← h3]
  refine ⟨{ u := U.u i, ex := U.ex i, ov := fun P hP => (U.unif i P hP).1,
            exp := fun P hP => (U.unif i P hP).2.2.1, ker := fun P hP => (U.unif i P hP).2.2.2.1,
            lin := ?_, hol := U.hol i, lift := ?_ }, fun _ => rfl, fun _ _ => rfl⟩
  · intro P P' h hP hP' hx z
    have e : U.u i P = U.u i P' :=
      (U.fibre i P P' hP hP').2 ⟨LinearEquiv.refl O _, h, refl_marked N _ _, fun x => hx x⟩
    exact key P P' h hP' hx _ _ _ _ e (U.unif i P hP) (U.unif i P' hP') z
  · intro m B y hB hy hhol b₀ hb₀ P₀ hP₀ hyb
    obtain ⟨B', i', P, hB', hb', hsub, hP, hu⟩ := U.lift m B y hB hy hhol b₀ hb₀
    have hPb := hP.1 b₀ hb'
    obtain rfl : i' = i := U.disj i' i (P b₀) P₀ hPb hP₀ ((hu b₀ hb').trans hyb)
    obtain ⟨w, h, hw, hwx⟩ := (U.fibre i' (P b₀) P₀ hPb hP₀).1 ((hu b₀ hb').trans hyb)
    have hc := commutes_rho hPb hP₀ w h hwx
    let P' : (Fin _ → ℂ) → ((U.Di i').La →+ (Fin g → ℂ)) := fun b =>
      (h.toLinearMap.toAddMonoidHom.comp (P b)).comp w.symm.toLinearMap.toAddMonoidHom
    have ev : ∀ b x, P' b x = h (P b (w.symm x)) := fun _ _ => rfl
    have hper : ∀ b ∈ B', IsPeriod (U.Di i') ρ (P' b) := fun b hb =>
      isPeriod_comp_isometry_symm _ _ w hw.1 _
        (GlobalTheory.T.comp_linearEquiv_intertwining O bar _ g ρ ρ (P b) h (hP.1 b hb) hc)
    refine ⟨B', P', hB', hb', hsub, ⟨hper, fun x => ?_⟩, ?_, fun b hb => ?_⟩
    · exact (LinearMap.toContinuousLinearMap h.toLinearMap).differentiable.comp_differentiableOn
        (hP.2 (w.symm x))
    · ext1 x
      rw [ev, ← hwx, LinearEquiv.apply_symm_apply]
    · rw [← hu b hb]
      exact ((U.fibre i' (P b) (P' b) (hP.1 b hb) (hper b hb)).2
        ⟨w, h, hw, fun x => by rw [ev, LinearEquiv.symm_apply_apply]⟩).symm

end UpperTheory.Gal.W2
end
end

