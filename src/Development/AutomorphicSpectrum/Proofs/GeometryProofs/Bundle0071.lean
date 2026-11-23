module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianNormSectionValue
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.EvalPt

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem aeval_div_mul_prod {F : Type} [Field F] (v : (Σ k, J k) → F) (t : K → F) (ht : ∀ k, t k ≠ 0)
    {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval (fun p => v p / t p.1) g * ∏ k, t k ^ d k = aeval v g := by
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_assoc]
  congr 1
  have key : ∏ k, t k ^ d k = ∏ p : (Σ k, J k), t p.1 ^ m p := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [key, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (ht p.1))]

theorem map_aeval_int {σ S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (s : σ → S) (f : MvPolynomial σ ℤ) :
    φ (aeval s f) = aeval (fun i => φ (s i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem norm_evC_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ} {A : HermLine J} {c₀ : Ω} {C : ℝ}
    {g h : MRing J} {dg dh : K → ℕ} (hz : genPt ξ ⤳ centre z) (hco : CoordsAt ξ y z w)
    (hyp : ∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) →
      ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = C * A.h w)
    (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh) (hd : ∀ k, (dg k : ℤ) - dh k = A.a k)
    (he : aeval y g = c₀ * aeval y h) (hw : evC w h ≠ 0) :
    ‖evC w g‖ = C * A.h w * ‖evC w h‖ := by
  classical
  obtain ⟨hcov, hco2⟩ := hco
  choose cc hcc using hcov
  have hw0 : ∀ k, w ⟨k, cc k⟩ ≠ 0 := fun k => (hcc k).ne_zero
  have hy0 : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => (hco2 k (cc k) (hcc k)).1
  have hr : ∀ p : (Σ k, J k), ∃ s : X.presheaf.stalk (centre z),
      genMap ξ ⟨centre z, hz⟩ s = y p / y ⟨p.1, cc p.1⟩ ∧
      w p = (Scheme.stalkClosedPointTo z).hom s * w ⟨p.1, cc p.1⟩ := by
    rintro ⟨k, i⟩
    obtain ⟨r, ⟨h', s, hs1, hs2⟩, hwr⟩ := (hco2 k (cc k) (hcc k)).2 i
    exact ⟨s, hs1, by rw [hwr, ← hs2]⟩
  choose s hs1 hs2 using hr
  have hφ1 : ∀ f : MRing J, genMap ξ ⟨centre z, hz⟩ (aeval s f) =
      aeval (fun p => y p / y ⟨p.1, cc p.1⟩) f := by
    intro f
    rw [map_aeval_int]
    simp only [hs1]
  have hwr : ∀ p : (Σ k, J k), w p / w ⟨p.1, cc p.1⟩ = (Scheme.stalkClosedPointTo z).hom (s p) := fun p => by
    rw [hs2 p, mul_div_cancel_right₀ _ (hw0 p.1)]
  have hφ2 : ∀ f : MRing J, (Scheme.stalkClosedPointTo z).hom (aeval s f) =
      aeval (fun p => w p / w ⟨p.1, cc p.1⟩) f := by
    intro f
    refine (map_aeval_int (Scheme.stalkClosedPointTo z).hom s f).trans ?_
    simp only [← hwr]
    try rfl
  have hev : ∀ f : MRing J, evC w f = aeval w f := fun f => by
    simp only [evC, MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]
  have hg1 : aeval (fun p => w p / w ⟨p.1, cc p.1⟩) g * ∏ k, w ⟨k, cc k⟩ ^ dg k = aeval w g :=
    aeval_div_mul_prod w (fun k => w ⟨k, cc k⟩) hw0 hg
  have hh1 : aeval (fun p => w p / w ⟨p.1, cc p.1⟩) h * ∏ k, w ⟨k, cc k⟩ ^ dh k = aeval w h :=
    aeval_div_mul_prod w (fun k => w ⟨k, cc k⟩) hw0 hh
  have hg2 : aeval (fun p => y p / y ⟨p.1, cc p.1⟩) g * ∏ k, y ⟨k, cc k⟩ ^ dg k = aeval y g :=
    aeval_div_mul_prod y (fun k => y ⟨k, cc k⟩) hy0 hg
  have hh2 : aeval (fun p => y p / y ⟨p.1, cc p.1⟩) h * ∏ k, y ⟨k, cc k⟩ ^ dh k = aeval y h :=
    aeval_div_mul_prod y (fun k => y ⟨k, cc k⟩) hy0 hh
  rw [hev, hev] at *
  set Pg := aeval (fun p => w p / w ⟨p.1, cc p.1⟩) g with hPg
  set Ph := aeval (fun p => w p / w ⟨p.1, cc p.1⟩) h with hPh
  set Qg := aeval (fun p => y p / y ⟨p.1, cc p.1⟩) g with hQg
  set Qh := aeval (fun p => y p / y ⟨p.1, cc p.1⟩) h with hQh
  have hTg : ∏ k, w ⟨k, cc k⟩ ^ dg k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hw0 k)
  have hTh : ∏ k, w ⟨k, cc k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hw0 k)
  have hYg : ∏ k, y ⟨k, cc k⟩ ^ dg k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy0 k)
  have hYh : ∏ k, y ⟨k, cc k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy0 k)
  have hPh0 : Ph ≠ 0 := by
    intro h0
    apply hw
    rw [← hh1, h0, zero_mul]
  have hunit : IsUnit (aeval s h : X.presheaf.stalk (centre z)) :=
    isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ (by rw [hφ2]; exact hPh0.isUnit)
  have hQh0 : Qh ≠ 0 := by
    have := (hunit.map (genMap ξ ⟨centre z, hz⟩)).ne_zero
    rwa [hφ1] at this
  have hyh0 : aeval y h ≠ 0 := by
    rw [← hh2]
    exact mul_ne_zero hQh0 hYh
  have hval : ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) (Pg / Ph) := by
    refine ⟨hz, aeval s g * ↑hunit.unit⁻¹, ?_, ?_⟩
    · rw [map_mul, map_units_inv, IsUnit.unit_spec, hφ1, hφ1]
      have hpow : ∏ k, y ⟨k, cc k⟩ ^ A.a k = (∏ k, y ⟨k, cc k⟩ ^ dg k) / ∏ k, y ⟨k, cc k⟩ ^ dh k := by
        rw [← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← hd k, zpow_sub₀ (hy0 k), zpow_natCast, zpow_natCast]
      have hc0 : c₀ = (Qg * ∏ k, y ⟨k, cc k⟩ ^ dg k) / (Qh * ∏ k, y ⟨k, cc k⟩ ^ dh k) := by
        rw [hg2, hh2, he, mul_div_assoc, div_self hyh0, mul_one]
      rw [hpow, hc0, ← hQg, ← hQh]
      field_simp
      try ring
    · have hq : (aeval s g * ↑hunit.unit⁻¹ : X.presheaf.stalk (centre z)) * aeval s h = aeval s g := by
        rw [mul_assoc, Units.inv_mul_of_eq hunit.unit_spec, mul_one]
      have key2 := (RingHom.map_mul (Scheme.stalkClosedPointTo z).hom _ _).symm.trans
        (congrArg (Scheme.stalkClosedPointTo z).hom hq)
      rw [hφ2, hφ2] at key2
      exact (eq_div_iff hPh0).2 key2
  have key := hyp cc (Pg / Ph) hw0 hval
  have hnpow : ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k =
      (∏ k, ‖w ⟨k, cc k⟩‖ ^ dg k) / ∏ k, ‖w ⟨k, cc k⟩‖ ^ dh k := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hd k, zpow_sub₀ (norm_ne_zero_iff.2 (hw0 k)), zpow_natCast, zpow_natCast]
  have hnh : ∏ k, ‖w ⟨k, cc k⟩‖ ^ dh k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hw0 k))
  have hPhn : ‖Ph‖ ≠ 0 := norm_ne_zero_iff.2 hPh0
  rw [← key, ← hg1, ← hh1, hnpow, norm_mul, norm_mul, norm_div, norm_prod, norm_prod]
  simp only [norm_pow]
  field_simp
  try ring

theorem norm_evC_of_forms : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [Nonempty K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (A : HermLine J) (c₀ : Ω) (C : ℝ) (g h : MRing J) (dg dh : K → ℕ), IsCptGen ξ → CoordsAt ξ y z w → (∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) → ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = C * A.h w) → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → evC w h ≠ 0 → ‖evC w g‖ = C * A.h w * ‖evC w h‖ := by
  intro X Ω _ ξ K _ _ J _ y z w A c₀ C g h dg dh _ hco hyp hg hh hd he hw
  obtain ⟨k⟩ := ‹Nonempty K›
  obtain ⟨c, hc⟩ := hco.1 k
  obtain ⟨r, ⟨hz, _⟩, _⟩ := (hco.2 k c hc).2 c
  exact norm_evC_of_specializes hz hco hyp hg hh hd he hw

end GlobalTheory.CompanionTheory.Ar.Flat.EvalPt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationsEqualBasicOpens
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.CommonLoc

open Mdl

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem mem_of_isLocAt {A : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω} (hq : q.IsPrime)
    (hR : IsLocAt A q R) {a : Ω} (ha : a ∈ A) : a ∈ R :=
  (hR a).2 ⟨1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simpa using ha⟩

theorem unit_of_not_mem {A : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω}
    (hR : IsLocAt A q R) {a : A} (ha : a ∉ q) : (a : Ω) ≠ 0 ∧ (a : Ω)⁻¹ ∈ R := by
  have h0 : (a : Ω) ≠ 0 := fun h => ha (by
    have e : a = 0 := Subtype.ext h
    rw [e]
    exact q.zero_mem)
  exact ⟨h0, (hR _).2 ⟨a, ha, by rw [mul_inv_cancel₀ h0]; exact A.one_mem⟩⟩

theorem not_mem_of_unit {A : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω}
    (hR : IsLocAt A q R) {b : A} (h0 : (b : Ω) ≠ 0) (hi : (b : Ω)⁻¹ ∈ R) : b ∉ q := by
  obtain ⟨s, hs, hsb⟩ := (hR _).1 hi
  intro hb
  apply hs
  have e : s = ⟨_, hsb⟩ * b := Subtype.ext (by
    rw [Subalgebra.coe_mul]
    exact (inv_mul_cancel_right₀ h0 _).symm)
  rw [e]
  exact q.mul_mem_left _ hb

theorem invAdj_le_of {A C : Subalgebra ℚ Ω} {h : Ω} (hA : A ≤ C) (hh : h⁻¹ ∈ C) : invAdj A h ≤ C :=
  Algebra.adjoin_le (by
    rintro x (rfl | hx)
    · exact hh
    · exact hA hx)

theorem invAdj_le_mul {A : Subalgebra ℚ Ω} {g s : Ω} (hs : s ∈ A) (h0 : g * s ≠ 0) :
    invAdj A g ≤ invAdj A (g * s) := by
  refine invAdj_le_of (le_invAdj _ _) ?_
  have hs0 : s ≠ 0 := right_ne_zero_of_mul h0
  have hg0 : g ≠ 0 := left_ne_zero_of_mul h0
  have e : g⁻¹ = s * (g * s)⁻¹ := by field_simp
  rw [e]
  exact Subalgebra.mul_mem _ (le_invAdj _ _ hs) (inv_mem_invAdj _ _)

theorem exists_den {A B : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω} (hq : q.IsPrime)
    (hR : IsLocAt A q R) (hB : B.FG) (hBR : ∀ b ∈ B, b ∈ R) : ∃ g : A, g ∉ q ∧ B ≤ invAdj A g := by
  classical
  have key : ∀ T : Finset Ω, (∀ b ∈ T, b ∈ R) → ∃ g : A, g ∉ q ∧ ∀ b ∈ T, b ∈ invAdj A g := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simp⟩
    | insert b T _ ih =>
      intro hT
      obtain ⟨g₁, hg₁, hg₁T⟩ := ih fun x hx => hT x (Finset.mem_insert_of_mem hx)
      obtain ⟨s, hs, hsb⟩ := (hR b).1 (hT b (Finset.mem_insert_self _ _))
      have hmul : g₁ * s ∉ q := fun h => (hq.mem_or_mem h).elim hg₁ hs
      have h0 : (g₁ : Ω) * s ≠ 0 := (unit_of_not_mem hR hmul).1
      have hs0 : (s : Ω) ≠ 0 := right_ne_zero_of_mul h0
      have hg0 : (g₁ : Ω) ≠ 0 := left_ne_zero_of_mul h0
      refine ⟨g₁ * s, hmul, ?_⟩
      rw [Subalgebra.coe_mul]
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · have e : x = ((s : Ω) * x) * g₁ * ((g₁ : Ω) * s)⁻¹ := by field_simp
        rw [e]
        exact Subalgebra.mul_mem _
          (Subalgebra.mul_mem _ (le_invAdj _ _ hsb) (le_invAdj _ _ g₁.2)) (inv_mem_invAdj _ _)
      · exact invAdj_le_mul s.2 h0 (hg₁T x hx)
  obtain ⟨S, rfl⟩ := hB
  obtain ⟨g, hg, hgS⟩ := key S fun b hb => hBR b (Algebra.subset_adjoin hb)
  exact ⟨g, hg, Algebra.adjoin_le fun b hb => hgS b hb⟩

theorem exists_clear {A B : Subalgebra ℚ Ω} {q : Ideal A} {q' : Ideal B} {R : Subring Ω}
    (hR : IsLocAt A q R) (hR' : IsLocAt B q' R) {g : A} {h : B} (hg : g ∉ q) (hh : h ∉ q')
    (hgh : (g : Ω) ∈ invAdj B h) : ∃ (a : B) (m : ℕ), a ∉ q' ∧ (a : Ω) = g * (h : Ω) ^ m := by
  obtain ⟨gn, gi⟩ := unit_of_not_mem hR hg
  obtain ⟨hn, hi⟩ := unit_of_not_mem hR' hh
  obtain ⟨m, hm⟩ := exists_mul_pow_mem h.2 hn hgh
  refine ⟨⟨_, hm⟩, m, not_mem_of_unit hR' (mul_ne_zero gn (pow_ne_zero _ hn)) ?_, rfl⟩
  show ((g : Ω) * (h : Ω) ^ m)⁻¹ ∈ R
  rw [mul_inv, ← inv_pow]
  exact R.mul_mem gi (R.pow_mem hi _)

theorem exists_common_loc : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A B : Subalgebra ℚ Ω) (q : Ideal A) (q' : Ideal B)
    (R : Subring Ω), A.FG → B.FG → q.IsPrime → q'.IsPrime → IsLocAt A q R → IsLocAt B q' R →
    ∃ (g : A) (h : B), g ∉ q ∧ h ∉ q' ∧ Mdl.invAdj A g = Mdl.invAdj B h := by
  intro Ω _ _ A B q q' R hA hB hq hq' hR hR'
  obtain ⟨g₀, hg₀, hBg⟩ := exists_den hq hR hB fun b hb => mem_of_isLocAt hq' hR' hb
  obtain ⟨h₀, hh₀, hAh⟩ := exists_den hq' hR' hA fun b hb => mem_of_isLocAt hq hR hb
  obtain ⟨a, m, ha, ea⟩ := exists_clear hR hR' hg₀ hh₀ (hAh g₀.2)
  obtain ⟨h, hh, eh⟩ : ∃ h : B, h ∉ q' ∧ (h : Ω) = h₀ * a :=
    ⟨h₀ * a, fun hm => (hq'.mem_or_mem hm).elim hh₀ ha, rfl⟩
  obtain ⟨a', l, ha', ea'⟩ := exists_clear hR' hR hh hg₀ (hBg h.2)
  obtain ⟨g, hg, eg⟩ : ∃ g : A, g ∉ q ∧ (g : Ω) = g₀ * a' :=
    ⟨g₀ * a', fun hm => (hq.mem_or_mem hm).elim hg₀ ha', rfl⟩
  have g0n := (unit_of_not_mem hR hg₀).1
  have h0n := (unit_of_not_mem hR' hh₀).1
  have gn := (unit_of_not_mem hR hg).1
  have hn := (unit_of_not_mem hR' hh).1
  have an := (unit_of_not_mem hR' ha).1
  have an' := (unit_of_not_mem hR ha').1
  refine ⟨g, h, hg, hh, ?_⟩

  have hAh' : invAdj B (h₀ : Ω) ≤ invAdj B h := by
    rw [eh]
    exact invAdj_le_mul a.2 (eh ▸ hn)
  have hBg' : invAdj A (g₀ : Ω) ≤ invAdj A g := by
    rw [eg]
    exact invAdj_le_mul a'.2 (eg ▸ gn)
  have g0inv : (g₀ : Ω)⁻¹ ∈ invAdj B h := by
    have e : (g₀ : Ω)⁻¹ = (h₀ : Ω) ^ m * h₀ * (h : Ω)⁻¹ := by
      rw [eh, ea]
      field_simp
    rw [e]
    exact Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ (le_invAdj _ _ (B.pow_mem h₀.2 _)) (le_invAdj _ _ h₀.2)) (inv_mem_invAdj _ _)
  have C1 : invAdj A (g₀ : Ω) ≤ invAdj B h := invAdj_le_of (hAh.trans hAh') g0inv
  have hinv : (h : Ω)⁻¹ ∈ invAdj A g := by
    have e : (h : Ω)⁻¹ = (g₀ : Ω) ^ l * g₀ * (g : Ω)⁻¹ := by
      rw [eg, ea']
      field_simp
    rw [e]
    exact Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ (le_invAdj _ _ (A.pow_mem g₀.2 _)) (le_invAdj _ _ g₀.2)) (inv_mem_invAdj _ _)
  have ginv : (g : Ω)⁻¹ ∈ invAdj B h := by
    have e : (g : Ω)⁻¹ = (g₀ : Ω)⁻¹ * ((h : Ω)⁻¹ * ((g₀ : Ω)⁻¹) ^ l) := by
      rw [eg, ea', mul_inv, mul_inv, inv_pow]
    rw [e]
    exact Subalgebra.mul_mem _ g0inv
      (Subalgebra.mul_mem _ (inv_mem_invAdj _ _) (Subalgebra.pow_mem _ g0inv _))
  exact le_antisymm (invAdj_le_of ((le_invAdj A _).trans C1) ginv)
    (invAdj_le_of (hBg.trans hBg') hinv)

end GlobalTheory.CompanionTheory.Ar.SncBase.CommonLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeDivisorsOfOmegaBundle
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.TieOfOrigin

theorem sum_fundOnRoot {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {G : Type} [AddCommGroup G]
    (f : Ψ × Fin N → G) (a : Ψ × Fin N) :
    ∑ r, fundOnRoot a r • f r = -∑ k ∈ Finset.Iic a.2, f (a.1, k) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a.1]
  · rw [← Finset.sum_neg_distrib, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic a.2))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp [fundOnRoot, Finset.mem_Iic.mp hk]
    · intro k _ hk
      have hk' : ¬ k ≤ a.2 := fun h => hk (Finset.mem_Iic.mpr h)
      simp [fundOnRoot, hk']
  · intro τ _ hτ
    simp [fundOnRoot, hτ]
  · simp

theorem log_combLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((Top.combLine ℓ n).h z) = ∑ j, n j • Real.log ((ℓ j).h z) := by
  show Real.log (∏ j, (ℓ j).h z ^ n j) = _
  rw [Real.log_prod fun j _ => (zpow_pos ((ℓ j).pos z hz) _).ne']
  simp [Real.log_zpow]

theorem sum_rootOnFund {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (f g : Ψ × Fin N → ℝ)
    (h : ∀ a, g a = -∑ k ∈ Finset.Iic a.2, f (a.1, k)) (r : Ψ × Fin N) :
    ∑ a, rootOnFund r a • g a = f r := by
  have h1 : ∀ a, g a = ∑ r', fundOnRoot a r' • f r' := fun a => by rw [h, sum_fundOnRoot]
  simp only [h1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, (rootOnFund_mul_fundOnRoot_inverse Ψ N r _).1]
  simp

end GlobalTheory.CompanionTheory.Ar.TieOfOrigin

open GlobalTheory.CompanionTheory.Ar.TieOfOrigin in
theorem GlobalTheory.CompanionTheory.Ar.hodgeTie_of_rootOrigin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → AlgOver (Or.Re.comap some) → ∃ T : HodgeTie Y S (Module.finrank ℚ c.F) RM, T.A = Or.𝔐 := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or hvb hdiscr halg
  refine ⟨{ A := Or.𝔐, Fl := Or.Fl, e := Or.e, roots := Or.lines, sing := Or.sing, sing_deg := Or.sing_deg
            hodge := Or.hodge, Sy := Sys.comap some, Re := Or.Re.comap some, alg := halg
            ref_deg := ?_, sing_eq := ?_, line_eq := ?_, δ_eq := Or.δ_eq, discr := hdiscr
            ht_vb := fun p hp s => (hvb p hp).2 s }, rfl⟩
  · rintro ⟨τ, i⟩
    refine (Or.fund_deg τ i).trans ?_
    refine Eq.trans ?_ (@sum_fundOnRoot _ _ (_) _ _ _ (fun r => (Or.sing r).a) (τ, i)).symm
    simp only [Or.sing_deg]
  · rintro ⟨τ, i⟩ x hx
    have hz := (Or.Re.R.mem x x (Or.Re.R.mem_U x)).1
    refine (log_combLine _ _ _ hz).trans ?_
    refine (@sum_fundOnRoot _ _ (_) _ _ _ (fun r => Real.log ((Or.sing r).h (Or.Re.R.lift x x))) (τ, i)).trans ?_
    exact (Or.fund_sing τ i x hx).symm
  · have h0 : 0 < Sys.t₀ := (Sys.reg none).1
    filter_upwards [Ioc_mem_nhdsGT h0] with t ht r z hz
    refine Real.log_injOn_pos ((RM.x t r).pos z hz.1) (HermLine.pos _ z hz.1) ?_
    refine Eq.trans ?_ (log_combLine _ _ _ hz.1).symm
    exact (@sum_rootOnFund _ _ (_) _ (fun r => Real.log ((RM.x t r).h z))
      (fun a => Real.log ((Or.Re.line (some a) t).h z))
      (fun a => Or.fund_reg a.1 a.2 t ht.1 ht.2 z hz) r).symm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothAdjoinInverse
section
namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem isLocalizationAway_invAdj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : Subalgebra ℚ Ω} {g : Ω}
    (hg : g ∈ A) (h0 : g ≠ 0) :
    letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
    IsLocalization.Away (⟨g, hg⟩ : A) (invAdj A g) := by
  letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
  have hmap : ∀ a : A, ((algebraMap A (invAdj A g) a : invAdj A g) : Ω) = a := fun _ => rfl
  refine IsLocalization.Away.mk (⟨g, hg⟩ : A) ?_ ?_ ?_
  · refine IsUnit.of_mul_eq_one (⟨g⁻¹, inv_mem_invAdj A g⟩ : invAdj A g) (Subtype.ext ?_)
    simp [hmap, h0]
  · intro s
    obtain ⟨k, hk⟩ := exists_mul_pow_mem hg h0 s.2
    refine ⟨k, ⟨_, hk⟩, Subtype.ext ?_⟩
    simp [hmap]
  · intro a b hab
    have hab' : a = b := Subtype.ext (by simpa [hmap] using congrArg Subtype.val hab)
    exact ⟨0, by rw [hab']⟩

theorem smooth_invAdj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 →
    Algebra.Smooth ℚ A → Algebra.Smooth ℚ (invAdj A g) := by
  intro Ω _ _ A g hg h0 hA
  letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ A (invAdj A g) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization.Away (⟨g, hg⟩ : A) (invAdj A g) := isLocalizationAway_invAdj hg h0
  haveI : Algebra.Smooth A (invAdj A g) := Algebra.Smooth.of_isLocalization_Away (⟨g, hg⟩ : A)
  exact Algebra.Smooth.comp ℚ A (invAdj A g)

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothOpenImmersionRangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_open_immersion_range : ∀ (A B T : Scheme.{0}) (j : A ⟶ B) [IsOpenImmersion j] (g : B ⟶ T) (n : ℕ), SmoothOfRelativeDimension n (j ≫ g) → SmoothOfRelativeDimension n (j.opensRange.ι ≫ g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp | exact GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothSchemeStalksDomainsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_scheme_stalks_domains : ∀ (K : Type) [Field K] (e : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp K), SmoothOfRelativeDimension e g → ∀ x : X, IsDomain (X.presheaf.stalk x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field | exact GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field <;> assumption)
end

