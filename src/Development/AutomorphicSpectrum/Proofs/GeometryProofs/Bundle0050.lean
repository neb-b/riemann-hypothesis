module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsRegularSectionGenerator
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropZProved
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.PropZPf

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem div_sub_mem {L : Lat ξ Ω} {q : Cpt ξ} {w σ tp tq y : Ω} (a : ℤ) (M : ℕ) (hw0 : w ≠ 0)
    (hwq : w ∈ regAt ξ q) (hσ : σ ≠ 0) (hgq : L.IsGenAt q tq) (htp : tp ≠ 0)
    (hhq : w ^ a / (σ / tq) ^ M ∈ regAt ξ q) (hy : y ∈ L q) (hd : tp - tq = w • y) :
    (w ^ a / (σ / tp) ^ M - w ^ a / (σ / tq) ^ M) / w ∈ regAt ξ q := by
  rw [hgq.2, Submodule.mem_span_singleton] at hy
  obtain ⟨r, rfl⟩ := hy
  have hr : ((r • tq : Ω)) = (r : Ω) * tq := rfl
  rw [hr, smul_eq_mul] at hd
  have htq := hgq.1
  have e1 : tp = tq * (1 + w * r) := by linear_combination hd
  have hu : (1 + w * (r : Ω)) ≠ 0 := by
    intro h0; apply htp; rw [e1, h0, mul_zero]
  have e2 : w ^ a / (σ / tp) ^ M = w ^ a / (σ / tq) ^ M * (1 + w * r) ^ M := by
    rw [e1, div_pow, div_pow, mul_pow]
    field_simp
  have g := geom_sum_mul (1 + w * (r : Ω)) M
  have e3 : (w ^ a / (σ / tp) ^ M - w ^ a / (σ / tq) ^ M) / w =
      w ^ a / (σ / tq) ^ M * (r : Ω) * ∑ i ∈ Finset.range M, (1 + w * (r : Ω)) ^ i := by
    rw [e2, div_eq_iff hw0]
    linear_combination (-(w ^ a / (σ / tq) ^ M)) * g
  rw [e3]
  refine mul_mem (mul_mem hhq r.2) (Subring.sum_mem _ fun i _ => pow_mem ?_ i)
  exact add_mem (one_mem _) (mul_mem hwq r.2)

end GlobalTheory.CompanionTheory.Ar.Flat.PropZPf


open GlobalTheory.CompanionTheory.Ar.Flat.PropZPf in
theorem GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds : GlobalTheory.CompanionTheory.Ar.Flat.PropZ := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hconn L σ hvb htriv hgen
  obtain ⟨M, a, hM, hreg, p₀, hp₀, -, hord₀⟩ :=
    GlobalTheory.CompanionTheory.Ar.Flat.exists_regular_section_generator X Ω ξ O s ϖ hϖ hinj hs hg hn hconn.nonempty L σ hvb hgen
  have hw0 : algebraMap O Ω ϖ ≠ 0 := fun e => hϖ.ne_zero (hinj (by rw [map_zero]; exact e))
  have hwreg : ∀ p : Cpt ξ, algebraMap O Ω ϖ ∈ regAt ξ p := fun p =>
    (GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.regular_const X Ω ξ O s hs p ϖ).1
  have hunit : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal :=
    fun p o => (GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.regular_const X Ω ξ O s hs p o).2 hg
  have hgf : ∀ q : Cpt ξ, unitAt ξ q (algebraMap O Ω ϖ) → q ∈ genFibre O ξ := by
    intro q hq o ho
    rw [hunit]
    intro hmem
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho hϖ
    have hP : (s q.1).asIdeal.IsPrime := (s q.1).isPrime
    rw [hu] at hmem
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (by
        have := Ideal.mul_mem_left _ ((u⁻¹ : Oˣ) : O) h1
        rwa [Units.inv_mul] at this))
    · exact (hunit q ϖ).1 hq (hP.mem_of_pow_mem n h1)
  have hσ : σ ≠ 0 := hord₀.ne_zero hM.ne'
  obtain ⟨t, ht⟩ := htriv
  have htq : ∀ q : Cpt ξ, ¬ unitAt ξ q (algebraMap O Ω ϖ) → L.IsGenAt q (t q) := fun q hq => by
    obtain ⟨U, hU, H⟩ := ht q hq
    obtain ⟨h0, h1, -⟩ := H q hU hq
    exact ⟨h0, h1⟩
  have hloc : ∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧
      ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) →
        (fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) p ∈ regAt ξ q ∧
        ((fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) p -
          (fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) q) / algebraMap O Ω ϖ ∈ regAt ξ q := by
    intro p hp
    obtain ⟨U, hU, H⟩ := ht p hp
    refine ⟨U, hU, fun q hqU hq => ?_⟩
    obtain ⟨h0, h1, y, hy, hd⟩ := H q hqU hq
    exact ⟨hreg q (t p) ⟨h0, h1⟩, div_sub_mem a M hw0 (hwreg q) hσ (htq q hq) h0
      (hreg q (t q) (htq q hq)) hy hd⟩
  have hu₀ : unitAt ξ p₀ ((fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) p₀) := by
    have := ZUnit.inv ((orderAt_iff_div (htq p₀ hp₀).1 (htq p₀ hp₀).2).1 hord₀)
    rwa [inv_div] at this
  have key := _root_.GlobalTheory.CompanionTheory.Ar.Flat.unitAt_of_localLifts_of_unitAt X Ω ξ O s ϖ hϖ hinj hs hg hconn
    (fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) hloc ⟨p₀, hp₀, hu₀⟩
  refine ⟨M, a, hM, fun p => ?_⟩
  by_cases hp : unitAt ξ p (algebraMap O Ω ϖ)
  · have hgp := hgen p (hgf p hp)
    rw [orderAt_iff_div hgp.1 hgp.2, div_self hσ, one_pow, one_div]
    refine ZUnit.inv ⟨zpow_ne_zero a hw0, ZLat.zpow_mem_regAt hp a, ?_⟩
    rw [← zpow_neg]
    exact ZLat.zpow_mem_regAt hp (-a)
  · rw [orderAt_iff_div (htq p hp).1 (htq p hp).2]
    have h1 : unitAt ξ p (algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) := key p hp
    have := ZUnit.inv h1
    rwa [inv_div] at this
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionsTwoComponents
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Centre.Sep

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem isLocalRing_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  show IsLocalRing (genMap ξ p).range
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem isUnit_regAt_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ)
    (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    have e : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have ha : (a : Ω) ≠ 0 := fun h0 => by simp [h0] at e
    refine ⟨ha, a.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right e]
    exact b.2
  · rintro ⟨h0, -, h2⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem unitAt_iff_of_dominated {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {i : Ω →+* Ω'} {p' : Cpt ξ'} {q : Cpt ξ}
    (h : (∀ a ∈ regAt ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ q, unitAt ξ' p' (i a) → unitAt ξ q a)
    {a : Ω} (ha : a ∈ regAt ξ q) : unitAt ξ q a ↔ unitAt ξ' p' (i a) := by
  refine ⟨fun hu => ⟨(map_ne_zero i).2 hu.1, h.1 a hu.2.1, ?_⟩, h.2 a ha⟩
  rw [← map_inv₀]
  exact h.1 _ hu.2.2

theorem eq_of_dominated_of_inChart {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    {i : Ω →+* Ω'} {p' : Cpt ξ'} {c : κ} {q r : Cpt M.ξ} (hq : InChart M.ξ x c q) (hr : InChart M.ξ x c r)
    (dq : (∀ a ∈ regAt M.ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q, unitAt ξ' p' (i a) → unitAt M.ξ q a)
    (dr : (∀ a ∈ regAt M.ξ r, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ r, unitAt ξ' p' (i a) → unitAt M.ξ r a) :
    q = r := by
  have cq := (_root_.GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation o Ω κ x M c q hq).1
  have cr := (_root_.GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation o Ω κ x M c r hr).1
  haveI := isLocalRing_regAt M.ξ q
  let f : chRing o x c →+* regAt M.ξ q :=
    ((chRing o x c).val : chRing o x c →+* Ω).codRestrict (regAt M.ξ q) fun u => cq _ u.2
  have hP : ∀ u : chRing o x c, u ∈ (IsLocalRing.maximalIdeal (regAt M.ξ q)).comap f ↔ ¬ unitAt M.ξ q (u : Ω) := by
    intro u
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_regAt_iff]
    rfl
  obtain ⟨p, -, huniq⟩ := _root_.GlobalTheory.CompanionTheory.Ar.chart_prime_point o Ω κ x M c hq.1 _
    (inferInstance : ((IsLocalRing.maximalIdeal (regAt M.ξ q)).comap f).IsPrime)
  have e1 := huniq q ⟨hq, hP⟩
  have e2 := huniq r ⟨hr, fun u => by
    rw [hP, unitAt_iff_of_dominated dq (cq _ u.2), unitAt_iff_of_dominated dr (cr _ u.2)]⟩
  exact e1.trans e2.symm

theorem eq_of_dominated : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ') (q₁ q₂ : Cpt M.ξ), ((∀ a ∈ regAt M.ξ q₁, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₁, unitAt ξ' p' (i a) → unitAt M.ξ q₁ a) → ((∀ a ∈ regAt M.ξ q₂, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₂, unitAt ξ' p' (i a) → unitAt M.ξ q₂ a) → q₁ = q₂ := by
  intro o _ Ω _ _ κ _ x M X' Ω' _ ξ' i p' q₁ q₂ d₁ d₂
  obtain ⟨c₁, hc₁⟩ := M.tie.cover q₁
  obtain ⟨c₂, hc₂⟩ := M.tie.cover q₂
  have hctr : p' ∈ ctrSet o x i ξ' :=
    ⟨c₁, hc₁.1, fun a ha => d₁.1 a ((_root_.GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation o Ω κ x M c₁ q₁ hc₁).1 a ha)⟩
  obtain ⟨p₀, d₀, -, hp₀⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Centre.exists_centre o Ω κ x M X' Ω' ξ' i p' hctr
  have e₁ : q₁ = p₀ := eq_of_dominated_of_inChart M hc₁ (hp₀ c₁ hc₁.1 fun j => d₁.1 _ (hc₁.2 j)) d₁ d₀
  have e₂ : q₂ = p₀ := eq_of_dominated_of_inChart M hc₂ (hp₀ c₂ hc₂.1 fun j => d₂.1 _ (hc₂.2 j)) d₂ d₀
  exact e₁.trans e₂.symm

end GlobalTheory.CompanionTheory.Ar.Centre.Sep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubringCoordsComplexValue
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RegVal

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem germ_frac {U : X.Opens} (hU : IsAffineOpen U) {p : X} (hp : p ∈ U) (s : X.presheaf.stalk p) :
    ∃ (n d : Γ(X, U)) (m : ℕ), IsUnit (X.presheaf.germ U p hp d) ∧
      s * X.presheaf.germ U p hp d ^ m = X.presheaf.germ U p hp n := by
  obtain ⟨V, hpV, t, rfl⟩ := X.presheaf.exists_germ_eq s
  obtain ⟨d, hdV, hpd⟩ := hU.exists_basicOpen_le (V := V) ⟨p, hpV⟩ hp
  have := hU.isLocalization_basicOpen d
  obtain ⟨m, n, e⟩ := IsLocalization.Away.surj (S := Γ(X, X.basicOpen d)) d
    (X.presheaf.map (homOfLE hdV).op t)
  refine ⟨n, d, m, (X.mem_basicOpen d p hp).1 hpd, ?_⟩
  have e' := congrArg (X.presheaf.germ (X.basicOpen d) p hpd) e
  rw [map_mul, map_pow] at e'
  have h0 : ∀ f : Γ(X, U), X.presheaf.germ (X.basicOpen d) p hpd (algebraMap Γ(X, U) Γ(X, X.basicOpen d) f) =
      X.presheaf.germ U p hp f := fun f =>
    X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le d)) p hpd f
  rw [h0, h0, TopCat.Presheaf.germ_res_apply] at e'
  exact e'

theorem genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) {U : X.Opens} {q : X} (hq : q ∈ U) (h : genPt ξ ⤳ q)
    (f : Γ(X, U)) :
    genMap ξ ⟨q, h⟩ (X.presheaf.germ U q hq f) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) (h.mem_open U.isOpen hq) f) := by
  have e := congr($(X.presheaf.germ_stalkSpecializes hq h) f)
  simp only [CommRingCat.comp_apply] at e
  simp only [genMap, CommRingCat.hom_comp, RingHom.comp_apply]
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom e

theorem add_val {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X} {a b : Ω} {r s : ℂ}
    (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a + b) (r + s) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨_, y, rfl, rfl⟩ := h'
  exact ⟨h, x + y, map_add _ _ _, map_add _ _ _⟩

def QV (i : Ω →+* Ω') (W : Subring Ω') (φ : W →+* ℂ) (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (n : Ω) : Prop :=
  ∃ h : i n ∈ W, ValAt ξ z n (φ ⟨i n, h⟩)

variable {i : Ω →+* Ω'} {W : Subring Ω'} {φ : W →+* ℂ} {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

theorem QV.add {a b : Ω} (ha : QV i W φ ξ z a) (hb : QV i W φ ξ z b) : QV i W φ ξ z (a + b) := by
  obtain ⟨h1, v1⟩ := ha
  obtain ⟨h2, v2⟩ := hb
  have hm : i (a + b) ∈ W := by rw [map_add (f := _)]; exact W.add_mem h1 h2
  refine ⟨hm, ?_⟩
  have e : (⟨i (a + b), hm⟩ : W) = ⟨_, h1⟩ + ⟨_, h2⟩ := Subtype.ext (by simp)
  rw [e, map_add (f := _)]
  exact add_val v1 v2

theorem QV.mul {a b : Ω} (ha : QV i W φ ξ z a) (hb : QV i W φ ξ z b) : QV i W φ ξ z (a * b) := by
  obtain ⟨h1, v1⟩ := ha
  obtain ⟨h2, v2⟩ := hb
  have hm : i (a * b) ∈ W := by rw [map_mul]; exact W.mul_mem h1 h2
  refine ⟨hm, ?_⟩
  have e : (⟨i (a * b), hm⟩ : W) = ⟨_, h1⟩ * ⟨_, h2⟩ := Subtype.ext (by simp)
  rw [e, map_mul]
  exact CxVal.mul v1 v2

theorem QV.int (hz : genPt ξ ⤳ centre z) (n : ℤ) : QV i W φ ξ z (n : Ω) := by
  have hm : i (n : Ω) ∈ W := by rw [map_intCast]; exact intCast_mem W n
  refine ⟨hm, ?_⟩
  have e : (⟨i (n : Ω), hm⟩ : W) = (n : W) := Subtype.ext (by simp)
  rw [e, map_intCast]
  exact ⟨hz, n, by simp, (map_intCast (Scheme.stalkClosedPointTo z).hom n).trans (by simp)⟩

theorem QV.prod {ι : Type} (hz : genPt ξ ⤳ centre z) (s : Finset ι) (f : ι → Ω)
    (h : ∀ k ∈ s, QV i W φ ξ z (f k)) : QV i W φ ξ z (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using QV.int (i := i) (W := W) (φ := φ) hz 1
  | insert k s hk ih =>
    rw [Finset.prod_insert hk]
    exact (h k (Finset.mem_insert_self k s)).mul (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

theorem QV.adjoin (hz : genPt ξ ⤳ centre z) {S : Set Ω} (hS : ∀ n ∈ S, QV i W φ ξ z n) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ S) : QV i W φ ξ z a := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap n => simpa using QV.int (i := i) (W := W) (φ := φ) hz n
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

theorem val_frac {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) {s g n : S} {m : ℕ} (e : s * g ^ m = n) :
    f s * f g ^ m = f n := by
  rw [← e, map_mul, map_pow]

theorem frac_mem (hU : ∀ a : W, φ a ≠ 0 → IsUnit a) {a nn dd : Ω} {m : ℕ} {r vn vd : ℂ}
    (hn : i nn ∈ W) (hd : i dd ∈ W) (vn' : φ ⟨_, hn⟩ = vn) (vd' : φ ⟨_, hd⟩ = vd) (hvd : vd ≠ 0)
    (e : a * dd ^ m = nn) (e' : r * vd ^ m = vn) : ∃ h : i a ∈ W, φ ⟨_, h⟩ = r := by
  obtain ⟨u, hu⟩ := hU ⟨_, hd⟩ (by rw [vd']; exact hvd)
  have h1 : ((u : W) : Ω') = i dd := by rw [hu]
  have h2 : (((u⁻¹ : Wˣ) : W) : Ω') * i dd = 1 := by
    rw [← h1]
    exact congrArg Subtype.val u.inv_mul
  have hia : i a = i nn * (((u⁻¹ : Wˣ) : W) : Ω') ^ m := by
    rw [← e, map_mul, map_pow, mul_assoc, ← mul_pow, mul_comm (i dd), h2, one_pow, mul_one]
  have hm : i a ∈ W := by
    rw [hia]
    exact W.mul_mem hn (W.pow_mem (SetLike.coe_mem _) m)
  refine ⟨hm, ?_⟩
  have e2 : (⟨i a, hm⟩ : W) = ⟨_, hn⟩ * ((u⁻¹ : Wˣ) : W) ^ m := Subtype.ext (by simpa using hia)
  have h3 : φ ((u⁻¹ : Wˣ) : W) * vd = 1 := by
    rw [← vd', ← hu, ← map_mul, u.inv_mul, map_one]
  rw [e2, map_mul, map_pow, vn', ← e', mul_assoc, ← mul_pow, mul_comm vd, h3, one_pow, mul_one]

theorem contains_localRing : ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω')
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (W : Subring Ω') (φ : W →+* ℂ),
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordsAt ξ y z w →
    (∀ a : W, φ a ≠ 0 → IsUnit a) →
    (∀ (k : K) (c e : J k), w ⟨k, c⟩ ≠ 0 →
      ∃ h : i (y ⟨k, e⟩ / y ⟨k, c⟩) ∈ W, φ ⟨_, h⟩ * w ⟨k, c⟩ = w ⟨k, e⟩) →
    ∀ (a : Ω) (r : ℂ), ValAt ξ z a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r := by
  intro X Ω Ω' _ _ i ξ K _ J y z w W φ tie hw hU hyp a r har
  obtain ⟨hz, s, hsa, hsr⟩ := har
  choose c hc using hw.1
  have hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (hc k)).1
  have hxc : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  have ratio : ∀ (k : K) (e : J k), QV i W φ ξ z (y ⟨k, e⟩ / y ⟨k, c k⟩) := fun k e => by
    obtain ⟨h, v⟩ := hyp k (c k) e (hc0 k)
    obtain ⟨t, ht, ht'⟩ := (hw.2 k (c k) (hc k)).2 e
    refine ⟨h, ?_⟩
    rwa [mul_right_cancel₀ (hc0 k) (v.trans ht')]
  have gen : ∀ c' : (k : K) → J k, QV i W φ ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) := fun c' => by
    rw [← Finset.prod_div_distrib]
    exact QV.prod hz _ _ fun k _ => ratio k (c' k)
  have hin : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre z, hz⟩ := by
    refine ⟨hxc, fun c' => ?_⟩
    obtain ⟨_, _, s', hs', _⟩ := gen c'
    exact ⟨s', hs'⟩
  obtain ⟨U, hUa, hUm⟩ := tie.affine c hxc
  have hpU : centre z ∈ U := (hUm _).2 ⟨hz, hin⟩
  obtain ⟨n, d, m, hd, e⟩ := germ_frac hUa hpU s
  have hgU : genPt ξ ∈ U := hz.mem_open U.isOpen hpU
  have hQ : ∀ f : Γ(X, U), QV i W φ ξ z
      ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU f)) := fun f => by
    refine QV.adjoin hz (S := Set.range fun j : (k : K) → J k =>
      (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ?_ ((tie.ring c hxc _).2 fun q hq => ?_)
    · rintro _ ⟨j, rfl⟩
      exact gen j
    · have hqU : q.1 ∈ U := (hUm _).2 ⟨q.2, hq⟩
      exact ⟨X.presheaf.germ U q.1 hqU f, genMap_germ ξ hqU q.2 f⟩
  have hval : ∀ f : Γ(X, U), ∃ h : i ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU f)) ∈ W,
      φ ⟨_, h⟩ = (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U (centre z) hpU f) := fun f => by
    obtain ⟨h, v⟩ := hQ f
    exact ⟨h, CxVal.unique v ⟨hz, _, genMap_germ ξ hpU hz f, rfl⟩⟩
  obtain ⟨hn, vn⟩ := hval n
  obtain ⟨hd', vd⟩ := hval d
  refine frac_mem (m := m) hU hn hd' vn vd (hd.map (Scheme.stalkClosedPointTo z).hom).ne_zero ?_ ?_
  · have e1 := congrArg (genMap ξ ⟨centre z, hz⟩) e
    rw [map_mul, map_pow, hsa, genMap_germ ξ hpU hz, genMap_germ ξ hpU hz] at e1
    exact e1
  · rw [← hsr]
    exact val_frac (Scheme.stalkClosedPointTo z).hom e

end GlobalTheory.CompanionTheory.Ar.RegVal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionsFiniteDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeFormAna

theorem pos_of_theta_power : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (N : ℕ) (J : Type) (Θ : J → (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) → 0 < N → (∀ i, Differentiable ℂ (Θ i)) → (∀ i (l : Λ) z, Θ i (z + l) = (χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ N * Θ i z) → (∃ i, Θ i ≠ 0) → (∀ w : Fin g → ℂ, w ≠ 0 → ¬ ∀ i (t : ℂ) z, Θ i (z + t • w) = Θ i z) → ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := by
  intro g Λ hΛ hspan Hm χ N J Θ hH hχ hN hΘ htr hne hinv z hz
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨H', hH'⟩ : ∃ H' : Matrix (Fin g) (Fin g) ℂ, H' = (N : ℂ) • Hm := ⟨_, rfl⟩
  have hH'h : H'.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hH', Matrix.conjTranspose_smul, hH.eq]
    simp
  have hform : ∀ u v : Fin g → ℂ, u ⬝ᵥ H'.mulVec v = (N : ℂ) * (u ⬝ᵥ Hm.mulVec v) := by
    intro u v
    rw [hH', Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hre : ∀ u : Fin g → ℂ,
      (u ⬝ᵥ H'.mulVec (star u)).re = N * (u ⬝ᵥ Hm.mulVec (star u)).re := by
    intro u
    rw [hform]
    simp
  have htr' : ∀ i (l : Λ) z, Θ i (z + l) =
      ((χ l) ^ N * Complex.exp (Real.pi * (z ⬝ᵥ H'.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ H'.mulVec (star (l : Fin g → ℂ))))) * Θ i z := by
    intro i l z
    rw [htr i l z, mul_pow, ← Complex.exp_nat_mul, hform, hform]
    congr 3
    ring
  have hχ' : ∀ l, ‖(χ l) ^ N‖ = 1 := fun l => by rw [norm_pow, hχ, one_pow]
  have hbd : ∀ i, ∃ C : ℝ, ∀ z, ‖Θ i z‖ ≤
      C * Real.exp (Real.pi / 2 * (z ⬝ᵥ H'.mulVec (star z)).re) := fun i =>
    GlobalTheory.ThetaPositivity.exists_norm_le Λ hH'h (fun l => χ l ^ N) hχ' (hΘ i).continuous (htr' i)
  obtain ⟨i0, hi0⟩ := hne
  obtain ⟨C0, hC0⟩ := hbd i0
  have hnn : ∀ w : Fin g → ℂ, 0 ≤ (w ⬝ᵥ Hm.mulVec (star w)).re := fun w =>
    not_lt.mp fun hw => hi0 (GlobalTheory.ThetaPositivity.eq_zero_of_neg hH'h (hΘ i0) hC0 (w := w)
      (by rw [hre]; exact mul_neg_of_pos_of_neg hNr hw))
  have him : ∀ w : Fin g → ℂ, (w ⬝ᵥ Hm.mulVec (star w)).im = 0 := fun w => by
    have h := congrArg Complex.im (GlobalTheory.ThetaPositivity.form_conj hH w w)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  refine lt_of_le_of_ne (hnn z) fun h0 => ?_
  open scoped ComplexOrder in
  have hpsd : Hm.PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hH, fun x => ?_⟩
    have h1 := hnn (star x)
    have h2 := him (star x)
    rw [star_star] at h1 h2
    exact Complex.le_def.mpr ⟨h1, h2.symm⟩
  have hker : Hm.mulVec (star z) = 0 :=
    hpsd.dotProduct_mulVec_zero_iff.mp (by
      rw [star_star]
      exact Complex.ext h0.symm (him z))
  have hker' : ∀ t : ℂ, H'.mulVec (star (t • z)) = 0 := by
    intro t
    rw [star_smul, Matrix.mulVec_smul, hH', Matrix.smul_mulVec, hker]
    simp
  refine hinv z hz fun i t y => ?_
  obtain ⟨C, hC⟩ := hbd i
  have hd : Differentiable ℂ fun t : ℂ => Θ i (y + t • z) :=
    (hΘ i).comp ((differentiable_const _).add (differentiable_id.smul_const z))
  have hq : ∀ t : ℂ, ((y + t • z) ⬝ᵥ H'.mulVec (star (y + t • z))).re =
      (y ⬝ᵥ H'.mulVec (star y)).re := by
    intro t
    rw [GlobalTheory.ThetaPositivity.form_add_self hH'h, hker' t]
    simp
  have hb : Bornology.IsBounded (Set.range fun t : ℂ => Θ i (y + t • z)) := by
    refine isBounded_iff_forall_norm_le.2
      ⟨C * Real.exp (Real.pi / 2 * (y ⬝ᵥ H'.mulVec (star y)).re), ?_⟩
    rintro _ ⟨t, rfl⟩
    have h := hC (y + t • z)
    rwa [hq t] at h
  have h := hd.apply_eq_apply_of_bounded hb t 0
  simpa using h

end GlobalTheory.CompanionTheory.Ar.HodgeFormAna
end

