module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GradedDifferentComparison
section
set_option autoImplicit false

noncomputable section

open scoped NNReal NumberField Classical
open GlobalTheory.HTLat GlobalTheory.EigenSplit

namespace GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison

section Valuations

variable {C : Type} [Field C]

def absDifferent (v : Valuation C ℝ≥0) {E : Type} [Field E] [NumberField E] (τ : E →+* C) : ℝ≥0 :=
  sSup {r | ∃ x ∈ differentIdeal ℤ (𝓞 E), v (τ x) = r}

def IsPowMul_vp (p : ℕ) (v : Valuation C ℝ≥0) {O : Type} [CommRing O] [Algebra O C] {U : Type}
    [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] (t : ℝ)
    (La La' : Submodule O U) : Prop :=
  ∃ u : C, (v u : ℝ) = (v (p : C) : ℝ) ^ t ∧ La' = scaleLat u La


set_option autoImplicit false in
open scoped NNReal NumberField Classical in
variable {C : Type} [Field C] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.exists_generator_different {v : Valuation C ℝ≥0} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
    (τ : E →+* C) :
    ∃ δ : O, (differentIdeal ℤ (𝓞 E)).map (_root_.GlobalTheory.HTLat.embO hv τ) =
        Ideal.span {δ} ∧
      v (algebraMap O C δ) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.absDifferent v τ ∧
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.absDifferent v τ ≠ 0 ∧ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.absDifferent v τ ≤ 1 := by
  set f := _root_.GlobalTheory.HTLat.embO hv τ with hf
  have hemb : ∀ x : 𝓞 E, algebraMap O C (f x) = τ x :=
    _root_.GlobalTheory.HTLat.algebraMap_embO hv τ
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian (differentIdeal ℤ (𝓞 E))
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hne
    rw [← hS]
    simp
  obtain ⟨g, hgS, hmax⟩ := Finset.exists_max_image S (fun g => v (τ g)) hSne
  have hgI : g ∈ differentIdeal ℤ (𝓞 E) := hS ▸ Submodule.subset_span hgS
  have hdvd : ∀ x ∈ differentIdeal ℤ (𝓞 E), f g ∣ f x := by
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      apply hv.dvd_of_le
      rw [hemb, hemb]
      exact hmax y hy
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact dvd_add ha hb
    | smul a b _ hb =>
      rw [smul_eq_mul, map_mul]
      exact dvd_mul_of_dvd_right hb _
  have hgreat : IsGreatest {r | ∃ x ∈ differentIdeal ℤ (𝓞 E), v (τ x) = r} (v (τ g)) := by
    refine ⟨⟨g, hgI, rfl⟩, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    rw [← hemb, ← hemb]
    exact hv.le_of_dvd (hdvd x hx)
  have habs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.absDifferent v τ = v (τ g) := hgreat.csSup_eq
  refine ⟨f g, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact hdvd x hx
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem f hgI
  · rw [habs, hemb]
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hx0' : v (τ x) ≠ 0 := by
      rw [Ne, map_eq_zero, map_eq_zero]
      exact_mod_cast hx0
    rw [habs]
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hx0') (hgreat.2 ⟨x, hx, rfl⟩))
  · rw [habs, ← hemb]
    exact hv.map_le_one _

end Valuations

section AtAPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] C] [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C] [IsAlgClosed C]
  [CharZero C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E))

variable {P} {Ψ : Finset (E →+* C)} {N j : ℕ}

end AtAPoint

section PadicComplex

@[reducible] def algInt (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] 𝓞_ℂ_[p] := (padicIntHom p).toAlgebra

@[reducible] def algField (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] ℂ_[p] :=
  ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (padicIntHom p)).toAlgebra

attribute [local instance] algInt algField

theorem tower (p : ℕ) [Fact p.Prime] :
    @IsScalarTower ℤ_[p] 𝓞_ℂ_[p] ℂ_[p] (algInt p).toSMul Algebra.toSMul (algField p).toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem fact_not_isUnit (p : ℕ) [Fact p.Prime] : Fact ¬IsUnit (p : 𝓞_ℂ_[p]) :=
  ⟨PadicComplexHost.not_isUnit_p p⟩

attribute [local instance] tower fact_not_isUnit PadicComplexHost.isAdicComplete

end PadicComplex

end GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.EigenSplit GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel

section AtPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  {Λ : Type} [CommRing Λ] [StarRing Λ]

def IsOpenFiniteFlatSubgroup (G : Over (Sp O)) [GrpObj G] (N : ℕ) {H : Over (Sp O)}
    (j : H ⟶ torsion G N) : Prop :=
  IsOpenImmersion j.left ∧ IsFinite H.hom ∧ Flat H.hom ∧
    (∀ S : Over (Sp O), ∃ z : S ⟶ H, z ≫ j ≫ torsion.ι G N = 1) ∧
    (∀ (S : Over (Sp O)) (x y : S ⟶ H), ∃ z : S ⟶ H,
      z ≫ j ≫ torsion.ι G N = (x ≫ j ≫ torsion.ι G N) * (y ≫ j ≫ torsion.ι G N)) ∧
    (∀ (S : Over (Sp O)) (x : S ⟶ H), ∃ z : S ⟶ H,
      z ≫ j ≫ torsion.ι G N = (x ≫ j ≫ torsion.ι G N)⁻¹)

def IsCharacter (G : Over (Sp O)) [GrpObj G] (N : ℕ) {H : Over (Sp O)} (j : H ⟶ torsion G N)
    (χ : H ⟶ Gm (Sp O)) : Prop :=
  ∀ (S : Over (Sp O)) (x y z : S ⟶ H),
    z ≫ j ≫ torsion.ι G N = (x ≫ j ≫ torsion.ι G N) * (y ≫ j ≫ torsion.ι G N) →
      z ≫ χ = (x ≫ χ) * (y ≫ χ)

omit [Fact p.Prime] in
theorem isNilpotent_dual {R : Type} [CommRing R] {n : ℕ} (h : (p : R) ^ n = 0) :
    IsNilpotent (p : DualNumber R) :=
  ⟨n, by rw [← map_natCast (algebraMap R (DualNumber R)), ← map_pow, h, map_zero]⟩

variable [Algebra ℤ_[p] O] (P : Point p v O Λ)

def alLeft : P.T →ₗ[ℤ_[p]] omega P.Gt := -P.al₀

def LevelReduction : Prop :=
  ∀ (n : ℕ) (H : Over (Sp O)) (j : H ⟶ torsion P.G (p ^ n)),
    IsOpenFiniteFlatSubgroup P.G (p ^ n) j →
    ∀ (t : P.T) (χ : H ⟶ Gm (Sp O)), IsCharacter P.G (p ^ n) j χ →
      (∀ (w : specO O O ⟶ H) (z : Pts P.A.A),
        z.left ≫ P.gen = spMap (algebraMap O C) ≫ (w ≫ j ≫ torsion.ι P.G (p ^ n)).left →
          algebraMap O C (unitOf (w ≫ χ) : O) = (weil P.A (p ^ n) (t.lev n) z : C)) →
      ∀ (R : Type) [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0) (x : LieG P.Gt)
        (w : specO O (DualNumber R) ⟶ H),
        w ≫ j ≫ torsion.ι P.G (p ^ n) =
          P.cmp (DualNumber R) (isNilpotent_dual hR) (ptMap (dualBC (Algebra.ofId O R)) ≫ x.1) →
        (unitOf (w ≫ χ) : DualNumber R) =
          TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (algebraMap O R ((alLeft P t).1 x))


variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

end AtPoint

end GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel
end
end

