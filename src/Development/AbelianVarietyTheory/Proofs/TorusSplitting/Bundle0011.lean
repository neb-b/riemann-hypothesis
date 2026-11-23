module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0026
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.FiniteExtensionRamificationEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EtaVal.FiniteExt

section Val

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem alg_ne {x : V} (hx : x ≠ 0) : algebraMap V (FractionRing V) x ≠ 0 := by
  simpa using hx

theorem vV_unit {u : V} (hu : IsUnit u) : vV V (algebraMap V (FractionRing V) u) = 0 := by
  have : valV V (algebraMap V (FractionRing V) u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal u).1 h hu
  simp [vV, this]

theorem vV_irr {p : V} (hp : Irreducible p) : vV V (algebraMap V (FractionRing V) p) = 1 := by
  have : valV V (algebraMap V (FractionRing V) p) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ hp.ne_zero
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer p).1 hp)
  simp [vV, this]

theorem vV_pow {x : FractionRing V} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  induction n with
  | zero => simp [vV]
  | succ n ih => rw [pow_succ, vV_mul (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem vV_eq {p : V} (hp : Irreducible p) {u : V} (hu : IsUnit u) (n : ℕ) :
    vV V (algebraMap V (FractionRing V) (u * p ^ n)) = n := by
  rw [map_mul, map_pow, vV_mul (alg_ne hu.ne_zero) (pow_ne_zero _ (alg_ne hp.ne_zero)), vV_unit hu,
    vV_pow (alg_ne hp.ne_zero), vV_irr hp]; simp

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vV_ext (g : O →+* V) (hg : Function.Injective g) (i : FractionRing O →+* FractionRing V)
    (hi : ∀ a, i (algebraMap O _ a) = algebraMap V _ (g a)) {p : O} (hp : Irreducible p) (x : FractionRing O) :
    vV V (i x) = vV V (algebraMap V (FractionRing V) (g p)) * vV O x := by
  have h1 : ∀ a : O, a ≠ 0 → vV V (i (algebraMap O _ a)) =
      vV V (algebraMap V (FractionRing V) (g p)) * vV O (algebraMap O (FractionRing O) a) := by
    intro a ha
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hp
    have hgp : g p ≠ 0 := fun h => hp.ne_zero (hg (h.trans (map_zero g).symm))
    rw [vV_eq hp u.isUnit, hi, map_mul, map_pow, map_mul, map_pow,
      vV_mul (alg_ne (u.isUnit.map g).ne_zero) (pow_ne_zero _ (alg_ne hgp)), vV_unit (u.isUnit.map g),
      vV_pow (alg_ne hgp)]
    ring
  by_cases hx : x = 0
  · subst hx; simp [vV]
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have e1 : algebraMap O (FractionRing O) a / algebraMap O _ s * algebraMap O _ s = algebraMap O _ a :=
    div_mul_cancel₀ _ (alg_ne hs0)
  have e2 := vV_mul (V := O) hx (alg_ne hs0)
  have e3 := vV_mul (V := V) ((map_ne_zero i).2 hx) ((map_ne_zero i).2 (alg_ne hs0))
  rw [← map_mul, e1, h1 a ha0, h1 s hs0] at e3
  rw [e1] at e2
  rw [e2] at e3
  linarith

end Val

theorem exists_extension {A B C : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    (φ : A →+* B) (hφ : Function.Injective φ) (hint : φ.IsIntegral) (e : A →+* C)
    (he : Function.Injective e) (h1 : ∀ a, ‖e a‖ ≤ 1) :
    ∃ g : B →+* C, Function.Injective g ∧ (∀ a, g (φ a) = e a) ∧ ∀ b, ‖g b‖ ≤ 1 := by
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra A C := e.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hint⟩
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hφ
  haveI : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).2 he
  let g : B →ₐ[A] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨g.toRingHom, ?_, fun a => g.commutes a, fun b => ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := A) ?_
    rw [eq_bot_iff]
    intro a ha
    have : g (algebraMap A B a) = 0 := ha
    rw [g.commutes] at this
    exact he (this.trans (map_zero e).symm)
  · have hb : IsIntegral A (g b) := (Algebra.IsIntegral.isIntegral b).map g
    let v := NormedField.valuation (K := C)
    let e' : A →+* v.integer := e.codRestrict v.integer (fun a => by
      rw [Valuation.mem_integer_iff]
      exact_mod_cast h1 a)
    letI : Algebra A v.integer := e'.toAlgebra
    haveI : IsScalarTower A v.integer C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hb' : IsIntegral v.integer (g b) := hb.tower_top
    have := (Valuation.integer.integers v).isIntegral_iff_v_le_one.1 hb'
    exact_mod_cast this

end GlobalTheory.EtaVal.FiniteExt

namespace GlobalTheory.EtaVal


open FiniteExt in
theorem finite_extension_ramification_embedding :
    ∀ (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ∃ (i : T.Fr →+* T'.Fr) (ρ : ℕ), 0 < ρ ∧ (∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (φ a)) ∧ (∀ x, vV T'.V (i x) = (ρ : ℤ) * vV T.V x) ∧ ∀ (p : ℕ) (C : SCF p) (eF : T.Fr →+* ↥C.S), (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) → (∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) → ∃ f : T'.V →+* intO ↥C.S, Function.Injective f ∧ (∀ a, ((f (φ a) : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) ∧ ∀ a ∈ maximalIdeal T'.V, ‖((f a : intO ↥C.S) : ↥C.S)‖ < 1 := by
  intro T T' φ hφ hfin
  have hint : φ.IsIntegral := hfin.to_isIntegral
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
  have hφp : φ p ≠ 0 := fun h => hp.ne_zero (hφ (h.trans (map_zero φ).symm))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hφp hq
  have hn : 0 < n := by
    haveI : IsLocalHom φ := hint.isLocalHom hφ
    rcases n with _ | n
    · exfalso
      apply hp.not_isUnit
      refine isUnit_of_map_unit φ p ?_
      rw [hu]; simp
    · omega
  have hinj : Function.Injective ((algebraMap T'.V T'.Fr).comp φ) :=
    (IsFractionRing.injective T'.V T'.Fr).comp hφ
  let i : T.Fr →+* T'.Fr := IsFractionRing.lift hinj
  have hi : ∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (φ a) := fun a =>
    IsFractionRing.lift_algebraMap hinj a
  refine ⟨i, n, hn, hi, fun x => ?_, fun l C eF h1 h2 => ?_⟩
  · rw [vV_ext φ hφ i hi hp x, hu, vV_eq hq u.isUnit]
  · obtain ⟨g, hg, hgφ, hg1⟩ := exists_extension φ hφ hint (eF.comp (algebraMap T.V T.Fr))
      (eF.injective.comp (IsFractionRing.injective T.V T.Fr)) h1
    refine ⟨g.codRestrict (intO ↥C.S) (fun b => hg1 b), fun a b h => hg (congrArg Subtype.val h),
      fun a => hgφ a, fun a ha => ?_⟩
    change ‖g a‖ < 1
    have hp1 : ‖g (φ p)‖ < 1 := by
      rw [hgφ]
      exact h2 p ((IsLocalRing.mem_maximalIdeal p).2 hp.not_isUnit)
    have hq1 : ‖g q‖ < 1 := by
      have e : q ^ n = (u⁻¹ : T'.Vˣ) * φ p := by rw [hu, Units.inv_mul_cancel_left]
      have : ‖g q‖ ^ n < 1 := by
        rw [← norm_pow, ← map_pow, e, map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hg1 _) (norm_nonneg _) hp1
      exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    rw [hq.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hq1 (hg1 _)

end GlobalTheory.EtaVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.PhiCSmulPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

open scoped Pointwise

theorem phiC_smul_of_nonneg {E : Type} [Field E] [NumberField E] (cj : E → E) {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] (b : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X) {t : ℝ} (ht : 0 ≤ t) :
    Formalism.MainNotions.ModuliIntegralCharts.phiC cj (t • b) = t * Formalism.MainNotions.ModuliIntegralCharts.phiC cj b := by
  rw [phiC_eq_sInf, phiC_eq_sInf, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg ht]
  congr 1
  ext x
  constructor
  · rintro ⟨l, h1, h2, rfl⟩
    exact ⟨l b, ⟨l, h1, h2, rfl⟩, (map_smul l t b).symm⟩
  · rintro ⟨_, ⟨l, h1, h2, rfl⟩, rfl⟩
    exact ⟨l, h1, h2, (map_smul l t b).symm⟩

theorem phiC_smul_pull : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (X X' : Type) [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup X'] [Module (𝓞 E) X'] (e : X ≃ₗ[𝓞 E] X') (β' : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X') (t : ℝ), 0 ≤ t → ∃ β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X, (∀ a b, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a b = t * (β' : X' →ₗ[ℤ] X' →ₗ[ℤ] ℝ) (e a) (e b)) ∧ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β = t * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β' := by
  intro E _ _ cj X X' _ _ _ _ e β' t ht
  refine ⟨t • pullS cj e β', fun a b => ?_, ?_⟩
  · rw [← pullS_apply cj e β' a b]
    rfl
  · rw [phiC_smul_of_nonneg cj _ ht, phiC_pull]

end GlobalTheory.EtaVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.SumCosetMinGePhiCDivSq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem sum_cosetMin_ge_phiC_div_sq : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E), (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) → ∀ w₀ : 𝓞 E, (w₀ : E) + cj w₀ = 1 → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite ℤ X] (Q : X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X), (∀ a, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → (∀ a, 0 ≤ Q a) → ∀ (m : ℕ), 2 ≤ m → ∀ (n : ℕ) (y : Fin n → X), (∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m ^ 2 • t) → ∀ v : Fin n → WithTop ℚ, (∀ b (q : ℚ), (∀ χ, q ≤ (Q (m • χ + y b) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v b) → ∀ q : ℚ, (q : ℝ) ≤ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β / (m : ℝ) ^ 2 → (q : WithTop ℚ) ≤ ∑ b, v b := by
  intro E _ _ cj hcj w₀ hw X _ _ _ Q β hβQ hQnn m hm n y hgen v hv q hq
  have hβpos : ∀ a, 0 ≤ (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a := fun a => by
    rw [hβQ a]
    have h' : (0 : ℝ) ≤ Q a := by exact_mod_cast hQnn a
    linarith
  choose z hz using fun b => Formalism.MainNotions.ModuliIntegralCharts.H1.etPoint_min Q hQnn (y b) m
  have hgen' : ∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m • t := fun a => by
    obtain ⟨u, hu, t, ht⟩ := hgen a
    exact ⟨u, hu, m • t, by rw [ht, smul_smul, pow_two]⟩
  have hspan := Formalism.MainNotions.ModuliIntegralCharts.H1.etSpan_holds E X m hm n y z hgen'
  have hphi := Formalism.MainNotions.ModuliIntegralCharts.H1.phiCSpan_holds E cj hcj X w₀ hw β hβpos n (fun b => y b + m • z b) hspan
  have hsum : Formalism.MainNotions.ModuliIntegralCharts.phiC cj β ≤ ∑ b, (Q (y b + m • z b) : ℝ) := by
    refine hphi.trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
    have h := Formalism.MainNotions.ModuliIntegralCharts.H1.two_mul_form_half_unit hcj w₀ hw β (y b + m • z b)
    rw [hβQ] at h
    linarith
  have hpt : ∀ b, (((Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) ≤ v b := by
    intro b
    refine hv b _ fun z' => ?_
    have h : (Q (y b + m • z b) : ℚ) ≤ (Q (m • z' + y b) : ℚ) := by
      rw [add_comm (m • z')]
      exact_mod_cast hz b z'
    exact div_le_div_of_nonneg_right h (by positivity)
  have hR : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  have hqR : (q : ℝ) ≤ ((∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : ℝ) := by
    push_cast
    rw [← Finset.sum_div]
    exact hq.trans (div_le_div_of_nonneg_right hsum hR.le)
  have hqQ : q ≤ ∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) := by exact_mod_cast hqR
  calc ((q : ℚ) : WithTop ℚ) ≤ ((∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) :=
        WithTop.coe_le_coe.2 hqQ
    _ = ∑ b, (((Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) := WithTop.coe_sum _ _
    _ ≤ ∑ b, v b := Finset.sum_le_sum fun b _ => hpt b

end GlobalTheory.EtaVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ValForm

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem hasVal_coord {D : DegPre V} {χ : D.X} {n : ℤ} {r : V} (hn : QForm.QVal D ϖ χ n) (hr : PsiCoord D χ r) :
    HasVal ϖ (algebraMap V (FractionRing V) r) n := by
  obtain ⟨j, hj, h, e⟩ := hr
  have htop : LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) j = ⊤ :=
    eq_top_of_closedPoint_mem _ (Set.mem_iInter.2 fun _ => hj trivial)
  obtain ⟨c, hc, eV, hce⟩ := genHasVal_top D.P.L (fun _ : PUnit => (D.c χ).left) (fun _ => -1) (D.psi χ) hn j htop h
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) (DegPre.toOpen (R := V) ⊤ r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at hnat
  have hid : (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (DegPre.toOpen ⊤ r) = r := by
    simp only [DegPre.toOpen, RingHom.coe_comp, Function.comp_apply]
    have : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of V)).Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]
    simp
  have hval : algebraMap V (FractionRing V) ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (DegPre.toOpen ⊤ r)) =
      c * algebraMap V (FractionRing V) (eV : V) := by
    rw [← hce]
    erw [← hnat]
    rw [CommRingCat.comp_apply]
    exact congrArg _ e
  rw [hid] at hval
  rw [hval]
  exact hasVal_mul_unit hc eV

omit [IsDiscreteValuationRing V] in
theorem hasVal_mul (hϖ : Irreducible ϖ) {a b : V} {n m : ℤ} (ha : HasVal ϖ (algebraMap V (FractionRing V) a) n)
    (hb : HasVal ϖ (algebraMap V (FractionRing V) b) m) :
    HasVal ϖ (algebraMap V (FractionRing V) (a * b)) (n + m) := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  refine ⟨u * v, ?_⟩
  rw [map_mul, hu, hv, zpow_add₀ ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero),
    Units.val_mul, map_mul]
  ring

omit [IsDiscreteValuationRing V] in
theorem logb_of_hasVal {a : V} {n : ℤ} (hn : 0 ≤ n) (ha : HasVal ϖ (algebraMap V (FractionRing V) a) n)
    {C : Type} [NormedField C] (f : V →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (p : ℝ) :
    Real.logb p ‖f a‖ = n * Real.logb p ‖f ϖ‖ := by
  obtain ⟨u, hu⟩ := ha
  lift n to ℕ using hn
  rw [zpow_natCast, ← map_pow, ← map_mul] at hu
  rw [IsFractionRing.injective V (FractionRing V) hu, map_mul, norm_mul, GlobalTheory.PeriodBalance.norm_unit f hf u,
    _root_.mul_one, map_pow, norm_pow, Real.logb_pow, Int.cast_natCast]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (G : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) G) (ϖ : V), Irreducible ϖ → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∃ (Q : P.D.toPre.X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj P.D.toPre.X), QForm.IsQ P.D.toPre ϖ Q ∧ (∀ a, 0 ≤ Q a) ∧ (∀ a b, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b = QForm.bOf P.D.toPre Q a b) ∧ (∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) ∧ ∀ (C : Type) [NormedField C] (f : V →+* C) (p : ℕ), Function.Injective f → (∀ a, ‖f a‖ ≤ 1) → ∀ a b, betaAt P.D.toPre f p a b = -Real.logb p ‖f ϖ‖ * (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b := by
  intro E _ _ _ H V _ _ _ _ _ G P ϖ hϖ cj hcj
  letI := H.starRing
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have hQ' : QForm.IsQ P.D.toPre ϖ Q := hQ
  have hex : ∀ χ, ∃ r, PsiCoord P.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main V P.D inferInstance χ).1).imp fun _ h => h.1
  have hv : ∀ χ, HasVal ϖ (algebraMap V (FractionRing V) (hex χ).choose) (Q χ) := fun χ =>
    hasVal_coord (hQ χ) (hex χ).choose_spec
  have h0 : ∀ a, 0 ≤ Q a := fun a => by
    by_cases ha : a = 0
    · rw [ha, QForm.Q_zero hϖ P.D hQ']
    · exact zero_le_one.trans (QForm.Q_pos hϖ P.D hQ' ha)
  have hbal : ∀ (x : 𝓞 E) a b, QForm.bOf P.D.toPre Q (x • a) b = QForm.bOf P.D.toPre Q a (H.bar x • b) := by
    intro x a b
    obtain ⟨u, hu⟩ := GlobalTheory.PeriodBalance.coord_balance P.D.toPre P.oD x a b (hex (x • a + b)).choose_spec
      (hex (x • a)).choose_spec (hex b).choose_spec (hex (a + H.bar x • b)).choose_spec (hex a).choose_spec
      (hex (H.bar x • b)).choose_spec
    have h1 := hasVal_mul_unit (hasVal_mul hϖ (hasVal_mul hϖ (hv (x • a + b)) (hv a)) (hv (H.bar x • b))) u
    have h2 := hasVal_mul hϖ (hasVal_mul hϖ (hv (a + H.bar x • b)) (hv (x • a))) (hv b)
    rw [← map_mul, _root_.mul_comm, hu] at h1
    have := hasVal_unique hϖ h1 h2
    simp only [QForm.bOf]
    linarith
  let β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ :=
    LinearMap.mk₂ ℤ (fun a b => (QForm.bHom hϖ P.D hQ' a b : ℝ))
      (fun a a' b => by simp only [map_add (f := _), AddMonoidHom.add_apply, Int.cast_add])
      (fun c a b => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul, Int.cast_mul, zsmul_eq_mul, Int.cast_id])
      (fun a b b' => by simp only [map_add (f := _), Int.cast_add])
      (fun c a b => by simp only [map_zsmul, smul_eq_mul, Int.cast_mul, zsmul_eq_mul, Int.cast_id])
  have hβ : ∀ a b, β a b = (QForm.bOf P.D.toPre Q a b : ℝ) := fun _ _ => rfl
  refine ⟨Q, ⟨β, fun a b => ?_, fun c c' hc a b => ?_⟩, hQ', h0, hβ, fun a => ?_, fun C _ f p _ hf a b => ?_⟩
  · rw [hβ, hβ, QForm.bOf_comm]
  · obtain rfl : c' = H.bar c := RingOfIntegers.ext (by rw [hc, hcj, H.bar_eq])
    rw [hβ, hβ, hbal]
  · show β a a = _
    rw [hβ, ← QForm.two_Q_eq hϖ P.D hQ']
    push_cast
    rfl
  · have hp : ∀ χ, vPsiAt P.D.toPre f p χ = -(Q χ * Real.logb p ‖f ϖ‖) := fun χ =>
      (dif_pos (hex χ)).trans (by rw [logb_of_hasVal (h0 χ) (hv χ) f hf])
    show _ = _ * β a b
    rw [hβ]
    simp only [betaAt, hp, QForm.bOf]
    push_cast
    ring

end GlobalTheory.ValForm
end
end

