module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1931
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalizationFiniteTypeComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory.EssFiniteDescent

theorem essFiniteType_of_eq_div : ∀ (K : Type) [Field K] (c : ℂ →+* K) (R : Subring K) (hcR : ∀ a, c a ∈ R) (E : ValuationSubring K) (hcE : ∀ a, c a ∈ E), R ≤ E.toSubring → (c.codRestrict R hcR).FiniteType → (∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s) → (c.codRestrict E hcE).EssFiniteType := by
  intro K _ c R hcR E hcE hRE hft hloc
  let f : R →+* E :=
    { toFun := fun r => ⟨(r : K), hRE r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let M : Submonoid R :=
    { carrier := {s | (s : K) ≠ 0 ∧ (s : K)⁻¹ ∈ E}
      mul_mem' := by
        rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
        refine ⟨by simpa using mul_ne_zero ha0 hb0, ?_⟩
        have : ((a * b : R) : K)⁻¹ = (b : K)⁻¹ * (a : K)⁻¹ := by
          push_cast; exact mul_inv_rev _ _
        rw [this]; exact E.mul_mem _ _ hb ha
      one_mem' := ⟨by simp, by simpa using E.one_mem⟩ }
  letI : Algebra ℂ R := (c.codRestrict R hcR).toAlgebra
  letI : Algebra R E := f.toAlgebra
  letI : Algebra ℂ E := (c.codRestrict E hcE).toAlgebra
  haveI : IsScalarTower ℂ R E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType ℂ R := hft
  haveI : IsLocalization M E := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, hs0, hs⟩
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hs⟩, ?_⟩
      apply Subtype.ext
      change (s : K) * (s : K)⁻¹ = 1
      exact mul_inv_cancel₀ hs0
    · rintro ⟨e, he⟩
      obtain ⟨a, ha, s, hs, hsE, rfl⟩ := hloc e he
      by_cases hs0 : s = 0
      · refine ⟨(0, 1), ?_⟩
        apply Subtype.ext
        change a / s * ((1 : M) : R) = (((0 : R)) : K)
        simp [hs0]
      · refine ⟨(⟨a, ha⟩, ⟨⟨s, hs⟩, by simpa using hs0, hsE⟩), ?_⟩
        apply Subtype.ext
        change a / s * s = a
        exact div_mul_cancel₀ a hs0
    · intro x y hxy
      refine ⟨1, ?_⟩
      have : (x : K) = y := congrArg (fun z : E => (z : K)) hxy
      simp [Subtype.ext this]
  haveI : Algebra.EssFiniteType R E := Algebra.EssFiniteType.of_isLocalization E M
  have h : Algebra.EssFiniteType ℂ E := Algebra.EssFiniteType.comp ℂ R E
  exact h

end GlobalTheory.EssFiniteDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalZEqOfSmulEqSum
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc

theorem evalZ_eq_of_smul_eq_sum {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {φ : InvFun ℤ} {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (h : φ.LinearOn γ) {b : LinearMap.BilinForm ℤ X} {k : ℕ} (hk : 0 < k)
    {cf : Fin m → ℕ} (he : k • b = ∑ j, cf j • γ j) : φ.evalZ b = ∑ j, ((cf j : ℝ) / k) * φ.evalZ (γ j) := by
  rw [← (linearOn_iff φ γ).1 h _ (fun j => by positivity), ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun x y => ?_
  have h1 := LinearMap.congr_fun₂ he x y
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] at h1
  have h2 : (k : ℝ) * b x y = ∑ j, (cf j : ℝ) * γ j x y := by exact_mod_cast h1
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [show ∑ j, (cf j : ℝ) / k * (γ j x y : ℝ) = (∑ j, (cf j : ℝ) * γ j x y) / k by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring, ← h2]
  field_simp

theorem polFn_eq_min_linear : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ r : ℕ, r ≤ g → ∀ (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ i, IsCone id φ (γ i)) → ∃ (Nℓ : ℕ) (ℓ : Fin p → LinearMap.BilinForm ℤ (Fin r → ℤ) →ₗ[ℤ] ℤ), 0 < Nℓ ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j) → (∀ i, (Nℓ : ℝ) * φ.evalZ b' ≤ ℓ i b') ∧ ∃ i, (Nℓ : ℝ) * φ.evalZ b' = ℓ i b' := by
  intro g φ _ r _ p m γ hγ
  choose N ℓ hN h1 h2 h3 using fun i => (hγ i).strict
  refine ⟨∏ i, N i, fun i => ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℤ) • ℓ i,
    Finset.prod_pos fun i _ => hN i, ?_⟩
  rintro b' hs hp ⟨i, k, cf, hk, he⟩
  have hb : b' ∈ balForms (id : ℤ → ℤ) (Fin r → ℤ) := mem_balForms_int.2 hs
  have key : ∀ i, ((∏ j, N j : ℕ) : ℝ) = ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℝ) * N i := fun i => by
    rw [← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have eq : ∀ i, (N i : ℝ) * φ.evalZ b' ≤ ℓ i b' := fun i => h2 i b' hb hp
  refine ⟨fun i' => ?_, i, ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i', mul_assoc]
    exact mul_le_mul_of_nonneg_left (eq i') (by positivity)
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i, mul_assoc]
    congr 1
    have hev := evalZ_eq_of_smul_eq_sum (hγ i).linear hk he
    have hl : (k : ℤ) * ℓ i b' = ∑ j, (cf j : ℤ) * ℓ i (γ i j) := by
      have := congrArg (ℓ i) he
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
    have hl' : (k : ℝ) * ℓ i b' = ∑ j, (cf j : ℝ) * ℓ i (γ i j) := by exact_mod_cast hl
    have hk' : (k : ℝ) ≠ 0 := by positivity
    rw [hev, Finset.mul_sum, show (ℓ i b' : ℝ) = (∑ j, (cf j : ℝ) * ℓ i (γ i j)) / k by
      rw [← hl']; field_simp, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1 i j]
    field_simp

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjectionBalancedForms
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem exists_avg_proj_balForms : ∀ (O : Type) [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] (n c : ℕ) (b : Fin n → O) (T : Matrix (Fin n) (Fin n) ℤ), 0 < c → (∀ s t, T s t = T t s) → (∀ (a : O) (g : O →ₗ[ℤ] O →ₗ[ℤ] ℤ), ∑ s, ∑ t, T s t * g (b s * a) (b t) = ∑ s, ∑ t, T s t * g (b s) (b t * bar a)) → ∑ s, ∑ t, T s t • (bar (b s) * b t) = (c : O) → (∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ s, ∑ t, T s t * v s * v t) → ∃ P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X, (∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → P β ∈ GlobalTheory.PolFan.balForms bar X) ∧ (∀ β ∈ GlobalTheory.PolFan.balForms bar X, P β = (c : ℤ) • β) ∧ ∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → P (GlobalTheory.PolFan.sqForm l) ≠ 0 ∧ ∀ x, 0 ≤ P (GlobalTheory.PolFan.sqForm l) x x := by
  intro O _ bar X _ _ n c b T hc hT hint hsum hpos
  let f : Fin n → X →ₗ[ℤ] X := fun s => DistribSMul.toLinearMap ℤ X (b s)
  let P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X :=
    { toFun := fun β => ∑ s, ∑ t, T s t • β.compl₁₂ (f s) (f t)
      map_add' := fun β γ => by
        ext x y
        simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun m β => by
        ext x y
        simp [Finset.mul_sum, mul_left_comm] }
  have hP : ∀ β x y, P β x y = ∑ s, ∑ t, T s t * β (b s • x) (b t • y) := by
    intro β x y
    simp [P, f, LinearMap.sum_apply]

  let sp : X → O →ₗ[ℤ] X := fun y => (LinearMap.toSpanSingleton O X y).restrictScalars ℤ
  have hsp : ∀ y u, sp y u = u • y := fun y u => rfl
  have hsumL : ∀ L : O →ₗ[ℤ] ℤ, ∑ s, ∑ t, T s t * L (bar (b s) * b t) = c * L 1 := by
    intro L
    have := congrArg L hsum
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, smul_eq_mul] at this
    rw [this]
    have hc1 : (c : O) = c • (1 : O) := (nsmul_one c).symm
    rw [hc1, map_nsmul, nsmul_eq_mul]
  refine ⟨P, ?_, ?_, ?_⟩
  · intro β hβ
    have key : (∀ y z, P β y z = P β z y) ∧ ∀ (a : O) y z, P β (a • y) z = P β y (bar a • z) := by
      constructor
      · intro x y
        rw [hP, hP, Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        rw [hT, hβ]
      · intro a x y
        rw [hP, hP]
        have := hint a (β.compl₁₂ (sp x) (sp y))
        simp only [LinearMap.compl₁₂_apply, hsp, mul_smul] at this
        exact this
    exact key
  · intro β hβ
    obtain ⟨h1, h2⟩ := hβ
    ext x y
    rw [hP]
    have e : ∀ s t, β (b s • x) (b t • y) = (β x ∘ₗ sp y) (bar (b s) * b t) := by
      intro s t
      rw [h2]
      simp [hsp, mul_smul]
    simp only [e]
    rw [hsumL]
    simp [hsp]
  · intro l hl
    have hQ : ∀ x, P (GlobalTheory.PolFan.sqForm l) x x = ∑ s, ∑ t, T s t * (fun s => l (b s • x)) s * (fun s => l (b s • x)) t := by
      intro x
      rw [hP]
      simp [GlobalTheory.PolFan.sqForm_apply, mul_assoc]
    have hnn : ∀ x, 0 ≤ P (GlobalTheory.PolFan.sqForm l) x x := by
      intro x
      rw [hQ]
      by_cases hv : (fun s => l (b s • x)) = 0
      · rw [hv]; simp
      · exact (hpos _ hv).le
    refine ⟨fun h0 => ?_, hnn⟩
    have hv : ∀ y t, l (b t • y) = 0 := by
      intro y t
      by_contra hne
      have hv : (fun s => l (b s • y)) ≠ 0 := fun h => hne (congrFun h t)
      have := hpos _ hv
      rw [← hQ, h0] at this
      simp at this
    obtain ⟨x, hx⟩ : ∃ x, l x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hl (LinearMap.ext h)
    have := hsumL (l ∘ₗ sp x)
    have hz : ∀ s t, (l ∘ₗ sp x) (bar (b s) * b t) = 0 := by
      intro s t
      simp only [LinearMap.comp_apply, hsp]
      rw [mul_comm, mul_smul]
      exact hv _ _
    simp only [hz, mul_zero, Finset.sum_const_zero] at this
    simp [hsp] at this
    omega

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorGroupQuotientDescent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.Cartier.Descent

theorem unitAt_functionFieldMap {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W)
    [IsDominant q] (x : X) {f : W.functionField} (h : UnitAt (q x) f) :
    UnitAt x (functionFieldMap q f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨q.stalkMap x a, ha.map _, (functionFieldMap_algebraMap q x a).symm⟩

theorem exists_cartierDiv_descent : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (D : CartierDiv X),
    (∀ y : W, ∃ b : W.functionFieldˣ, ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) →
    ∃ E : CartierDiv W, ∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b) := by
  intro X W _ _ Γ _ _ ρ q _ hq D h
  choose b hb using h
  have : IsIntegralHom q := hq.isIntegralHom
  have hcl : IsClosedMap q := q.isClosedMap

  have hloc : ∀ y : W, ∃ U : W.Opens, y ∈ U ∧ ∃ f, ∀ y' ∈ U, germOf y' (b y') = germOf y' f := by
    intro y
    let O : Set X := {x | D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom (b y))}
    have hO : IsOpen O := isOpen_iff_forall_mem_open.2 fun x hx => by
      obtain ⟨U, hU, hU'⟩ := CartierDiv.IsEqn.exists_nhds hx
      exact ⟨U, fun z hz => hU' z hz, U.isOpen, hU⟩
    have hZ : IsClosed (q '' Oᶜ) := hcl _ hO.isClosed_compl
    refine ⟨⟨(q '' Oᶜ)ᶜ, hZ.isOpen_compl⟩, ?_, b y, fun y' hy' => ?_⟩
    · rintro ⟨x, hx, hxy⟩
      exact hx (hb y x hxy)
    · refine (germOf_eq_iff.2 ?_).symm
      refine _root_.GlobalTheory.OrbitSep.unitAt_of_forall_unitAt_fibre X W Γ ρ q hq y' _ fun x hx => ?_
      have h1 : x ∈ O := by
        by_contra hn
        exact hy' ⟨x, hn, hx⟩
      have h2 := (h1 : D.IsEqn x _).iff_unitAt.1 (hb y' x hx)
      simpa only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀] using h2
  let E : CartierDiv W := show cartierGroup W from ⟨fun y => germOf y (b y), hloc⟩
  refine ⟨E, fun y b' hE x hx => ?_⟩
  have hu : UnitAt y ((b' : W.functionField) / b y) := germOf_eq_iff.1 hE
  subst hx
  refine (hb (q x) x rfl).iff_unitAt.2 ?_
  have := unitAt_functionFieldMap q x hu
  simpa only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀] using this

end GlobalTheory.Cartier.Descent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmIntegralAveragingTraceTensor
section
set_option autoImplicit false

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
open NumberField

namespace GlobalTheory

namespace TraceTensor

variable {E : Type} [Field E] [NumberField E]

theorem exists_integral_orthogonal (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) :
    ∃ (n : ℕ) (b : Fin n → 𝓞 E) (e : Module.Basis (Fin n) ℚ E), (∀ i, e i = (b i : E)) ∧
      ∀ i j, i ≠ j → Algebra.trace ℚ E (σ (e i) * e j) = 0 := by
  classical
  let B : LinearMap.BilinForm ℚ E := (Algebra.traceForm ℚ E).comp σ.toLinearMap LinearMap.id
  have hB : ∀ x y, B x y = Algebra.trace ℚ E (σ x * y) := fun _ _ => rfl
  have hs : LinearMap.IsSymm B := ⟨fun x y => by
    rw [RingHom.id_apply, hB, hB, ← Algebra.trace_eq_of_algEquiv σ, map_mul, hσ, mul_comm]⟩
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs
  have hint : ∀ y : E, ∃ (m : ℕ) (b : 𝓞 E), m ≠ 0 ∧ (m : ℚ) • y = (b : E) := by
    intro y
    have halg : IsAlgebraic ℤ y :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic y)
    obtain ⟨m, b, hm, hb⟩ := halg.exists_nsmul_eq (S := 𝓞 E)
    exact ⟨m, b, hm, by rw [Nat.cast_smul_eq_nsmul, hb]⟩
  choose m b hm hb using hint
  have hu : ∀ i, IsUnit ((m (e i) : ℕ) : ℚ) := fun i => IsUnit.mk0 _ (Nat.cast_ne_zero.2 (hm _))
  refine ⟨_, fun i => b (e i), e.isUnitSMul hu, fun i => ?_, fun i j hij => ?_⟩
  · rw [Module.Basis.isUnitSMul_apply, hb]
  · have h : Algebra.trace ℚ E (σ (e i) * e j) = 0 := he hij
    rw [Module.Basis.isUnitSMul_apply, Module.Basis.isUnitSMul_apply, Rat.smul_def (m (e i) : ℚ), map_mul σ,
      map_ratCast, ← Rat.smul_def, smul_mul_assoc,
      mul_smul_comm, map_smul, map_smul, h, smul_zero, smul_zero]

theorem trace_mul_eq_repr (σ : E ≃ₐ[ℚ] E) {ι : Type} [Fintype ι] (e : Module.Basis ι ℚ E)
    (ho : ∀ i j, i ≠ j → Algebra.trace ℚ E (σ (e i) * e j) = 0) (y : E) (i : ι) :
    Algebra.trace ℚ E (σ (e i) * y) = e.repr y i * Algebra.trace ℚ E (σ (e i) * e i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← e.sum_repr y, Finset.mul_sum, map_sum]
  rw [Finset.sum_eq_single i]
  · rw [mul_smul_comm, map_smul, smul_eq_mul]
  · intro j _ hj
    rw [mul_smul_comm, map_smul, ho i j hj.symm, smul_zero]
  · simp

end TraceTensor


open TraceTensor in
theorem exists_cm_trace_tensor : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ∃ (n c : ℕ) (b : Fin n → NumberField.RingOfIntegers E) (T : Matrix (Fin n) (Fin n) ℤ), 0 < c ∧ (∀ s t, T s t = T t s) ∧ (∀ (a : NumberField.RingOfIntegers E) (g : NumberField.RingOfIntegers E →ₗ[ℤ] NumberField.RingOfIntegers E →ₗ[ℤ] ℤ), ∑ s, ∑ t, T s t * g (b s * a) (b t) = ∑ s, ∑ t, T s t * g (b s) (b t * H.bar a)) ∧ ∑ s, ∑ t, T s t • (H.bar (b s) * b t) = (c : NumberField.RingOfIntegers E) ∧ ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ s, ∑ t, T s t * v s * v t := by
  intro E _ _ _ H
  classical
  let σ : E ≃ₐ[ℚ] E := (IsCMField.complexConj E).restrictScalars ℚ
  have hσσ : ∀ x, σ (σ x) = x := fun x => IsCMField.complexConj_apply_apply E x
  have hbar : ∀ x : 𝓞 E, ((H.bar x : 𝓞 E) : E) = σ (x : E) := fun x => H.bar_eq x
  obtain ⟨n, b, e, heb, ho⟩ := exists_integral_orthogonal σ hσσ
  have htr : ∀ x y : 𝓞 E, ((Algebra.trace ℤ (𝓞 E) (H.bar x * y) : ℤ) : ℚ)
      = Algebra.trace ℚ E (σ (x : E) * (y : E)) := by
    intro x y
    rw [Algebra.coe_trace_int, ← hbar]
    rfl
  let d : Fin n → ℤ := fun i => Algebra.trace ℤ (𝓞 E) (H.bar (b i) * b i)
  have hdq : ∀ i, (d i : ℚ) = Algebra.trace ℚ E (σ (e i) * e i) := fun i => by
    rw [heb]; exact htr _ _
  have hdq0 : ∀ i, 0 < Algebra.trace ℚ E (σ (e i) * e i) := fun i =>
    StarNormBound.trace_conj_mul_pos _ (e.ne_zero i)
  have hd : ∀ i, 0 < d i := fun i => by
    have := hdq0 i
    rw [← hdq] at this
    exact_mod_cast this
  let t : Fin n → ℤ := fun i => ∏ j ∈ Finset.univ.erase i, d j
  let C : ℤ := ∏ j, d j
  have hC : 0 < C := Finset.prod_pos fun j _ => hd j
  have ht : ∀ i, 0 < t i := fun i => Finset.prod_pos fun j _ => hd j
  have htd : ∀ i, d i * t i = C := fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have htq : ∀ i, (t i : ℚ) = C * (Algebra.trace ℚ E (σ (e i) * e i))⁻¹ := fun i => by
    rw [← hdq, ← htd i]
    have : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
    push_cast
    field_simp
  have hexp : ∀ x : 𝓞 E, C • x = ∑ j, (t j * Algebra.trace ℤ (𝓞 E) (H.bar (b j) * x)) • b j := by
    intro x
    apply RingOfIntegers.coe_injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zsmul, map_sum]
    have hx := e.sum_repr (x : E)
    change C • (x : E) = _
    conv_lhs => rw [← hx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    change _ = _ • (b j : E)
    rw [← heb, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    rw [Int.cast_mul, htr, ← heb, trace_mul_eq_repr σ e ho, htq]
    have := (hdq0 j).ne'
    field_simp
  have hsym : ∀ x y a : 𝓞 E, Algebra.trace ℤ (𝓞 E) (H.bar x * (y * H.bar a))
      = Algebra.trace ℤ (𝓞 E) (H.bar y * (x * a)) := by
    intro x y a
    have : ((Algebra.trace ℤ (𝓞 E) (H.bar x * (y * H.bar a)) : ℤ) : ℚ)
      = ((Algebra.trace ℤ (𝓞 E) (H.bar y * (x * a)) : ℤ) : ℚ) := by
      rw [htr, htr, ← Algebra.trace_eq_of_algEquiv σ]
      congr 1
      have h1 : ((y * H.bar a : 𝓞 E) : E) = (y : E) * σ (a : E) := by rw [← hbar]; rfl
      have h2 : ((x * a : 𝓞 E) : E) = (x : E) * (a : E) := rfl
      rw [h1, h2, map_mul, map_mul, hσσ, hσσ]
      ring
    exact_mod_cast this
  refine ⟨n, C.toNat, b, Matrix.diagonal t, by omega, fun s u => ?_, fun a g => ?_, ?_, fun v hv => ?_⟩
  · by_cases h : s = u
    · rw [h]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  · simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    apply mul_left_cancel₀ hC.ne'
    have h1 : ∀ i, C * (t i * g (b i * a) (b i)) =
        ∑ j, t i * (t j * Algebra.trace ℤ (𝓞 E) (H.bar (b j) * (b i * a))) * g (b j) (b i) := by
      intro i
      have : C * g (b i * a) (b i) = g (C • (b i * a)) (b i) := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [mul_left_comm, this, hexp, map_sum, LinearMap.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have h2 : ∀ j, C * (t j * g (b j) (b j * H.bar a)) =
        ∑ i, t i * (t j * Algebra.trace ℤ (𝓞 E) (H.bar (b j) * (b i * a))) * g (b j) (b i) := by
      intro j
      have : C * g (b j) (b j * H.bar a) = g (b j) (C • (b j * H.bar a)) := by
        rw [map_smul, smul_eq_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [mul_left_comm, this, hexp, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, hsym]
      ring
    rw [Finset.mul_sum, Finset.mul_sum]
    simp only [h1, h2]
    exact Finset.sum_comm
  · simp only [Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hc := StarNormBound.casimir σ e ho fun i => (hdq0 i).ne'
    apply RingOfIntegers.coe_injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_natCast, ← Int.cast_natCast, Int.toNat_of_nonneg hC.le, ← mul_one (C : E), ← hc,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, map_mul]
    change t i • (((H.bar (b i) : 𝓞 E) : E) * (b i : E)) = _
    rw [hbar, ← heb, ← Int.cast_smul_eq_zsmul ℚ, htq, mul_smul, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
  · simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · rw [mul_assoc]; exact mul_nonneg (ht j).le (mul_self_nonneg _)
    · rw [mul_assoc]; exact mul_pos (ht i) (mul_self_pos.2 hi)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrSplitExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SplitExtDVR

theorem exists_complete_dvr_split_ext : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G →
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W) (g : V →+* W),
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ g.IsIntegral ∧ Function.Injective g ∧ IsLocalHom g ∧
      ∃ E : SplitExt (Sp (IsLocalRing.ResidueField W)),
        E.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj ((Over.pullback (spMap g)).obj G)) := by
  intro V _ _ _ _ hcV G _ hG
  haveI := hcV
  let F := AlgebraicClosure (FractionRing V)
  have : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V) (C := F)).2 inferInstance
  have hi : Function.Injective (algebraMap V F) := by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) F]
    exact (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective _ _)
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  obtain ⟨W, hd, hc, hfin, hs⟩ := GlobalTheory.Ex.UnifModel.exists_split V F G hG
  have hW : Function.Injective (algebraMap V W) := fun _ _ h => hi (congrArg (fun z : W => (z : F)) h)
  have : CharZero W := charZero_of_injective_algebraMap hW
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hW
  have hl : IsLocalHom (algebraMap V W) := inferInstance
  have hint : (algebraMap V W).IsIntegral := by
    have : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
    exact Algebra.IsIntegral.isIntegral
  exact ⟨W, inferInstance, inferInstance, hd, inferInstance, algebraMap V W, hc, hint, hW, hl, hs⟩

end GlobalTheory.SplitExtDVR
end

