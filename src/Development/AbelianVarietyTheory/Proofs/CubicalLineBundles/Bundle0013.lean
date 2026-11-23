module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PowObjSmoothOfRelativeDimensionMul
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurvesOfWeierstrassCurves
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors

namespace GlobalTheory

namespace CMData

variable {K : Type} [Field K] [NumberField K]

theorem exists_periodPair (h2 : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ¬ ComplexEmbedding.IsReal σ) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ x ∈ I.1, z = σ x := by
  obtain ⟨b, hspan⟩ : ∃ b : Module.Basis (Fin 2) ℚ K, ∀ x : K, x ∈ I.1 ↔ x ∈ Submodule.span ℤ (Set.range b) := by
    have hcard := (Module.finrank_eq_card_basis (basisOfFractionalIdeal K I)).symm.trans h2
    refine ⟨(basisOfFractionalIdeal K I).reindex (Fintype.equivFinOfCardEq hcard), fun x => ?_⟩
    rw [Module.Basis.coe_reindex, EquivLike.range_comp, mem_span_basisOfFractionalIdeal]
    exact Iff.rfl
  obtain ⟨a, ha⟩ := CMLattice.exists_im_ne_zero σ hσ
  have hX : (σ (b 0) * starRingEnd ℂ (σ (b 1))).im ≠ 0 := by
    intro h0
    have e := CMLattice.im_mul_conj_eq_det σ b ![1, (a : K)]
    rw [h0, mul_zero] at e
    apply ha
    simpa using e
  have e2 : (σ (b 0) * starRingEnd ℂ (σ (b 1))).im =
      (σ (b 0)).im * (σ (b 1)).re - (σ (b 0)).re * (σ (b 1)).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hind : LinearIndependent ℝ ![σ (b 0), σ (b 1)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      have e1 := congrArg (fun w => (starRingEnd ℂ (σ (b 0)) * w).im) hst
      simp only [Complex.real_smul, mul_add, Complex.add_im, Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, mul_zero,
        Complex.zero_im] at e1
      have hprod : t * ((σ (b 0)).im * (σ (b 1)).re - (σ (b 0)).re * (σ (b 1)).im) = 0 := by
        linear_combination -e1
      rcases mul_eq_zero.mp hprod with h | h
      · exact h
      · exact absurd (e2.trans h) hX
    subst ht
    have h0 : σ (b 0) ≠ 0 := by
      intro h
      apply hX
      rw [h, zero_mul, Complex.zero_im]
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right h0, rfl⟩
  refine ⟨⟨σ (b 0), σ (b 1), hind⟩, fun z => ?_⟩
  show z ∈ Submodule.span ℤ {σ (b 0), σ (b 1)} ↔ _
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m • b 0 + n • b 1, ?_, by simp⟩
    rw [hspan]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · rintro ⟨x, hx, rfl⟩
    rw [hspan, Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, rfl⟩ := hx
    refine ⟨c 0, c 1, ?_⟩
    simp [Fin.sum_univ_two]

theorem exists_mul_of_invariants {L L' : PeriodPair} {c₄ Δ : ℂ}
    (h : c₄ ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = 1728 * L.g₂ ^ 3 * Δ)
    (h₄ : c₄ = 12 * L'.g₂) (hΔ : Δ = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ L'.lattice ↔ ∃ w ∈ L.lattice, z = c * w := by
  subst h₄ hΔ
  exact (lattice_determined_by_invariants L L').2 (by linear_combination (-1 / 1728 : ℂ) * h)

theorem exists_field (h2 : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ¬ ComplexEmbedding.IsReal σ) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ a, σ a ∈ M) ∧
      ∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∃ W : WeierstrassCurve (𝓞 M), IsUnit W.Δ ∧
        ∀ L' : PeriodPair,
          ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) W.c₄ = 12 * L'.g₂ →
          ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) W.Δ = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 →
          ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ L'.lattice ↔ ∃ x ∈ I.1, z = c * σ x := by
  obtain ⟨M, hfin, hσM, hF⟩ := exists_field_cm_curves_unit_discriminant K h2 σ hσ
  refine ⟨M, hfin, hσM, fun I => ?_⟩
  obtain ⟨L, hL⟩ := exists_periodPair h2 σ hσ I
  have hstab : ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice := by
    intro a z hz
    obtain ⟨x, hx, rfl⟩ := (hL z).1 hz
    refine (hL _).2 ⟨(a : K) * x, ?_, by rw [map_mul]⟩
    have hax := Submodule.smul_mem (I.1 : Submodule (𝓞 K) K) a hx
    simpa [Algebra.smul_def] using hax
  obtain ⟨W, hW, hj⟩ := hF L hstab
  refine ⟨W, hW, fun L' h4 hD => ?_⟩
  obtain ⟨c, hc, hc'⟩ := exists_mul_of_invariants hj h4 hD
  refine ⟨c, hc, fun z => ?_⟩
  rw [hc' z]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (hL w).1 hw
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨σ x, (hL _).2 ⟨x, hx, rfl⟩, rfl⟩

theorem mem_inv_iff (𝔟 : (Ideal (𝓞 K))⁰) (x : K) :
    x ∈ ((FractionalIdeal.mk0 K 𝔟)⁻¹).1 ↔ ∀ b ∈ (𝔟 : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K)) := by
  have hne : ((FractionalIdeal.mk0 K 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    Units.ne_zero _
  rw [Units.val_inv_eq_inv_val, FractionalIdeal.mem_inv_iff hne, FractionalIdeal.coe_mk0]
  constructor
  · intro h b hb
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩))
    have hint : IsIntegral ℤ (algebraMap (𝓞 K) K a) := RingOfIntegers.isIntegral_coe a
    rw [ha] at hint
    exact hint
  · intro h y hy
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨_, h b hb⟩, rfl⟩

end CMData


open CMData in
theorem exists_cm_curves_of_weierstrass_curves :
    (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) ∧ ∀ s : R →+* ℂ, s W.c₄ = 12 * (Lf s).g₂ ∧ s W.c₆ = 216 * (Lf s).g₃ ∧ s W.Δ = (Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) → ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (κ : K →+* M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞 K) → Out.PolAV (Sp (𝓞 M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+* ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀ s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) ∧ ∃ β : ClassGroup (𝓞 K) → ℂ, (∀ C, β C ≠ 0) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → ∀ z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice, β C * σ₀ x * z ∈ (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), ∀ z ∈ (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice, (β C)⁻¹ * σ₀ (y : K) * z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice := by
  intro H K _ _ h2 σ₀ hσ₀ 𝔟
  obtain ⟨M, hfin, hσM, hF⟩ := CMData.exists_field h2 σ₀ hσ₀
  have hNF : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨W₀, hW₀, hF₀⟩ := hF 1
  obtain ⟨P, v, L₀, hP, hP₀⟩ := H (𝓞 M) W₀ hW₀
  obtain ⟨c₀, hc₀, hc₀L⟩ := hF₀ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)))
    (hP₀ _).1 (hP₀ _).2.2
  have hL0 : ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔
      ∃ a : 𝓞 K, z = c₀ * σ₀ (a : K) := by
    intro z
    rw [hc₀L z, Units.val_one]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : K), (FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩, rfl⟩
  choose W hW hWL using fun C : ClassGroup (𝓞 K) => hF (FractionalIdeal.mk0 K (𝔟 C))⁻¹
  choose Q t L hQ hQL using fun C => H (𝓞 M) (W C) (hW C)
  choose c hc hcL using fun C => hWL C (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)))
    (hQL C _).1 (hQL C _).2.2
  refine ⟨M, hNF, σ₀.codRestrict M hσM, P, v, L₀, Q, t, L, fun C => (hW C).unit, fun a => rfl, hP, hQ,
    fun C s => ?_, ⟨c₀, hc₀, hL0⟩, fun C => c C / c₀, fun C => div_ne_zero (hc C) hc₀, ?_, ?_⟩
  · rw [IsUnit.unit_spec]
    exact ((hQL C s).2.2).symm
  · intro C x hx z hz
    obtain ⟨a, rfl⟩ := (hL0 z).1 hz
    have hxI := (CMData.mem_inv_iff (𝔟 C) x).2 hx
    rw [hcL C]
    refine ⟨x * (a : K), ?_, ?_⟩
    · have hax := Submodule.smul_mem (((FractionalIdeal.mk0 K (𝔟 C))⁻¹).1 : Submodule (𝓞 K) K) a hxI
      simpa [Algebra.smul_def, mul_comm] using hax
    · rw [map_mul]
      field_simp
  · intro C y hy z hz
    obtain ⟨x', hx', rfl⟩ := (hcL C z).1 hz
    have hint := (CMData.mem_inv_iff (𝔟 C) x').1 hx' y hy
    rw [hL0]
    refine ⟨⟨x' * (y : K), hint⟩, ?_⟩
    show _ = c₀ * σ₀ (x' * (y : K))
    have hcC := hc C
    rw [map_mul]
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodModelOfIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory

namespace IsogenyModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
private theorem over_pullback_map_left_fst {S S' : Scheme} (φ : S' ⟶ S) (Ga X : Over S) (io : Ga ⟶ X) :
    ((Over.pullback φ).map io).left ≫ pullback.fst X.hom φ = pullback.fst _ _ ≫ io.left :=
  pullback.lift_fst _ _ _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
private theorem over_pullback_map_left_snd {S S' : Scheme} (φ : S' ⟶ S) (Ga X : Over S) (io : Ga ⟶ X) :
    ((Over.pullback φ).map io).left ≫ pullback.snd X.hom φ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
theorem _root_.GlobalTheory.IsogenyModel.exists_flat_closure (T K : Type) [CommRing T] [IsDedekindDomain T] [Field K] [Algebra T K]
    [IsFractionRing T K] (X : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp T)) (Z : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K))
    (i : Z ⟶ (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))).obj X) (hi : IsClosedImmersion i.left) :
    ∃ (Ga : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp T)) (io : Ga ⟶ X)
      (e : (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left ∧
      Flat Ga.hom ∧ e.hom ≫ i = (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))).map io := by
  haveI := hi
  haveI : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := _root_.GlobalTheory.flat_specMap_localization (nonZeroDivisors T) K
  haveI : Mono (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := _root_.GlobalTheory.mono_specMap_localization (nonZeroDivisors T) K
  set u := pullback.fst X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) with hu
  set j := i.left ≫ u with hj
  have hjs : Z.hom ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) = j ≫ X.hom := by
    rw [hj, Category.assoc, hu, pullback.condition, ← Category.assoc]
    congr 1
    exact (Over.w i).symm
  haveI : QuasiCompact (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := by dsimp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]; infer_instance
  haveI : QuasiCompact j := by rw [hj, hu]; infer_instance
  have hflat : Flat (j.imageι ≫ X.hom) :=
    _root_.GlobalTheory.flat_image_of_over_fractionField j X.hom Z.hom hjs
  have hA : IsPullback i.left j.toImage u j.imageι :=
    _root_.GlobalTheory.isPullback_toImage_of_isClosedImmersion j i.left u rfl
  have hB : IsPullback u (pullback.snd X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))) X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := IsPullback.of_hasPullback X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))
  have hC : IsPullback j.toImage (i.left ≫ pullback.snd X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))) (j.imageι ≫ X.hom) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) :=
    IsPullback.paste_vert hA.flip hB
  have hZ : i.left ≫ pullback.snd X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) = Z.hom := Over.w i
  rw [hZ] at hC
  refine ⟨Over.mk (j.imageι ≫ X.hom), Over.homMk j.imageι rfl,
    Over.isoMk hC.isoPullback.symm (by simp), (show IsClosedImmersion j.imageι from inferInstance), hflat, ?_⟩
  ext1
  simp only [Over.comp_left, Over.isoMk_hom_left, Iso.symm_hom]
  rw [Iso.inv_comp_eq]
  apply pullback.hom_ext
  · rw [Category.assoc, over_pullback_map_left_fst]
    erw [hC.isoPullback_hom_fst_assoc]
    simp [hj, hu]
  · rw [Category.assoc, over_pullback_map_left_snd]
    erw [hC.isoPullback_hom_snd]
    exact hZ

variable {S : Scheme.{0}}


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.IsogenyModel.exists_kernel {G B : Over S} [GrpObj G] [GrpObj B] [IsSeparated B.hom] (f : G ⟶ B)
    [IsMonHom f] [IsFinite f.left] :
    ∃ (Z : Over S) (_ : GrpObj Z) (i : Z ⟶ G), IsMonHom i ∧ IsClosedImmersion i.left ∧
      IsFinite Z.hom ∧ IsPullback i (toUnit Z) f η[B] := by
  have hP := IsPullback.of_hasPullback f η[B]
  have hL := IsPullback.map (Over.forget S) hP
  haveI : IsClosedImmersion η[B].left :=
    _root_.GlobalTheory.Retract.isClosedImmersion_section (f := 𝟙 S) (r := B.hom) (Over.w η[B])
      (Category.comp_id _)
  haveI : Mono η[B] := ⟨fun a b _ => toUnit_unique a b⟩
  set i := pullback.fst f η[B] with hi
  have key : ∀ {X : Over S} (a : X ⟶ pullback f η[B]), (a ≫ i) ≫ f = 1 := fun a => by
    rw [Category.assoc, hi, pullback.condition, ← Category.assoc,
      toUnit_unique (a ≫ pullback.snd f η[B]) (toUnit _), ← Hom.one_def]
  have key1 : i ≫ f = 1 := by simpa using key (𝟙 _)
  have hinv : ∀ {X : Over S} (a : X ⟶ G), a⁻¹ ≫ f = (a ≫ f)⁻¹ := by
    intro X a
    exact GrpObj.inv_comp a f
  obtain ⟨inst, hmon⟩ := _root_.GlobalTheory.exists_grpObj_of_mono i
    (pullback.lift η[G] (𝟙 _) (by simp))
    (pullback.lift ((fst _ _ ≫ i) * (snd _ _ ≫ i)) (toUnit _)
      (by rw [mul_comp, key, key, _root_.mul_one, Hom.one_def]))
    (pullback.lift i⁻¹ (toUnit _) (by rw [hinv, key1, _root_.inv_one, Hom.one_def]))
    (pullback.lift_fst _ _ _)
    (by rw [pullback.lift_fst, Hom.mul_def, lift_fst_comp_snd_comp])
    (by rw [pullback.lift_fst, Hom.inv_def])
  refine ⟨pullback f η[B], inst, i, hmon, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hL.flip (show IsClosedImmersion η[B].left from inferInstance)
  · have hw := Over.w (pullback.snd f η[B])
    have : IsFinite (pullback.snd f η[B]).left :=
      MorphismProperty.of_isPullback (P := @IsFinite) hL (show IsFinite f.left from inferInstance)
    rw [← hw]
    simpa using this
  · simpa [toUnit_unique (pullback.snd f η[B]) (toUnit _)] using hP


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.IsogenyModel.exists_iso_of_same_kernel {G A B Z : Over S} [GrpObj G] [GrpObj A] [GrpObj B]
    (q : G ⟶ A) (f : G ⟶ B) (i : Z ⟶ G) [IsMonHom q] [IsMonHom f] [Flat q.left]
    [Surjective q.left] [QuasiCompact q.left] [Surjective f.left] [IsProper A.hom]
    [IsSeparated B.hom] [IsReduced B.left] (hq : IsPullback i (toUnit Z) q η[A])
    (hf : IsPullback i (toUnit Z) f η[B]) :
    ∃ e : A ≅ B, IsMonHom e.hom ∧ q ≫ e.hom = f := by
  obtain ⟨β, hβ, hqβ⟩ := _root_.GlobalTheory.FlatQuotient.exists_desc q i f hq hf.w
  have htriv : ∀ {X : Over S} (x : X ⟶ A), x ≫ β = 1 → x = 1 := by
    intro X x hx
    have hP := IsPullback.of_hasPullback x q
    have hL := IsPullback.map (Over.forget S) hP
    haveI : Flat (pullback.fst x q).left :=
      MorphismProperty.of_isPullback (P := @Flat) hL.flip (show Flat q.left from inferInstance)
    haveI : Surjective (pullback.fst x q).left :=
      MorphismProperty.of_isPullback (P := @Surjective) hL.flip
        (show Surjective q.left from inferInstance)
    haveI : Epi (pullback.fst x q) := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective _
    have hg : pullback.snd x q ≫ f = toUnit _ ≫ η[B] := by
      rw [← hqβ, ← Category.assoc, ← pullback.condition, Category.assoc, hx, Hom.one_def,
        ← Category.assoc, toUnit_unique (pullback.fst x q ≫ toUnit X) (toUnit _)]
    have hgq : pullback.snd x q ≫ q = toUnit _ ≫ η[A] := by
      rw [← hf.lift_fst _ _ hg, Category.assoc, hq.w, ← Category.assoc,
        toUnit_unique (hf.lift _ _ hg ≫ toUnit Z) (toUnit _)]
    rw [← cancel_epi (pullback.fst x q), pullback.condition, hgq, Hom.one_def, ← Category.assoc,
      toUnit_unique (pullback.fst x q ≫ toUnit X) (toUnit _)]
  haveI : Mono β := ⟨fun a b hab => by
    have h1 : (a * b⁻¹) ≫ β = 1 := by
      rw [mul_comp, GrpObj.inv_comp, hab, _root_.mul_inv_cancel]
    have h2 := htriv _ h1
    exact (mul_inv_eq_one.mp h2)⟩
  haveI : Surjective (q.left ≫ β.left) := by
    rw [← Over.comp_left, hqβ]; infer_instance
  haveI : Surjective β.left := Surjective.of_comp q.left β.left
  haveI : IsProper (β.left ≫ B.hom) := by rw [Over.w β]; infer_instance
  haveI : IsProper β.left := IsProper.of_comp β.left B.hom
  haveI : IsClosedImmersion β.left :=
    (IsClosedImmersion.iff_isProper_and_mono (f := β.left)).mpr ⟨inferInstance, inferInstance⟩
  haveI : IsIso β.left := isIso_of_isClosedImmersion_of_surjective β.left
  refine ⟨Over.isoMk (asIso β.left) (Over.w β), ?_, ?_⟩
  · have : (Over.isoMk (asIso β.left) (Over.w β)).hom = β := by ext1; rfl
    rw [this]; exact hβ
  · have : (Over.isoMk (asIso β.left) (Over.w β)).hom = β := by ext1; rfl
    rw [this]; exact hqβ

end IsogenyModel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemePower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CM

theorem exists_polAV_isPowGrp : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (n : ℕ), ∃ (Q : Out.PolAV (Sp R)) (_ : Out.IsPowGrp Q.A P.A n), Q.g = n * P.g := by
  intro R _ P n
  have := P.isAb.comm
  obtain ⟨hL, hS, hr⟩ := BoxPower.boxPower_basic R P n
  obtain ⟨rig, hrig⟩ := P.rigid
  exact ⟨{ A := Out.powObj P.A n
           isAb := (PowGrp.powers _ _ _ n (Out.powIsPowGrp P.A n)).2.2.2.1 P.isAb
           g := n * P.g
           smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ n P.smoothDim
           L := Out.boxLB P.L (Out.powPr P.A (n := n))
           isLB := hL
           rigid := ⟨_, hr rig hrig⟩
           sym := hS
           ample := relAmple_powObj_boxLB R P n
           ktriv := kTriv_boxLB _ (Out.powObj P.A n) P.A n (Out.powIsPowGrp P.A n) P.L P.isLB P.ktriv },
    Out.powIsPowGrp P.A n, rfl⟩

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.AnyUnif

theorem injective_of_ker_le_discrete {g g' : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (h : ∀ z, F z = 0 → z ∈ Λ) : Function.Injective F := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  let c : ℂ → Λ := fun t => ⟨t • z, h _ (by rw [map_smul, hz, smul_zero])⟩
  have hc : Continuous c := Continuous.subtype_mk (by fun_prop) _
  have e : c 1 = c 0 := (IsLocallyConstant.iff_continuous c).2 hc |>.apply_eq_of_preconnectedSpace 1 0
  simpa [c] using congrArg Subtype.val e

theorem lbIso_pow_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) :
    LBIso (lbPow (L.pull (𝟙 X)) n) (lbPow L n) := by
  obtain ⟨w, hw⟩ : LBIso (L.pull (𝟙 X)) L :=
    LBIso.chartPull (chartPullPull L (𝟙 X) (𝟙 X) rfl) (chartPullId L) (PolBaseChange.lbIso_refl hL)
  exact ⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩

theorem tangent_and_unimodular : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g),
    (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
    ∀ (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
      ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧
        Function.Bijective Ef := by
  intro hU P u
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u', Hm', χ', Ef', hA', -, h1, h2, -, -, hE, hB, -⟩ := hU P rig hrig
  obtain ⟨F, hF₀, -⟩ := HomLinear.exists_linear_of_isMonHom P.A P.A P.isAb P.isAb P.L P.L P.g P.g u u' h1 h2
    (𝟙 P.A) inferInstance
  have hF : ∀ z, u'.ex (F z) = u.ex z := fun z => (hF₀ z).trans (Category.comp_id _)
  have hΛ : ∀ z, F z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => by rw [← u'.ker, hF, u.ker]
  haveI := u.discrete
  have hinj := injective_of_ker_le_discrete u.Λ F fun z hz => (hΛ z).1 (hz ▸ u'.Λ.zero_mem)
  let e := LinearEquiv.ofInjectiveEndo F hinj
  have he : ∀ z, e z = F z := fun _ => rfl
  have hd : ∀ w v, IsTangent v → (u.IsDiff w v ↔ u'.IsDiff (e w) v) := fun w v hv => by
    constructor
    · intro h
      simpa [he] using HomLinear.isDiff_comp u u' (𝟙 P.A) F hF₀ hv h
    · intro h
      simpa using HomLinear.isDiff_comp u' u (𝟙 P.A) e.symm.toLinearMap
        (fun z => by rw [Category.comp_id, ← hF, ← he]; simp) hv h
  refine ⟨fun v hv => ?_, fun w => ?_, fun Hm χ hA => ?_⟩
  · obtain ⟨w, hw, hu⟩ := h1 v hv
    refine ⟨e.symm w, (hd _ v hv).2 (by simpa using hw), fun w' hw' => ?_⟩
    rw [← hu _ ((hd _ v hv).1 hw'), e.symm_apply_apply]
  · obtain ⟨v, ⟨hv, hw⟩, hu⟩ := h2 (e w)
    exact ⟨v, ⟨hv, (hd w v hv).2 hw⟩, fun v' hv' => hu v' ⟨hv'.1, (hd w v' hv'.1).1 hv'.2⟩⟩
  · have hH := hermForm_pull_eq_of_lbIso_pow P.A P.A P.L P.L P.isLB P.isLB P.g P.g u u' Hm χ Hm' χ' hA hA'
      (𝟙 P.A) F hF₀ 1 1 (lbIso_pow_pull_id P.isLB 1)
    simp only [Nat.cast_one, _root_.one_mul] at hH
    let l : u.Λ ≃ₗ[ℤ] u'.Λ :=
      { toFun := fun a => ⟨e a, (hΛ a).2 a.2⟩
        invFun := fun b => ⟨e.symm b, (hΛ _).1 (by rw [← he, e.apply_symm_apply]; exact b.2)⟩
        map_add' := fun a b => Subtype.ext (map_add e _ _)
        map_smul' := fun n a => Subtype.ext (map_zsmul e n _)
        left_inv := fun a => Subtype.ext (e.symm_apply_apply _)
        right_inv := fun b => Subtype.ext (e.apply_symm_apply _) }
    refine ⟨Ef'.comp l.toLinearMap l.toLinearMap, fun a b => ?_, ?_⟩
    · rw [← hH]
      exact hE (l a) (l b)
    · exact l.dualMap.bijective.comp (hB.comp l.bijective)

end GlobalTheory.AnyUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ReEqZeroAndImSq
section
namespace GlobalTheory.SquareEqNegReIm

theorem re_im_of_sq_eq_neg {z : ℂ} {c : ℝ} (hc : 0 ≤ c) (hz : z ^ 2 = -(c : ℂ)) :
    z.re = 0 ∧ z.im ^ 2 = c := by
  have hs : ((Real.sqrt c : ℝ) : ℂ) ^ 2 = (c : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hc]
  have h : z ^ 2 = (((Real.sqrt c : ℝ) : ℂ) * Complex.I) ^ 2 := by
    rw [mul_pow, hs, Complex.I_sq, hz]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · rw [h]; simp [Real.sq_sqrt hc]
  · rw [h]; simp [Real.sq_sqrt hc]

theorem re_eq_zero_and_im_sq {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    H.rt0.re = (0 : ℝ) ∧ H.rt0.im ^ (2 : ℕ) = (H.d : ℝ) := by
  refine re_im_of_sq_eq_neg (by positivity) ?_
  rw [H.sqrt_neg_disc_sq]; simp

end GlobalTheory.SquareEqNegReIm
end

