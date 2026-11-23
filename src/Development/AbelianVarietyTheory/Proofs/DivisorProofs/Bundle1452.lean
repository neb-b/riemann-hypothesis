module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnValuationRings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfForall
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianFormCharPoly
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharInCuspidalSupportOfJacquetSubquotientFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthFilterFinRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import GroundTheory.GlobalFields.Adele.Discrete
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertiaElementRestrictingToFiniteGalois
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaRestrict

variable {Ω : Type} [Field Ω]

theorem lt_one_iff_of_sub_lt (V : ValuationSubring Ω) {x y : Ω} (h : V.valuation (x - y) < 1) :
    V.valuation x < 1 ↔ V.valuation y < 1 := by
  constructor
  · intro hx
    have : y = x - (x - y) := by ring
    rw [this]
    exact Valuation.map_sub_lt _ hx h
  · intro hy
    have : x = y + (x - y) := by ring
    rw [this]
    exact Valuation.map_add_lt _ hy h

theorem comap_valuation_lt_one_iff {L : Type} [Field L] (f : L →+* Ω) (V : ValuationSubring Ω) (z : L) :
    (V.comap f).valuation z < 1 ↔ V.valuation (f z) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero_iff f f.injective]

theorem valuation_eq_one {V : ValuationSubring Ω} {s : Ω} (hs : s ∈ V) (h : ¬ V.valuation s < 1) :
    V.valuation s = 1 :=
  le_antisymm ((V.valuation_le_one_iff s).2 hs) (not_lt.1 h)

end GlobalTheory.InertiaRestrict

namespace GlobalTheory.InertiaRestrict

open GlobalTheory.ProlongConj IntermediateField

theorem exists_den_integral (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [Algebra.IsSeparable K Ω] (V : ValuationSubring Ω) (hR : ∀ r : R, algebraMap R Ω r ∈ V) {x : Ω}
    (hx : x ∈ V) :
    ∃ s t : Ω, IsIntegral R s ∧ IsIntegral R t ∧ V.valuation s = 1 ∧ s * x = t := by
  let M : IntermediateField K Ω := K⟮x⟯
  haveI : FiniteDimensional K M := adjoin.finiteDimensional (Algebra.IsSeparable.isIntegral K x)
  haveI : Algebra.IsSeparable K M := Algebra.isSeparable_tower_bot_of_isSeparable K M Ω
  haveI : IsDedekindDomain (integralClosure R M) := integralClosure.isDedekindDomain R K M
  haveI : IsFractionRing (integralClosure R M) M := integralClosure.isFractionRing_of_finite_extension K M
  haveI : IsScalarTower R M Ω := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K Ω, IsScalarTower.algebraMap_apply R K M]
    rfl
  let A := V.comap (algebraMap M Ω)
  have hint : ∀ s : integralClosure R M, IsIntegral R ((s : M) : Ω) := fun s =>
    (s.2).map (IsScalarTower.toAlgHom R M Ω)
  have hS : ∀ s : integralClosure R M, algebraMap (integralClosure R M) M s ∈ A := fun s =>
    mem_of_isIntegral V hR (hint s)
  obtain ⟨s, t, hs, e⟩ := exists_den (integralClosure R M) A hS (x := ⟨x, mem_adjoin_simple_self K x⟩) hx
  refine ⟨((s : M) : Ω), ((t : M) : Ω), hint s, hint t, valuation_eq_one (hS s) ?_, ?_⟩
  · intro h
    have h2 : A.valuation (algebraMap (integralClosure R M) M s) < 1 :=
      (comap_valuation_lt_one_iff (algebraMap M Ω) V _).2 h
    rw [hs] at h2
    exact lt_irrefl _ h2
  · have := congrArg (algebraMap M Ω) e
    simpa using this

end GlobalTheory.InertiaRestrict

namespace GlobalTheory.InertiaRestrict

open GlobalTheory.ProlongConj

section crit

variable (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [Algebra.IsSeparable K Ω] (V : ValuationSubring Ω) (hR : ∀ r : R, algebraMap R Ω r ∈ V)

include hR in
theorem map_mem_of_lt_one_iff (g : Ω ≃ₐ[K] Ω)
    (hg : ∀ b : Ω, IsIntegral R b → (V.valuation (g b) < 1 ↔ V.valuation b < 1)) {x : Ω} (hx : x ∈ V) :
    g x ∈ V := by
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den_integral R K Ω V hR hx
  have hgs : V.valuation (g s) = 1 :=
    valuation_eq_one (mem_of_isIntegral V hR (hs.map (g.restrictScalars R))) (by
      rw [hg s hs, hs1]; exact lt_irrefl 1)
  have e' : g s * g x = g t := by rw [← map_mul, e]
  have := congrArg V.valuation e'
  rw [Valuation.map_mul, hgs, _root_.one_mul] at this
  rw [← V.valuation_le_one_iff, this, V.valuation_le_one_iff]
  exact mem_of_isIntegral V hR (ht.map (g.restrictScalars R))


include hR in
theorem smul_eq_of_lt_one_iff (g : Ω ≃ₐ[K] Ω)
    (hg : ∀ b : Ω, IsIntegral R b → (V.valuation (g b) < 1 ↔ V.valuation b < 1)) : g • V = V := by
  have hgi : ∀ y : Ω, g (g⁻¹ y) = y := fun y => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hg' : ∀ b : Ω, IsIntegral R b → (V.valuation (g⁻¹ b) < 1 ↔ V.valuation b < 1) := by
    intro b hb
    have := hg (g⁻¹ b) (hb.map ((g⁻¹ : Ω ≃ₐ[K] Ω).restrictScalars R))
    rw [hgi] at this
    exact this.symm
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  constructor
  · intro h
    have := map_mem_of_lt_one_iff R K Ω V hR g hg h
    rwa [hgi] at this
  · intro h
    exact map_mem_of_lt_one_iff R K Ω V hR g⁻¹ hg' h


include hR in
theorem mem_inertia_of_sub_lt_one (g : Ω ≃ₐ[K] Ω)
    (h : ∀ b : Ω, IsIntegral R b → V.valuation (g b - b) < 1) : g ∈ inertia K V := by
  have hg : g • V = V := smul_eq_of_lt_one_iff R K Ω V hR g fun b hb => lt_one_iff_of_sub_lt V (h b hb)
  rw [mem_inertia_iff]
  refine ⟨hg, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den_integral R K Ω V hR hx
  have hgs : V.valuation (g s) = 1 :=
    valuation_eq_one (mem_of_isIntegral V hR (hs.map (g.restrictScalars R))) (by
      rw [lt_one_iff_of_sub_lt V (h s hs), hs1]; exact lt_irrefl 1)
  have key : g s * (g x - x) = (g t - t) - x * (g s - s) := by
    rw [← e, map_mul]; ring
  have := congrArg V.valuation key
  rw [Valuation.map_mul, hgs, _root_.one_mul] at this
  rw [this]
  refine Valuation.map_sub_lt _ (h t ht) ?_
  rw [Valuation.map_mul]
  calc V.valuation x * V.valuation (g s - s) ≤ 1 * V.valuation (g s - s) :=
        mul_le_mul_left ((V.valuation_le_one_iff x).2 hx) _
    _ < 1 := by rw [_root_.one_mul]; exact h s hs

end crit

end GlobalTheory.InertiaRestrict

namespace GlobalTheory.InertiaRestrict

open GlobalTheory.ProlongConj

theorem exists_mem_inertia_eq_on : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsGalois K L] (τ : L ≃ₐ[K] L), τ ∈ inertia K (V.comap (algebraMap L Ω)) →
    ∃ σ ∈ inertia K V, ∀ y : L, σ (y : Ω) = (τ y : Ω) := by
  first
  | exact @_root_.GlobalTheory.IntegralFractionLift.inertia_surjective
  | exact _root_.GlobalTheory.IntegralFractionLift.inertia_surjective
  | (apply _root_.GlobalTheory.IntegralFractionLift.inertia_surjective <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralFractionLift.inertia_surjective <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralFractionLift.inertia_surjective <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralFractionLift.inertia_surjective ..)

end GlobalTheory.InertiaRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralElementCharPolyNonsplit
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ExInertUnit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem eventually_mem_integers (a : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) a ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) a).2

theorem mem_KGL_of_entries (w : Pl E) (g : GLw n w)
    (h1 : ∀ a b, g.val a b ∈ w.adicCompletionIntegers E)
    (h2 : ∀ a b, (g⁻¹).val a b ∈ w.adicCompletionIntegers E) : g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  let O : Subring (w.adicCompletion E) := Ov E w
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => funext fun i => funext fun j => Subtype.ext (congrFun (congrFun h i) j)
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem entries_of_mem_KGL {w : Pl E} {k : GLw n w} (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) (i j : Fin n) :
    k.val i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨a, rfl⟩ := hk
  exact (a.val i j).2

theorem mul_entries {w : Pl E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E) (hB : ∀ i j, B i j ∈ w.adicCompletionIntegers E)
    (i j : Fin n) : (A * B) i j ∈ w.adicCompletionIntegers E := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)


set_option maxHeartbeats 800000 in
theorem local_step (hE : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (M G : Matrix (Fin n) (Fin n) E)
    (hG : IsUnit G) (hGh : cT (IsCMField.complexConj E).toRingEquiv.toRingHom G = G)
    (hMG : cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * G * M = G)
    (hM : ∀ i j, algebraMap E (w.adicCompletion E) (M i j) ∈ w.adicCompletionIntegers E)
    (hG1 : ∀ i j, algebraMap E (w.adicCompletion E) (G i j) ∈ w.adicCompletionIntegers E)
    (hG2 : ∀ i j, algebraMap E (w.adicCompletion E) (G⁻¹ i j) ∈ w.adicCompletionIntegers E) :
    ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = M.charpoly.map (algebraMap E (w.adicCompletion E)) := by
  obtain ⟨-, -, hv, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hE w
  obtain ⟨hconj, ⟨ϖ, q, hU, -⟩, -⟩ := hns hw
  let f := algebraMap E (w.adicCompletion E)
  let c := (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hcT : ∀ A : Matrix (Fin n) (Fin n) E, cT (cj w) (f.mapMatrix A) = f.mapMatrix (cT c A) := by
    intro A
    refine Matrix.ext fun i j => ?_
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, RingHom.mapMatrix_apply]
    exact hconj _
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hGu : IsUnit (f.mapMatrix G) := hG.map _
  have hginv : ((hGu.unit)⁻¹ : GLw n w).val = f.mapMatrix G⁻¹ := by
    have h : f.mapMatrix G⁻¹ * f.mapMatrix G = 1 := by
      rw [← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one]
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
    exact Matrix.inv_eq_left_inv h
  have hgK : hGu.unit ∈ GlobalTheory.LFun.KGL w (n := n) :=
    mem_KGL_of_entries w _ (fun a b => by rw [IsUnit.unit_spec]; exact hG1 a b)
      (fun a b => by rw [hginv]; exact hG2 a b)
  have hgh : cT (cj w) hGu.unit.val = hGu.unit.val := by
    rw [IsUnit.unit_spec, hcT, hGh]
  obtain ⟨k, hk, hkk⟩ := GlobalTheory.LFun.InertChart.exists_norm hU hgK hgh
  have hMu : IsUnit M := by
    have h : (G⁻¹ * cT c M * G) * M = 1 := by
      have h' := hMG
      simp only [Matrix.mul_assoc] at h' ⊢
      rw [h', Matrix.nonsing_inv_mul _ hdet]
    exact (Matrix.isUnit_iff_isUnit_det M).2 (Matrix.isUnit_det_of_left_inverse h)
  have hMwu : IsUnit (f.mapMatrix M) := hMu.map _
  have hmG : cT (cj w) hMwu.unit.val * hGu.unit.val * hMwu.unit.val = hGu.unit.val := by
    rw [IsUnit.unit_spec, IsUnit.unit_spec, hcT, ← map_mul, ← map_mul, hMG]
  have hkinv : cT (cj w) (k⁻¹ : GLw n w).val * cT (cj w) k.val = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  set γ0 : GLw n w := k * hMwu.unit * k⁻¹ with hγ0
  have hγU : cT (cj w) γ0.val * 1 * γ0.val = 1 := by
    calc cT (cj w) γ0.val * 1 * γ0.val
        = cT (cj w) (k⁻¹ : GLw n w).val * (cT (cj w) hMwu.unit.val * (cT (cj w) k.val * k.val) * hMwu.unit.val)
            * (k⁻¹ : GLw n w).val := by
          rw [hγ0, Units.val_mul, Units.val_mul, cT_mul, cT_mul]
          simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = cT (cj w) (k⁻¹ : GLw n w).val * (cT (cj w) k.val * k.val) * (k⁻¹ : GLw n w).val := by
          rw [hkk, hmG]
      _ = 1 := by
          simp only [← Matrix.mul_assoc]
          rw [hkinv, Matrix.one_mul, Units.mul_inv]
  have hγUL : γ0 ∈ UL n w := by
    rw [UL, if_neg hw]
    exact hγU
  refine ⟨⟨γ0, hγUL⟩, ?_, ?_⟩
  · rw [KL, Subgroup.mem_subgroupOf]
    have hinv : cT (cj w) γ0.val = (γ0⁻¹ : GLw n w).val := by
      rw [Matrix.coe_units_inv]
      exact (Matrix.inv_eq_left_inv (by simpa using hγU)).symm
    have hint : ∀ a b, γ0.val a b ∈ w.adicCompletionIntegers E := by
      intro a b
      rw [hγ0, Units.val_mul, Units.val_mul]
      refine mul_entries (mul_entries (entries_of_mem_KGL hk) (fun i j => ?_))
        (entries_of_mem_KGL (inv_mem hk)) a b
      rw [IsUnit.unit_spec]
      exact hM i j
    refine mem_KGL_of_entries w γ0 hint (fun a b => ?_)
    rw [← hinv]
    have h0 := hint b a
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h0 ⊢
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [hv]
    exact h0
  · show (k.val * hMwu.unit.val * (k⁻¹ : GLw n w).val).charpoly = _
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj, IsUnit.unit_spec]
    exact Matrix.charpoly_map M f

end GlobalTheory.ExInertUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfExtTensor
section
noncomputable section

namespace GlobalTheory.ReducedFactor

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nontrivial_of_irr {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : Nontrivial V := by
  have : IsSimpleOrder (Subrepresentation ρ) := h
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext x
  rw [Subsingleton.elim x 0]
  exact iff_of_true (zero_mem _) (zero_mem _)

end General

section Tensor

variable {G H V V' U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup U] [Module ℂ U]

end Tensor

end GlobalTheory.ReducedFactor

namespace GlobalTheory.ReducedFactor

end GlobalTheory.ReducedFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonnegAdelicSchwartzBumpTest
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

open Topology Filter

namespace GlobalTheory.AdelicBumpTest

theorem exists_nonneg_test : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : Set (κ → AF F)), U ∈ nhds 0 →
    ∃ Φ ∈ schA F κ, Continuous Φ ∧ (∀ x, Φ x ≠ 0 → x ∈ U) ∧ (∀ x, (Φ x).im = 0 ∧ 0 ≤ (Φ x).re) ∧ Φ 0 = 1 := by
  intro F _ _ κ _ U hU
  classical
  let e' : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
    fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  have he' : Continuous e' := continuous_pi fun i =>
    ((GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp ((continuous_apply i).comp continuous_fst)).prodMk
      ((continuous_apply i).comp continuous_snd)
  have he'0 : e' (0, 0) = 0 := by
    funext i
    refine Prod.ext ?_ rfl
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0 = 0
    exact map_zero _
  have hpre : e' ⁻¹' U ∈ 𝓝 ((0 : κ → mixedEmbedding.mixedSpace F), (0 : κ → FiniteAdeleRing (𝓞 F) F)) :=
    he'.continuousAt.preimage_mem_nhds (by rw [he'0]; exact hU)
  obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV₁

  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ y, f y = ((b y : ℝ) : ℂ) := fun y => rfl

  obtain ⟨L, hLo, hLc, hL⟩ : ∃ L : AddSubgroup (FiniteAdeleRing (𝓞 F) F), IsOpen (L : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact (L : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i, u i ∈ L) → u ∈ V₂ := by
    let q := Fintype.equivFin κ
    have hc : Continuous fun (u : Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) (i : κ) => u (q i) :=
      continuous_pi fun i => continuous_apply _
    have hV' : (fun (u : Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) (i : κ) => u (q i)) ⁻¹' V₂ ∈
        𝓝 (0 : Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) :=
      hc.continuousAt.preimage_mem_nhds hV₂
    obtain ⟨L, hLo, hLc, hL⟩ := GlobalTheory.SWQ.FinAnnih.basis_nhds (F := F) _ hV'
    refine ⟨L, hLo, hLc, fun u hu => ?_⟩
    have := hL (fun l => u (q.symm l)) fun l => hu _
    simpa using this
  let S : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.pi Set.univ fun _ => (L : Set (FiniteAdeleRing (𝓞 F) F))
  have hSo : IsOpen S := isOpen_set_pi Set.finite_univ fun _ _ => hLo
  have hSc : IsClosed S := isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen L hLo
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := S.indicator 1
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨?_, ?_⟩
    · refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
      by_cases hx : x ∈ S
      · exact ⟨S, hSo, hx, fun y hy => by simp only [g, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]⟩
      · exact ⟨Sᶜ, hSc.isOpen_compl, hx, fun y hy => by simp only [g, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
    · exact HasCompactSupport.intro (isCompact_univ_pi fun _ => hLc) fun x hx => Set.indicator_of_notMem hx _
  refine ⟨pureA F f g, Submodule.subset_span ⟨f, g, hg, rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact (f.continuous.comp (continuous_pi fun i => (GlobalTheory.Core.Rk.RapidInt.continuous_toMixed F).comp
      (continuous_fst.comp (continuous_apply i)))).mul
      (hg.1.continuous.comp (continuous_pi fun i => continuous_snd.comp (continuous_apply i)))
  · intro x hx
    have hx1 : f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ≠ 0 := left_ne_zero_of_mul hx
    have hx2 : g (fun i => (x i).2) ≠ 0 := right_ne_zero_of_mul hx
    have hb : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ∈ V₁ := by
      refine hball ?_
      rw [← b.support_eq]
      intro h0
      apply hx1
      rw [hf, h0]; simp
    have hS : (fun i => (x i).2) ∈ S := by
      by_contra h
      exact hx2 (Set.indicator_of_notMem h _)
    have hmem := hsub (Set.mk_mem_prod hb (hL _ fun i => hS i (Set.mem_univ i)))
    have hxe : e' ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1), fun i => (x i).2) = x := by
      funext i
      refine Prod.ext ?_ rfl
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _
    rw [← hxe]
    exact hmem
  · intro x
    show (f _ * g _).im = 0 ∧ 0 ≤ (f _ * g _).re
    rw [hf]
    by_cases h : (fun i => (x i).2) ∈ S
    · simp only [g, Set.indicator_of_mem h, Pi.one_apply, mul_one, Complex.ofReal_im, Complex.ofReal_re, true_and]
      exact b.nonneg
    · simp only [g, Set.indicator_of_notMem h, mul_zero, Complex.zero_im, Complex.zero_re, le_refl, and_self]
  · show f _ * g _ = 1
    have h0 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
      funext i
      exact map_zero _
    have hS0 : (fun i => ((0 : κ → AdeleRing (𝓞 F) F) i).2) ∈ S := fun i _ => L.zero_mem
    rw [h0, hf, b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hε).le)]
    simp only [g, Set.indicator_of_mem hS0, Pi.one_apply, Complex.ofReal_one, mul_one]

end GlobalTheory.AdelicBumpTest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionAdelesStableRangeOne
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.StableRange

theorem adeles_tensor_stableRange_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a b : AF F ⊗[F] E),
    IsCoprime a b → ∃ t : AF F ⊗[F] E, IsUnit (a + t * b) := by
  intro F E _ _ _ _ _ a b h
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Algebra.IsIntegral (AF F) (AF F ⊗[F] E) := Algebra.IsIntegral.of_finite _ _
  exact stable_adele F a b h

end GlobalTheory.StableRange
end

