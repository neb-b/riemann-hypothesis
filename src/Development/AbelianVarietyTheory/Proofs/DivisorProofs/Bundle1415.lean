module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanish
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1390
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0758

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmCurveGoodOutsidePrime
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField

namespace GlobalTheory.CMModel

theorem shortTwist_Δ (d a b : ℂ) :
    (shortTwist d a b).Δ = d ^ 6 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ := by
  simp only [shortTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem shortTwist_c₄ (d a b : ℂ) :
    (shortTwist d a b).c₄ = d ^ 2 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).c₄ := by
  simp only [shortTwist, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem shortTwist_j {d a b : ℂ} (hd : d ≠ 0) [(shortTwist d a b).IsElliptic]
    [(⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).IsElliptic] :
    (shortTwist d a b).j = (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).j := by
  have h0 : (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ ≠ 0 :=
    (WeierstrassCurve.IsElliptic.isUnit (W := (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ))).ne_zero
  simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    shortTwist_Δ, shortTwist_c₄]
  field_simp

theorem j_congr_of_eq {W W' : WeierstrassCurve ℂ} (h : W = W') [W.IsElliptic] [W'.IsElliptic] :
    W.j = W'.j := by
  subst h; rfl

end GlobalTheory.CMModel

namespace GlobalTheory.Published

theorem cmCurveGoodOutsidePrime : CMCurveGoodOutsidePrimeSt := by
  intro p hp h4 h3
  obtain ⟨L₀, hL₀⟩ := exists_isIntegersLattice (p := p) hp.pos
  obtain ⟨-, -, hms⟩ := _root_.GlobalTheory.CMModel.integersLattice_invariants_ne_zero p L₀ hp h3 hL₀
  have him : (sqrtNegNat p).im ≠ 0 := by
    simp only [sqrtNegNat, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, mul_zero, add_zero]
    exact (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)).ne'
  have hjint := _root_.GlobalTheory.CMModel.LatticeJInt.main L₀ (sqrtNegNat p) hms him
  have hjQ : IsIntegral ℚ (latticeCurve L₀).j := hjint.tower_top
  haveI : FiniteDimensional ℚ ℚ⟮(latticeCurve L₀).j⟯ := IntermediateField.adjoin.finiteDimensional hjQ
  haveI hNF : NumberField ℚ⟮(latticeCurve L₀).j⟯ := NumberField.of_module_finite ℚ _
  obtain ⟨L₁, t₁, hD₁, hj₁⟩ := _root_.GlobalTheory.CMModel.exists_datum_of_isIntegersLattice p L₀ hp h4 h3 hL₀
  obtain ⟨L, t, hD, hj, hsq⟩ := _root_.GlobalTheory.CMModel.exists_datum_sqProd_mem p _ L₁ t₁ hp h4 h3 hD₁
  set F := ℚ⟮(latticeCurve L₀).j⟯ with hFdef
  have hg₂ : -L.g₂ / 4 ∈ F := div_mem (neg_mem hD.g₂_mem) (ofNat_mem _ 4)
  have hg₃ : -L.g₃ / 4 ∈ F := div_mem (neg_mem hD.g₃_mem) (ofNat_mem _ 4)
  let dF : F := if p % 8 = 3 then 1 else -(p : F)
  let dC : ℂ := if p % 8 = 3 then 1 else -(p : ℂ)
  have hdC : ((dF : F) : ℂ) = dC := by
    simp only [dF, dC]; split_ifs <;> simp
  have hdC0 : dC ≠ 0 := by
    simp only [dC]; split_ifs
    · exact one_ne_zero
    · exact neg_ne_zero.mpr (by exact_mod_cast hp.ne_zero)
  let A : WeierstrassCurve F := shortTwist dF ⟨-L.g₂ / 4, hg₂⟩ ⟨-L.g₃ / 4, hg₃⟩
  have hmap : A.map (algebraMap F ℂ) = shortTwist dC (-L.g₂ / 4) (-L.g₃ / 4) := by
    rw [← hdC]
    ext <;> simp [A, shortTwist, WeierstrassCurve.map]
  have hlat : (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ) = latticeCurve L := rfl
  have hΔA : A.Δ ≠ 0 := by
    intro h0
    have := congrArg (algebraMap F ℂ) h0
    rw [← WeierstrassCurve.map_Δ, hmap, shortTwist_Δ, hlat, map_zero] at this
    exact mul_ne_zero (pow_ne_zero _ hdC0) (latticeCurve_Δ_ne_zero L) this
  haveI hE : A.IsElliptic := ⟨Ne.isUnit hΔA⟩
  have hmin : HasMinimalDiscriminant A (-(p : F) ^ 3) := by
    intro w
    obtain ⟨V, hV⟩ := _root_.GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime F w
    have hloc := _root_.GlobalTheory.CMModel.twist_modelAt_all p F L t hp h4 h3 hD hsq V
    have hD0 : (-(p : F) ^ 3) ≠ 0 :=
      neg_ne_zero.mpr (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
    have hmod : ModelAt V F (A.map (algebraMap F ℂ)) ((-(p : F) ^ 3 : F) : ℂ) := by
      rw [hmap]
      convert hloc using 1
    obtain ⟨C, u, hI, hΔ⟩ := GlobalTheory.T.exists_variableChange_isIntegral_of_modelAt F w V A _ hV hD0 hmod
    have hram := _root_.GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j p L₀ w hp hL₀
    exact ⟨C, u, _root_.GlobalTheory.CMModel.isMinimal_of_discr_eq_unit_mul_neg_cube p F w (C • A) u hram hI hΔ, hΔ⟩
  refine ⟨F, hNF, A, ⟨hNF, hE, L₀, hL₀, rfl, ?_, hmin.hasGoodReductionOutside⟩, hmin⟩
  have e1 : ((A.j : F) : ℂ) = (A.map (algebraMap F ℂ)).j := (A.map_j (algebraMap F ℂ)).symm
  haveI : (shortTwist dC (-L.g₂ / 4) (-L.g₃ / 4)).IsElliptic := hmap ▸ inferInstance
  haveI : (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ).IsElliptic :=
    inferInstanceAs (latticeCurve L).IsElliptic
  rw [e1, j_congr_of_eq hmap, shortTwist_j hdC0, j_congr_of_eq hlat, hj, hj₁]

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemStandardLeviWittFrame
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.Cusp.ConjLevi

variable {D : D7} {V : HSp D}

theorem ratAct_mul_apply (a b : GF V) (v : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V (a * b) v = GlobalTheory.Cusp.ratAct D.sp.cm V a (GlobalTheory.Cusp.ratAct D.sp.cm V b v) := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (a * b).1.1 = a.1.1 * b.1.1 from rfl, Matrix.toLin_mul V.frame V.frame V.frame]
  rfl

theorem ratAct_one_apply (v : V.V) : GlobalTheory.Cusp.ratAct D.sp.cm V 1 v = v := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (1 : GF V).1.1 = 1 from rfl, Matrix.toLin_one]
  rfl

theorem ratAct_inv_apply (g : GF V) (v : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V g⁻¹ (GlobalTheory.Cusp.ratAct D.sp.cm V g v) = v := by
  rw [← ratAct_mul_apply, inv_mul_cancel, ratAct_one_apply]

theorem conj_maps (γ g : GF V) (S : Submodule D.host.E V.V)
    (h : ∀ v ∈ S, GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ S) :
    ∀ w ∈ S.map (GlobalTheory.Cusp.ratAct D.sp.cm V g),
      GlobalTheory.Cusp.ratAct D.sp.cm V (g * γ * g⁻¹) w ∈ S.map (GlobalTheory.Cusp.ratAct D.sp.cm V g) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [ratAct_mul_apply, ratAct_inv_apply, ratAct_mul_apply]
  exact ⟨_, h y hy, rfl⟩

theorem map_span_range (g : GF V) {a : ℕ} (x : Fin a → V.V) (y : Fin a → V.V)
    (hx : ∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = y i) :
    (Submodule.span D.host.E (Set.range x)).map (GlobalTheory.Cusp.ratAct D.sp.cm V g) =
      Submodule.span D.host.E (Set.range y) := by
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext i
  exact hx i

end GlobalTheory.Cusp.ConjLevi


open GlobalTheory.Cusp.ConjLevi in
theorem GlobalTheory.Cusp.ConjLevi.conj_mem_levi_stdVec : ∀ {D : D7} {V : HSp D} (Φ : WittFrame V) (γ g : GF V) {a : ℕ} (ha : a ≤ wittIndex V) (j : Fin (wittIndex V)), j.val + 1 = a → ∀ (x x' : Fin a → V.V), (∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = Φ.e (Fin.castLE ha i)) → (∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x' i) = Φ.f (Fin.castLE ha i)) → (∀ v ∈ Submodule.span D.host.E (Set.range x), GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ Submodule.span D.host.E (Set.range x)) → (∀ v ∈ Submodule.span D.host.E (Set.range x'), GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ Submodule.span D.host.E (Set.range x')) → rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) {stdVec j} := by
  intro D V Φ γ g a ha j hj x x' hx hx' h1 h2
  have hmem : ∀ i : Fin (wittIndex V), i ≤ j ↔ ∃ k : Fin a, Fin.castLE ha k = i := fun i => by
    constructor
    · intro hi
      exact ⟨⟨i.val, by have := Fin.le_def.1 hi; omega⟩, Fin.ext rfl⟩
    · rintro ⟨k, rfl⟩
      exact Fin.le_def.2 (by simp only [Fin.val_castLE]; omega)
  have hE : Φ.sub (stdVec j) = Submodule.span D.host.E (Set.range fun i : Fin a => Φ.e (Fin.castLE ha i)) := by
    rw [WittFrame.sub]
    congr 1
    ext v
    simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, stdVec]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · by_cases h : i ≤ j
        · obtain ⟨k, rfl⟩ := (hmem i).1 h; exact ⟨k, rfl⟩
        · rw [if_neg h] at hi; exact absurd hi (by decide)
      · by_cases h : i ≤ j
        · rw [if_pos h] at hi; exact absurd hi (by decide)
        · rw [if_neg h] at hi; exact absurd hi (by decide)
    · rintro ⟨k, rfl⟩
      exact Or.inl ⟨_, by rw [if_pos ((hmem _).2 ⟨k, rfl⟩)], rfl⟩
  have hF : Φ.sub (-stdVec j) = Submodule.span D.host.E (Set.range fun i : Fin a => Φ.f (Fin.castLE ha i)) := by
    rw [WittFrame.sub]
    congr 1
    ext v
    simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, stdVec, Pi.neg_apply]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · by_cases h : i ≤ j
        · rw [if_pos h] at hi; exact absurd hi (by decide)
        · rw [if_neg h] at hi; exact absurd hi (by decide)
      · by_cases h : i ≤ j
        · obtain ⟨k, rfl⟩ := (hmem i).1 h; exact ⟨k, rfl⟩
        · rw [if_neg h] at hi; exact absurd hi (by decide)
    · rintro ⟨k, rfl⟩
      refine Or.inr ⟨_, ?_, rfl⟩
      rw [if_pos ((hmem _).2 ⟨k, rfl⟩)]
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  unfold WittFrame.levi
  simp only [Finset.mem_singleton, iInf_iInf_eq_left]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH _ _ _ (g * γ * g⁻¹) ∈ _
    rw [GlobalTheory.Cusp.diagH_mem_parab, hE, ← map_span_range g x _ hx]
    exact conj_maps γ g _ h1
  · show GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH _ _ _ (g * γ * g⁻¹) ∈ _
    rw [GlobalTheory.Cusp.diagH_mem_parab, hF, ← map_span_range g x' _ hx']
    exact conj_maps γ g _ h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormEqZeroOfWhittakerVanishing
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.JSW

theorem eq_zero_of_whit_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsCuspForm φ → (∀ g, GlobalTheory.JSW.whit φ.1 g = 0) → φ = 0 := by
  intro E _ _ _ a φ hφ hW
  have hc : Continuous φ.1 := GlobalTheory.T.automorphicForm_GL_continuous E a φ hφ.1
  have hcusp := GlobalTheory.T.isCuspidal_of_isCuspForm' E a φ hφ
  have hl : GroundTheory.Automorphic.AutomorphicForm.IsLeftInvariant (K := E) (n := a) φ.1 :=
    fun γ g => hφ.1.left γ g
  let V : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | finRep E a k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hV : ∃ V : OpenSubgroup (GroundTheory.Automorphic.AdelicGLn.FiniteAdelicGL E a),
      ∀ g, ∀ v ∈ V, φ.1 (g * GroundTheory.Automorphic.AutomorphicForm.finEmb E a v) = φ.1 g :=
    ⟨⟨V, hφ.1.level⟩, fun g v hv => by
      rw [GlobalTheory.FinConj.finEmb_eq_finGL]
      have : (finRep E a v φ).1 g = φ.1 g := by rw [show finRep E a v φ = φ from hv]
      exact this⟩
  apply Subtype.ext
  exact GroundTheory.Automorphic.MultiplicityOne.eq_zero_of_whittaker_eq_zero hc hl hcusp hV hW

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsUniformlySmallOutsideCompactBand
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

noncomputable section
namespace GlobalTheory.HCF.Tail

theorem compactPart : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ω : Set (GA E a)), IsCompact ω →
    ∀ t R : ℝ, 0 < t → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ R * ρ j) →
        ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ C := GlobalTheory.T.exists_isCompact_detBand_siegelSet

theorem finConj : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ ω : Set (GA E a), IsCompact ω →
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
      ∀ z : BlockIx a r → Ad E, (∀ p, (z p).1 = 0) →
      (∀ p, ∃ c ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, (z p).2 = (M : Af E) * c) →
      ∃ l ∈ L, (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k)⁻¹ * unip z *
        (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k) = finGL E a l := GlobalTheory.T.exists_conj_finiteUnipotent_mem_openSubgroup

theorem infConj : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (U : Set (GA E a)), U ∈ 𝓝 (1 : GA E a) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : GA E a) (P : BlockIx a r → Ad E), (∀ p, (P p).2 = 0) →
      ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)))‖ ≤ δ →
      x⁻¹ * unip P * x ∈ U := _root_.GlobalTheory.InfConj.conj_unip_mem_nhds

theorem meanZero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (B : ℝ),
      (∀ X ∈ GroundTheory.Automorphic.scaledUnipFD E a r M, ‖φ (unip X * x) - φ x‖ ≤ B) → ‖φ x‖ ≤ B := _root_.GlobalTheory.CuspTail.norm_le_of_osc_scaledUnipFD

section Band
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem absDetA_mul (g h : GA E a) : absDetA (g * h) = absDetA g * absDetA h := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E),
    GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), map_mul, map_mul]
  rfl

theorem absDetA_ratGL (γ : GL (Fin a) E) : absDetA (ratGL E a γ) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (ratGL E a γ) = GroundTheory.Global.IdeleGroup.diagonal E (Matrix.GeneralLinearGroup.det γ) :=
    Units.ext (det_map _ γ)
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), h, GroundTheory.Global.IdeleGroup.ideleModule_diagonal]
  rfl

theorem absDetA_unip {r : ℕ} (P : BlockIx a r → Ad E) : absDetA (unip P) = 1 := by
  unfold absDetA
  rw [det_unip]
  simpa [absDetA] using (absDetA_one (E := E) (a := a))

theorem absDetA_conj (x u : GA E a) (hu : absDetA u = 1) : absDetA (x * (x⁻¹ * u * x)) = absDetA x := by
  have h1 : absDetA x⁻¹ * absDetA x = 1 := by rw [← absDetA_mul, inv_mul_cancel, absDetA_one]
  rw [absDetA_mul, absDetA_mul, absDetA_mul, hu, mul_one, h1, mul_one]

theorem mem_band_ratGL_mul {γ : GL (Fin a) E} {g : GA E a} (hg : g ∈ band E a) : ratGL E a γ * g ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, absDetA_mul, absDetA_ratGL, one_mul] at hg ⊢
  exact hg

end Band

section Span
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {L : Subgroup (GL (Fin a) (Af E))}
  {W : Submodule ℂ (Kinf E a → ℂ)} {X : Set (Module.End ℂ (Sm E a) → ℂ)} {N : ℕ}

theorem span_left {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx.1.left
  | zero => intro γ g; rfl
  | add x y _ _ hx hy => intro γ g; simp [hx γ g, hy γ g]
  | smul c x _ hx => intro γ g; simp [hx γ g]

theorem span_fin {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    ∀ l ∈ L, finRep E a l φ = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx.2.1
  | zero => intro l _; exact map_zero _
  | add x y _ _ hx hy => intro l hl; rw [map_add (f := _), hx l hl, hy l hl]
  | smul c x _ hx => intro l hl; rw [map_smul, hx l hl]

theorem span_right {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) {l : GL (Fin a) (Af E)} (hl : l ∈ L)
    (g : GA E a) : φ.1 (g * finGL E a l) = φ.1 g :=
  congrFun (congrArg Subtype.val (span_fin hφ l hl)) g

theorem span_cont (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) : Continuous φ.1 := by
  refine GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E a φ ?_
  refine isOpen_iff_forall_mem_open.2 fun k hk => ⟨(fun l => k * l) '' (L : Set (GL (Fin a) (Af E))), ?_, ?_, ⟨1, L.one_mem, mul_one k⟩⟩
  · rintro _ ⟨l, hl, rfl⟩
    change finRep E a (k * l) φ = φ
    rw [map_mul, Module.End.mul_apply, span_fin hφ l hl]
    exact hk
  · exact (Homeomorph.mulLeft k).isOpenMap _ hL

end Span

open GroundTheory.Automorphic.Reduction in
theorem oneRoot (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) (W : Submodule ℂ (Kinf E a → ℂ)) (hW : FiniteDimensional ℂ W)
    (X : Set (Module.End ℂ (Sm E a) → ℂ)) (hX : X.Finite) (N : ℕ)
    {ω : Set (GA E a)} (hω : IsCompact ω) (hωB : ω ⊆ (adelicBorel (K := E) (n := a) : Set (GA E a)))
    {t : ℝ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) {r : ℕ} (hr : 0 < r) (hra : r < a) :
    ∃ R : ℝ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) →
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ k ∈ (maxCompact (K := E) (n := a)),
      b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
      R * ρ ⟨r, hra⟩ ≤ ρ ⟨r - 1, by omega⟩ →
      ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k)‖ ≤ ε * M := by
  obtain ⟨U, hU, hequi⟩ := _root_.GlobalTheory.HCF.Equi.equicontinuous_band E a L hL W hW X hX N ε hε
  obtain ⟨M₀, hM₀, hfin⟩ := finConj E a r L hL ω hω
  obtain ⟨C₁, hC₁⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_norm_archMat_conj_le hω hωB ht hr hra
    (GroundTheory.Automorphic.isCompact_scaledInfSet (K := E) M₀)
  obtain ⟨δ, hδ, hinf⟩ := infConj E a r U hU
  refine ⟨max C₁ 0 / δ + 1, ?_⟩
  intro φ hφ hcusp M hM b hb ρ hρ hs k hk hband hR
  set x := b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k with hx
  have hq0 : 0 < ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩ := div_pos (hρ _) (hρ _)
  have hgain : C₁ * (ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩) ≤ δ := by
    set q := ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩
    set c := max C₁ 0
    have hc0 : 0 ≤ c := le_max_right _ _
    have hRq : (c / δ + 1) * q ≤ 1 := by
      rw [show q = ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩ from rfl, mul_div_assoc', div_le_one (hρ _)]
      exact hR
    have h1 : C₁ * q ≤ c * q := mul_le_mul_of_nonneg_right (le_max_left _ _) hq0.le
    have h2 : c * q ≤ δ := by
      have e : c = δ * (c / δ) := by field_simp
      nlinarith [mul_nonneg (div_nonneg hc0 hδ.le) hq0.le]
    linarith
  refine meanZero E a r hr hra φ.1 (span_left hφ) hcusp (span_cont hL hφ) M₀ hM₀ x (ε * M) ?_
  intro Y hY
  have hsplit : unip Y * x = x * (x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y) * x) *
      (x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncFin Y) * x) := by
    conv_lhs => rw [← GroundTheory.Automorphic.CuspidalSpectrum.truncInf_add_truncFin Y, unip_add]
    group
  obtain ⟨l, hl, hle⟩ := hfin b hb ρ hρ k hk (GroundTheory.Automorphic.CuspidalSpectrum.truncFin Y) (fun p => rfl)
    (fun p => GroundTheory.Automorphic.exists_finite_eq_natCast_mul hM₀ hY p)
  have hv : x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y) * x ∈ U :=
    hinf x _ (fun p => rfl) ((hC₁ b hb ρ hρ hs k hk (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y) (fun p => rfl)
      (fun p => GroundTheory.Automorphic.infinite_mem_scaledInfSet hM₀ hY p)).trans hgain)
  rw [hsplit, hle, span_right hφ hl]
  refine hequi φ hφ M hM x hband _ hv ?_
  have h := absDetA_conj x (unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y)) (absDetA_unip _)
  simp only [band, Set.mem_setOf_eq] at hband ⊢
  rw [h]
  exact hband


open GroundTheory.Automorphic.Reduction in
theorem tails : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W →
    ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : Set (GA E a), IsCompact C ∧
    C ⊆ band E a ∧ ∀ g ∈ band E a, (∃ γ : GL (Fin a) E, ratGL E a γ * g ∈ C) ∨
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) →
      ‖φ.1 g‖ ≤ ε * M := by
  intro E _ _ _ a L hL W hW X hX N ε hε
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) a
  have hex : ∀ r : ℕ, ∀ (hr : 0 < r) (hra : r < a), ∃ R : ℝ, _ := fun r hr hra =>
    oneRoot E a L hL W hW X hX N hω hωB ht hε hr hra
  choose Rf hRf using hex
  set R : ℝ := 1 + ∑ r : Fin a, if h : 0 < (r : ℕ) then max (Rf r h r.2) 0 else 0 with hRdef
  have hRle : ∀ (r : ℕ) (hr : 0 < r) (hra : r < a), Rf r hr hra ≤ R := by
    intro r hr hra
    have h1 := Finset.single_le_sum (f := fun r : Fin a => if h : 0 < (r : ℕ) then max (Rf r h r.2) 0 else 0)
      (fun r _ => by split_ifs <;> simp) (Finset.mem_univ ⟨r, hra⟩)
    simp only [hr, dif_pos] at h1
    linarith [le_max_left (Rf r hr hra) 0]
  obtain ⟨C, hC, hCb, hCmem⟩ := compactPart E a ω hω t R ht
  refine ⟨C, hC, hCb, fun g hg => ?_⟩
  obtain ⟨γ, hγ⟩ := hsieg g
  obtain ⟨b, hb, _, ⟨ρ, hρ, hs, rfl⟩, k, hk, he⟩ := hγ
  have he' : ratGL E a γ * g = b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k := he
  have hgb : ratGL E a γ * g ∈ band E a := mem_band_ratGL_mul hg
  by_cases hall : ∀ (r : ℕ) (hr : 0 < r) (hra : r < a), ρ ⟨r - 1, by omega⟩ ≤ R * ρ ⟨r, hra⟩
  · refine Or.inl ⟨γ, ?_⟩
    rw [he'] at hgb ⊢
    refine hCmem b hb ρ hρ hs (fun i j hij => ?_) k hk hgb
    have h1 := hall j (by omega) j.2
    have e : (⟨(j : ℕ) - 1, by omega⟩ : Fin a) = i := Fin.ext (by simp; omega)
    rwa [e] at h1
  · push_neg at hall
    obtain ⟨r, hr, hra, hlt⟩ := hall
    refine Or.inr fun φ hφ hc M hM => ?_
    rw [← span_left hφ γ g, he']
    rw [he'] at hgb
    refine hRf r hr hra φ hφ hc M hM b hb ρ hρ hs k hk hgb ?_
    exact (mul_le_mul_of_nonneg_right (hRle r hr hra) (hρ _).le).trans hlt.le

end GlobalTheory.HCF.Tail

end
end

