module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsNormPlaceLeOfFrobenius
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory
namespace NormLeFrob

theorem valuation_algebraMap_le_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (x : 𝓞 E) :
    A.valuation (algebraMap E Ω (x : E)) ≤ 1 := by
  have h1 : IsIntegral ℤ (algebraMap E Ω (x : E)) := (x.2).map (IsScalarTower.toAlgHom ℤ E Ω)
  have h2 : IsIntegral A (algebraMap E Ω (x : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact A.valuation_le_one y

noncomputable def toResidue {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) : 𝓞 E →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp
    { toFun := fun x => ⟨algebraMap E Ω (x : E), (A.valuation_le_one_iff _).mp (valuation_algebraMap_le_one A x)⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }

theorem toResidue_eq_zero_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hw : IsPlaceOver A w) (x : 𝓞 E) :
    toResidue A x = 0 ↔ x ∈ w.asIdeal := by
  rw [← hw x]
  simp only [toResidue, RingHom.coe_comp, Function.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]

theorem toResidue_isRoot {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (q : ℕ) (σ : G E Ω) (hσ : IsFrob A q σ) (x : 𝓞 E) :
    (X ^ q - X : (IsLocalRing.ResidueField A)[X]).IsRoot (toResidue A x) := by
  have hx := valuation_algebraMap_le_one A x
  have h := hσ.2 _ hx
  rw [AlgEquiv.commutes] at h
  have hmem : (⟨algebraMap E Ω (x : E), (A.valuation_le_one_iff _).mp hx⟩ : A) ^ q
      - ⟨algebraMap E Ω (x : E), (A.valuation_le_one_iff _).mp hx⟩ ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    rw [← Valuation.map_neg]
    convert h using 2
    simp
  rw [← IsLocalRing.residue_eq_zero_iff] at hmem
  simp only [IsRoot, eval_sub, eval_pow, eval_X]
  have e : toResidue A x = IsLocalRing.residue A
      ⟨algebraMap E Ω (x : E), (A.valuation_le_one_iff _).mp hx⟩ := rfl
  rw [e, ← map_pow, ← map_sub]
  exact hmem

theorem normV_le_of_isFrob : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ q : ℕ, 1 < q → ∀ σ : G E Ω, IsFrob A q σ → normV w ≤ q := by
  intro E Ω _ _ _ _ A w hw q hq σ hσ
  classical
  set k := IsLocalRing.ResidueField A
  set P : k[X] := X ^ q - X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero hq
  let f : 𝓞 E ⧸ w.asIdeal →+* k :=
    Ideal.Quotient.lift w.asIdeal (toResidue A) (fun x hx => (toResidue_eq_zero_iff A w hw x).mpr hx)
  have hf : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (toResidue_eq_zero_iff A w hw x).mp ha
  let g : 𝓞 E ⧸ w.asIdeal → {y : k // y ∈ P.roots.toFinset} := fun a =>
    ⟨f a, by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Multiset.mem_toFinset, mem_roots hP0]
      exact toResidue_isRoot A q σ hσ x⟩
  have hg : Function.Injective g := fun a b h => hf (congrArg Subtype.val h)
  calc normV w = Nat.card (𝓞 E ⧸ w.asIdeal) := rfl
    _ ≤ Nat.card {y : k // y ∈ P.roots.toFinset} := Nat.card_le_card_of_injective g hg
    _ = P.roots.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ = q := Polynomial.natDegree_X_pow_sub_X (R := k) hq

end NormLeFrob
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterEqProdSupercuspidalSupportStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralCharacter_eq_prod_supercuspidalSupport : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (s : Multiset (IrrGL (k := k))) (ω : kˣ →* ℂˣ), HasSupport x.rep s → HasCentralChar x.rep ω → ∃ f : IrrGL (k := k) → kˣ →* ℂˣ, (∀ y ∈ s, HasCentralChar y.rep (f y)) ∧ ∀ z, ω z = (s.map fun y => f y z).prod := by
  first | exact @GlobalTheory.CentralSupport.centralChar_eq_prod_support | exact GlobalTheory.CentralSupport.centralChar_eq_prod_support | (intros; apply GlobalTheory.CentralSupport.centralChar_eq_prod_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexHeckeConjugatePlacePeterssonAdjoint
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ComplexHeckeAdjoint

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

theorem levChi_one {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    ∀ k ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv), levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := by
  intro k _
  have h1 : ext1 (R.datWp i R.triv).P.H (R.datWp i R.triv).P.chi (rTup (R.βW i) (R.datWp i R.triv) (Lev.finE (Wc D i) k)) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h1]
  simp [LevCh.datWp, datY]

theorem conj_eq {D : D7} {P P' : PlE D.host} (h : Formalism.BasicNotions.IsConjPl D.host P P') : P' = Formalism.DivisionValues.conjPl P := by
  have hc : ∀ y : 𝓞 D.host.E, Formalism.HermitianLattices.Ext.L3.conjO D.host.E y = Formalism.DivisionValues.cO D.host.E y := fun y =>
    RingOfIntegers.ext (by simp [Formalism.DivisionValues.cO, Formalism.HermitianLattices.Ext.L3.conjO_coe])
  have hcc : ∀ y : 𝓞 D.host.E, Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E y) = y := fun y =>
    RingOfIntegers.ext (by simp [Formalism.DivisionValues.cO])
  rw [GlobalTheory.ConjPlaceOff.isConjPl_iff] at h
  ext x
  show x ∈ P'.asIdeal ↔ x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro hx
    refine ⟨Formalism.DivisionValues.cO D.host.E x, (h _).2 ?_, hcc x⟩
    rwa [hc, hcc]
  · rintro ⟨y, hy, rfl⟩
    rw [← hc]
    exact (h y).1 hy


open GlobalTheory.HeckeParts in
theorem keep_adj {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    {L : LevDat D.host.E ℂ V.rank} (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P)
    (hχ : ∀ k ∈ levG V β L, levChi V β L k = 1) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {HM : HMod (MMap M)} {U : Submodule ℂ (MMap M)}
    (hU : U = Mult θ M (levS V β L) (levChi V β L)) {ip : MMap M → MMap M → ℂ} {c : ℂ}
    (hip : ∀ T T', ip T T' = c * ipM M μ 𝓕 T T') (h : HM.Is U ip) {x : GA D V} {A A' : Finset (GA D V)}
    (hA : LocRep (levG V β L) P x A) (hA' : LocRep (levG V β L) P x⁻¹ A') :
    (∀ y, ∃ y', HM.e y' = heckeOn M A (HM.e y)) ∧ (∀ y, ∃ y', HM.e y' = heckeOn M A' (HM.e y)) ∧
      ∀ y z y' z', HM.e y' = heckeOn M A (HM.e y) → HM.e z' = heckeOn M A' (HM.e z) → inner ℂ y' z = inner ℂ y z' := by
  subst hU
  have h' : HM.Is (Mult θ M (levS V β L) (levChi V β L)) fun T T' => c * ipM M μ 𝓕 T T' :=
    ⟨h.1, h.2.1, fun y z => (h.2.2 y z).trans (hip _ _)⟩
  have hmem : ∀ y, HM.e y ∈ Mult θ M (levS V β L) (levChi V β L) := fun y => h.2.1 ▸ LinearMap.mem_range_self _ y
  have keep : ∀ {w : GA D V} {C : Finset (GA D V)}, LocRep (levG V β L) P w C → ∀ y,
      heckeOn M C (HM.e y) ∈ LinearMap.range HM.e := by
    intro w C hC y
    rw [h.2.1]
    exact hC.mult hβ hP (fun k hk => levG_le_flag hk) (hmem y) (fun v => rInv_of_mem hχ (hmem y) v)
  have lift : ∀ {w : GA D V} {C : Finset (GA D V)}, LocRep (levG V β L) P w C →
      ∃ t : Module.End ℂ HM.H, ∀ y, HM.e (t y) = heckeOn M C (HM.e y) := by
    intro w C hC
    refine ⟨(LinearEquiv.ofInjective _ h.1).symm.toLinearMap ∘ₗ ((heckeOn M C ∘ₗ HM.e).codRestrict _ (keep hC)),
      fun y => ?_⟩
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ h.1).apply_symm_apply _)
  obtain ⟨t, ht⟩ := lift hA
  obtain ⟨t', ht'⟩ := lift hA'
  refine ⟨fun y => keep hA y, fun y => keep hA' y, fun y z y' z' hy hz => ?_⟩
  obtain rfl : y' = t y := h.1 (hy.trans (ht y).symm)
  obtain rfl : z' = t' z := h.1 (hz.trans (ht' z).symm)
  exact inner_hecke hχ hμ h𝓕 h' le_rfl hA.2 hA'.2 (hA.card hβ hP hA') ht ht' y z

end GlobalTheory.ComplexHeckeAdjoint

namespace GlobalTheory.CxHeckeAdj


set_option maxHeartbeats 1600000 in
theorem hecke_adjoint : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3),
    Rl.Char3 F → ∀ (i : Fin D.R.m) (k : ℕ) (P P' : PlE D.host), IsSplitPl D.host P → IsConjPl D.host P P' →
    Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    Formalism.IndefR.Bridge.SplitOff P' (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal → 1 ≤ k → k ≤ D.R.r →
    ∃ (α α' : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i)) (R R' : Finset (Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i))),
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P k α ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α R ∧
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P' k α' ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α' R' ∧
      (∀ x, ∃ x', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x)) ∧
      (∀ y, ∃ y', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y)) ∧
      ∀ x y x' y' : (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).H,
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x) →
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y) →
        ⟪x', y⟫_ℂ = ⟪x, y'⟫_ℂ := by

  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ Rl F hc i k P P' _hsp hcj hso hso' _h2 _h2' _hk1 hk
  classical
  obtain ⟨c, hβ⟩ := hc.lev.βW i
  have hrk : k ≤ (Formalism.IndefR.Links.Wc D i).rank := by
    rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2]; exact hk
  have hoff : ∀ Q : Formalism.L2.DIV.Pl D.host.E, Formalism.IndefR.Bridge.SplitOff Q (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
      GlobalTheory.HeckeParts.OffLevel (Rl.datWp i Rl.triv) (1 ^ c) Q := by
    intro Q hQ
    refine ⟨hQ.1, ?_, ?_⟩
    · rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top
    · intro PP hPP
      have hPP' : PP ∈ Rl.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
      have hS : PP ∈ (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hc.fam.Sb hPP'
      refine ⟨fun h => hQ.2.1 (h ▸ hS), fun h => hQ.2.2 PP hS ?_⟩
      rw [Formalism.L2.Col.conjIdeal_asIdeal]
      refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ Q).isPrime.ne_top fun a ha => ?_
      obtain ⟨a', ha', e⟩ := h a ha
      rw [Formalism.L2.Col.mem_conjP]
      have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
      rwa [this]
  obtain ⟨α, A, A', hα, hA, hA'⟩ := GlobalTheory.HeckeParts.exists_hecke hβ (hoff P hso) hrk
  obtain ⟨α₂, B, B', hα₂, -, -⟩ := GlobalTheory.HeckeParts.exists_hecke hβ (hoff P' hso') hrk
  have hα₂' : Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) (Formalism.DivisionValues.conjPl P) k α₂ :=
    GlobalTheory.ComplexHeckeAdjoint.conj_eq hcj ▸ hα₂
  obtain ⟨e, ϖ, he, -, -, -⟩ := id hα
  obtain ⟨a, ha, b, hb, hab⟩ := GlobalTheory.SplitHeckeAdj.hecke_conj (Formalism.IndefR.Links.Wc D i) he hα hα₂'
  obtain ⟨Lp, -, -, -, hK⟩ := GlobalTheory.HeckeParts.loc_package hβ (hoff P hso) he
  have hA₂ : Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α₂ A :=
    GlobalTheory.SplitHeckeAdj.isDC_of_mem (Subgroup.inv_mem _ ((hK a).1 ha).1) (Subgroup.inv_mem _ ((hK b).1 hb).1)
      (by rw [hab]; group) hA.2

  obtain ⟨hk1, hk2, hadj⟩ := GlobalTheory.ComplexHeckeAdjoint.keep_adj hβ (hoff P hso) (GlobalTheory.ComplexHeckeAdjoint.levChi_one Rl.toRealDat i)
    (hc.models.νW i).1.1 (hc.models.νW i).2 rfl
    (fun _ _ => rfl) (hc.models.HW i (Formalism.IndefR.Links.sg0 D A3.A)) hA' hA
  exact ⟨α, α₂, A', A, hα, hA'.2, hα₂, hA₂, hk1, hk2, hadj⟩

end GlobalTheory.CxHeckeAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalFieldIso

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem continuous_symm (i : k ≃+* k') (hi : Continuous i) : Continuous i.symm := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k')
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi
  exact (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous


variable (k) in
theorem valuation_le_one_iff_ord (x : kˣ) : valuation k (x : k) ≤ 1 ↔ 0 ≤ GlobalTheory.SmGL.ord k x := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (x : k)) ≠ 0 := by simp
  rw [GlobalTheory.SmGL.ord, neg_nonneg, ← φ.strictMono.le_iff_le, map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  simp [φ]


variable (k) in
theorem valuation_le_one_iff_nabs (x : kˣ) : valuation k (x : k) ≤ 1 ↔ GlobalTheory.SplitWeil.nabs k x ≤ 1 := by
  rw [valuation_le_one_iff_ord, GlobalTheory.LGrp.nabs_eq_zpow,
    zpow_le_one_iff_right₀ (by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k)]
  omega

theorem nabs_map (i : k ≃+* k') (hi : Continuous i) (x : kˣ) :
    GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x :=
  GlobalTheory.SplitWeil.nabs_map_of_homeomorph i hi (continuous_symm i hi) x

theorem valuation_map_le_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := valuation_le_one_iff_nabs k' (Units.map i.toRingHom.toMonoidHom (Units.mk0 x hx))
  rw [nabs_map i hi, ← valuation_le_one_iff_nabs k] at h
  simpa using h

theorem map_integer (i : k ≃+* k') (hi : Continuous i) :
    (𝒪[k] : Subring k).map i.toRingHom = 𝒪[k'] := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Valuation.mem_integer_iff _ _).2 ((valuation_map_le_one_iff i hi x).2 ((Valuation.mem_integer_iff _ _).1 hx))
  · intro hy
    refine ⟨i.symm y, (Valuation.mem_integer_iff _ _).2 ?_, i.apply_symm_apply y⟩
    rw [← valuation_map_le_one_iff i hi, RingEquiv.apply_symm_apply]
    exact (Valuation.mem_integer_iff _ _).1 hy

theorem resCard_eq (i : k ≃+* k') (hi : Continuous i) : GlobalTheory.SplitWeil.resCard k' = GlobalTheory.SplitWeil.resCard k := by
  let e : 𝒪[k] ≃+* 𝒪[k'] := (i.subringMap (s := 𝒪[k])).trans (RingEquiv.subringCongr (map_integer i hi))
  exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv).symm

theorem ord_map (i : k ≃+* k') (hi : Continuous i) (x : kˣ) :
    GlobalTheory.SmGL.ord k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SmGL.ord k x := by
  have h := nabs_map i hi x
  rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, resCard_eq i hi] at h
  have hq : (1 : ℝ) < GlobalTheory.SplitWeil.resCard k := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k
  exact neg_inj.1 (zpow_right_injective₀ (by linarith) hq.ne' h)

theorem absPow_map (i : k ≃+* k') (hi : Continuous i) (s : ℂ) (x : kˣ) :
    GlobalTheory.SmGL.absPow k' s (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SmGL.absPow k s x := by
  ext
  rw [GlobalTheory.SmGL.val_absPow, GlobalTheory.SmGL.val_absPow, nabs_map i hi]

end GlobalTheory.LocalFieldIso

theorem GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → Continuous i.symm ∧ (∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) ∧ (∀ x : kˣ, ord k' (Units.map i.toRingHom.toMonoidHom x) = ord k x) ∧ resCard k' = resCard k ∧ ∀ (s : ℂ) (x : kˣ), absPow k' s (Units.map i.toRingHom.toMonoidHom x) = absPow k s x := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  exact ⟨GlobalTheory.LocalFieldIso.continuous_symm i hi, GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi,
    GlobalTheory.LocalFieldIso.ord_map i hi, GlobalTheory.LocalFieldIso.resCard_eq i hi, GlobalTheory.LocalFieldIso.absPow_map i hi⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConvolutionSingleFactorGoodProjectorEqZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_singleFactor_goodProjector_eq_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (eR : G ≃* G0g D.nd) (kv0 : Σ k : Fin 2, D.nd.PlG k),
    haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
    ∀ M : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv0.1))),
    (∀ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) →
      M * D.ntypes.eSer kv0.1 (Formalism.CyclotomicNorms.monicOf (a kv0)) = 0) → ∀ x : G,
    ∑ y : G, (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then M.coeff (eR y kv0) else 0) *
      D.ntypes.e0.coeff (eR (y⁻¹ * x)) = 0 := by
  first | exact @GlobalTheory.DownLift.conv_single_goodProj_eq_zero | exact GlobalTheory.DownLift.conv_single_goodProj_eq_zero | (intros; apply GlobalTheory.DownLift.conv_single_goodProj_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticePrismaticFCrystalPerfectPrismStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_prismaticFCrystal_perfectPrism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∃ (M : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] ↥L.T)), Realises K M (ainfObj K) (ainfId K) ↥L.T (fun g => actT L g) j := by
  first | exact @GlobalTheory.BSP.clause1_perfectPrism | exact GlobalTheory.BSP.clause1_perfectPrism | (intros; apply GlobalTheory.BSP.clause1_perfectPrism <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspKillHolds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.CuspKillProof

theorem cuspKill_holds : ∀ D : D7, CuspKill D := by
  intro D W ν hν s I hI Γ hΓQ hNΓ hnorm 𝓓 h𝓓 Φ φ hΦc hΦΓ hΦN hφ hcusp hint
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W
  haveI : BorelSpace (GA D W) := ⟨rfl⟩
  haveI : Countable (GQ W) := GlobalTheory.AutomorphicL2Unitary.countable_of_discrete
  haveI : Countable Γ := Function.Injective.countable (Subgroup.inclusion_injective hΓQ)
  have hNc : IsClosed (NI W I : Set (GA D W)) := by
    rw [← GlobalTheory.Cusp.NA_frameFlag hI]
    haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
    exact GlobalTheory.Cusp.IsoFlag.isClosed_unip _ _ _
  have hcc : GlobalTheory.Cusp.Cocompact (GQ W) (NI W I) := by
    rw [← GlobalTheory.Cusp.NA_frameFlag hI]
    exact GlobalTheory.Cusp.cocompact_single _
  haveI : LocallyCompactSpace (NI W I) := hNc.locallyCompactSpace
  have hsub : Γ.subgroupOf (NI W I) = (GQ W).subgroupOf (NI W I) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => hΓQ h, fun h => hNΓ ⟨x.2, h⟩⟩
  set κ : Measure (NI W I) := Measure.haar
  set 𝓝 : Set (NI W I) := GlobalTheory.AutomorphicL2Unitary.stdDom ((GQ W).subgroupOf (NI W I))
  have h𝓝Q : IsFundamentalDomain ((GQ W).subgroupOf (NI W I)) 𝓝 κ := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ κ
  have h𝓝Γ : IsFundamentalDomain (Γ.subgroupOf (NI W I)) 𝓝 κ := by rw [hsub]; exact h𝓝Q
  have h𝓝t : κ 𝓝 ≠ ⊤ := hcc.measure_ne_top h𝓝Q
  have h0 : ∀ g, ∫ n in 𝓝, φ ((n : GA D W) * g) ∂κ = 0 := hcusp s I hI κ 𝓝 inferInstance h𝓝Q
  exact GlobalTheory.UnfoldNormal.unfold_zero_mean (GA D W) ν Γ (NI W I) inferInstance hNc hnorm κ 𝓝 inferInstance h𝓝Γ h𝓝t
    Φ φ hΦc.measurable hφ.cont.measurable hΦN hΦΓ (fun γ hγ g => hφ.left γ (hΓQ hγ) g) h0 𝓓 h𝓓 hint

end GlobalTheory.CuspKillProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitar
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.DefU

theorem exists_hasWeightAt_of_isAutRepU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ τ : E →+* ℂ, ∃ lam : Formalism.BasicNotions.DomWeight n, HasWeightAt π τ lam :=
  fun E _ _ _ n _ π hπ τ => (_root_.GlobalTheory.DefU.AU.existsUnique_hasWt E n (AU.mk ⟨π, hπ⟩) τ).exists

end GlobalTheory.DefU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinBasisOfSemistablePeriodsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisinBasis_of_semistablePeriods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (N : ℕ) (F : Pre bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T ∧ IsUnit Z ∧ ∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA := by
  first | exact @GlobalTheory.BKLim.exists_pre_of_wseed | exact GlobalTheory.BKLim.exists_pre_of_wseed | (intros; apply GlobalTheory.BKLim.exists_pre_of_wseed <;> assumption)
end

