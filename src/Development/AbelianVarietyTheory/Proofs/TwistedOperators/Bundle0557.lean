module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeCoefficientsSqIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0338
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatesOfRationalThetaLiftFromCharacterisatio
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarFiniteTensorEqDatumSmallModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0552
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateBaseLevelOfHoweUnramifiedCorrespondence
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalConjRow

theorem galD_of_inputs : GlobalTheory.Hk3.HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.LiftRows.SourceLevelLawC R.toRealDat F.lv2 → GlobalTheory.LiftRows.InnerProductFormulaC R.toRealDat F.lv2 → GlobalTheory.LiftRows.FockCoefficientC R.toRealDat F.lv2 → GlobalTheory.LiftRows.FiniteZetaL R.toRealDat F.lv2 → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).GalD F.cr false := by
  intro hH D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s hOk hsep hC hEx h1 h2 h3 h4 hph hstd fw hbar hio hom hone hpt hR hL hHe hU hE hblk hrt hlt hltb honto hk hl hun hlev hA hsum
  have core := (GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx).1
  exact _root_.GlobalTheory.ConjScalarOff.galD_base hH _root_.GlobalTheory.ConjRatLiftFive.conjRatLift5 T R F κ v₀ O s hOk hC hEx
    (_root_.GlobalTheory.ConjScalarProof.conjScalarAt_of_sourceLevelLaw_fock_zeta R.toRealDat F.lv2 core hOk.ok2.irr h1 h2 h3 h4
      (GlobalTheory.RealCoefSq.lowestKType_coefficients_sq_integrable R.toRealDat F.lv2 core))
    hstd fw hbar hio hom hone hpt hun
    (GlobalTheory.scalConj_base_facts R F s hOk hsep hC hR hL hHe hU hE hblk hrt hlt hltb honto hk hl hun hlev hA hsum)

end GlobalTheory.ScalConjRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetOfSelfDual
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeLatCoset

theorem selfDual_eq : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (X Y : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.Col.conjPrime₂ P ≠ P → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ X, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ X) → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ Y, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ Y) →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • X ≤ Y → (Formalism.L2.Col.conjPrime₂ P).asIdeal • Y ≤ X → X = Y := by
  intro D V P X Y hP hX hY hXY hYX
  have hcc : ∀ s : 𝓞 D.host.E,
      ReciprocityTheory.ChartRestriction.G.FD.cc ((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) = (s : D.host.E) := by
    intro s
    show IsCMField.complexConj D.host.E (star (s : D.host.E)) = (s : D.host.E)
    exact star_star (s : D.host.E)
  have hcO : ∀ s : 𝓞 D.host.E, Formalism.L2.Col.cO D.host.E (Formalism.L2.Col.cO D.host.E s) = s := by
    intro s
    apply RingOfIntegers.ext
    show star (star (s : D.host.E)) = (s : D.host.E)
    exact star_star _
  have key : ∀ (s : 𝓞 D.host.E) (v y : Fin V.rank → D.host.E),
      ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) (s • v) y =
        ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v (Formalism.L2.Col.cO D.host.E s • y) := by
    intro s v y
    unfold ReciprocityTheory.ChartRestriction.G.FD.herm
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have e1 : (s • v) a = (s : D.host.E) * v a := rfl
    have e2 : (Formalism.L2.Col.cO D.host.E s • y) b = ((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) * y b := rfl
    have e3 : ReciprocityTheory.ChartRestriction.G.FD.cc (((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) * y b) =
        (s : D.host.E) * ReciprocityTheory.ChartRestriction.G.FD.cc (y b) := by
      rw [← hcc s]
      exact map_mul (IsCMField.complexConj D.host.E) _ _
    rw [e1, e2, e3]
    ring
  have hne : P.asIdeal ≠ (Formalism.L2.Col.conjPrime₂ P).asIdeal := fun h =>
    hP (IsDedekindDomain.HeightOneSpectrum.ext h.symm)
  have hcop : P.asIdeal ⊔ (Formalism.L2.Col.conjPrime₂ P).asIdeal = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne P.isMaximal (Formalism.L2.Col.conjPrime₂ P).isMaximal hne
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ P.asIdeal ⊔ (Formalism.L2.Col.conjPrime₂ P).asIdeal)
  have hsc : Formalism.L2.Col.cO D.host.E s ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal := by
    rw [Formalism.L2.Col.mem_conjP, hcO]
    exact hs
  have incl : ∀ X Y : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ X, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ X) → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ Y, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ Y) →
      (Formalism.L2.Col.conjPrime₂ P).asIdeal • X ≤ Y → (Formalism.L2.Col.conjPrime₂ P).asIdeal • Y ≤ X → Y ≤ X := by
    intro X Y hX hY hXY hYX l hl
    have h1 : t • l ∈ X := hYX (Submodule.smul_mem_smul ht hl)
    have h2 : s • l ∈ X := by
      rw [← hX]
      intro x hx
      have hx' : Formalism.L2.Col.cO D.host.E s • x ∈ Y := hXY (Submodule.smul_mem_smul hsc hx)
      obtain ⟨n, hn⟩ := (hY l).2 hl _ hx'
      exact ⟨n, by rw [key]; exact hn⟩
    have e : l = s • l + t • l := by rw [← add_smul, hst, one_smul]
    rw [e]
    exact X.add_mem h2 h1
  exact le_antisymm (incl Y X hY hX hYX hXY) (incl X Y hX hY hXY hYX)

theorem latG_mul_levG : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (x κ : GA D (Wc D i)),
    κ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) → latG (Wc D i) (x * κ) = latG (Wc D i) x := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL i x κ hκ
  have hκ' : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 κ :=
    ⟨hκ.1, hκ.2.1, Subgroup.mem_bot.1 hκ.2.2⟩
  have hS := GlobalTheory.DictMove.latGHat_eq (hL.βW i) hκ'
  ext v
  rw [(GlobalTheory.MarkCoset.latG_spec D _ (x * κ)).1, (GlobalTheory.MarkCoset.latG_spec D _ x).1,
    (GlobalTheory.MarkCoset.latG_spec D _ (x * κ)).2, (GlobalTheory.MarkCoset.latG_spec D _ x).2]
  constructor
  · rintro ⟨y, hy, hyz⟩
    refine ⟨(finHom (Wc D i) κ).1.mulVec y, ?_, ?_⟩
    · rw [← hS]
      exact ((GlobalTheory.MarkCoset.latG_spec D _ κ).2 _).2 ⟨y, hy, rfl⟩
    · rw [← hyz, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  · rintro ⟨y, hy, hyz⟩
    rw [← hS] at hy
    obtain ⟨y', hy', rfl⟩ := ((GlobalTheory.MarkCoset.latG_spec D _ κ).2 _).1 hy
    exact ⟨y', hy', by rw [← hyz, map_mul, Units.val_mul, Matrix.mulVec_mulVec]⟩

theorem exists_coset_of_selfDual : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))),
    Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → IsHeckeAt (Wc D i) P k α →
    Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    ∀ (g : GA D (Wc D i)) (L' : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E)),
    P.asIdeal • latG (Wc D i) g ≤ L' → (Formalism.L2.Col.conjPrime₂ P).asIdeal • L' ≤ latG (Wc D i) g →
    (∀ v : Fin (Wc D i).rank → D.host.E, (∀ y ∈ L', ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(Wc D i).gram.transpose) v y) = n) ↔ v ∈ L') →
    (L' ⊓ latG (Wc D i) g).toAddSubgroup.relIndex (latG (Wc D i) g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a ∈ Rc, latG (Wc D i) (g * a) = L' ∧ ∃ (e : AE D) (a₀ : GA D (Wc D i)), Formalism.L2.NTheta.IsIdemAt e P ∧
      SuppAt e (Wc D i) a₀ ∧ a⁻¹ * a₀ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) ∧ latG (Wc D i) (g * a₀) = L' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF i P k α Rc hso hα hRc g L' h1 h2 hsd hidx
  obtain ⟨e, ϖ, he, hϖ1, hϖ2, hαe⟩ := hα
  have hP : Formalism.L2.Col.conjPrime₂ P ≠ P := by
    intro h
    apply hso.1
    rw [Formalism.L2.Col.conjIdeal_asIdeal, h]
  obtain ⟨a₀, ha₀, hT, hT2⟩ := _root_.GlobalTheory.HeckeLocStep.exists_hecke D (Wc D i) P e ϖ k g (L' ⊓ latG (Wc D i) g) he hϖ1 hϖ2
    (le_inf h1 Submodule.smul_le_right) inf_le_right hidx
  obtain ⟨a, ha, hK⟩ := _root_.GlobalTheory.HeckeDC.exists_rep D R hL hF i P k α Rc e ϖ a₀ hso ⟨e, ϖ, he, hϖ1, hϖ2, hαe⟩ hRc he hϖ1 hϖ2 ha₀
  have hTL : latG (Wc D i) (g * a₀) = L' := by
    refine selfDual_eq D (Wc D i) P _ _ hP (GlobalTheory.Member.latG_selfDual D (Wc D i) (g * a₀) _ rfl).2.2 hsd ?_ ?_
    · refine le_trans ?_ (inf_le_left : L' ⊓ latG (Wc D i) g ≤ L')
      rw [← hT]
      exact le_inf Submodule.smul_le_right hT2
    · refine le_trans ?_ (inf_le_left : latG (Wc D i) (g * a₀) ⊓ latG (Wc D i) g ≤ _)
      rw [hT]
      exact le_inf Submodule.smul_le_right h2
  have hga : latG (Wc D i) (g * a) = latG (Wc D i) (g * a₀) := by
    have := latG_mul_levG D R hL i (g * a) (a⁻¹ * a₀) hK
    rw [← this, mul_assoc, mul_inv_cancel_left]
  exact ⟨a, ha, hga.trans hTL, e, a₀, he, ha₀.2.1, hK, hTL⟩

end GlobalTheory.HeckeLatCoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGaussianVacuumProductUnitVacuaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussianVacuum_product_unitVacua : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M.IsGauss Bs.ψ Bs.emb f₀ ∧
      IsDatumA (t := t) W e Γ (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) := by
  first | exact @GlobalTheory.FlipVac.exists_gauss_vac | exact GlobalTheory.FlipVac.exists_gauss_vac | (intros; apply GlobalTheory.FlipVac.exists_gauss_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalOperatorThetaQuotientFinitePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LocalDescent

theorem descend {A A' P : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A'] [AddCommGroup P]
    [Module ℂ P] (S : Submodule ℂ A) (S' : Submodule ℂ A') (p : A →ₗ[ℂ] P) (p' : A' →ₗ[ℂ] P)
    (hp : S.map p = ⊤) (hp' : S'.map p' = ⊤) (r : A → A → Prop) (r' : A' → A' → Prop)
    (hex : ∀ x ∈ S, ∃ y ∈ S, r x y) (hex' : ∀ x ∈ S', ∃ y ∈ S', r' x y)
    (hlin : ∀ x ∈ S, ∀ z ∈ S, ∀ y w, r x y → r z w → ∀ s t : ℂ, r (s • x + t • z) (s • y + t • w))
    (heq : ∀ x ∈ S, ∀ x' ∈ S', ∀ y ∈ S, ∀ y' ∈ S', r x y → r' x' y' → p x = p' x' → p y = p' y') :
    ∃ T : Module.End ℂ P, (∀ x ∈ S, ∀ y ∈ S, r x y → p y = T (p x)) ∧
      ∀ x ∈ S', ∀ y ∈ S', r' x y → p' y = T (p' x) := by
  have hwd : ∀ x ∈ S, ∀ z ∈ S, ∀ y ∈ S, ∀ w ∈ S, r x y → r z w → p x = p z → p y = p w := by
    intro x hx z hz y hy w hw h1 h2 h3
    obtain ⟨x', hx', e⟩ : p x ∈ S'.map p' := hp' ▸ Submodule.mem_top
    obtain ⟨y', hy', h'⟩ := hex' x' hx'
    rw [heq x hx x' hx' y hy y' hy' h1 h' e.symm, heq z hz x' hx' w hw y' hy' h2 h' (h3.symm.trans e.symm)]
  have hsec : ∀ ξ : P, ∃ x ∈ S, ∃ y ∈ S, p x = ξ ∧ r x y := by
    intro ξ
    obtain ⟨x, hx, e⟩ : ξ ∈ S.map p := hp ▸ Submodule.mem_top
    obtain ⟨y, hy, h⟩ := hex x hx
    exact ⟨x, hx, y, hy, e, h⟩
  choose f hf g hg hfp hfg using hsec
  have hcomb : ∀ (ξ η : P) (s t : ℂ), p (g (s • ξ + t • η)) = s • p (g ξ) + t • p (g η) := by
    intro ξ η s t
    have := hwd _ (hf (s • ξ + t • η)) _ (add_mem (S.smul_mem s (hf ξ)) (S.smul_mem t (hf η))) _ (hg _) _
      (add_mem (S.smul_mem s (hg ξ)) (S.smul_mem t (hg η))) (hfg _)
      (hlin _ (hf ξ) _ (hf η) _ _ (hfg ξ) (hfg η) s t) (by rw [hfp, map_add (f := _), map_smul, map_smul, hfp, hfp])
    rw [this, map_add (f := _), map_smul, map_smul]
  let T : Module.End ℂ P :=
    { toFun := fun ξ => p (g ξ)
      map_add' := fun ξ η => by simpa using hcomb ξ η 1 1
      map_smul' := fun s ξ => by simpa using hcomb ξ ξ s 0 }
  refine ⟨T, fun x hx y hy h => ?_, fun x hx y hy h => ?_⟩
  · exact hwd x hx _ (hf (p x)) y hy _ (hg _) h (hfg _) (hfp _).symm
  · exact (heq _ (hf (p' x)) x hx _ (hg _) y hy (hfg _) h (hfp _)).symm

theorem acts_comb {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hex : ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T φ φ₁)
    {φ ψ φ₁ ψ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) (hψ : ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    (h₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T φ φ₁)
    (h₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T ψ ψ₁) (s t : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T (s • φ + t • ψ) (s • φ₁ + t • ψ₁) := by
  have hs : s • φ + t • ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) :=
    add_mem ((GlobalTheory.WeilM.SB _).smul_mem s hφ) ((GlobalTheory.WeilM.SB _).smul_mem t hψ)
  obtain ⟨χ, -, hχ⟩ := hex _ hs
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have e : ∀ α β : (κ → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (s • α + t • β) R =
      s • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) α R + t • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) β R := by
    intro α β
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have key : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) χ R =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (s • φ₁ + t • ψ₁) R := by
    rw [← hχ R (hR _ hs), e, map_add (f := _), map_smul, map_smul, h₁ R (hR φ hφ), h₂ R (hR ψ hψ), e]
  have hχe : χ = s • φ₁ + t • ψ₁ := by
    funext y
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    have hRz : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
      simpa using (hR φ hφ).1 0 _ hz
    have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (y i))
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
    exact mul_right_cancel₀ hR0 this
  rw [← hχe]
  exact hχ

theorem exists_localOp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a a' : ℕ)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ hv ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.W (GlobalTheory.AdelicU.evFin F v),
    ∃ T : Module.End ℂ (Rf.Pi v),
      (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, hv)) φ φ₁ → Rf.p v φ₁ = T (Rf.p v φ)) ∧
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, hv)) φ φ₁ → Rf.p' v φ₁ = T (Rf.p' v φ) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM v h hh
  have hex := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ Bs a a' Γ Xc om om' hM.triple v h hh
  have hex' := GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ Bs a a' Γ Xc om om' hM.triple v h hh
  exact descend _ _ (Rf.p v) (Rf.p' v) (hM.fin.onto v) (hM.fin.onto' v)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, h))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, h)))
    hex hex' (fun x hx z hz y w h1 h2 s t => acts_comb v (om (1, h)) hex hx hz h1 h2 s t) (hM.fin.equiv v h hh)

end GlobalTheory.LocalDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRowPlacementFiniteElementMatchesLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem rowPlacement_iota_eq {D : D7} {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.IndefR.RationalEmbedding.inst D)
    (ι : GA D (Yc D 0) ≃* I.GA) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) :
    ι = ((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)).toMulEquiv := by
  subst h
  have := eq_of_heq hι
  subst this
  rfl

theorem rowPlacement_exists : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (h : X.B.I = Formalism.IndefR.RationalEmbedding.inst D) (ι : GA D (Yc D 0) ≃* X.B.I.GA) (tS : GA D (Yc D 0)) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → IdempotentRealFixed D → HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → tS ∈ GfC (Yc D 0) → ((∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) → ConjLevel (tS)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h tS) → (∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) ∧ ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd ι tS c' := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X Gd h ι tS cG hlev hgrp hmod hhost hE0 hι hιE hpin htS hmove
  have hιeq : ι = (iotaX X h).toMulEquiv := rowPlacement_iota_eq h ι hι
  subst hιeq
  have hfirst : ∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)))
      (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)))
      ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2})
      (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) ∧ RowLevelMatchAt R F X h t := by
    obtain ⟨t, ht, hconj, hframe⟩ := _root_.GlobalTheory.SeeConj.exists_conj_level R F X h hlev hgrp hmod
    exact ⟨t, ht, hconj, _root_.GlobalTheory.rowLevelMatchAt_of_conjLevel R F X h hlev hgrp hmod cG t hιE hpin hE0 ht hconj hframe⟩
  obtain ⟨hconjS, hmatchS⟩ := hmove hfirst
  exact ⟨hfirst, _root_.GlobalTheory.SeeEval.evalTieT_of_levelMatch hDS R F X h hlev hgrp hmod hhost hιE Gd tS htS hconjS hmatchS⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarFiniteTensorEqDatumSmallModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_finiteTensor_eq_datum_smallModel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∀ f₀, IsDatumB (t := t) W e Γ (Finsupp.single (((), ρ.vT i j), ρ.vX i j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) →
    ∀ ι : ∀ w : Pl D.host.E, ((Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
      (Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ),
    (∀ w ∈ locPl G t, IsLagrModel Γ.M' W.ψ (w.under (𝓞 D.host.F)) (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w) (ι w)) →
    ∃ s : ℂ, s ≠ 0 ∧ ∀ ε, IsIdemSum ε (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Ψ (τ : TotT G (routeSmall t i j)),
      (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Ψ w)) →
      HasLocal B t ε (X := (i, j + 1)) (M := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩
        (IsLocVec W (.mu t i j) ε (ρ.vT i j)) (IsLocVec W (.chi i j) ε (ρ.vX i j)) τ Ψ →
      ∀ φ, IsFinPart Γ.M' X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ψ w) →
        IsDatumB W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (s • f₀) φ) := by
  first | exact @GlobalTheory.SmallPlaces.exists_scalar_datum | exact GlobalTheory.SmallPlaces.exists_scalar_datum | (intros; apply GlobalTheory.SmallPlaces.exists_scalar_datum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumLocalFunctionsEqPureTensorScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_localFunctions_eq_pureTensor_scalar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ f₀, IsDatumA (t := t) W e Γ (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) →
    ∀ ι : ∀ w : Pl D.host.E, ((Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
      (Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ),
    (∀ w ∈ locPl G t, IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) (ι w)) →
    ∃ s : ℂ, s ≠ 0 ∧ ∀ ε, IsIdemSum ε (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Ψ (τ : TotT G (routeBig t i j)),
      (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Ψ w)) →
      HasLocal B t ε (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
        (IsLocVec W (.chi i (j + 1)) ε (ρ.vX i (j + 1))) (IsLocVec W (.mu t (i + 1) j) ε (ρ.vT (i + 1) j)) τ Ψ →
      ∀ φ, IsFinPart Γ.M X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ψ w) →
        IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (s • f₀) φ) := by
  first | exact @GlobalTheory.FlipMatch.datum_placesA | exact GlobalTheory.FlipMatch.datum_placesA | (intros; apply GlobalTheory.FlipMatch.datum_placesA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapHeisenbergAndHomTransformation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFlatLaws

theorem flatS_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ f, IsThetaFunO ψ V W f → (∀ N : Mx D ρ ρ, (∀ i j, j ≤ i → N i j = 0) → flatS dV dW s (rat x₀) y (heisO ψ V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N)) f) = psiE ψ (upSum N) • flatS dV dW s (rat x₀) y f) ∧ ∀ ξ : Mx D σ V₀.rank, flatS dV dW s (rat x₀) y (heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) f) = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • flatS dV dW s (rat x₀) y f := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x₀ y _ f hf
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  refine ⟨fun N hN => ?_, fun ξ => ?_⟩
  · exact GlobalTheory.FlatShiftPf.flatAt_shift hψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν s.vU.unit.1 _ _ f N hN
  · exact GlobalTheory.FlatLawsDuality.flatAt_iso dV dW s.vS s.vT s.vU.ν _ _ hψ f hf ξ

end GlobalTheory.AscFlatLaws

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaEighth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LiftTypeDn

theorem hasTypeAt_of_approx {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (S : SPar) (ψ : GA D V → ℂ)
    (h : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ χ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S χ ∧ ∀ x ∈ C, ‖ψ x - χ x‖ < δ) :
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S ψ := by
  intro C hC δ hδ
  obtain ⟨χ, hχ, h1⟩ := h C hC (δ / 2) (by linarith)
  obtain ⟨ψ', hψ', h2⟩ := hχ C hC (δ / 2) (by linarith)
  refine ⟨ψ', hψ', fun x hx => ?_⟩
  have e : ψ x - ψ' x = (ψ x - χ x) + (χ x - ψ' x) := by ring
  rw [e]
  have := norm_add_le (ψ x - χ x) (χ x - ψ' x)
  linarith [h1 x hx, h2 x hx]

end GlobalTheory.LiftTypeDn
end
end

