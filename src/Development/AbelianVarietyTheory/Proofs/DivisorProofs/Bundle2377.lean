module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCochainsEqDeRhamCochainsSmoothLif
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsomorphismMonHomDescendsFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ

namespace GlobalTheory.IsoFinExt

theorem isPullback_compare {X S L S' T : Scheme.{0}} (a : X ⟶ S) (b : L ⟶ S) (i : S' ⟶ S) (j : T ⟶ L)
    (l : T ⟶ S') (hc : l ≫ i = j ≫ b) :
    ∃ q : pullback (pullback.snd a b) j ⟶ pullback a i,
      q ≫ pullback.fst a i = pullback.fst _ _ ≫ pullback.fst a b ∧
      IsPullback q (pullback.snd _ _) (pullback.snd a i) l := by
  have hw : (pullback.fst (pullback.snd a b) j ≫ pullback.fst a b) ≫ a = (pullback.snd _ _ ≫ l) ≫ i := by
    rw [Category.assoc, pullback.condition, pullback.condition_assoc, Category.assoc, hc]
  refine ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback a i)
  rw [pullback.lift_fst, hc]
  exact (IsPullback.of_hasPullback (pullback.snd a b) j).paste_horiz (IsPullback.of_hasPullback a b)

theorem isIso_of_compare {X₁ X₂ S L S' T : Scheme.{0}} (a₁ : X₁ ⟶ S) (a₂ : X₂ ⟶ S) (b : L ⟶ S) (i : S' ⟶ S)
    (j : T ⟶ L) (l : T ⟶ S') [Surjective l] [Flat l] [QuasiCompact l] (hc : l ≫ i = j ≫ b)
    (f : pullback a₁ b ⟶ pullback a₂ b) [IsIso f] (hf : f ≫ pullback.snd _ _ = pullback.snd _ _)
    (f' : pullback a₁ i ⟶ pullback a₂ i) (hf' : f' ≫ pullback.snd _ _ = pullback.snd _ _)
    (h : ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback a₁ b) (p' : Z ⟶ pullback a₁ i) (t : Z ⟶ T),
      p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ j →
      p' ≫ pullback.snd _ _ = t ≫ l → p ≫ f ≫ pullback.fst _ _ = p' ≫ f' ≫ pullback.fst _ _) :
    IsIso f' := by
  obtain ⟨q₁, e₁, H₁⟩ := isPullback_compare a₁ b i j l hc
  obtain ⟨q₂, e₂, H₂⟩ := isPullback_compare a₂ b i j l hc
  let F : pullback (pullback.snd a₁ b) j ⟶ pullback (pullback.snd a₂ b) j :=
    pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hf]) (by simp)
  have hF₁ : F ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f := pullback.lift_fst _ _ _
  have hF₂ : F ≫ pullback.snd _ _ = pullback.snd _ _ := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hw : q₁ ≫ f' = F ≫ q₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, e₂, ← Category.assoc F, hF₁, Category.assoc]
      exact (h _ _ q₁ _ e₁.symm pullback.condition H₁.w).symm
    · rw [Category.assoc, Category.assoc, hf', H₂.w, ← Category.assoc, hF₂, H₁.w]
  have H : IsPullback q₁ F f' q₂ := by
    refine IsPullback.of_bot ?_ hw H₂
    rw [hF₂, hf']
    exact H₁
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) q₂ :=
    ⟨⟨MorphismProperty.of_isPullback H₂.flip ‹Surjective l›,
      MorphismProperty.of_isPullback H₂.flip ‹Flat l›⟩,
      MorphismProperty.of_isPullback H₂.flip ‹QuasiCompact l›⟩
  have hF : IsIso F := inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
    H.flip hq hF

theorem exists_finite_iso : ∀ (K L : Type) [Field K] [CharZero K] [Field L] (β : K →+* L) (A₁ A₂ : Over (Sp K)) [GrpObj A₁] [GrpObj A₂], IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ (f : (Over.pullback (spMap β)).obj A₁ ≅ (Over.pullback (spMap β)).obj A₂), IsMonHom f.hom → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω : Type) (_ : Field Ω) (j : L →+* Ω) (l : K' →+* Ω) (φ : (Over.pullback (spMap io)).obj A₁ ≅ (Over.pullback (spMap io)).obj A₂), io.Finite ∧ l.comp io = j.comp β ∧ IsMonHom φ.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback A₁.hom (spMap β)) (p' : Z ⟶ pullback A₁.hom (spMap io)) (t : Z ⟶ Sp Ω), p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ spMap j → p' ≫ pullback.snd _ _ = t ≫ spMap l → p ≫ f.hom.left ≫ pullback.fst _ _ = p' ≫ φ.hom.left ≫ pullback.fst _ _ := by
  intro K L _ _ _ β A₁ A₂ _ _ h₁ h₂ f hf
  obtain ⟨K', _, io, Ω, _, j, l, f', hfin, hc, hm, h⟩ := _root_.GlobalTheory.HomFinExt.exists_finite_hom K L β A₁ A₂ h₁ h₂ f.hom hf
  have hc' : spMap l ≫ spMap io = spMap j ≫ spMap β := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hc]
  have : Flat (spMap l) := by
    rw [Flat.SpecMap_iff]
    letI := l.toAlgebra
    exact (inferInstance : Module.Flat K' Ω)
  have : Surjective (spMap l) := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hl : IsIso f.hom.left := inferInstanceAs (IsIso ((Over.forget _).map f.hom))
  have : IsIso f'.left :=
    @isIso_of_compare _ _ _ _ _ _ A₁.hom A₂.hom (spMap β) (spMap io) (spMap j) (spMap l) _ _ _ hc'
      f.hom.left hl (Over.w f.hom) f'.left (Over.w f') h
  have : IsIso ((Over.forget _).map f') := this
  have : IsIso f' := isIso_of_reflects_iso f' (Over.forget _)
  exact ⟨K', inferInstance, io, Ω, inferInstance, j, l, asIso f', hfin, hc, hm, h⟩

end GlobalTheory.IsoFinExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetsOnCopiesAny
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.PowGerm GlobalTheory.PtTie GlobalTheory.RefSum
open GlobalTheory.ThetaLeast

open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.JetsLevelZero

theorem jets_on_copies_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∀ (C : IntegralChartA3 Xo c T io y),
    FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n : ℕ), 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (q D : ℕ), 4 * D + 4 ≤ q → (D : ℝ) * M0 < q →
  ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f →
    ∃ (s : Fam D'.toPre F q) (σ' : U'.toUnifPre.SecGF F q) (g : PS F n (chD C.ch)) (lam : F),
      NuGe D' (sumQ pD.xe Q) F v q s 0 ∧ U'.toUnifPre.ExpandsG F q σ' s ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' g ∧
      lam ≠ 0 ∧ (∃ ρ : ℚ, v lam = (ρ : WithTop ℚ) ∧ (ρ : ℝ) ≤ (D : ℝ) ^ 2 * Φ / q) ∧
      ∀ e : Fin n × Fin (chD C.ch) →₀ ℕ, e.degree ≤ D →
        MvPowerSeries.coeff e g = MvPowerSeries.coeff e (lam • MvPowerSeries.map (algebraMap T.Fr F) f) := by
  obtain ⟨L1, L2, -, L4, -⟩ := GlobalTheory.firstFiveLaws
  have TB := GlobalTheory.twistBaseChange_and_valuation_statements.1
  intro E _ _ _ H Dw l Xo c inst hstar
  obtain rfl : inst = H.starRing := starSt E H inst hstar
  letI := H.starRing
  intro T io y C htr P ϖ hϖ Q hQ Φ M0 r b hΦ0 hΦ hM n _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ _ v hv q D hq hD f hf
  choose f₀ hf₀ using hf
  obtain ⟨τ, hτ, htrunc, hgerm⟩ := frameNSt_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hu := _root_.GlobalTheory.PowGerm.univPow T.V C.I.G.G G' n (chD C.ch) pG C.xT (_root_.GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C)
  obtain ⟨r', b', h1, h2⟩ := GlobalTheory.PowJets.exists_basis_bounds pD.xe Q (Q_zero hϖ P.D hQ) (RoundingSumAlt.Q_nonneg hϖ hQ) Φ M0 b hΦ hM
  have hD' : (D : ℝ) * max M0 0 < q := by
    rcases le_total M0 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact_mod_cast (by omega : 0 < q)
    · rwa [max_eq_left h]
  obtain ⟨s, σ', g, lam, a1, a2, a3, a4, a5, a6⟩ := GlobalTheory.UnifJets.jets L1 L2 L4 TB T.V ϖ hϖ D' A' G' U' (Fin n × Fin (chD C.ch))
    (zV pG C.xT) hu τ hτ (htrunc htr) (sumQ pD.xe Q) (GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) Φ (max M0 0) r' b' hΦ0
    (le_max_right _ _) h1 h2 F v hv q D hq hD' (fun e => f₀ e)
  refine ⟨s, σ', g, lam, a1, a2, (hgerm F q σ' g).2 a3, a4, a5, fun e he => ?_⟩
  rw [a6 e he, map_smul, MvPowerSeries.coeff_map, ← hf₀ e, smul_eq_mul, ← IsScalarTower.algebraMap_apply]
  rfl

theorem rPoint_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a) (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z)))
    (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G']
    (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n)
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → 1 ≤ n →
  ∀ (α : 𝓞 E) (N Dg : ℕ), α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) → IsUnit ((N : ℕ) : T.V) →
    4 * Dg + 4 ≤ N → (Dg : ℝ) * M0 < N →
  ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 → ThFrame D' ϖ F θ →
    PullAl D' F oD' α 1 N θ θα →
  ∀ (I : Type) [Fintype I] (Pi : I → MvPolynomial (LtN Dw n) F) (a : I → F), (∀ i, 0 ≤ v (a i)) →
    (∑ i, a i • Pi i).totalDegree ≤ Dg → ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f → ∀ gm : ℚ,
    letI := io.toAlgebra
    v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) (MvPowerSeries.map (algebraMap T.Fr F) f) (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (∑ i, a i • Pi i)) = (gm : WithTop ℚ) →
    ∃ (i : I) (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F)
      (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (σ' : U'.toUnifPre.SecGF F (1 * N)) (h : PS F n (chD C.ch)) (ρ : ℚ),
      w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D' F (1 * N) p w ζ ∧ QkToAkU U'.toUnifPre F (1 * N) p x ∧
      (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) ∧ PhiRel D'.toPre F (1 * N) p w θα t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
      U'.toUnifPre.ExpandsG F (1 * N) σ' t ∧ IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (1 * N) σ' h ∧
      v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) h (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (Pi i)) = (ρ : WithTop ℚ) ∧
      (ρ : ℝ) ≤ gm + (Dg : ℝ) ^ 2 * Φ / N := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have hT := GlobalTheory.twistBaseChange_and_valuation_statements.1
  intro E _ _ _ H Dw l Xo c
  let _ := H.starRing
  intro T io y C hFT P hP ϖ hϖ Q hQ F _ _ _ _ _ _ v hv I Φ M0 r b hΦ hb hbw n D' A' G' _ _ pD pA pG U' PU _ oD' hx hoD hn
    α N Dg hα hcop hu hN hM θ θα hθ hθF hθα J _ Pi a ha hdeg f hf gm hval
  let _ := io.toAlgebra
  have hN1 : 1 ≤ 1 * N := by omega
  obtain ⟨s, σ', g, lam, hs, hσ', hg, -, ⟨ρl, hlam, hρl⟩, hjet⟩ :=
    jets_on_copies_any E H Dw l Xo c (fun _ => rfl) T io y C hFT P ϖ hϖ Q hQ Φ M0 r b hΦ hb hbw n hn D' A' G'
      pD pA pG U' PU F v hv (1 * N) Dg (by omega) (by rwa [Nat.one_mul]) f hf
  obtain ⟨m, p, x, w, ζ, t, cf, e1, e2, e3, e4, e5, e6⟩ := GlobalTheory.SmallTranslate.span_pow h1 h2 h3 h4 h5 hT T.V E H C.I.G P Dw ϖ hϖ Q hQ F v hv I
    n D' A' G' pD pA pG U' PU oD' hx hoD α N (by omega) hα hcop hu θ θα hθ hθF hθα s hs
  obtain ⟨τ, hτ, hτT, hiff⟩ := GlobalTheory.PowGerm.frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := _root_.GlobalTheory.PowGerm.univPow T.V C.I.G.G G' n _ pG C.xT (_root_.GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C)
  obtain ⟨huniq, hlin, hex⟩ := GlobalTheory.GermBasic.main T.V D' A' G' U' _ _ hz τ hτ F (1 * N)
  have hbij := (GlobalTheory.expandsG_bijective_of_dvr h1 h2 h4 hT T.V D' A' G' U' F (1 * N) hN1).2
  choose σ hσ using fun j => (hbij (t j)).exists
  choose h hh using fun j => hex (hτT hFT) (σ j)
  have hsum : g = ∑ j, cf j • h j := by
    let σ₀ : U'.toUnifPre.SecGF F (1 * N) := GlobalTheory.ExpansionLinear.secComb
      (fun j => Out.scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj G')).left (cf j)) σ
    have k1 := GlobalTheory.GroupExpansionLinear.expandsG_sum T.V D' A' G' U' F (1 * N) m cf σ t σ₀ hσ (fun _ => rfl)
    rw [← e6] at k1
    have k2 : σ' = σ₀ := (hbij s).unique hσ' k1
    exact huniq σ' _ _ ((hiff F _ σ' g).1 hg) (hlin m cf σ h σ' hh (fun _ => by rw [k2]; rfl))
  obtain ⟨n1, n2, n3⟩ := GlobalTheory.PowGerm.nabJet _ _ _ C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) n
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
  have k1 := n1 (∑ i, a i • Pi i) _ _ (fun e he => hjet e (he.trans hdeg))
  have k2 := n2 (∑ i, a i • Pi i) Unit (fun _ => lam) (fun _ => MvPowerSeries.map (algebraMap T.Fr F) f)
  rw [Finset.univ_unique, Finset.sum_singleton, Finset.sum_singleton] at k2
  have k3 := n2 (∑ i, a i • Pi i) (Fin m) cf h
  rw [← hsum, k1, k2, Finset.sum_congr rfl fun j _ => congrArg (cf j * ·) (n3 (h j) J a Pi)] at k3
  have k4 := congrArg v k3
  rw [v.map_mul, hlam] at k4
  obtain ⟨i, j, ρ, hρ, hle⟩ := GlobalTheory.SmallTranslate.exists_term_le v a cf _ ha e5 (ρl + gm)
    (k4.symm.trans (by rw [WithTop.coe_add]; exact congrArg _ hval))
  obtain ⟨t₀, ht₀, ht⟩ := e4 j
  refine ⟨i, p j, w j, ζ j, x j, t₀, t j, σ j, h j, ρ, (e3 j).1, (e3 j).2.1, (e3 j).2.2, e1 j, e2 j, ht₀, ht, hσ j,
    (hiff F _ _ _).2 (hh j), hρ, ?_⟩
  rw [Nat.one_mul] at hρl
  have : (ρ : ℝ) ≤ ρl + gm := by exact_mod_cast hle
  linarith

end GlobalTheory.JetsLevelZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelExtends
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LineNorm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped Classical

namespace GlobalTheory.LabelExt

section Gen

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem lift_finite [IsIntegrallyClosed R] {X S : Scheme.{0}} (f : X ⟶ S) [IsFinite f] (y : Sp R ⟶ S) (w : Sp K ⟶ X)
    (h : w ≫ f = spMap (algebraMap R K) ≫ y) : ∃ v : Sp R ⟶ X, v ≫ f = y ∧ spMap (algebraMap R K) ≫ v = w :=
  _root_.UpperTheory.Reformulated.B.Yt7.lift_finite f y w h

theorem ext_frac {S : Scheme.{0}} {G : Over S} [IsSeparated G.hom] {y : Sp R ⟶ S} {u v : Over.mk y ⟶ G}
    (h : spMap (algebraMap R K) ≫ u.left = spMap (algebraMap R K) ≫ v.left) : u = v := by
  haveI : IsDominant (spMap (algebraMap R K)) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]; exact bot_le)
  haveI : IsReduced (Over.mk y).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  ext1
  exact ext_of_isDominant_of_isSeparated G.hom (by rw [Over.w u, Over.w v]) (spMap (algebraMap R K)) h

theorem lift_tors [IsIntegrallyClosed R] {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) {q : ℕ}
    (hq : q ≠ 0) {y : Sp R ⟶ S} {y' : Sp K ⟶ S} (hy : spMap (algebraMap R K) ≫ y = y') (w : Over.mk y' ⟶ G)
    (hw : w ^ q = 1) : ∃ v : Over.mk y ⟶ G, spMap (algebraMap R K) ≫ v.left = w.left := by
  haveI := (AbTorsionAnyBase.isFinite_and_flat_torsion S G hG q (Nat.one_le_iff_ne_zero.2 hq)).1
  have e : w ≫ mulN G q = CartesianMonoidalCategory.toUnit _ ≫ η[G] := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hw]; rfl
  let w₁ : Over.mk y' ⟶ torsion G q := Limits.pullback.lift w _ e
  have h₁ : w₁ ≫ torsion.ι G q = w := Limits.pullback.lift_fst _ _ _
  obtain ⟨v, hv, hv'⟩ := lift_finite (torsion G q).hom y w₁.left ((Over.w w₁).trans hy.symm)
  refine ⟨(Over.homMk v hv : Over.mk y ⟶ torsion G q) ≫ torsion.ι G q, ?_⟩
  rw [← h₁, Over.comp_left, Over.comp_left, ← hv', Category.assoc]
  rfl

end Gen

end GlobalTheory.LabelExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamPtsPull
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensPair

theorem lamPts_comp {S : Scheme.{0}} {B T T' : Over S} [GrpObj B] (f : T' ⟶ T) (x y : T ⟶ B) (l : Fin 4) :
    f.left ≫ GlobalTheory.PolDeg.lamPts x y l = GlobalTheory.PolDeg.lamPts (f ≫ x) (f ≫ y) l := by
  fin_cases l <;> simp [GlobalTheory.PolDeg.lamPts, ← Over.comp_left, MonObj.comp_mul]

theorem lamPts_pull {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) (l : Fin 4) :
    (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A).left ≫
      GlobalTheory.PolDeg.lamPts (fst D'.P.A D'.P.A ≫ T.pr i) (snd D'.P.A D'.P.A ≫ T.pr j) l =
    GlobalTheory.PolDeg.lamPts (if i = i₀ then fst D.P.A D.P.A else 1) (snd D.P.A D.P.A ^ m j i₀) l := by
  have h1 : (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A) ≫
      fst D'.P.A D'.P.A ≫ T.pr i = if i = i₀ then fst D.P.A D.P.A else 1 := by
    rw [lift_fst_assoc, Category.assoc, T.inc_pr']
    split_ifs <;> simp
  have h2 : (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A) ≫
      snd D'.P.A D'.P.A ≫ T.pr j = snd D.P.A D.P.A ^ m j i₀ := by
    rw [lift_snd_assoc, Category.assoc, Category.assoc, T.act_pr]
    have e : ∀ k, (snd D.P.A D.P.A ≫ T.inc i₀) ≫ T.pr k = if k = i₀ then snd D.P.A D.P.A else 1 := fun k => by
      rw [Category.assoc, T.inc_pr']; split_ifs <;> simp
    rw [← Category.assoc]
    change preHom (snd D.P.A D.P.A ≫ T.inc i₀) (∏ k, T.pr k ^ m j k) = _
    rw [map_prod]
    simp only [map_zpow]
    change ∏ k, ((snd D.P.A D.P.A ≫ T.inc i₀) ≫ T.pr k) ^ m j k = _
    simp only [e]
    rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
  rw [lamPts_comp, h1, h2]

theorem xe_xi {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ i : Fin r) (a : D.X) : T.xe (T.xi i₀ a) i = if i = i₀ then a else 0 := by
  simp [Tens.xi, Pi.single_apply]

theorem c_zsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (n : ℤ) (b : D.X) : D.c (n • b) = D.c b ^ n := by
  let φ : D.X →+ Additive (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (D.c x)) (fun a b => by
      show Additive.ofMul (D.c (a + b)) = Additive.ofMul (D.c a * D.c b)
      rw [D.c_add]; rfl)
  exact congrArg Additive.toMul (map_zsmul φ n b)

theorem pt_pull {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (a b : D.X) (a' b' : D'.X)
    (ha : ∀ i, T.xe a' i = if i = i₀ then a else 0) (hb : ∀ j, T.xe b' j = m j i₀ • b) :
    (lift (toUnit (TK R) ≫ D'.c a') (toUnit (TK R) ≫ D'.c b') : TK R ⟶ G2 D'.P.A) =
      lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) ≫
        lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) := by
  have c0 : D.c 0 = 1 := by
    have := c_zsmul D 0 a; rwa [zero_smul, zpow_zero] at this
  rw [comp_lift, lift_fst_assoc, lift_snd_assoc]
  congr 1
  · refine T.lim.hom_ext fun ⟨i⟩ => ?_
    simp only [Fan.mk_π_app, Category.assoc]
    rw [T.c_pr, ha, T.inc_pr']
    split_ifs <;> simp [c0]
  · refine T.lim.hom_ext fun ⟨i⟩ => ?_
    simp only [Fan.mk_π_app, Category.assoc]
    rw [T.c_pr, hb, c_zsmul, T.act_pr]
    have e : ∀ k, (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ T.pr k = if k = i₀ then toUnit (TK R) ≫ D.c b else 1 := fun k => by
      rw [Category.assoc, Category.assoc, T.inc_pr']; split_ifs <;> simp
    calc toUnit (TK R) ≫ D.c b ^ m i i₀ = (toUnit (TK R) ≫ D.c b) ^ m i i₀ := map_zpow (preHom (toUnit (TK R))) _ _
      _ = ∏ k, ((toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ T.pr k) ^ m i k := by
        simp only [e]
        rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
      _ = (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ ∏ k, T.pr k ^ m i k := by
        change _ = preHom (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) (∏ k, T.pr k ^ m i k)
        rw [map_prod]
        simp only [map_zpow]
        rfl
      _ = _ := by simp only [Category.assoc]

end GlobalTheory.TensPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsBijectiveDegreeOneTwo
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem lift_forms_bij : ∀ (D : Data) (Λ : Lift D) (U : AffOp D.X),
    Function.Bijective (fun ω : Ω[Sec D.s U.unop.1⁄D.R] ↦
      (Submodule.Quotient.mk ((Λ.semi U).m1 ω) : K1 D.R (Λ.L.obj U).δ)) ∧
    Function.Bijective (fun x : Om D.R (Sec D.s U.unop.1) 2 ↦
      (Submodule.Quotient.mk ((Λ.semi U).mOm 2 x) : K D.R (Λ.L.obj U).δ 2)) :=
  fun _ Λ U ↦ ⟨LiftRes.liftOneFormsToCompatible_bijective Λ U, LiftRes.fm_bij Λ U 2⟩

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEighthPowerGroupPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem lift_left_comp {T T' : Scheme.{0}} {B C : Over T} {B' C' : Over T'} {φB : B'.left ⟶ B.left}
    {χ : C'.left ⟶ C.left} {χ₂ : (C' ⊗ C').left ⟶ (C ⊗ C).left} (hsq : IsSquare χ χ₂)
    (x y : B ⟶ C) (x' y' : B' ⟶ C') (hx : x'.left ≫ χ = φB ≫ x.left) (hy : y'.left ≫ χ = φB ≫ y.left) :
    (lift x' y').left ≫ χ₂ = φB ≫ (lift x y).left := by
  have f1 : (lift x y).left ≫ (fst C C).left = x.left := congrArg (fun q => q.left) (lift_fst x y)
  have f2 : (lift x y).left ≫ (snd C C).left = y.left := congrArg (fun q => q.left) (lift_snd x y)
  have f1' : (lift x' y').left ≫ (fst C' C').left = x'.left := congrArg (fun q => q.left) (lift_fst x' y')
  have f2' : (lift x' y').left ≫ (snd C' C').left = y'.left := congrArg (fun q => q.left) (lift_snd x' y')
  apply pullback.hom_ext
  · show (_ ≫ _) ≫ (fst C C).left = (_ ≫ _) ≫ (fst C C).left
    rw [Category.assoc, hsq.1, ← Category.assoc, f1', hx, Category.assoc, f1]
  · show (_ ≫ _) ≫ (snd C C).left = (_ ≫ _) ≫ (snd C C).left
    rw [Category.assoc, hsq.2, ← Category.assoc, f2', hy, Category.assoc, f2]

theorem lbIso_eighth_pull : ∀ {T T' : Scheme.{0}} {B C : Over T} {B' C' : Over T'} {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} {χ₂ : (C' ⊗ C').left ⟶ (C ⊗ C).left} (Q : LB (C ⊗ C).left) (Q' : LB (C' ⊗ C').left) (L : LB B.left) (L' : LB B'.left) (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (W : Matrix (Fin 8) (Fin 8) ℤ), Q.IsLB → Q'.IsLB → L.IsLB → L'.IsLB → IsSquare χ χ₂ → LBIso Q' (Q.pull χ₂) → (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) → LBIso L' (L.pull φB) → LBIso L (LB.LinComb Q (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → LBIso L' (LB.LinComb Q' (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) := by
  intro T T' B C B' C' φB χ χ₂ Q Q' L L' pr pr' W hQ hQ' hL hL' hsq HQ hpr h1 hLL
  have h3 := GlobalTheory.ShapePull.iso_linComb_pull HQ (K := Fin 8 × Fin 8)
    (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2) φB (fun ab => lift_left_comp hsq _ _ _ _ (hpr ab.1) (hpr ab.2))
  have h2 := GlobalTheory.SiegelPullComp.iso_pull φB hLL
  have lc : (LB.LinComb Q (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
      (fun ab => W ab.1 ab.2)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hQ _ _
  have lc' : (LB.LinComb Q' (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left)
      (fun ab => W ab.1 ab.2)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hQ' _ _
  exact LBIso.trans hL' (pull_isLB hL φB) lc' h1
    (LBIso.trans (pull_isLB hL φB) (pull_isLB lc φB) lc' h2 h3.symm)

end GlobalTheory.Poinc.Eq8
end

