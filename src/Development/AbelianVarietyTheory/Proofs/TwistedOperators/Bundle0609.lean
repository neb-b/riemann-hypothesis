module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairCompactLineAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0549
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingLimit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.KerStabCpt

theorem isHecke_quot' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_quot' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) (hk : k = n + m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isPair_small' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {a a' : ℕ} {G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E}
    {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W} {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') :
    GlobalTheory.ThK.IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_quot' h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_quot' h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem algD_eq_polData {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) : algD M B.ψ B.emb = GlobalTheory.ThK.PolData B M := by
  unfold algD GlobalTheory.ThK.PolData
  congr 1
  ext Φ
  constructor
  · rintro ⟨f, φ, hf, hφ, hv, rfl⟩; exact ⟨f, hf, φ, hφ, hv, rfl⟩
  · rintro ⟨f, hf, φ, hφ, hv, rfl⟩; exact ⟨f, φ, hf, hφ, hv, rfl⟩

end GlobalTheory.SquareAgree.KerStabCpt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardPairFirstInvariantCongruenceOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairFirst_invariant_congruenceOne : ∀ (D : D7) (A WW : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (Sf : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e Sf → ∀ (I : Ideal (𝓞 D.host.E)) (βA : GL (Fin A.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ((N : ℕ) : 𝓞 D.host.E) ∈ I → (∀ w ∈ Sf, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) → (∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1) → ∀ (κ : GA D WW) (z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), Formalism.L2.DIV.frGL βW z = Lev.finE WW κ → (∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin WW.rank) (Fin WW.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w) → ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (actO (GlobalTheory.Grid.neg A) WW 1 κ x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW x := by
  first | exact @GlobalTheory.StdFstInv.stdFst_actO | exact GlobalTheory.StdFstInv.stdFst_actO | (intros; apply GlobalTheory.StdFstInv.stdFst_actO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftInjectiveGoodPartJointEigenspace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

set_option maxHeartbeats 1000000

namespace GlobalTheory.InjEigen

theorem label_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ), ∃ h, GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h ∧ ∃ e : Eig D, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → GlobalTheory.Hk3.IsLab (Vc D j) P d → h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = e P d • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hOk hpg j c
  obtain ⟨h, hops, hnf⟩ :=
    (GlobalTheory.DefiniteOps.definite_ops R.toRealDat F.lv2 hch.base.lev hch.base.fam hch.base.models).2 j A3.A.fam.μ0
  have key : ∀ P d, ∃ a : ℂ, GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P →
      GlobalTheory.Hk3.IsLab (Vc D j) P d → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
        h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
          a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro P d
    by_cases hg : GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P
    · by_cases hl : GlobalTheory.Hk3.IsLab (Vc D j) P d
      · first
          | exact (Classical.em (Formalism.L2.DIV.conjPl P = P)).elim
              (fun hc => (GlobalTheory.InertEigScalar.inert_label_scalar R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
              (fun hc => (GlobalTheory.SplitEigen.label_scalar_split R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
          | exact (Classical.em (Formalism.DivisionValues.conjPl P = P)).elim
              (fun hc => (GlobalTheory.InertEigScalar.inert_label_scalar R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
              (fun hc => (GlobalTheory.SplitEigen.label_scalar_split R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
      · exact ⟨0, fun _ hl' => absurd hl' hl⟩
    · exact ⟨0, fun hg' => absurd hg' hg⟩
  choose e he using key
  exact ⟨h, hops, e, fun x hx P d hg hl => he P d hg hl x hx⟩

theorem inj_eig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (x y : (R.toCx3 F).FLC j A3.A.fam.μ0), x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c → (R.toCx3 F).θ' j A3.A.fam.μ0 x ≠ 0 → y ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c ⊓ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → (R.toCx3 F).θ' j A3.A.fam.μ0 y = 0 → y = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hinj hOk hpg j c x y hx hθx hy hθy
  obtain ⟨h, hops, e, he⟩ := label_eigensystem R F hok hch hex hOk hpg j c
  have hy' := Submodule.mem_inf.mp hy
  have hgood := GlobalTheory.goodV_of_goodL R F hok hch hex hOk hpg j y hy'.2
  clear hok hch hex hOk hpg hy
  have hθ : ∀ z : (R.toCx3 F).FLC j A3.A.fam.μ0, (R.toCx3 F).θ' j A3.A.fam.μ0 z =
      R.phs j • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j A3.A.fam.μ0) z := fun z => rfl
  have hp : R.phs j ≠ 0 := by
    intro h0
    apply hθx
    rw [hθ, h0]
    exact zero_smul ℂ _
  have hcj : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) ≠ 0 := by
    intro h0
    apply hp
    rw [← Formalism.IndefR.Links.cj_cj (twAt D.what₂.embLL A3.A.v0) (R.phs j), h0, map_zero]
  have hx0 : R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) ≠ 0 := by
    intro h0
    apply hθx
    rw [hθ]
    have h1 : Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j A3.A.fam.μ0) x = 0 := h0
    rw [h1]
    first
      | exact smul_zero (M := Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j _).H) (R.phs j)
      | exact smul_zero (M := Tw (twAt D.what₂.embLL A3.A.v0) _) (R.phs j)
      | (simp only [smul_zero]; rfl)
  have hy0 : R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) = 0 := by
    have h2 : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) = 0 := hθy
    exact (smul_eq_zero.mp h2).resolve_left hcj
  exact hinj j h hops e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) (fun P d hg hl => he x hx P d hg hl)
    (fun P d hg hl => he y hy'.1 P d hg hl) hx0 hgood hy0

end GlobalTheory.InjEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeMemUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

open scoped Matrix

namespace GlobalTheory.RealColAct

variable {D : D7}

theorem gramAt_of_gram_one {V : HSp D} (hV : HSpace.gram V = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold gramAt
  rw [hV]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem compAt_mem_unitary {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hV : HSpace.gram V = 1) (g : GA D V)
    (τ : D.what₂.Tau) : compAt θ τ (Formalism.L2.Theta.mt V g) ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
  have h := GlobalTheory.StdUnn.CartanMove.compAt_isom hθ V g τ
  rw [gramAt_of_gram_one hV, Matrix.mul_one] at h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact h

theorem transpose_mem_unitary {n : ℕ} {K : Matrix (Fin n) (Fin n) ℂ} (hK : K ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Kᵀ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have h2 : K * star K = 1 := Matrix.mem_unitaryGroup_iff.1 hK
  rw [Matrix.mem_unitaryGroup_iff']
  have e : star Kᵀ = (star K)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]; rfl
  rw [e, ← Matrix.transpose_mul, h2, Matrix.transpose_one]

def realCol (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) :
    GinfC V →* (D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ) where
  toFun g τ := ⟨(compAt θ τ (Formalism.L2.Theta.mt V ((g : GA D V)⁻¹)))ᵀ,
    transpose_mem_unitary (compAt_mem_unitary hθ hV _ τ)⟩
  map_one' := by
    funext τ
    apply Subtype.ext
    simp only [OneMemClass.coe_one, inv_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.transpose_one, Pi.one_apply]
  map_mul' g h := by
    funext τ
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_inv_rev, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, Matrix.transpose_mul, Pi.mul_apply]
    rfl

theorem realCol_apply (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) (g : GinfC V) (τ : D.what₂.Tau) :
    (realCol θ hθ V hV g τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) = (compAt θ τ (Formalism.L2.Theta.mt V ((g : GA D V)⁻¹)))ᵀ := rfl

end GlobalTheory.RealColAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopLevelInv

section Local

variable {k : Type} [Field k]

def colMove {G : Grid k} (j : ℕ) (κ : GL (Fin (topRank G (j + 1))) k) (x : ColArgs G) : ColArgs G :=
  Function.update (Function.update x j ((κ⁻¹).val * x j)) (j + 1) (x (j + 1) * κ.val)


open Classical in
def stepVol [MeasurableSpace k] (ν : Measure k) (n : Type) [Fintype n] (c : ℕ) (n' : Type) [Fintype n'] :
    Measure (StepVar n c n' → k) := Measure.pi fun _ => ν

theorem varsVol_eq [MeasurableSpace k] (G : Grid k) (ν : Measure k) :
    varsVol G ν = Measure.pi fun j : Fin (G.m - 1) => stepVol ν (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)) := rfl

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem gdet_of_mem_N {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) : gdet g = 1 := by
  refine (show N k n c p ≤ (Matrix.GeneralLinearGroup.det (n := n ⊕ Fin c) (R := k)).ker from
    (Subgroup.closure_le _).2 fun g hg => ?_) hg
  apply Units.ext
  change g.val.det = 1
  rw [(GlobalTheory.RootEx.Model.inN_tri hg).det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : g.val.toSquareBlock (lev p) a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [hg i j (by rw [hi, hj]), Matrix.one_apply, Matrix.one_apply]
    simp [Subtype.ext_iff]
  rw [this, det_one]

theorem gdet_of_mem_symN {g : GL (n ⊕ Fin c) k} (hg : g ∈ symN k n c) : gdet g = 1 :=
  (show symN k n c ≤ (Matrix.GeneralLinearGroup.det (n := n ⊕ Fin c) (R := k)).ker from
    sup_le (fun _ h => gdet_of_mem_N h) fun _ h => gdet_of_mem_N h) hg

theorem gdet_embX (g : GL n k) : gdet (embX c g) = gdet g :=
  Units.ext (by
    change (fromBlocks g.val 0 0 (1 : Matrix (Fin c) (Fin c) k)).det = g.val.det
    rw [det_fromBlocks_zero₂₁, det_one, mul_one])

theorem gdet_toFrame {G : Grid k} (hs : 1 ≤ G.s) {j : ℕ} (hj : j < G.m) (g : GL (Fin (G.rank (G.m, j))) k) :
    gdet (toFrame hs hj g) = gdet g :=
  Units.ext (det_submatrix_equiv_self _ _)

theorem exists_of_mem_symPr {G : Grid k} (hs : 1 ≤ G.s) {J : G.Level} {g : G.VertexGroup} {j : ℕ} (hj : j < G.m)
    {κ : GL (Fin (topRank G j)) k} (hκ : κ ∈ symPr (conjLevel hs J g hj)) :
    ∃ u ∈ J (G.m, j), ∃ v ∈ symN k (Fin (topRank G j)) (G.m - 1 - j),
      toFrame hs hj (g (G.m, j) * u * (g (G.m, j))⁻¹) = v * embX _ κ ∧ gdet κ = gdet u := by
  obtain ⟨v, hv, _, ⟨u, hu, rfl⟩, h⟩ := hκ
  refine ⟨u, hu, v, hv, h, ?_⟩
  have := congrArg gdet h
  rw [gdet_mul, gdet_of_mem_symN hv, one_mul, gdet_embX] at this
  rw [← this]
  change gdet (toFrame hs hj (g (G.m, j) * u * (g (G.m, j))⁻¹)) = _
  rw [gdet_toFrame, gdet_mul, gdet_mul, mul_right_comm, ← gdet_mul, mul_inv_cancel]
  simp

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def movedPt (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1)))
    (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T))) :
    ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) :=
  Function.update (Function.update x ⟨j, by omega⟩ (actO _ _ 1⁻¹ (g : GA D (G.V (.top (j + 1))))⁻¹ (x ⟨j, by omega⟩)))
    ⟨j + 1, hj⟩ (actO _ _ (g : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ (x ⟨j + 1, hj⟩))

theorem movedFn_apply (S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1)))
    (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T))) (j' : Fin D.R.m) :
    movedFn S d j hj g j' (x j') = (d.1 j').fn (movedPt t j hj g x j') := by
  rcases eq_or_ne j' ⟨j + 1, hj⟩ with rfl | h1
  · simp only [movedFn, movedPt, Function.update_self]
  rcases eq_or_ne j' ⟨j, by omega⟩ with rfl | h2
  · simp only [movedFn, movedPt, Function.update_of_ne h1, Function.update_self]
  · simp only [movedFn, movedPt, Function.update_of_ne h1, Function.update_of_ne h2]

def kapAt (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (w : Pl D.host.E) :
    GL (Fin (topRank (locGrid G t w) (j + 1))) (Kw w) :=
  inBasis (topRank_eq G t w hj.le) (S.βp (j + 1)) w (finG (G.V (.top (j + 1))) k)

theorem kapAt_mem (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {j : ℕ} (hj : j + 1 < D.R.m)
    {k : FinPt G (.top (j + 1))} (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) (w : locPl G t) :
    kapAt S t j hj k w ∈ (S.term t Φ β w).pr (j + 1) j.succ_pos hj :=
  Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk).1 w

theorem givenLevel_col (t : T) (w : Pl D.host.E) (j : ℕ) : givenLevel G t w (D.R.m, j + 1) = KO (Kw w) _ := by
  have key : ∀ i, 0 < i → givenLevel G t w (i, j + 1) = KO (Kw w) _ := by
    rintro (_ | i) h
    · omega
    · rfl
  exact key _ (by have := D.R.two_le_m; omega)

theorem valuation_gdet_kapAt (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {j : ℕ} (hj : j + 1 < D.R.m)
    {k : FinPt G (.top (j + 1))} (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) (w : locPl G t) :
    valuation (Kw w.1) (gdet (kapAt S t j hj k w) : Kw w.1) = 1 := by
  obtain ⟨u, hu, -, -, -, h⟩ := exists_of_mem_symPr (G := locGrid G t w) one_le_sLen hj (kapAt_mem S hj hk w)
  rw [h]
  exact valuation_gdet_of_mem_KO (givenLevel_col t w.1 j ▸ hu)

end GlobalTheory.TopLevelInv

end
end

