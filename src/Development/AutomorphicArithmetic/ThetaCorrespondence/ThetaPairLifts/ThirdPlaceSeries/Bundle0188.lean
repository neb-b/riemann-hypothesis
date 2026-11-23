module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0685
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0114
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0690
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0092
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0066
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0127
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0036
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0045
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0053
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0115
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0170
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0167
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0182

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePlacesCover
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.TypePlacesCover
variable {D : D7}
end GlobalTheory.TypePlacesCover
open GlobalTheory.TypePlacesCover in
theorem GlobalTheory.TypePlacesCover.gPlaces_all_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → GPlaces (Dof x) :=
  fun _ => StepW.of_all fun _ _ _ _ _ _ _ _ _ x _ => gPlaces (Dof x)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValuesAsToricSums
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
noncomputable section
namespace GlobalTheory.ThmARatio
open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols Formalism.L2.Host
end GlobalTheory.ThmARatio
theorem GlobalTheory.ThmARatio.values_as_toric_sums_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → (∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c : Option Bool,
    ∃ x, IsTor d.G i j s (fam d.G p.P.A3.A.μ0 i j c) x ∧ x ≠ 0 ∧ (∀ Λ, GlobalTheory.CMVal.IsHeckeL (fam d.G p.P.A3.A.μ0 i j c) Λ → x = Λ s) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) Λ x)) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ), 1 ≤ s → s ≤ halfRank D i j →
    GlobalTheory.CMVal.IsHeckeL ((nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) * p.Tp.psi w) Λ → GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) Λd →
    ∃ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ∧
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ ∧ T₀ ≠ 0 ∧ Λd s = T₀ ∧
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) ∧
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) ∧ Λ s = T ψc := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d _ hfit _ hF hTor w hw i j s Λ Λd hs1 hs2 hΛ hΛd
  obtain ⟨_, _, hfd, hb, -⟩ := hF
  have hχ : fam d.G p.P.A3.A.μ0 i j (some (decide (D.what₂.places.resChar w = D.host.pde))) =
      nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) := by
    unfold fam GlobalTheory.FunObj.SqNum.delOf Formalism.L2.Host.CharFrame.delAt
    by_cases h : D.what₂.places.resChar w = D.host.pde
    · simp only [h, decide_true, cond_true, if_true]
    · simp only [h, decide_false, cond_false, if_false]
  obtain ⟨T₀, ⟨hv, h0⟩, hne, hL, -⟩ := hTor i j s hs1 hs2 (some (decide (D.what₂.places.resChar w = D.host.pde)))
  rw [hχ] at hv h0 hL
  have hP := p.Tp.psi_is w hw
  obtain ⟨a, ha⟩ := hP.ord
  have hQ := (GlobalTheory.ToricDenom.placesBelow_splitCoprimeConductor_of_admissible (hfit.1.cond w hw) (𝔣 := GlobalTheory.FunObj.SqNum.condF d.G.pl) fun P h =>
    (hfit.1.list _ (hfit.1.setting.inW1 hw)).1 P (GlobalTheory.ThmARatio.dvd_cond0 d.G.pl _ h)).1
  obtain ⟨ψc, T, h1, h2, h3⟩ := GlobalTheory.ThmARatio.twisted_value hfd.2.2.2.2.2.2.1 hfd.2.2.1 hs1 hb hQ hv
    (pow_ne_zero a (D.what₂.places.resChar_prime w).ne_zero) ha hP.triv hP.tame hP.ram hΛ
  exact ⟨T₀, ψc, T, hv, h0, hne, (hL Λd hΛd).symm, h1, h2, h3⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightOnePlacesFiniteOfWitness
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
set_option maxHeartbeats 4000000 in
theorem zscale_f0_of_witness_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) (hsc : q.O.L.sc = K.s) :
    HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)) := by
  have hK : DV.KapDef (q.w.D q.Z) := b.R.T.what₂.ka
  have hB : ∀ Zs, HEq ((_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b).Zsc Zs).F0 (F0K K.s (q.w.D q.Z)) := by
    intro Zs
    apply heq_of_eq
    funext y j
    rw [← hsc]
    exact (forcedContent_eq_closedContent_numericalDatum _ _ _ _ hK y j).symm
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  have hX := y.eq ▸ hB
  letI := a.x.grp
  letI := a.x.fin
  have hX' : ∀ Zs : DefSub a.x.A3.fam3.amb3, HEq (a.x.F.Zsc Zs).F0 (F0K K.s (q.w.D q.Z)) := hX
  dsimp only
  clear * - hX'
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x', pack, _⟩ := a
  dsimp only at hX' ⊢
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x'
  dsimp only at pack hX' ⊢
  cases pack
  exact hX' _
set_option maxHeartbeats 4000000 in
theorem weight_one_places_finite_of_witness : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K) (c : ℝ)
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → q.O.L.sc = K.s →
    (∀ v, (b.B.Q.Rl.toCx3 b.B.Q.F).W1 b.B.Q.F.cr (b.B.Q.Rl.num b.B.Q.F 0 0) v → v ∈ b.B.Q.Rl.twPl) ∧
      b.B.Q.Rl.toRealDat.ExAt ∧ Finite b.P.T := by
  intro hL p K q c b w hsc
  have hZ := _root_.GlobalTheory.Mem.Top.Bl.zscale_f0_of_witness_alt q b w hsc
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  letI := a.x.grp
  letI := a.x.fin
  letI : Algebra (↥a.x.core.Q.c.F) (q.w.D q.Z).what₂.LL := a.x.alg
  have h3 : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput y.y) :=
    _root_.GlobalTheory.Mem.R3.realPins3_realTOf_alt K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a b.R b.S y.y hZ
  have hP : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree r.B.Q ∧ r.B.Q.Rl.toRealDat.ExAt ∧ Finite r.P.T) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y) :=
    ⟨h3, y.intersectionNumber_baseChange.aux.ex, finite_T_of_twArgs a⟩
  rw [← y.eq] at hP
  exact ⟨hP.1.w1 0 0, hP.2.1, hP.2.2⟩
end GlobalTheory.Mem.Top.Bl
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtTieStatement
section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_of_size_bound' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt → _root_.GlobalTheory.BigTop.Fun.LeafWeightBound @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.wt_tie_alt | exact _root_.GlobalTheory.BigTop.Fun.wt_tie_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.wt_tie_alt <;> assumption)
end
end

