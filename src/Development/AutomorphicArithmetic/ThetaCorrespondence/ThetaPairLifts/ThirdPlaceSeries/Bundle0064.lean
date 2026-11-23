module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Formalism.LocalToGlobal.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1774

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SymRead
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {a : XGeo D}
structure SymReadAlt (l : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP.1) (S : ∀ PP, SymData (l PP).k (l PP).s D.R.k) : Prop where
  char : ∀ PP, (ofSplit (l PP).q).IsChar (_root_.GlobalTheory.Fam.pk_z W).ψ (S PP).ψ
  mu : ∀ PP j, 1 ≤ j → j ≤ D.R.m → (ofSplit (l PP).q).IsComp (Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1⁻¹ ((S PP).μ j)
  grp : ∀ g : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP PP.1), g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H ↔ ∀ PP, ∃ x, (l PP).Red (S PP) x (g PP)
  chr : ∀ (g : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP PP.1)) (hg : g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H) (x : ∀ PP, (S PP).P.J),
    (∀ PP, (l PP).Red (S PP) (x PP) (g PP)) → (_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g, hg⟩ = ∏ PP, (S PP).P.lam (x PP)
end GlobalTheory.Fam
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
def TwistSelectionFunctions {eps : ℝ} (Fm : FamP eps) : Type _ :=
  Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.RecTAlt (Fm.ex x hx i)
def TwistSelection (𝒞 : FamClass) : Type _ := ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → _root_.Formalism.L2.TwistSelectionFunctions Fm
theorem TwistSelectionFunctions.tiedRec {eps : ℝ} {Fm : FamP eps} (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.ExtraDataRecursive (Fm.ex x hx i) :=
  ⟨s.1, fun x hx h i => ⟨s.2 x hx h i⟩⟩
end Formalism.L2
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedGoodIdem
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
noncomputable section
namespace GlobalTheory.TieIdem
end GlobalTheory.TieIdem
namespace GlobalTheory.TieIdem
theorem tied_good_idem_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    (∀ k : p.P.Gp, ∑ g, (idemOf p.P.A3.A.X).coeff g * (idemOf p.P.A3.A.X).coeff (g⁻¹ * k) = (idemOf p.P.A3.A.X).coeff k) ∧
    (∀ g h : p.P.Gp, (idemOf p.P.A3.A.X).coeff (h * g * h⁻¹) = (idemOf p.P.A3.A.X).coeff g) ∧
    (∀ g : p.P.Gp, IsIntegral ℤ ((Fintype.card p.P.Gp : D.what₂.LL) * (idemOf p.P.A3.A.X).coeff g)) ∧
    ∀ (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp), σ ((idemOf p.P.A3.A.X).coeff g⁻¹) = starRingEnd ℂ (σ ((idemOf p.P.A3.A.X).coeff g)) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p hr _
  exact idemOf_props p.P.A3.A.X hr.ok.ok2.irr
end GlobalTheory.TieIdem
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TransportStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_vector_theta_compatible_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ sp : SplitPlace D.host.E, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i))) = s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) • (P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) := by
  first | exact @_root_.GlobalTheory.EigTransport.transport_alt | exact _root_.GlobalTheory.EigTransport.transport_alt | (intros; apply _root_.GlobalTheory.EigTransport.transport_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
section
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {D : D7}
section Real
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
def QAllAlt (PP : Pl D.host.E) : Prop := ∃ t, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t
structure PackageHypotheses : Prop where
  bot : _root_.GlobalTheory.MiTop.BottomHypotheses W
  lev : _root_.GlobalTheory.MiS.LevelHypothesis W
  ex : (_root_.GlobalTheory.Fam.pk_z W).ExAt
  hTop : ∀ t, LinearMap.range ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e) =
    MultT (_root_.GlobalTheory.Fam.pk_z W).θ (_root_.GlobalTheory.Fam.pk_z W).MX (levS _ (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt t))
  gap : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D
  fin : Finite W.P.T
  sel : ∀ PP PP', _root_.GlobalTheory.Fam.QAllAlt W PP → _root_.GlobalTheory.Fam.QAllAlt W PP' → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP'
  aa : ∀ PP : Pl D.host.E, (_root_.GlobalTheory.Fam.QAllAlt W PP ∨ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ ∃ u, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal
variable {W} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
structure FamilyCharacter.RowOK : Prop where
  meas : GeoMeas (_root_.GlobalTheory.Fam.pk_z W) f.g
  last : f.c.VolLast
  x : ∀ j, j ≤ D.R.m → (f.g.x j).Is
  row : ∀ t, (f.row t).Is
  same : ∀ t t', (f.row t).Same (f.row t')
structure FamilyCharacter.ColOK : Prop where
  kom : ∀ t j, j < D.R.m → IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1)) ((f.col t).kom j)
  ker : ∀ t j, j < D.R.m → ∀ α γ, ((f.t t).ker j α γ).Is f.c.ψ f.c.θ (f.c.x j) (f.c.x (j + 1))
  e : ∀ t j α, ∀ g ∈ ((f.col t).e j α).support, g ∈ GfC (Yc D j)
  eT : ∀ t n h β, ∀ g ∈ ((f.col t).eT n h β).support, g ∈ GfC D.sp.X'
  stabK : ∀ t j, j < D.R.m → ∀ ψ ∈ (f.col t).Ram j, (f.t t).K j ψ ∈ (f.col t).Ram (j + 1)
  stabS : ∀ t j, j ≤ D.R.m → ∀ ψ ∈ (f.col t).Ram j, (f.col t).S j ψ ∈ (f.col t).Ram j
structure CommutingVectorTie (v : VCom f.c) : Prop where
  b : ∀ j, v.b j = f.g.b j
  bT : v.bT = f.g.bT ∧ v.NT = f.g.LT
  gP : ∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  tP : ∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal
  moves : ∀ j, j < D.R.m → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) →
    GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) (v.N j) P
  movesT : ∀ P, GlobalTheory.FinPl.Moves D.sp.X' f.g.bT (_root_.GlobalTheory.Fam.pk_z W).ΛX f.g.LT P
  Ψ : ∀ j, j + 1 < D.R.m → ∃ o, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧ ∀ P a a', v.Ψ j P a a' = comb f.c.ψ _ _ o
    ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) (pureTensorO f.c.ψ f.c.θ (Yc D j) (Yc D (j + 1))
      (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) P))
  ΨT : ∀ j h, ∃ o, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧ ∀ P, v.ΨT j h P = comb f.c.ψ _ _ o
    (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (pureTensorO f.c.ψ f.c.θ (Yc D (j + 1)) D.sp.X'
      (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) P))
  nz : (∀ j, j + 1 < D.R.m → ∃ P, v.Ψ j P 1 1 ≠ 0) ∧ ∀ j h, ∃ P, v.ΨT j h P ≠ 0
def IsDivisorGlobal (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (j : ℕ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (Λ : GlobalTheory.FinPl.Lat V)
    (β : GL (Fin V.rank) (Lev.EAf D)) (vac : WO (Yc D j) V → ℂ) (d : WO (Yc D j) V →₀ ℂ) : Prop :=
  GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) d ∧
    IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β
      (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ∅ (fun _ => 1) vac
      (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ d vac)
def IsDivisorRational (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (j : ℕ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (Λ : GlobalTheory.FinPl.Lat V)
    (β : GL (Fin V.rank) (Lev.EAf D)) (vac : WO (Yc D j) V → ℂ) (d : WO (Yc D j) V →₀ ℂ) : Prop :=
  GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) d ∧
    IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β
      (datY _ D.R.r D.R.t j (r_le_Y j) ∅ ((_root_.GlobalTheory.Fam.pk_z W).Q t) (LevelP.triv _ _ _) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR t) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1))
      ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) vac (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ d vac)
def RationalVectorCondition {t : W.P.T} (w : VTup (f.t t)) : Prop :=
  (∀ j, j + 1 < D.R.m → ∀ d, _root_.GlobalTheory.Fam.IsDivisorRational W t j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d →
    ∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (· ∈ w.Q) g →
      (f.t t).om j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d g) =
        comb f.c.ψ _ _ (w.eQ j) ((f.t t).om j (f.g.b j, f.g.b (j + 1)) g)) ∧
  ∀ j h d, _root_.GlobalTheory.Fam.IsDivisorRational W t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d →
    ∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX (· ∈ w.Q) g →
      (f.t t).omT j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d g) =
        comb f.c.ψ _ _ (w.eQT j h) ((f.t t).omT j h (f.g.b (j + 1), f.g.bT) g)
structure LocalGroupReading {v : VCom f.c} {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) : Prop where
  idem : ∀ i, Formalism.L2.NTheta.IsIdemAt (G i).q.e (pl i).1 ∧ (G i).q.v = (pl i).1.under (𝓞 D.host.F)
  mu : ∀ i j, 1 ≤ j → j ≤ D.R.m → (ofSplit (G i).q).IsComp (Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1⁻¹ ((G i).S.μ j)
  frame : ∀ i j c (hc : j + c = (G i).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((G i).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (G i).q) (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).βY j)
      ((((G i).FY j c hc).β * (((G i).S.T (Fin D.R.t)).bas j c hc).val).submatrix id
        fun a => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm a))
  frameTop : ∀ i, ∃ e : Ix (Fin D.R.k ⊕ Fin ((G i).s + 1)) (Fin D.R.t) ((G i).s + 2) ≃ Fin D.sp.X'.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (G i).q) D.sp.X' f.g.bT (_root_.GlobalTheory.Fam.pk_z W).βX ((G i).FT.β.submatrix id e.symm)
  lev : ∀ (g : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP PP.1)),
    (g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H ↔ ∀ i, ∃ x : (G i).S.P.J, ∀ (a b : Fin D.R.k ⊕ Fin ((G i).s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
        Ideal.Quotient.mk (pl i).1.asIdeal z = (g (pl i)).val a' b' →
        valuation (G i).k ((x : GL (Fin D.R.k ⊕ Fin ((G i).s + 1)) (G i).k).val a b - (ofSplit (G i).q).pr (z : D.host.E)) < 1) ∧
    ∀ (hg : g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H) (x : ∀ i, (G i).S.P.J), (∀ i (a b : Fin D.R.k ⊕ Fin ((G i).s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
        Ideal.Quotient.mk (pl i).1.asIdeal z = (g (pl i)).val a' b' →
        valuation (G i).k ((x i : GL (Fin D.R.k ⊕ Fin ((G i).s + 1)) (G i).k).val a b - (ofSplit (G i).q).pr (z : D.host.E)) < 1) →
      (_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g, hg⟩ = ∏ i, (G i).S.P.lam (x i)
end Real
section True
open GlobalTheory.Mem GlobalTheory.Mem.Col2
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}
structure ValidRealPackage (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop where
  ok : I.Ok
  pins : Nonempty (TC.Pins B X)
  tw : I.IsTw
  std : Nonempty (I.StdC l Z W.R.T.cols)
  chr : ∀ j : Fin B.R.m, ChrEq ((_root_.GlobalTheory.Fam.pk_z W).mu0 ((j : ℕ) + 1)) (I.C.mu0 j)
  top : _root_.GlobalTheory.Fam.LeadingReadStatement W
end True
end GlobalTheory.Fam
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwoLogCardLevelsLe
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
noncomputable section
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem two_log_card_levels_le_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ PP A : ℝ, GlobalTheory.CovTop.HostNum D L PP A 3 → 2 * Real.log (Fintype.card p.P.Gp : ℕ) ≤ L.sc.b := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p _ _ PP A hN
  have hq : ∀ k, D.host.g k ≠ 0 := by
    intro k h0
    have h := hN.cop
    fin_cases k <;> simp_all [Nat.Coprime]
  have hcard : Nat.card p.P.Gp =
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nat.card (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
    rw [Nat.card_congr (p.R.eG.trans p.cG).toEquiv]
    exact Nat.card_pi
  have hleN : Fintype.card p.P.Gp ≤
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), D.host.g kv.1 ^ (D.R.r * D.R.r) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun kv _ => card_GL_zmod_le _ _ (hq kv.1))
  have hpos : (0 : ℝ) < (Fintype.card p.P.Gp : ℝ) := by exact_mod_cast Fintype.card_pos
  have hleR : (Fintype.card p.P.Gp : ℝ) ≤
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℝ) ^ (D.R.r * D.R.r)) := by
    exact_mod_cast hleN
  have hlog : Real.log (Fintype.card p.P.Gp : ℝ) ≤
      (2 * D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1) := by
    refine (Real.log_le_log hpos hleR).trans ?_
    rw [Real.log_prod (fun kv _ => pow_ne_zero _ (by exact_mod_cast hq kv.1))]
    calc ∑ kv : (Σ k : Fin 2, D.nd.PlG k), Real.log ((D.host.g kv.1 : ℝ) ^ (D.R.r * D.R.r))
        ≤ ∑ _kv : (Σ k : Fin 2, D.nd.PlG k), ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1) := by
          refine Finset.sum_le_sum fun kv _ => ?_
          rw [Real.log_pow]
          push_cast
          exact mul_le_mul_of_nonneg_left (hN.logg kv.1) (by positivity)
      _ = (2 * D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_sigma]
          simp [D.nd.card_PlG, nsmul_eq_mul]
          ring
  obtain ⟨-, hL10, hLx, -⟩ := hN.big
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
  obtain ⟨-, -, hpoly⟩ := hN.poly
  have hroom := hN.room
  have hx0 : 0 < L.sc.x := by linarith
  have hX0 : 0 < L.sc.x ^ A := Real.rpow_pos_of_pos hx0 A
  have h3 : (L.sc.x ^ A) ^ (3 : ℝ) = (L.sc.x ^ A) ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3] at hroom
  have hrn : (D.R.r : ℝ) ≤ D.R.nV := by
    have : D.R.r ≤ D.R.nV := by unfold Formalism.BasicNotions.Ranks.nV; omega
    exact_mod_cast this
  set X := L.sc.x ^ A with hX
  set f : ℝ := (D.R.f : ℝ)
  set r : ℝ := (D.R.r : ℝ)
  set Lr := L.sc.L
  have hr0 : 0 ≤ r := by positivity
  have hY : f * r * r * Lr ≤ X := by
    refine le_trans ?_ hpoly
    have : f * r * r * Lr = (f * r) * Lr * r := by ring
    have : f * r * (D.R.nV : ℝ) * Lr = (f * r) * Lr * D.R.nV := by ring
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ f) hr0) (by linarith : (0:ℝ) ≤ Lr)]
  have key : 2 * ((2 * f) * (r * r) * (9 * Lr + 1)) ≤ L.sc.b := by
    rcases Nat.eq_zero_or_pos D.R.r with h0 | h1
    · have : r = 0 := by simp [r, h0]
      rw [this]; nlinarith [pow_pos hX0 3]
    · have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr h1
      have hY80 : 80 ≤ f * r * r * Lr := by
        have : (1:ℝ) ≤ r * r := by nlinarith
        have : (80:ℝ) ≤ f * Lr := by nlinarith
        nlinarith
      have hX80 : 80 ≤ X := le_trans hY80 hY
      have hA : 2 * ((2 * f) * (r * r) * (9 * Lr + 1)) ≤ 40 * (f * r * r * Lr) := by
        have : 0 ≤ f * r * r := by positivity
        nlinarith
      have hB : 40 * X ≤ X ^ 3 := by
        have hXX : 40 ≤ X * X := by nlinarith
        calc 40 * X ≤ X * X * X := by nlinarith
          _ = X ^ 3 := by ring
      nlinarith
  nlinarith [hlog]
end GlobalTheory.CovTop
end
end
end

