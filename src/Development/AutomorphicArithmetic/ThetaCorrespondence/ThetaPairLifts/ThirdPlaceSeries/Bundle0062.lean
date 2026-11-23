module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0056
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1811
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NmjTAtTied
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.BigTop.PtAt.nmjT_at_tied_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q), NChTie D ex.nch → DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I → _root_.GlobalTheory.ExportPin.IndefiniteClassSumCondition B.Q → _root_.Formalism.IndefR.NX.RealExpansionMajorant B.Q B.Q.cG B.Q.Sx B.Q.nexp ex.nch := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR hTie hDiv hPin
  obtain ⟨jD, eM, hAg, hKs, hSum, hEmb, hLi⟩ := _root_.GlobalTheory.T.lattice_family_adoption_first_alt D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR hTie
  have hLat := _root_.GlobalTheory.T.lattice_family_adoption_second_alt D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR jD eM hTie hAg hSum
  have hTh := _root_.GlobalTheory.T.lattice_family_adoption_third_alt D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR jD eM hDiv hPin hAg hSum
  exact ⟨jD, hAg, ⟨{ eMj := eM, eMj_li := hLi, eMj_lat := hLat, eMj_th := hTh, ks := hKs, eMj_sum := hSum, embW_Ks := hEmb }⟩⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormSqBlockValue
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameAut
theorem norm_sq_blockValue_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W _ _ w _ _ _ ν hν Q
  have h := norm_sq_firstValA p.R.toRealDat p.F.lv2 p.charW.base.lev p.charW.base.fam j (p.R.mu w) Q.1 Q.2
  obtain rfl : ν = fun Q => Formalism.L2.Col.firstValA (p.P.A3.A.muVal j (p.R.mu w)) p.P.A3.A.etaVal p.P.A3.A.q p.P.A3.A.r Q.1 :=
    List.mem_singleton.1 hν
  have e : (blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t = p.P.A3.A.r := Nat.add_sub_cancel ..
  rw [e]
  exact h
end GlobalTheory.FrameAut
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
def col0_alt (t : W.P.T) (φ : D.what₂.Mu u) : (f.t t).Col 0 := D.e0Tw u (W.P.I.tup t) (D.eMu u φ).1
def descentToLevelZero (n : ℕ) (h : 2 * n + 2 * 0 + 2 = D.R.m) (t : W.P.T) (F : (f.t t).CT) :
    SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h F)).1
def LinkVanishes (d : _root_.GlobalTheory.MiTop.BottomData W u) : Prop :=
  ∀ n (h₀ : 0 + 2 * n + 2 = D.R.m) t φ, _root_.GlobalTheory.MiTop.col0_alt f t φ ∈ (f.t t).Ram 0 ∧
    ∀ G y v, (f.t t).per 0 n h₀ (_root_.GlobalTheory.MiTop.col0_alt f t φ) G y v = d.per φ G.1 y v
def LinkTailCondition : Prop :=
  ∀ n (h : 2 * n = D.R.m) t φ (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL)
    (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), HEq F F' → ∀ G : (f.t t).CT, G.1 = _root_.GlobalTheory.Fam.leadingLinearMap W t F' →
    (f.t t).tail (2 * n) h ((f.t t).col (2 * n) (_root_.GlobalTheory.MiTop.col0_alt f t φ)) G =
      D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F))
def LinkDescends : Prop :=
  ∀ n (h : 2 * n + 2 * 0 + 2 = D.R.m) t (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL),
    ∃ G : (f.t t).CT, G.1 = _root_.GlobalTheory.Fam.leadingLinearMap W t F' ∧ _root_.GlobalTheory.MiTop.descentToLevelZero f n h t G = _root_.GlobalTheory.MiTop.rowFormOfTuple W t F'
def LinkSurjective : Prop :=
  ∀ n (h : 2 * n + 2 * 0 + 2 = D.R.m), ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∃ G : (f.t W.P.A3.A.μ0).CT, _root_.GlobalTheory.MiTop.descentToLevelZero f n h W.P.A3.A.μ0 G = T
def LinkCommutes : Prop :=
  ∀ n (h : 2 * n = D.R.m), ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ) (s : ℂ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧ s ≠ 0 ∧
    ∀ t φ F, (f.t t).tail (2 * n) h ((f.t t).up n (_root_.GlobalTheory.MiTop.col0_alt f t φ)) F =
      s * (f.t t).tail (2 * n) h ((f.t t).col (2 * n) (_root_.GlobalTheory.MiTop.col0_alt f t (S φ))) F
variable (W)
def CoveredCondition : Prop :=
  ∀ w (p : ℕ), p.Prime → (∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q (W.Q.Rl.mu w), ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (p : 𝓞 D.what₂.LL) ∉ w.asIdeal
open Formalism.L2.Host in
theorem served' : _root_.GlobalTheory.MiTop.CoveredCondition W := by
  rintro w p hp ⟨PP, hP, h1⟩ h2
  have lev := W.Q.charW.base.lev
  have hr : ¬ (W.Q.Rl.xiH (W.Q.Rl.mu w)).UnrAt PP := (lev.Q_ram _ PP).2 (Or.inl hP)
  have hl : Formalism.EigenvalueLevelCeiling.plc w = p :=
    (Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime w) hp).1
      ((ringChar.spec _ p).1 (by simpa using Ideal.Quotient.eq_zero_iff_mem.2 h2))
  by_cases hw : w ∈ W.Q.Rl.twPl
  · obtain ⟨ψ, Q, hψ, e⟩ := W.Q.charW.tup.mu_on w hw
    have e' : W.Q.Rl.xiH (W.Q.Rl.mu w) = W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    have key : ∀ q : ℕ, q.Prime → OverP D.host q PP → q = p := fun q hq ho => by
      by_contra hne
      have hc : IsCoprime ((q : ℕ) : 𝓞 D.host.E) ((p : ℕ) : 𝓞 D.host.E) :=
        Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)
      obtain ⟨a, b, hab⟩ := hc
      have ho' : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := ho
      exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ ho') (PP.asIdeal.mul_mem_left _ h1)))
    have hd : (W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt PP := by
      unfold CharFrame.delAt
      split_ifs with hh
      · refine W.Q.Rl.C.isDel'.unr PP fun ho => D.host.pde_ne ?_
        rw [← hh, hl, key _ D.host.pde'_prime ho]
      · exact W.Q.Rl.C.isDel.unr PP fun ho => hh (by rw [hl, key _ D.host.pde_prime ho])
    refine hr fun x hx => ?_
    have a1 := hd x hx
    have a2 := hψ.atl PP (hl ▸ h1) x
    rw [e']
    change (W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc PP x * ψ.loc PP x = 1
    rw [a1, a2, mul_one]
  · have e : W.Q.Rl.mu w = W.P.A3.A.μ0 := W.Q.charW.tup.mu_off w hw
    refine hr fun x _ => ?_
    rw [e, show W.Q.Rl.xiH W.P.A3.A.μ0 = 1 from lev.xi_base]
    rfl
theorem not_mem_Q_base' (PP : HeightOneSpectrum (𝓞 D.host.E)) : PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 := by
  intro hP
  have lev := W.Q.charW.base.lev
  refine (lev.Q_ram _ PP).2 (Or.inl hP) fun x _ => ?_
  rw [show W.Q.Rl.xiH W.P.A3.A.μ0 = 1 from lev.xi_base]
  rfl
end GlobalTheory.MiTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OffBadStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplit_at_good_place_of_used0_av : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (Q : D.naut.AV i), ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g :=
  _root_.GlobalTheory.SummandEig.main_alt_alt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OmpinsOnto
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.BigOn
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end
theorem ompins_onto_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' →
    BarTie (fw2 p) ∧ (∀ i, OMPins p.T (R2 p) p.κ p.v₀ (om2 p) i) ∧
      ∀ i, PhaseTie p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i :=
  fun _ _ _ _ _ _ _ _ _ _ p what₂ => ⟨conjugateReadingsVanishing_splitPart p, thetaRowData_pins_splitPart p, phaseCompatible_splitPart_of_liftUniformisation p what₂.prim.unif⟩
end GlobalTheory.BigOn
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PostOnMemEEatOfCenter
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
noncomputable section
set_option maxHeartbeats 800000
open Formalism.BasicNotions.TH Formalism.IndefR.Lev
namespace GlobalTheory.MiTop.CentralShift
section General
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
end General
section Main
open GlobalTheory.MiTop.CentralShift
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem postOn_rTrL_mem_EEat_of_mem_center (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {z : GA D (Yc D 0)} (hzf : z ∈ GfC (Yc D 0))
    (hzc : z ∈ Subgroup.center (GA D (Yc D 0))) (Pl : LevelP W.Q.Rl.toRealDat.Pg D.R.r ℂ) {T : MMap (W.Q.Rl.MY 0)}
    (hT : T ∈ W.Q.Rl.toRealDat.EEat Pl) :
    postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) T ∈ W.Q.Rl.toRealDat.EEat Pl := by
  unfold RealDat.EEat at hT ⊢
  refine GlobalTheory.MultTranslate.postOn_mem_goodPart hzf (fun k hk => ?_) (fun f => ?_) hT
  · have e : z⁻¹ * k * z = k := by
      rw [mul_assoc, Subgroup.mem_center_iff.mp hzc k, inv_mul_cancel_left]
    rw [e]
    exact ⟨hk, rfl⟩
  · unfold RealDat.e0
    exact gaL_rTr_of_center _ _ _ _ hzc f
end Main
end GlobalTheory.MiTop.CentralShift
namespace GlobalTheory.MiTop
open GlobalTheory.MiTop.CentralShift
theorem exists_isShift_of_center_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∃ V, _root_.GlobalTheory.MiTop.IsShiftOperator W z V := by
  intro D L hT Gi Gl Kc Yd cX ex W hB z hzf hzc
  have hM := hB.hyp.2.2.2.1.models
  have hE := hM.HE
  have h0 := hM.ν0
  have hHaar : W.Q.Rl.ν0.IsHaarMeasure := h0.1.1
  have hFD := h0.2
  obtain ⟨hinj, hrange, hip⟩ := hE
  have he : ∀ e, W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat W.Q.Rl.toRealDat.triv := fun e => by
    rw [← hrange]; exact LinearMap.mem_range_self _ e
  have hmem : ∀ e, postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e) ∈ LinearMap.range W.Q.Rl.HE.e :=
    fun e => by rw [hrange]; exact _root_.GlobalTheory.MiTop.CentralShift.postOn_rTrL_mem_EEat_of_mem_center W hzf hzc _ (he e)
  let Lr : W.Q.Rl.HE.H →ₗ[ℂ] LinearMap.range W.Q.Rl.HE.e :=
    (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) ∘ₗ W.Q.Rl.HE.e).codRestrict _ hmem
  let Vz : W.Q.Rl.HE.H →ₗ[ℂ] W.Q.Rl.HE.H := (LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm.toLinearMap ∘ₗ Lr
  have hV : ∀ e, W.Q.Rl.HE.e (Vz e) = postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e) := by
    intro e
    have h1 : ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm (Lr e)) : LinearMap.range W.Q.Rl.HE.e) : MMap (W.Q.Rl.MY 0)) =
        W.Q.Rl.HE.e ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm (Lr e)) := LinearEquiv.ofInjective_apply _ _
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hzc' : z⁻¹ ∈ Subgroup.center (GA D (Yc D 0)) := Subgroup.inv_mem _ hzc
  have hipv : ∀ e e' : W.Q.Rl.HE.H,
      ipM (W.Q.Rl.MY 0) W.Q.Rl.ν0 W.Q.Rl.fd0 (W.Q.Rl.HE.e e) (W.Q.Rl.HE.e e') =
        ipM (W.Q.Rl.MY 0) W.Q.Rl.ν0 W.Q.Rl.fd0 (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e))
          (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e')) := by
    intro e e'
    have m1 := (Submodule.mem_inf.mp (he e)).1
    have m2 := (Submodule.mem_inf.mp (he e')).1
    have m3 := (Submodule.mem_inf.mp (_root_.GlobalTheory.MiTop.CentralShift.postOn_rTrL_mem_EEat_of_mem_center W hzf hzc _ (he e))).1
    have m4 := (Submodule.mem_inf.mp (_root_.GlobalTheory.MiTop.CentralShift.postOn_rTrL_mem_EEat_of_mem_center W hzf hzc _ (he e'))).1
    apply ipM_eq_of_iff
    intro c
    constructor
    · exact GlobalTheory.isMultiplicityInner_of_unit_twist_shift _ _ _ _ _ _ hHaar hFD z 1 (by simp) (map_mul_right_center _ hHaar hzc)
        _ m1 _ m2 _ _ (fun v g => by rw [one_mul]; rfl) (fun v g => by rw [one_mul]; rfl) c
    · exact GlobalTheory.isMultiplicityInner_of_unit_twist_shift _ _ _ _ _ _ hHaar hFD z⁻¹ 1 (by simp) (map_mul_right_center _ hHaar hzc')
        _ m3 _ m4 _ _ (fun v g => by rw [one_mul]; exact congrArg (W.Q.Rl.HE.e e v) (inv_mul_cancel_right g _).symm)
        (fun v g => by rw [one_mul]; exact congrArg (W.Q.Rl.HE.e e' v) (inv_mul_cancel_right g _).symm) c
  refine ⟨Vz, fun e v => ?_, fun e => ?_, fun e hel => ?_⟩
  · unfold _root_.GlobalTheory.MiTop.rowFormOfVector
    rw [hV]
    exact lift_postOn _ _ _
  · rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hip, hip, hV, ← hipv]
  · rw [hV]
    exact _root_.GlobalTheory.MiTop.CentralShift.postOn_rTrL_mem_EEat_of_mem_center W hzf hzc _ hel
end GlobalTheory.MiTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
def pointOfRealisation (pin : _root_.Formalism.L2.Rows.RowSideDeterminedAlt Rc.T P) {Del h0 : ℕ} (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) {c : ℝ}
    (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf (zscOf P Del h0 c) S) (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) : PtAt ex c where
  P := rowSideOfCompatibleThetaPair P
  Del := Del
  h0 := h0
  hDel := hDel
  hh0 := hh0
  Dcf := Dcf
  Spf := Spf
  gamDvd := pin.gamDvd
  T := B.T
  alg := B.alg
  R := B.Q.Rl
  charW := B.Q.charW
  zs := B.Q.zs
  s0 := B.Q.s0
  s1 := B.Q.s1
  dc := B.Q.dc
  stdChar := B.Q.stdChar
  signs := B.Q.signs
  cG := B.Q.cG
  Sx := B.Q.Sx
  nexp := B.Q.nexp
  stdV := B.Q.stdV
  stdX := B.Q.stdX
  host := B.Q.host
  err_eq := B.Q.err_eq
  vpos := B.Q.vpos
  κ := B.κ
  v₀ := B.v₀
  fw := B.fw
  bar := B.bar
  O := B.O
  pins := B.pins
  rhoGeo := B.rhoGeo
  equivAll := B.equivAll
  cTie := B.cTie
  phase := B.phase
  qGuard := Qp.qGuard
  hF := Qp.hF
  phsOne := Qp.phsOne
  prXunit := Qp.prXunit
  grpRecPin := Qp.grpRecPin
  fdiag := Qp.fdiag
  eGtie := Qp.eGtie
  betaStd := Qp.betaStd
  tupT := Qr.tupT
  hm := Qr.hm
  Tp := Qr.Tp
  tupXi := Qr.recR.tupXi
  tupAt := Qr.recR.tupAt
  tupTie := Qr.tupTie
  tupT_tup := Qr.tupT_tup
  muEq := Qr.muEq
def PointSummands.pt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : PtAt O.ex c :=
  _root_.GlobalTheory.Fc.Ind.pointOfRealisation b.pin b.DH.2.1 b.DH.2.2 b.B b.pins b.Rr
def conditionOnPoint (G : PtP) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun D O c b => G D O c b.pt
def RowPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => b.pt.PointConditions'
end GlobalTheory.Fc.Ind
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReductionYZero
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamTraceChi
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
abbrev reductionYZero_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (h : GA D (D.sp.Y 0)) : Formalism.L2.DIV.G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r :=
  Formalism.L2.DIV.rTup ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).dat0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) (finE (Yc D 0) h)
theorem rChi_eq_lvP_chi_of_mem (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {h : GA D (D.sp.Y 0)} (hh : h ∈ _root_.GlobalTheory.MiTop.rJ_z W) :
    ∃ hg : _root_.GlobalTheory.FamTraceChi.reductionYZero_alt W h ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H, _root_.GlobalTheory.MiTop.realCharacter W h = (((_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨_, hg⟩ : ℂˣ) : ℂ) := by
  have h2 := hh.2
  have h3 := (Formalism.L2.DIV.mem_lev.1 h2).2
  refine ⟨h3, ?_⟩
  simp only [_root_.GlobalTheory.MiTop.realCharacter, Formalism.IndefR.Lev.levChi, Formalism.L2.DIV.levFn]
  rw [Formalism.L2.DIV.extendOne_of_mem _ h3]
  simp [Formalism.IndefR.Links.LevCh.dat0, Formalism.IndefR.Lev.datY]
  rfl
end GlobalTheory.FamTraceChi
end
end
end

