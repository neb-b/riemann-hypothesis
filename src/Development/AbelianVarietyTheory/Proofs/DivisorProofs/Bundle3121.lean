module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3116
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0001
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0012
public import Development.AutomorphicArithmetic.DivisorFrames.IsSBHalfThetaFunOfHalfIdempotentPlaces
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0010
public import Development.AutomorphicArithmetic.DivisorFrames.BigPStdSchwartzTranslateEqSmallPOfIsUnif
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0017
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0007
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0008
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsLatticeThetaDataOfRamificationPlacesCMDatu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0692
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerOfCommutingHeatOperatorsRaynaudStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_of_commuting_heat_operators_raynaud : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix h.Θ) := by
  first | exact @GlobalTheory.KBracket.isKS_of_heat | exact GlobalTheory.KBracket.isKS_of_heat | (intros; apply GlobalTheory.KBracket.isKS_of_heat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectExistsCharZeroLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLift0

theorem exists_lift_domain : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K]
    (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal →
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (βV : cycAway n →+* V) (π : V →+* K)
      (cV : SiegPre g n (zetaAway n) (spMap βV)),
      Function.Injective βV ∧ π.comp βV = β ∧ cV.Principal ∧ SiegPB c cV (spMap π) := by
  intro g n hg hn hodd K _ _ β c hc
  obtain ⟨V, _, _, _, _, βV, π, hV, hinj, hπ, hβ⟩ := _root_.GlobalTheory.SiegelTor.CycLift.exists_complete_domain_lift n hn K β
  subst hβ
  obtain ⟨AV, _, _, φ, φ₂, PV, hAV, hpb, hsq, hPV, r₁, r₂, hsy, ham, hker, hiso⟩ :=
    _root_.GlobalTheory.PolLiftComplete.exists_lift K V hV π hπ c.A c.ab c.P c.isLB c.rig₁ c.rig₂ c.symm hc.1 hc.2
  obtain ⟨lev, hadd, htor, hgeom, hcomp⟩ :=
    GlobalTheory.T.exists_unique_symplecticLevel_lift_closedPoint g n hn hodd K V hV βV π hπ c hc AV φ φ₂ PV hAV hpb hsq hPV r₁ r₂ hsy ham hker hiso
  let cV : SiegPre g n (zetaAway n) (spMap βV) :=
    { A := AV, ab := hAV, P := PV, isLB := hPV, rig₁ := r₁, rig₂ := r₂, symm := hsy, lev := lev,
      lev_add := hadd, lev_tors := htor, geom := hgeom }
  exact ⟨V, inferInstance, inferInstance, βV, π, cV, hinj, rfl, ⟨ham, hker⟩, φ, φ₂, hpb, hsq, hiso, hcomp⟩

end GlobalTheory.SiegLift0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseRootBundleRosatiDescendedActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverse_root_bundle_rosati_descended_action : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → ∀ a : D.O, LBIso (P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left) (P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left) := by
  first | (exact @GlobalTheory.UPel.HT.ES.rosati_of_quasiInv_root) | (exact GlobalTheory.UPel.HT.ES.rosati_of_quasiInv_root) | (intros; apply GlobalTheory.UPel.HT.ES.rosati_of_quasiInv_root  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseRootBundleSymmetricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverse_root_bundle_symmetric : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → LBIso P' (P'.pull (lift (snd B B) (fst B B)).left) := by
  first | (exact @GlobalTheory.QuasiInvPull.root_symm) | (exact GlobalTheory.QuasiInvPull.root_symm) | (intros; apply GlobalTheory.QuasiInvPull.root_symm  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageFiniteCompat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.StageFinNonzero

theorem gBig_of_two {Q₁ Q₂ Q₃ : GlobalTheory.SqTop.GP} (h₁ : GlobalTheory.SqTop.GBig Q₁) (h₂ : GlobalTheory.SqTop.GBig Q₂)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b) : GlobalTheory.SqTop.GBig Q₃ := by
  obtain ⟨a₁, h₁⟩ := h₁
  obtain ⟨a₂, h₂⟩ := h₂
  refine ⟨max a₁ a₂, fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, h₁⟩ := h₁ ε CF (le_of_max_le_left hCF)
  obtain ⟨C₂, x₂, h₂⟩ := h₂ ε CF (le_of_max_le_right hCF)
  exact ⟨max C₁ C₂, max x₁ x₂, fun C hC D large₂ he hx r T Lc μ hLc G =>
    H G μ C _ _ (h₁ C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) r T Lc μ hLc G)
      (h₂ C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) r T Lc μ hLc G)⟩

end GlobalTheory.StageFinNonzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageFiniteFactor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.StageFinMatch

theorem gBig_two' {Q₁ Q₂ Q₃ : GlobalTheory.SqTop.GP} (h₁ : GlobalTheory.SqTop.GBig Q₁) (h₂ : GlobalTheory.SqTop.GBig Q₂)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b) : GlobalTheory.SqTop.GBig Q₃ := by
  obtain ⟨a₁, h₁⟩ := h₁
  obtain ⟨a₂, h₂⟩ := h₂
  refine ⟨max a₁ a₂, fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, h₁⟩ := h₁ ε CF (le_of_max_le_left hCF)
  obtain ⟨C₂, x₂, h₂⟩ := h₂ ε CF (le_of_max_le_right hCF)
  exact ⟨max C₁ C₂, max x₁ x₂, fun C hC D large₂ he hx r T Lc μ hLc G =>
    H G μ C _ _ (h₁ C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) r T Lc μ hLc G)
      (h₂ C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) r T Lc μ hLc G)⟩

theorem tmul_right_prop {K V U : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {a a' : V} {b b' : U} (h : a ⊗ₜ[K] b = a' ⊗ₜ[K] b') (hne : a ⊗ₜ[K] b ≠ 0) : ∃ μ : K, μ ≠ 0 ∧ b = μ • b' := by
  have ha : a ≠ 0 := by rintro rfl; exact hne (TensorProduct.zero_tmul _ _)
  have hb : b ≠ 0 := by rintro rfl; exact hne (TensorProduct.tmul_zero _ _)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ a ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact ha ((Module.forall_dual_apply_eq_zero_iff K a).mp hc)
  have k := congrArg (fun z => TensorProduct.lid K U (LinearMap.rTensor U φ z)) h
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at k
  have hb' : b = (φ a' / φ a) • b' := by
    rw [div_eq_inv_mul, mul_smul, ← k, smul_smul, inv_mul_cancel₀ hφ, one_smul]
  refine ⟨φ a' / φ a, ?_, hb'⟩
  intro h0
  rw [h0, zero_smul] at hb'
  exact hb hb'

end GlobalTheory.StageFinMatch

namespace GlobalTheory.StageFinMatch

end GlobalTheory.StageFinMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory

noncomputable section

namespace GlobalTheory.ConvThetaNe

open GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Over

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}

theorem int_eq (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) {ΦD : _} {Φ : WO W X → ℂ}
    (hD : IsDatum Γ.M ψ cA ΦD Φ) (h : GA D X) : thetaInt ωA ν 𝓕 Φ h = Γ.M.I om ΦD (kapX X e hO.JX h) :=
  thetaInt_eq_modelI D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (kapX X e hO.JX) ΦD Φ hO.measW hO.domW (hO.theta_eq_A hD) h

theorem integrable_big (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB)
    (hC : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F _, Γ.M.Conv om Φ) {Φ : WO W X → ℂ} (hΦ : Φ ∈ algF ψ θ true A B) (h : GA D X) :
    IntegrableOn (fun g => thetaKO ωA g h Φ) 𝓕 ν := by
  obtain ⟨ΦD, -, hD⟩ := hO.algA Φ hΦ
  have he := conjU_measurableEmbedding W 1 hO.JW
  have h1 := hC ΦD hD.1 (kapX X e hO.JX h)
  rw [hO.measW, hO.domW, he.integrableOn_map_iff, Set.preimage_image_eq _ he.injective] at h1
  have e1 : (fun g => thetaKO ωA g h Φ) = (fun g => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om ΦD g (kapX X e hO.JX h)) ∘
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW := funext fun g => (hO.theta_eq_A hD g h).symm
  rw [e1]
  exact h1

theorem exists_big_ne (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om') :
    ∃ Φ ∈ algF ψ θ true A B, thetaInt ωA ν 𝓕 Φ ≠ 0 := by
  obtain ⟨R, Rf, hm⟩ := hL _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨dec, hk⟩ := hK.1 _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨hc, hco⟩ := hk R Rf hm
  obtain ⟨l, hla, hl⟩ := GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral Γ.M Bs.ψ _ _ om hT.weil dec.1
  obtain ⟨f, hf, φ, hφ, hne⟩ := GlobalTheory.BigNZ.exists_I_ne_zero hm hc hco hla hl
  obtain ⟨Φ, hΦ, hD⟩ := hO.algA' _ (Submodule.subset_span ⟨f, φ, hf, hφ.fam.1, hφ.fam.2, rfl⟩)
  refine ⟨Φ, hΦ, fun h0 => hne (funext fun x => ?_)⟩
  obtain ⟨h, rfl⟩ := GlobalTheory.LineAtPlace.kapX_surj X e hO.JX x
  rw [← int_eq hO hD, h0]
  rfl

end Over

end GlobalTheory.ConvThetaNe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPointInductionKltPairSeparationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoPoint_induction_kltPair_separation : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ε : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → 0 < ε → ∃ (D : X → ℚ) (d : ℚ), d ≤ ∑ e ∈ Finset.Icc 1 n, (h e + ε) ∧ QNum p N d D ∧ ((LcCut p n (Δ + D) x₁ 0 ∧ ¬ KltAt p n (Δ + D) x₂) ∨ (LcCut p n (Δ + D) x₂ 0 ∧ ¬ KltAt p n (Δ + D) x₁)) := by
  first | exact @GlobalTheory.PairStep.two_point_induction | exact GlobalTheory.PairStep.two_point_induction | (intros; apply GlobalTheory.PairStep.two_point_induction <;> assumption)
end

