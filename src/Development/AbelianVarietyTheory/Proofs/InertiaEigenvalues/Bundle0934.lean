module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0927
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0928
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0913
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0012
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0920
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointConcreteThetaInjectiveReferenceTupleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.RecTie Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_concrete_theta_injective_reference_tuple : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → ∀ (i : Fin D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y) = 0 → y = 0 := by
  first | exact @GlobalTheory.AdjInjLevel.adjoint_eW_inj | exact GlobalTheory.AdjInjLevel.adjoint_eW_inj | (intros; apply GlobalTheory.AdjInjLevel.adjoint_eW_inj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointThetaKillsReferenceTupleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.RecTie Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointTheta_kills_referenceTuple : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → ∀ (i : Fin D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y = 0 → LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y) = 0 := by
  first | exact @GlobalTheory.Mem.AdjLevel.adjoint_eW_eq_zero | exact GlobalTheory.Mem.AdjLevel.adjoint_eW_eq_zero | (intros; apply GlobalTheory.Mem.AdjLevel.adjoint_eW_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumsTwistedDefiniteFormsRationalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_sums_twisted_definite_forms_rational : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (rd : Rd ρ D.nexp i j b) (T : CellTie hρ D.nexp rd), RatTwist hρ rd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  ∀ k Q ψ, TwOK i k Q ψ → ClsQ (D := D) Q → ∀ f, ρ.sum i j b k Q ψ (T.rdV k Q ψ f) ∈ Set.range (rdK rd hρ k) := by
  first | exact @GlobalTheory.ClassSumRat.sum_mem_range | exact GlobalTheory.ClassSumRat.sum_mem_range | (intros; apply GlobalTheory.ClassSumRat.sum_mem_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsNormIsRatScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.NormRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}

theorem fixBase_of_fix (hRF : GlobalTheory.NT.RayField) {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A}
    {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    (hT : LawsJ T) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hfw : Nonempty (FWTie T Rl.toRealDat κ v₀))
    (hti : TieIn T Rl.toRealDat κ v₀) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (j : Fin D.R.m) (τ : ℂ ≃+* ℂ) (hτ : ∀ z ∈ (embLL0 D).fieldRange, τ z = z) :
    FixBase T Rl.toRealDat j τ :=
  _root_.GlobalTheory.FixBaseSmall.fixBase_of_fixes D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ hT hcore hfw hti hgal hval hray hroots j τ hτ

theorem exists_extC {G : Type} [Group G] [Fintype G] {T1 : Type} {A : FamIn D.what₂.LL G Pl0 T1 D.R.m} {T : CoreJ D}
    [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {j : Fin D.R.m} {Tp : Type} {tup : Tp → T1}
    (O : OMDat T.toCore R j Tp tup) : ∃ c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W, ExtC R j (inC O.c') O.c0' c :=
  _root_.GlobalTheory.ExtCoeff.exists_extC D G Pl0 T1 A T R j Tp tup O

theorem exists_ser_ne_zero {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {F : Face D A3.A}
    {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hfw : Nonempty (FWTie T Rl.toRealDat κ v₀)) (hio : IoExt Rl.toRealDat)
    (j : Fin D.R.m) (hpins : OMPins T Rl.toRealDat κ v₀ O j) (hrow0 : OneMapRow0 T Rl.toRealDat κ v₀ O j)
    (hcusp : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥)
    (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W) (hc : ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c)
    (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ) (hu : ∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) :
    ∃ (v : VsV D j D.what₂.LL) (x : VsV D j ℂ) (h : GA D (Vc D j)) (g : GA D (Wc D j)),
      (∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m = (q : D.what₂.LL)) ∧
      (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) ∧
      h ∈ GfC (Vc D j) ∧ ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g ≠ 0 :=
  _root_.GlobalTheory.SeriesTie.RatNe.exists_ser_rat_ne D Γ Pl0 I0 T0 A3 T Rl F κ v₀ O hnV hcore hfw hio j hpins hrow0 hcusp c hc u hu

theorem expands_of_isRatPhase (hRF : GlobalTheory.NT.RayField) {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL]
    {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
    {F : Face D A3.A} {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
    {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (hT : LawsJ T) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F)
    (hfw : Nonempty (FWTie T Rl.toRealDat κ v₀)) (hti : TieIn T Rl.toRealDat κ v₀) (hio : IoExt Rl.toRealDat)
    (hQ : QGuard Rl.toRealDat) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    {j : Fin D.R.m} (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) (hpins : OMPins T Rl.toRealDat κ v₀ O j)
    (hfp : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV)
    {gramR c0R c0L} (hft : Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L)
    (hbc : CoefficientBaseChange Rl.toRealDat j (O j).jL (inC (O j).c') (c0L j) (O j).c0')
    {u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ} (hu : ∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) {ph₀ : ℂ}
    (hph : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph₀)
    (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W) (hc : ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c)
    (v : VsV D j D.what₂.LL)
    (hv : ∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m = (q : D.what₂.LL))
    (x : VsV D j ℂ)
    (hx : (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank))
    (h : GA D (Vc D j)) (hh : h ∈ GfC (Vc D j)) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n),
      Expands (O j) (κ j) (fun g => ph₀ * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g) e f ∧
        ∀ k, e k ∈ (embLL0 D).fieldRange :=
  _root_.GlobalTheory.SeriesTie.RatExpand.expands_of_isRatPhase D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ O hnV hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp gramR c0R c0L hft hbc u hu ph₀ hph c hc v hv x hx h hh

theorem fixed_of_expands {G : Type} [Group G] [Fintype G] {T1 : Type} {A : FamIn D.what₂.LL G Pl0 T1 D.R.m} {T : CoreJ D}
    [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {j : Fin D.R.m} {Tp : Type} {tup : Tp → T1}
    (O : OMDat T.toCore R j Tp tup) (κ : WeightFamilies.Wt D ((j : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {Φ Ψ Ψ' : GA D (Wc D j) → ℂ} {a : ℂ}
    (hc : ConjFun O κ τ 1 Ψ Ψ') (hΨ : ∀ g, Ψ g = a * Φ g) (hΨ' : ∀ g, Ψ' g = a * Φ g) {n : ℕ} {e : Fin n → ℂ}
    {f : Fin n → T.toCore.cuspA ((j : ℕ) + 1) (wtA κ) κ.n} (he : Expands O κ Φ e f) (hτ : ∀ k, τ (e k) = e k)
    {g₀ : GA D (Wc D j)} (hg₀ : Φ g₀ ≠ 0) : τ a = a := by
  have h1 : Expands O κ Ψ (fun k => a * e k) f := by
    intro g
    rw [hΨ g, he g, Finset.mul_sum]
    simp only [mul_assoc]
  have h2 := hc.2 _ _ _ h1 g₀
  have h3 : a * Φ g₀ = τ a * Φ g₀ := by
    rw [← hΨ' g₀, h2, he g₀, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show 1 * τ (a * e k) * _ = _
    rw [one_mul, map_mul, hτ, mul_assoc]
  exact (mul_right_cancel₀ hg₀ h3).symm

theorem conjVec_self_of_rat (j : Fin D.R.m) (τ : ℂ ≃+* ℂ) (v : VsV D j D.what₂.LL)
    (hv : ∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m = (q : D.what₂.LL))
    (x : VsV D j ℂ)
    (hx : (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) :
    ConjVec j τ x x := by
  unfold ConjVec
  rw [hx]
  ext m
  obtain ⟨q, hq⟩ := hv m
  simp [MvPolynomial.coeff_map, hq]

end GlobalTheory.SeriesTie.NormRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsScaleTwistedPlaceCoefficientMapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scale_twisted_place_coefficient_map : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∃ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (cc : VsV D j ℂ →ₗ[ℂ] (X.R.cV j).W) (κ : ℂ), IsLow X j u ∧ ExtC X.R.toRealDat j (inC (X.geo.O j).c') (X.geo.O j).c0' cc ∧ κ ≠ 0 ∧
    (∀ x, X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x) ∈ (baseOf Z c w j).valSpace) ∧
    (∀ x : VsV D j ℂ, harmFn (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS (X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x)) = κ • coefFn (RingHom.id ℂ) (lamV D j) (x : Pol ℂ D.what₂.Tau (Vc D j).rank)) ∧
    IsScale X.R X.geo.v₀ (baseOf Z c w j) κ ∧ IsRoot1 (Z.ν (c.twI w) j (c.sd w) / κ) := by
  first | exact @GlobalTheory.PlaceScale.exists_scale | exact GlobalTheory.PlaceScale.exists_scale | (intros; apply GlobalTheory.PlaceScale.exists_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitPrimeProductOfTwistedPlaceTupleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_primeProduct_of_twistedPlaceTuple : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) ≠ 0 ∧ (∀ P ∈ X.R.Q (Y.tupT (D.what₂.muTw w)), ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) ∧
  IsUnit ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : c.Oe w) := by
  first | exact @GlobalTheory.PlaceUnit.tupPrime_isUnit | exact GlobalTheory.PlaceUnit.tupPrime_isUnit | (intros; apply GlobalTheory.PlaceUnit.tupPrime_isUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelTwistCharacterMemCoefficientIntegersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_twist_character_mem_coefficientIntegers : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ k : (baseOf Z c w j).levJ (twVia Z.ρ ι), (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ) ∈ intLL D := by
  first | exact @GlobalTheory.PlaceRead.LevVal.levLam_twVia_mem_intLL | exact GlobalTheory.PlaceRead.LevVal.levLam_twVia_mem_intLL | (intros; apply GlobalTheory.PlaceRead.LevVal.levLam_twVia_mem_intLL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeTwistedTupleSpanTopStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalLatticeTwistedTuple_span_top : ∀ (D : D7) (w : D.what₂.places.Pl) (j : ℕ), Submodule.span D.what₂.LL (latS (D := D) w j) = ⊤ := by
  first | exact @GlobalTheory.PlaceRead.span_latS | exact GlobalTheory.PlaceRead.span_latS | (intros; apply GlobalTheory.PlaceRead.span_latS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleDatumFormReadsThetaLiftInnerProduc
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefThetaRead

open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult
  Formalism.L2.Theta Formalism.L2.DIV GlobalTheory.ThetaTri GlobalTheory.ThetaRead
open scoped TensorProduct InnerProductSpace

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem fire (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (core : GlobalTheory.Hk3.Core R.toRealDat F.lv2) :
    ThetaFireRow (toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj) Y.IL :=
  ⟨fun μ _ i => GlobalTheory.ThetaPRead.isThetaP_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj core.thP.thF μ i,
    GlobalTheory.ThetaFireLift.thetaFireL R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj core.lev core.grp core.models
      core.thP R.toRealDat.hv0 Y.IL,
    GlobalTheory.LiftResInj.resInjL_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj core.models.inf⟩


set_option maxHeartbeats 1000000 in
theorem ipM_theta (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (core : GlobalTheory.Hk3.Core R.toRealDat F.lv2)
    (hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ) {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m)
    (x : D.what₂.Mt μ (j.1 + 1)) (y : D.what₂.Mj (j.1 + 1))
    (T' T'' : MMap (R.MW j (sg0 D A3.A))) (hT : PiTensorProduct.lift T' = (Y.IL.jMj j y).1)
    (hT' : PiTensorProduct.lift T'' = (Y.IL.jMj j (D.what₂.thetaP μ (j.1 + 1) x)).1) :
    ipM (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) T' T'' =
      ∫ g in R.fdW j, star (PiTensorProduct.lift T' (emb _ (kUnit (R.MW j (sg0 D A3.A)))) g) *
        (∫ h in R.fdV j (Y.tupT μ), thetaKO (R.ωP j (Y.tupT μ)) h g
          (R.ptP j (Y.tupT μ) (R.ioP j (kUnit (R.MW j (sg0 D A3.A))) ((Y.IL.jMt μ hμ j x).1 h))) ∂(R.νV j (Y.tupT μ)))
        ∂(R.νW j) := by
  have hM := core.models
  have hF := fire Y core
  obtain ⟨w, hw1, hw2, hw3⟩ := hF.2.1 μ hμ j x
  have hth := Y.tied.lift.theta μ hμ j x w (hF.1 _ hμ j) hw1 hw2 hw3
  obtain ⟨U, hU, hUw⟩ := hw1
  have hUw' : PiTensorProduct.lift U = w := hUw
  obtain ⟨T₀, hT₀, hT₀y⟩ := (Y.IL.jMj j y).2
  have hTT : T₀ = T' := PiTensorProduct.lift.injective (hT₀y.trans hT.symm)
  subst hTT
  obtain ⟨hT1, hT2⟩ := (mem_goodPart _ _ _ _ _ _).1 hT₀
  have hT'U : T'' = postOn (R.MW j (sg0 D A3.A)) (R.eWf j (sg0 D A3.A)) U := by
    apply PiTensorProduct.lift.injective
    rw [hT', hth, ← hUw']
    exact (lift_post (R.MW j (sg0 D A3.A)) _ U).symm
  have hin : ∀ g, (∫ h in R.fdV j (Y.tupT μ), thetaKO (R.ωP j (Y.tupT μ)) h g
      (R.ptP j (Y.tupT μ) (R.ioP j (kUnit (R.MW j (sg0 D A3.A))) ((Y.IL.jMt μ hμ j x).1 h))) ∂(R.νV j (Y.tupT μ))) =
      PiTensorProduct.lift U (emb _ (kUnit (R.MW j (sg0 D A3.A)))) g := by
    intro g
    have e1 := (hF.1 _ hμ j).eq (Y.IL.jMt μ hμ j x) (kUnit (R.MW j (sg0 D A3.A))) g
    rw [← hw2, ← hUw'] at e1
    exact e1.symm
  obtain ⟨p1, p2⟩ := ipM_proj R.toRealDat hM hX j (mult_le_wall R.toRealDat F.lv2 false j hT1)
    (mult_le_wall R.toRealDat F.lv2 false j hU) hT2
  simp only [hin]
  rw [hT'U]
  refine p1.trans ?_
  by_cases hne : ∀ τ, lowT (R.MW j (sg0 D A3.A)) τ ≠ ⊥
  · exact (integral_kUnit _ hne _ _ _ _ p2).symm
  · push Not at hne
    obtain ⟨τ, hτ⟩ := hne
    have h0 := emb_eq_zero _ hτ
    have hw0 : w = 0 := hF.2.2 j w ⟨U, hU, hUw⟩
      ((congrArg (fun e => w ∘ₗ e) h0).trans (LinearMap.comp_zero _))
    have hU0 : U = 0 := PiTensorProduct.lift.injective (by rw [hUw', hw0, map_zero])
    exact integral_zero_right (R.MW j (sg0 D A3.A)) _ _ _ _ hU0 _


set_option maxHeartbeats 1000000 in
theorem fV_eq (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (core : GlobalTheory.Hk3.Core R.toRealDat F.lv2) {M : MtFam D}
    (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (x : D.what₂.Mt D.what₂.mu0 (i.1 + 1))
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ))
    (hFm : (Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) =
      (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x) :
    GlobalTheory.RefTheta.fV Ad i Fm = (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 := by
  have e : (fun k => Ad.eW D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i
      ((Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))) =
      fun k => (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 ((Ad.PV i).ψ (preF (Ad.PV i) k)) := by
    funext k
    rw [hFm]
    exact Ad.read _ _ i x _
  change (R.cV i).ext (fun k => Ad.eW D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i
      ((Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))) = _
  rw [e]
  obtain ⟨z, hz⟩ : (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 ∈
      LinearMap.range (R.extV i (Y.tupT D.what₂.mu0)) := (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).2.1
  have hz' : (R.cV i).ext ((R.HV i (Y.tupT D.what₂.mu0)).e z) = (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 := hz
  generalize (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 = φ at hz' ⊢
  subst hz'
  exact ext_pre _ (core.models.cV i).1 _ _


set_option maxHeartbeats 1000000 in
theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (x : D.what₂.Mt D.what₂.mu0 (i.1 + 1)) (y : D.what₂.Mj (i.1 + 1)) (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)), (Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x → inner ℂ y (D.what₂.thetaP D.what₂.mu0 (i.1 + 1) x) = GlobalTheory.RefTheta.lamV Ad i hc (GlobalTheory.RefTheta.phi0 Y i) Fm ⟨X.φ y, X.φ_mem y⟩ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hEx M Ad i X hc x y Fm hFm
  have core := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hH.ok.ok2.irr
  have hf := fV_eq Y core Ad i x Fm hFm
  obtain ⟨-, -, -, -, hB, hφ⟩ := Classical.choose_spec (Classical.choose_spec hc)
  have key : inner ℂ y (D.what₂.thetaP D.what₂.mu0 (i.1 + 1) x) = (GlobalTheory.RefTheta.cC hc : ℂ) *
      ∫ g in R.fdW i, star (GlobalTheory.RefTheta.yv hc ⟨X.φ y, X.φ_mem y⟩ g) *
        (∫ h in R.fdV i (Y.tupT D.what₂.mu0), thetaKO (R.ωP i (Y.tupT D.what₂.mu0)) h g
          (GlobalTheory.RefTheta.phi0 Y i ((Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 h))
            ∂(R.νV i (Y.tupT D.what₂.mu0))) ∂(R.νW i) := by
    refine (X.φ_inner _ _).trans ((hB _ (X.φ_mem _) _ (X.φ_mem _)).trans (congrArg (fun z => (GlobalTheory.RefTheta.cC hc : ℂ) * z) ?_))
    exact ipM_theta Y core hX (GlobalTheory.RefTheta.reference_tuple_used D) i x y _ _ (hφ y) (hφ _)
  rw [key, ← hf]
  rfl

end GlobalTheory.RefThetaRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleWeilDatumCharacters
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

namespace GlobalTheory.RefTupleChars

theorem ref_chars : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (i : Fin D.R.m), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).1 (R.C.mu0 i) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).2 (R.C.mu0 i * R.C.eta⁻¹) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _ hEx i
  have hlev := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1.lev
  have ht : GlobalTheory.RefTheta.t0 Y = A3.A.μ0 := by
    show Y.tupT D.what₂.mu0 = A3.A.μ0
    rw [← Y.tup0, Y.tupT_tup]
  rw [ht]
  have hxC := hlev.xi A3.A.μ0
  rw [hlev.xi_base] at hxC
  have hxi : R.toLevCh.xi A3.A.μ0 = 1 := MonoidHom.ext fun x =>
    GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one hxC x
  have e : Formalism.IndefR.Lift.chrTh (R.toLevCh.mu A3.A.μ0) R.eta (i.1 + 1) =
      (R.toLevCh.mu0 (i.1 + 1), R.toLevCh.mu0 (i.1 + 1) * R.eta⁻¹) := by
    simp only [Formalism.IndefR.Lift.chrTh, Formalism.IndefR.Links.LevCh.mu, Formalism.IndefR.Lift.tup, hxi, mul_one]
  rw [e]
  have hm := hlev.mu0 i
  have h2 := GlobalTheory.ClassScalarValue.chrEq_mul_inv hm hxC hlev.eta
  rw [hxi, mul_one, mul_one] at h2
  exact ⟨hm, h2⟩

end GlobalTheory.RefTupleChars
end

