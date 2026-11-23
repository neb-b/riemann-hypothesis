module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedThetaGeneratorEqClassSumIntegralForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0926
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0921

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacteristicFunctionIntegralApply
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefTheta

open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame GlobalTheory.ThetaTri
open scoped TensorProduct

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem reference_tuple_used (D : D7) : Used0 D D.what₂.mu0 := Or.inl rfl

abbrev t0 (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : T := Y.tupT D.what₂.mu0

def repY (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : D.what₂.FT → NG.FinTyp D.host.E D.R.r :=
  fun σ => rowRepR R.θ (Y.eFT σ)

def IsCanonR (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (i : Fin D.R.m) {j : ℕ} (hj : i.1 + 1 = j) (X : GlobalTheory.NPin.RowMod D rep j) : Prop :=
  ∃ (e : X.A →ₗ[ℂ] Mult.MMap (R.MW i (sg0 D A3.A))) (c : ℝ), Function.Injective e ∧ 0 < c ∧
    X.C.map e = Minf R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) ∧
    (∀ h x, e (X.ρ h x) = actM (Y.PW i) (R.MW i (sg0 D A3.A)) h (e x)) ∧
    (∀ x ∈ X.C, ∀ y ∈ X.C, X.B x y = (c : ℂ) * Mult.ipM (R.MW i (sg0 D A3.A)) (R.νW i) (R.fdW i) (e x) (e y)) ∧
    ∀ y : D.what₂.Mj (i.1 + 1), PiTensorProduct.lift (e (X.φ (hj ▸ y))) = (Y.IL.jMj i y).1

variable {Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

def eC {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) : X.A →ₗ[ℂ] Mult.MMap (R.MW i (sg0 D A3.A)) :=
  Classical.choose hc

def cC {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) : ℝ :=
  Classical.choose (Classical.choose_spec hc)

def yv {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    ↥X.C →ₗ[ℂ] (Formalism.L2.Theta.GA D (Wc D i) → ℂ) :=
  LinearMap.applyₗ (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype)
      (kUnit (R.MW i (sg0 D A3.A)))) ∘ₗ
    (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ eC hc ∘ₗ X.C.subtype

variable {M : MtFam D}

def fV (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) :
    ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ) →ₗ[ℂ]
      (Formalism.L2.Theta.GA D (Vc D i) → (R.cV i).W) :=
  (R.cV i).ext ∘ₗ
    { toFun := fun F k => Ad.eW D.what₂.mu0 (reference_tuple_used D) i
        ((F : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))
      map_add' := fun F F' => by funext k; simp
      map_smul' := fun c F => by funext k; simp }

def omStd (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (t : T) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
  (R.ωP i t).comp ((Ad.PV i).ψ.prodMap (Y.PW i).ψ)

def Om (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    Submodule ℂ ((R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) :=
  OmSub (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) R.ψ (omStd Ad i (t0 Y))

def om (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ ↥(Om Ad i hc) :=
  omSub (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) R.ψ (omStd Ad i (t0 Y))

def lamV (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) (φ : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ))
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) (y : ↥X.C) : ℂ :=
  GlobalTheory.ThetaTri.lamV (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) (cC hc : ℂ) φ Fm y

def lamL (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    ↥(Om Ad i hc) →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ) →ₗ[ℂ] ↥X.C →ₗ⋆[ℂ] ℂ :=
  lam (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) (cC hc : ℂ) R.ψ
    (omStd Ad i (t0 Y))


variable (Y) in
def phi0 (i : Fin D.R.m) : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A3.A))) (R.BV i)
    (onb (R.MW i (sg0 D A3.A))) (R.vP i (t0 Y)) ∘ₗ R.ioP i (kUnit (R.MW i (sg0 D A3.A)))

end GlobalTheory.RefTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistViaEmbeddingGoodConjugate
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

noncomputable section

namespace GlobalTheory.PlaceRead

open GlobalTheory.TwistGood

theorem twistOf_good (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X) (hρ : ρ.Good)
    (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ)
    (e : X.Ok i k →+* ℂ) (hψ : Formalism.MainNotions.IntegralHeckeForms.TwOK i k Q ψ) :
    (twistOf ρ.rc e (ρ.ch i) Q ψ).Good ∧ (ρ.B i j b).admitted (twistOf ρ.rc e (ρ.ch i) Q ψ).Q := by
  classical
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := hψ
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) Q) := _root_.GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D N X ρ hρ i j b Q hsplit hdisj
  let g : (X.Ok i k)ˣ →* Circle := unitPart.comp (Units.map e.toMonoidHom)
  have hkey : charOf ρ.rc e ψ = ρ.rc.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  have hz : X.zk i k ^ (X.l i ^ k) = 1 := Units.ext (by simpa using (X.zk_prim i k).pow_eq_one)
  have hpow : ∀ σ, ψ σ ^ (X.l i ^ k) = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine ⟨?_, hadm⟩
  show (⟨half (ρ.ch i) Q, charOf ρ.rc e ψ, resOf (charOf ρ.rc e ψ)⟩ : Twist D Circle).Good
  rw [hkey]
  refine GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D N X ρ.rc hρ.rc Circle (g.comp ψ) (X.l i) (X.lPrime i).out
    (fun σ => ⟨k, by rw [MonoidHom.comp_apply, ← map_pow, hpow, map_one]⟩) ?_ ?_ _ ?_ ?_ ?_
  · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) hopen
  · intro x x' hx
    show g (ψ x') = (g (ψ x))⁻¹
    rw [hanti x x' hx, map_inv]
  · obtain ⟨P, -, h2, h3⟩ := hadm.1.split
    exact h3.mono (Finset.subset_union_right.trans h2)
  · intro P hP hl
    exact Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 (X.twistExcludedPlaces_contains_residueChar i (show P ∈ placesOver D.host.E (X.l i) from hl))
  · intro v hv hnc B hB σ hσ
    have hvQ : v ∉ Q := by
      intro hvQ
      by_cases hc : v ∈ ρ.ch i
      · exact hv (mem_half.2 ⟨hvQ, hc⟩)
      · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
        have hv'Q : v' ∈ Q := ramExactly_conj X ψ _ hanti hram v hvQ v' hv'
        have hne := ne_of_split (hsplit v hvQ) hv'
        have hv'c : v' ∈ ρ.ch i := by
          by_contra h
          exact hc (((hρ.ch i).pair v v' hv' hne).2 h)
        exact hnc v' (mem_half.2 ⟨hv'Q, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
    have h1 : ψ σ = 1 := by
      by_contra h
      exact hvQ ((hram v B hB).1 ⟨σ, hσ, h⟩)
    rw [MonoidHom.comp_apply, h1, map_one]

theorem twVia_good : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → ∀ (j : Fin D.R.m) (ι : KE c w →+* ℂ),
  (twVia ρ ι).Good ∧ (ρ.B (c.twI w) j (c.sd w)).admitted (twVia ρ ι).Q ∧ ∀ τ : ℂ ≃+* ℂ, ConjChar τ (twVia ρ ι) (twVia ρ ((τ : ℂ →+* ℂ).comp ι)) := by
  intro D c w ρ hρ hψ j ι
  obtain ⟨h1, h2⟩ := twistOf_good D D.nd D.ntw ρ hρ (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) (viaOk ι) hψ
  refine ⟨h1, h2, fun τ => ⟨rfl, fun x => ?_⟩⟩
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  have hn : D.ntw.l (c.twI w) ^ (c.k' w) ≠ 0 := pow_ne_zero _ (D.ntw.lPrime (c.twI w)).out.ne_zero
  have hp : chr c w σ ^ (D.ntw.l (c.twI w) ^ (c.k' w)) = 1 := by
    obtain ⟨n, hn⟩ := hψ.2.2.2.2.1 σ
    have hz : D.ntw.zk (c.twI w) (c.k' w) ^ (D.ntw.l (c.twI w) ^ (c.k' w)) = 1 :=
      Units.ext (by simpa using (D.ntw.zk_prim (c.twI w) (c.k' w)).pow_eq_one)
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  change ((charOf ρ.rc (viaOk ((τ : ℂ →+* ℂ).comp ι)) (chr c w) x : Circle) : ℂ) =
    τ ((charOf ρ.rc (viaOk ι) (chr c w) x : Circle) : ℂ)
  rw [charOf_eq ρ.rc _ hψ.2.2.1 hσ hn hp, charOf_eq ρ.rc _ hψ.2.2.1 hσ hn hp]
  rfl

end GlobalTheory.PlaceRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumsTwistedDefiniteFormsRational
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

noncomputable section

namespace GlobalTheory.ClassSumRat

variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)

theorem add_mem_range {k : ℕ} {x y : GA D (Wc D j) → ℂ} (hx : x ∈ Set.range (rdK rd hρ k)) (hy : y ∈ Set.range (rdK rd hρ k)) :
    x + y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  exact ⟨x + y, map_add _ _ _⟩

theorem zero_mem_range {k : ℕ} : (0 : GA D (Wc D j) → ℂ) ∈ Set.range (rdK rd hρ k) := ⟨0, map_zero _⟩

theorem e_smul_mem_range {k : ℕ} (c : FractionRing (D.ntw.O i)) {y : GA D (Wc D j) → ℂ} (hy : y ∈ Set.range (rdK rd hρ k)) :
    ρ.e i b c • y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨x, rfl⟩ := hy
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add (f := _), smul_add]; exact add_mem_range hρ rd hx hy
  | tmul a f => exact ⟨a ⊗ₜ (c • f), by rw [rdK_tmul, rdK_tmul, LinearMap.map_smulₛₗ, smul_comm]⟩

theorem ek_smul_mem_range {k : ℕ} (a : FractionRing (D.ntw.Ok i k)) {y : GA D (Wc D j) → ℂ} (hy : y ∈ Set.range (rdK rd hρ k)) :
    ρ.ek i b k a • y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨p, d, hd, e⟩ := D.ntw.Ok_gen i k a
  generalize Polynomial.aeval (D.ntw.zk i k : D.ntw.Ok i k) p = u at e
  have h1 : ρ.ek i b k a * ρ.eO i b d = ρ.eOk i b k u := by
    rw [← hρ.ek_e i b k d]
    exact (map_mul (ρ.ek i b k) _ _).symm.trans (congrArg (ρ.ek i b k) e)
  have hd0 : ρ.eO i b d ≠ 0 := fun h => hd (ρ.eO_injective i b (h.trans (map_zero _).symm))
  have h2 : ρ.ek i b k a = ρ.e i b (algebraMap (D.ntw.O i) _ d)⁻¹ * ρ.eOk i b k u := by
    rw [map_inv₀, ← h1, mul_comm (ρ.ek i b k a)]
    exact (inv_mul_cancel_left₀ hd0 _).symm
  obtain ⟨x, rfl⟩ := hy
  rw [h2, mul_smul]
  exact e_smul_mem_range hρ rd _ ⟨u • x, LinearMap.map_smulₛₗ _ _ _⟩


include hρ in
theorem exists_rep (t : Twist D Circle) (h : GA D (Vc D j)) : ∃ (γ : GQ (Vc D j)) (s : Finset (Pl D.host.E)) (h' : GA D (Vc D j))
    (κ : (ρ.B i j b).levJ t), SplitSet s ∧ (∀ v ∈ s, ((ρ.bad i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) ∧ h' ∈ GfC (Vc D j) ∧
      SuppAt (idem s) (Vc D j) h' ∧
      finPt (Vc D j) h = Bridge.ratF (Vc D j) γ * finPt (Vc D j) h' * (κ : Bridge.Gf (Vc D j)) := by
  obtain ⟨N₀, hN₀, hK⟩ := GlobalTheory.LevFinCong.exists_finCong_lev D (Vc D j) (ρ.B i j b).F.βS ((ρ.B i j b).levS t)
  have hbad : 0 < ρ.bad i := Nat.pos_of_ne_zero (hρ.bad_ne i)
  have hK' : ∀ k ∈ GfC (Vc D j), GlobalTheory.Member.FinCong (Vc D j) N₀ k → FWT.fin (Vc D j) k ∈ (ρ.B i j b).levJ t :=
    fun k hk hc => ((ρ.B i j b).finPt_mem_levJ _ hk).2 (hK k hk hc).1
  obtain ⟨h', ⟨hh', hs⟩, γ, k, e⟩ := GlobalTheory.SplitReps.exists_split_rep (Vc D j) hN₀ hK' hbad (finPt (Vc D j) h)
  obtain ⟨-, e', P, hP, hoff, hsupp⟩ := GlobalTheory.SplitReps.splitOffBad_of_suppSplit (Vc D j) (ρ.bad i) h' hh' hs
  refine ⟨γ, P, h', k, ⟨e', hP⟩, hoff, hh', ?_, e⟩
  rw [idem_eq hP]
  exact hsupp

theorem series_datum (hR : RatTwist hρ rd) {k Q ψ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q) {s h P}
    (hd : ρ.IsDatum i j b s h P) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b k Q ψ).chi) ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ)) h P ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨ht, hadm, hval⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have h1 := hR k Q ψ hψ hQ s h P hd ⟨1, GlobalTheory.SplitLinear.suppAt_one _ _, rfl⟩
  rw [mul_one, GlobalTheory.TwTraceCx.gen_eq_smul (hρ.base i j b) ht hadm (hρ.weil_base i j b) (hρ.weil i j b _ ht)] at h1
  obtain ⟨u, hu⟩ := hval (detRoot (Vc D j) h)
  have hc : ((detChar (Vc D j) (ρ.tw i b k Q ψ).chi h : Circle) : ℂ) = ρ.ek i b k (algebraMap (D.ntw.Ok i k) _ u) := hu
  have h2 := ek_smul_mem_range hρ rd (algebraMap (D.ntw.Ok i k) _ u)⁻¹ h1
  rwa [map_inv₀, ← hc, inv_smul_smul₀ (Circle.coe_ne_zero _)] at h2

theorem term_mem (hR : RatTwist hρ rd) {k Q ψ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q) {F} (hF : F ∈ ρ.mt i j b k Q ψ)
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b k Q ψ).chi) ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ)) h (F (finPt _ h)) ∈
      Set.range (rdK rd hρ k) := by
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have hB := hρ.base i j b
  obtain ⟨hF1, hF2⟩ := ((ρ.B i j b).mem_mtLat _ _ _).1 hF
  obtain ⟨γ, s, h', κ, hs, hoff, hh', hsupp, e⟩ := exists_rep hρ (i := i) (b := b) (ρ.tw i b k Q ψ) h
  have hlaw := ((ρ.B i j b).mem_formsC.1 hF1).2 γ (finPt _ h') κ
  have hinv : ((ρ.B i j b).act ((γ⁻¹ : GQ (Vc D j)) : GA D (Vc D j))) ((ρ.B i j b).act (γ : GA D (Vc D j)) (F (finPt _ h'))) =
      F (finPt _ h') := by
    rw [← mul_apply_eq_comp, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, one_apply_eq_self]
  rw [e, hlaw, LinearMap.map_smul, GlobalTheory.BaseClassSum.series_move hB (D.sp.V_sig _) ht hadm (hρ.weil i j b _ ht) hh hh' γ κ e, hinv,
    smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  have hspan : F (finPt _ h') ∈ Submodule.span (ρ.eOk i b k).range
      (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) :=
    GlobalTheory.SmallSpan.harmLat_le_span (RingHom.id _) (embLL0 D) (labLL0 D) (ρ.eO i b).range (ρ.eOk i b k).range
      (hρ.isCoefRing_k i b k).int _ _ hB.wt (GlobalTheory.CoefLatConj.pq_le hB) (GlobalTheory.SmallSpan.isLattice_latAt hB.frame _) (hF2 _)
  generalize F (finPt _ h') = P at hspan
  induction hspan using Submodule.span_induction with
  | mem P hP => exact series_datum hρ rd hR hψ hQ ⟨hs, hoff, hh', hsupp, hP⟩
  | zero => rw [map_zero]; exact zero_mem_range hρ rd
  | add x y _ _ hx hy => rw [map_add]; exact add_mem_range hρ rd hx hy
  | smul a x _ hx =>
    obtain ⟨_, u, rfl⟩ := a
    have h2 := ek_smul_mem_range hρ rd (algebraMap (D.ntw.Ok i k) _ u) hx
    rw [← map_smul] at h2
    exact h2

theorem sum_mem_range : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (rd : Rd ρ D.nexp i j b) (T : CellTie hρ D.nexp rd), RatTwist hρ rd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  ∀ k Q ψ, TwOK i k Q ψ → ClsQ (D := D) Q → ∀ f, ρ.sum i j b k Q ψ (T.rdV k Q ψ f) ∈ Set.range (rdK rd hρ k) := by
  intro D ρ hρ i j b rd T hR _ k Q ψ hψ hQ f
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have hc := hρ.classes i j b _ ht hadm
  have hf : f ∈ Submodule.span (FractionRing (D.ntw.Ok i k)) (D.nexp.MtLat i ((j : ℕ) + 1) b k Q ψ : Set (D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ)) := by
    rw [D.nexp.MtLat_span]; trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    have hF := (T.mtLat_iff k Q ψ hψ _).2 ⟨f, hf, rfl⟩
    rw [Setup.sum, Base.classSum_apply]
    refine Finset.sum_induction _ (· ∈ Set.range (rdK rd hρ k)) (fun _ _ => add_mem_range hρ rd) (zero_mem_range hρ rd) fun c _ => ?_
    rw [← map_natCast (ρ.ek i b k), ← map_inv₀]
    exact ek_smul_mem_range hρ rd _ (term_mem hρ rd hR hψ hQ hF (hc.fin c))
  | zero => rw [map_zero, map_zero]; exact zero_mem_range hρ rd
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact add_mem_range hρ rd hx hy
  | smul a x _ hx => rw [LinearMap.map_smulₛₗ, map_smul]; exact ek_smul_mem_range hρ rd a hx

end GlobalTheory.ClassSumRat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientLatticeEqSmallCoefficientField
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

noncomputable section

namespace GlobalTheory.PlaceSmall

section BaseChange

variable {E K₀ K ι : Type} [Field E] [NumberField E] [Field K₀] [NumberField K₀] [Field K] [NumberField K] [Fintype ι]
  {n : ℕ}

theorem map_mem_nabAtr (f : K₀ →+* K) (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E))
    (hM : Submodule.IsFullLattice E M) {x : VV K₀ lam} (hx : x ∈ nabAtr emb lam M) :
    (⟨MvPolynomial.map f x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV f lam _ x.2⟩ : VV K lam) ∈
      nabAtr (fun τ => f.comp (emb τ)) lam M := by
  classical
  unfold nabAtr nabK at hx ⊢
  rw [Submodule.mem_comap] at hx ⊢
  change MvPolynomial.map f x.1 ∈ nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)
  change x.1 ∈ nabP lam (fun τ => dualFr (tauLat emb τ M)) at hx
  refine GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => ?_
  obtain ⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀),
      ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by
    refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩
    have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at h1
    exact w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))
  have hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal :=
    fun t ht h => ht ((hw₀ t).2 h)
  obtain ⟨hLoc, -, -⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hT : ∀ τ, Submodule.IsFullLattice K₀ (tauLat emb τ M) := fun τ => tauLatLattice E K₀ ι n emb τ M hM
  choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀
  let B₀ : ι → GL (Fin n) K₀ := fun τ => inside₂ K₀ n (C τ)
  have hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ)) := fun τ =>
    GlobalTheory.NabBC.isBasisAt_dualFr_tauLat_comp f emb τ M hM w₀ w hw (C τ) (hC τ)
  have L1 := (hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1
  have L0 := (hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1
  have hx0 : x.1 ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M)) :=
    GlobalTheory.NabBC.mem_localization_of_mem' _ hx
  rw [L0] at hx0
  obtain ⟨g, ⟨s, hs, hsg⟩, hg⟩ := hx0
  rw [L1]
  refine ⟨MvPolynomial.map f g, ⟨RingOfIntegers.mapRingHom f s, hw s hs, ?_⟩, ?_⟩
  · refine (congrArg (· ∈ nabStd K lam) (GlobalTheory.NabBC.map_smul_int f s g)).mpr ?_
    have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1
    have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
    have h3 : MvPolynomial.map f (s • g) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))) :=
      Submodule.subset_span ⟨_, hsg, rfl⟩
    rw [h1, ← h2] at h3
    have h4 : (MvPolynomial.map (RingHom.id K) '' (nabStd K lam : Set (Pol K ι n))) = (nabStd K lam : Set (Pol K ι n)) := by
      ext y
      simp [MvPolynomial.map_id]
    rw [h4, Submodule.span_eq] at h3
    exact h3
  · change actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) = MvPolynomial.map f x.1
    rw [← GlobalTheory.ValCmp.use₂]
    exact congrArg (MvPolynomial.map f) hg

end BaseChange

theorem harmLat_le {D : D7} {m n : ℕ} {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K] (f : K₀ →+* K)
    (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K₀)) (O : Subring ℂ) (w : GlobalTheory.ExportSeries.Weight D n) (B : GLR D n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsFullLattice D.host.E M) :
    harmLat (σ.comp f) emb O m w B M ≤ harmLat σ (fun τ => f.comp (emb τ)) O m w B M := by
  refine inf_le_inf_left _ (Submodule.comap_mono (Submodule.span_mono ?_))
  rintro _ ⟨F, hF, rfl⟩
  refine ⟨_, map_mem_nabAtr f emb w.lam M hM hF, funext fun y => ?_⟩
  rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom]

theorem coefLat_eq_small : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ O : Subring ℂ, intLL D ≤ O → ∀ h, B.coefLat D.what₂.embLL (labLL D) O h = B.coefLat (embLL0 D) (labLL0 D) O h := by
  intro D S T B hB O hO h
  have hm : ∀ τ, B.w.p τ + B.w.q τ ≤ T.rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (Formalism.BasicNotions.TH.tauE D τ)
    rw [← h1] at h2
    exact h2.le
  have hS := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice S B.F.ΛS hB.frame.sdS
  have hM : Submodule.IsFullLattice D.host.E (B.latAt h) :=
    Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.2 hS.fg) hS.span_eq_top _
  refine le_antisymm (fun P hP => ?_)
    (harmLat_le D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O B.w B.F.BS hM)
  have h1 := GlobalTheory.SmallSpan.harmLat_le_span D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O O (fun a => hO ⟨a, rfl⟩)
    B.w B.F.BS hB.wt hm hM hP
  rw [Submodule.span_eq] at h1
  exact h1

end GlobalTheory.PlaceSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParam
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.ParAsm

theorem one_le_nV (D : D7) : 1 ≤ D.R.nV := by
  have := D.R.m_add_three_le_k
  simp only [Ranks.nV, Ranks.r] at *
  omega

end GlobalTheory.ParAsm
end

