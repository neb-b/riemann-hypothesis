module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsActFockVectorsAnyDatum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.FockAnyDatum

theorem om_ioP_of_datum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (φ : WO (Vc D i) (Wc D i) → ℂ), IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) R.Pg Q ξR (R.vacP i) φ → ∀ u ∈ GinfC (Vc D i), ∀ x w, R.ωP i A.μ0 (u, 1) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i x w)) = pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i x ((R.cV i).ρ u w)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξR Q φ hφ u hu x w
  have hθ : IsInfFam R.θ := hR.models.inf
  have hω := hR.thP.ωP
  have hthφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ := by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hφ
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  have hthv : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i A.μ0) := by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hR.thP.vP i A.μ0
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  have hvφ := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hφ hthφ
  have hvv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hR.thP.vP i A.μ0) hthv
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ =>
    GlobalTheory.JointHarm.onb_eq_one (hR.models.BV i τ)
  have hBu : ∀ τ, IsUnit (R.BV i τ) := fun τ => IsUnit.of_mul_eq_one_right _ (hBS τ)
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights D i (sg0 D A) (sgAt_mk _ R.hv0) (R.MW i (sg0 D A)) (hR.models.order i)
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank := fun τ =>
    (_root_.GlobalTheory.PairWeightArith.arithAt D i τ).rank.1.trans hrk.symm
  have hfr : ∀ τ, (R.MW i (sg0 D A)).fr τ * ((R.MW i (sg0 D A)).fr τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ))
  have e : (fun τ => (R.MW i (sg0 D A)).fr τ * compAt R.θ τ (Formalism.L2.Theta.mt (Wc D i) 1) *
      ((R.MW i (sg0 D A)).fr τ)⁻¹) = 1 := by
    funext τ; rw [GlobalTheory.JointHarm.compAt_mt_one', Matrix.mul_one, hfr]; rfl
  have act := fun (f : WO (Vc D i) (Wc D i) → ℂ) (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) hv =>
    _root_.GlobalTheory.FockCompactAction.om_pureTensorO_eq_fact D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i A.μ0) _ (R.MW i (sg0 D A)) (R.BV i) (hω i A.μ0) hθ
      (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq (hR.models.order i) _ _
      (fun τ => (_root_.GlobalTheory.PairInfTypes.infTypesAt D T0 R.toLevCh A.μ0 hR.lev i A.μ0 τ).chiV)
      (fun τ => (_root_.GlobalTheory.PairInfTypes.infTypesAt D T0 R.toLevCh A.μ0 hR.lev i A.μ0 τ).chiW) x₁ x₂ x₃ (fun τ => (hx τ).1) (fun τ => (hx τ).2.1)
      (fun τ => (hx τ).2.2.1) f hf hv u hu 1 (one_mem _)
      (fun τ => by rw [congrFun e τ]; exact GlobalTheory.JointHarm.one_mem_K)
  have aφ := (act φ hthφ hvφ).2
  have av := (act _ hthv hvv).2
  rw [e] at aφ av
  have hcV : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) ((fun _ => (1 : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ)) τ) :=
    fun τ => by
      have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (hBu τ)
      have h1 := Matrix.mul_nonsing_inv _ hu'
      have hG : gramAt D (Vc D i) τ = ((R.BV i τ)⁻¹)ᴴ * (R.BV i τ)⁻¹ := by
        calc gramAt D (Vc D i) τ
            = ((R.BV i τ)⁻¹)ᴴ * ((R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ) * (R.BV i τ)⁻¹ := by
              rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one,
                Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
          _ = _ := by rw [hBS τ, Matrix.mul_one]
      refine ⟨Matrix.one_mul _, by simp, ?_⟩
      rw [Matrix.mul_one, hG]
      exact Matrix.PosDef.conjTranspose_mul_self _
        (Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 (hBu τ)))
  have hne : R.vP i A.μ0 ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hR.lev.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hR.lev.βW i))
      (hrk.trans_le (r_le_V i)) (hR.thP.vP i A.μ0)
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) (hω i A.μ0).std hθ
    (fun _ => 1) (R.BV i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) _ hcV
    (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ) (hR.models.BV i)
    (fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hR.models.order i τ))
    (D.sp.V_sig _) (D.sp.W_sig _) (R.vP i A.μ0) hthv hvv hne
  have key := (hR.thP.ioP i A.μ0).1 u hu x w
  unfold RealDat.ptP at key
  rw [av] at key
  rw [aφ, hinj key]

end GlobalTheory.FockAnyDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantSupportedEqSmulVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacUniq

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem schr_schr {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → K) × (κ → K)) (φ : (κ → K) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : K) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  have key : (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) + ((x + w.1) ⬝ᵥ w'.2 + ⅟(2 : K) * (w'.1 ⬝ᵥ w'.2)) =
      ⅟(2 : K) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) +
        (x ⬝ᵥ (w + w').2 + ⅟(2 : K) * ((w + w').1 ⬝ᵥ (w + w').2)) := by
    have h2 : ⅟(2 : K) * 2 = 1 := invOf_mul_self 2
    simp only [Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
    linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2
  show ψ _ * (ψ _ * φ (x + w.1 + w'.1)) = ψ _ * (ψ _ * φ (x + (w + w').1))
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key, Prod.fst_add, add_assoc]

theorem acts_unique {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ] {φ : (κ → Fv F v) → ℂ}
    {r : (κ → AF F) → ℂ} (hr : Rest (evFin F v) φ r) {x₀ : κ → AF F} (hx₀ : r x₀ ≠ 0)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h1 : Acts (evFin F v) T φ φ₁) (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i)) with hz
  have hza : At (evFin F v) z := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hrx : r (x₀ + z) = r x₀ := hr.1 x₀ z hza
  have hy : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [hz, Pi.add_apply, map_add (f := _), GlobalTheory.LatVac.evFin_liftV, add_sub_cancel]
  have e := congrFun ((h1 r hr).symm.trans (h2 r hr)) (x₀ + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ hx₀ e

theorem phase {V : Type} [AddCommGroup V] [Module ℂ V] {φ ψ S : V} {c χ : ℂ} (hne : φ ≠ 0)
    (h1 : φ = (c * χ) • φ) (h2 : ψ = c • S) : S = χ • ψ := by
  have hcχ : c * χ = 1 := by
    by_contra hne'
    have h4 : (c * χ - 1) • φ = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact hne ((smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hne'))
  rw [h2, smul_smul, mul_comm, hcχ, one_smul]

theorem sa_bd_uniq : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ)) (hι : Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)), (∀ s ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂, ∀ Y, g (Y + s) = g Y) →
      (∀ Y ∉ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂, g Y = 0) → ∃ c : ℂ, g = c • ι φ₀ := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ θ hθ ι hι φ₀ h0 hne hfix huniq g hg hSa hBd
  have hψc : Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 Bs.v₁
  have hSB : ∀ γ, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁),
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ ∈ GlobalTheory.WeilM.SB _ :=
    fun γ φ hφ => GlobalTheory.SchrSBFin.schr_mem_SB _ _ hψc _ _ hφ
  have hat : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁, At (evFin D.host.F Bs.v₁) γ :=
    (GlobalTheory.LatVac.latAtV_at_stable _ _ _).1
  have hacts : ∀ γ, At (evFin D.host.F Bs.v₁) γ → ∀ φ, Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ
      (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) :=
    fun γ hγ φ => GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ
  obtain ⟨r, hr, x₀, hx₀⟩ := _root_.GlobalTheory.RestComplement.exists_rest_ne_zero Bs.v₁ φ₀ h0
  obtain ⟨χ, hχ⟩ : ∃ χ : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E) → ℂ, ∀ γ, χ γ =
      Bs.ψ (⅟(2 : AF D.host.F) * symp (cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
        (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) γ γ) := ⟨_, fun _ => rfl⟩
  have hφ₀ : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ₀ = χ γ • φ₀ := by
    intro γ hγ
    rw [hχ]
    exact acts_unique Bs.v₁ hr hx₀ _ _ _ (hacts γ (hat γ hγ) φ₀) (hfix γ hγ)
  have hχ1 : ∀ u, At (evFin D.host.F Bs.v₁) u →
      (u.map (piW Bs.τ₁) = 0 ∨ u.map (piW (Bs.τ₁.comp D.sp.cm.sig)) = 0) → χ u = 1 := by
    intro u hu h
    rw [hχ, GlobalTheory.T.traceSymplectic_self_zero_splitSupported Bs Γ X om om' hTr u hu h, mul_zero, AddChar.map_zero_eq_one]
  obtain ⟨ψ₀, hψ₀, hιψ₀⟩ := hι.bij.surjOn hg
  have hA : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁, γ.map (piW Bs.τ₁) = 0 →
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀ = ψ₀ := by
    intro γ hγ h
    refine hι.bij.injOn (hSB γ ψ₀ hψ₀) hψ₀ ?_
    funext Y
    have ht : ι (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀) Y =
        ι ψ₀ (Y + GlobalTheory.VacShape.coBar Bs Γ γ) :=
      hι.trans γ (hat γ hγ) h ψ₀ hψ₀ _ (hSB γ ψ₀ hψ₀) (hacts γ (hat γ hγ) ψ₀) Y
    have hs : GlobalTheory.VacShape.coBar Bs Γ γ ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ := ⟨γ, hγ, h, rfl⟩
    rw [ht, hιψ₀]
    exact hSa _ hs Y
  have hB : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      γ.map (piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 →
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀ = ψ₀ := by
    intro γ hγ h
    refine hι.bij.injOn (hSB γ ψ₀ hψ₀) hψ₀ ?_
    funext Y
    obtain ⟨x, hx, hx0, rfl⟩ := GlobalTheory.T.exists_splitSupported_oppositeLagrangian_coordinate Bs Γ X om om' hTr Y
    have hm : ι (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀) (GlobalTheory.VacShape.coBar Bs Γ x) =
        Bs.ψ (symp (cA D.sp.cm.sig) (-1) (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) x γ) *
          ι ψ₀ (GlobalTheory.VacShape.coBar Bs Γ x) :=
      hι.mult γ (hat γ hγ) h ψ₀ hψ₀ _ (hSB γ ψ₀ hψ₀) (hacts γ (hat γ hγ) ψ₀) x hx hx0
    rw [hm, hιψ₀]
    by_cases hY : GlobalTheory.VacShape.coBar Bs Γ x ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂
    · rw [hY x hx hx0 rfl γ hγ h, one_mul]
    · rw [hBd _ hY, mul_zero]
  have hfixψ : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
        (Bs.ψ (⅟(2 : AF D.host.F) * symp (cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
          (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) γ γ) • ψ₀) := by
    intro γ hγ
    rw [← hχ]
    obtain ⟨γA, hγA, γB, hγB, rfl, hA0, hB0⟩ := GlobalTheory.T.tensorLatticeSplitPlace_eq_add_componentParts Bs Γ X om om' hTr L₁ L₂ γ hγ
    have e0 : GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (γA + γB) =
        GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA + GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB := map_add _ _ _
    have hc := schr_schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA)
      (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB)
    have hφA : schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA) φ₀ = φ₀ := by
      rw [hφ₀ γA hγA, hχ1 γA (hat γA hγA) (Or.inl hA0), one_smul]
    have hφB : schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB) φ₀ = φ₀ := by
      rw [hφ₀ γB hγB, hχ1 γB (hat γB hγB) (Or.inr hB0), one_smul]
    have h1 := hc φ₀
    rw [hφB, hφA, ← e0, hφ₀ _ hγ, smul_smul] at h1
    have h2 := hc ψ₀
    rw [hB γB hγB hB0, hA γA hγA hA0, ← e0] at h2
    have key := phase hne h1 h2
    have := hacts _ (hat _ hγ) ψ₀
    rwa [key] at this
  obtain ⟨c, hc⟩ := huniq ψ₀ hψ₀ hfixψ
  exact ⟨c, by rw [← hιψ₀, hc, map_smul]⟩

end GlobalTheory.VacUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartialEvaluation
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SliceSB

theorem continuous_sumElim {k : Type} [TopologicalSpace k] {κ κ' : Type} :
    Continuous (fun p : (κ → k) × (κ' → k) => (Sum.elim p.1 p.2 : κ ⊕ κ' → k)) := by
  refine continuous_pi fun i => ?_
  cases i with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr i => exact (continuous_apply i).comp continuous_snd

theorem slice_mem : ∀ (k : Type) [TopologicalSpace k] [T2Space k] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ f ∈ SB (κ ⊕ κ' → k),
    (∀ x₁ : κ → k, (fun x₂ : κ' → k => f (Sum.elim x₁ x₂)) ∈ SB (κ' → k)) ∧
      ∀ l : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ, (fun x₁ : κ → k => l fun x₂ => f (Sum.elim x₁ x₂)) ∈ SB (κ → k) := by
  intro k _ _ κ κ' _ _ f hf
  obtain ⟨hlc, hcs⟩ := hf
  have hΦ := continuous_sumElim (k := k) (κ := κ) (κ' := κ')
  refine ⟨fun x₁ => ?_, fun l => ?_⟩
  · have he : Continuous (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k)) :=
      hΦ.comp (Continuous.prodMk continuous_const continuous_id)
    have hli : Function.LeftInverse (fun z : κ ⊕ κ' → k => z ∘ Sum.inr) (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k)) :=
      fun x₂ => rfl
    have hce : Topology.IsClosedEmbedding (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k)) :=
      hli.isClosedEmbedding (continuous_pi fun i => continuous_apply _) he
    exact ⟨hlc.comp_continuous he, hcs.comp_isClosedEmbedding hce⟩
  · set K := (fun z : κ ⊕ κ' → k => z ∘ Sum.inr) '' tsupport f
    have hK : IsCompact K := hcs.isCompact.image (continuous_pi fun i => continuous_apply _)
    have hloc : IsLocallyConstant (fun x₁ : κ → k => fun x₂ : κ' → k => f (Sum.elim x₁ x₂)) := by
      rw [IsLocallyConstant.iff_eventually_eq _]
      intro x₀
      have hF : IsLocallyConstant (fun p : (κ → k) × (κ' → k) => f (Sum.elim p.1 p.2)) := hlc.comp_continuous hΦ
      have h1 : ∀ y ∈ K, ∀ᶠ z : (κ → k) × (κ' → k) in nhds (x₀, y),
          (fun x y => f (Sum.elim x y) = f (Sum.elim x₀ y)) z.1 z.2 := by
        intro y _
        have h0 := (IsLocallyConstant.iff_eventually_eq _).mp hF (x₀, y)
        have hc : Continuous (fun z : (κ → k) × (κ' → k) => (x₀, z.2)) := continuous_const.prodMk continuous_snd
        have h3 : ∀ᶠ z : (κ → k) × (κ' → k) in nhds (x₀, y), f (Sum.elim x₀ z.2) = f (Sum.elim x₀ y) :=
          (hc.tendsto (x₀, y)).eventually h0
        filter_upwards [h0, h3] with z hz hz'
        exact hz.trans hz'.symm
      have h2 := hK.eventually_forall_of_forall_eventually (P := fun x y => f (Sum.elim x y) = f (Sum.elim x₀ y)) h1
      filter_upwards [h2] with x hx
      funext y
      by_cases hy : y ∈ K
      · exact hx y hy
      · have hz : ∀ x', f (Sum.elim x' y) = 0 := by
          intro x'
          by_contra hne
          exact hy ⟨Sum.elim x' y, subset_tsupport f hne, rfl⟩
        rw [hz, hz]
    refine ⟨(hloc.comp l), ?_⟩
    refine HasCompactSupport.intro (hcs.isCompact.image (f := fun z : κ ⊕ κ' → k => z ∘ Sum.inl) (continuous_pi fun i => continuous_apply _)) ?_
    intro x hx
    have : (fun x₂ : κ' → k => f (Sum.elim x x₂)) = 0 := by
      funext x₂
      by_contra hne
      exact hx ⟨Sum.elim x x₂, subset_tsupport f hne, rfl⟩
    simp only [this, map_zero]

end GlobalTheory.SliceSB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortSeriesBoundCoprimeTorsionMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SupFull

section Coprime
open GlobalTheory.ShortPrime
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem isotropicLPart_shortSeries_bound_mul (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a) (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C) (nab : NabV Xo c)
    (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e) (hB : ChBound C e ρ w n)
    (ℓ : ℕ) (hp : ℓ.Prime) (hl : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N M : ℕ) (hU : Λ.Unimod) (hL : Λ.LevOK N M)
    (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (hR : AllRat Xo (xOf y) (N ^ 2)) (J : Type) [Fintype J] (a : J → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (hinj : Function.Injective a) (ha : ∀ u, (∃ i, a i = u) ↔ (InZh Xo Λ N u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1))
    (F₀ : Fin n → SecN Xo (xOf y) (N ^ 2)) (F : J → Fin n → SecN Xo (xOf y) (N ^ 2))
    (hre : ∀ b, Reach Xo (sOf1 y) (N ^ 2) (F₀ b))
    (hfix : ∀ b (u : ptO Xo (xOf y) ⟶ Xo.univ.t.G), (∃ j : ℕ, u ^ (ℓ ^ j) = 1) → u ^ N = 1 → Moves Xo u (F₀ b) (F₀ b))
    (hF : ∀ i b, Moves Xo (a i b) (F₀ b) (F i b)) (s : c.F)
    (hs : ∀ A : Adapt Λ N ℓ, 0 ≤ nval T.V e (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ))) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (s * (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) *
      ∑ i, hv Xo c nab y.1 (N ^ 2) (F i) P) := by
  letI := io.toAlgebra
  obtain ⟨A, hsim⟩ := GlobalTheory.T.exists_adapted_similitude_data_at_prime E H n Λ N M ℓ hU hL hp
  have hN : Odd N := hL.1
  have hkN : Odd (A.k * N) := A.odd.mul hN
  have hlev : (A.k * N) ^ 2 = N ^ 2 * A.k ^ 2 := by ring
  have hz := fun u hu => GlobalTheory.inZh_iff_kills_adapted E H Dw l Xo n Λ N ℓ hp hN.pos A (ptO Xo (xOf y)) u hu
  have ha' : ∀ u, (∃ i, a i = u) ↔ (Kills Xo (A.p * A.q) u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1) := fun u =>
    (ha u).trans (and_congr_left fun hu => (hz u hu).1)
  have hZ : ∀ i, InZh Xo Λ (A.k * N) (a i) := fun i =>
    have h := (ha' _).1 ⟨i, rfl⟩
    (hz _ h.2).2.2 h.1
  obtain ⟨π, hπ⟩ := exists_perm Xo A.cop _ a hinj ha'
  have hpull := fun G => (GlobalTheory.existsUnique_pulls E H Dw l Xo _ (xOf y) (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) ((A.k * N) ^ 2)
    (nat_mul_bar A.k) hlev G).exists
  choose pl hpl using hpull
  have hmv : ∀ (u : ptO Xo (xOf y) ⟶ Xo.univ.t.G) G G', u ^ ((A.k * N) ^ 2) = 1 → Moves Xo (u ^ A.k) G G' →
      Moves Xo u (pl G) (pl G') := fun u G G' hu h =>
    moves_of_pulls E H Dw l Xo _ (xOf y) (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) ((A.k * N) ^ 2) (nat_mul_bar A.k) hlev
      hkN.pow _ u (comp_act_nat Xo u A.k) hu G G' _ _ h (hpl G) (hpl G')
  have hsub : Ideal.span {((A.k * N : ℕ) : 𝓞 E)} • stdLat E n ≤ Λ.La := by
    refine le_trans (Submodule.smul_mono_left ?_) (hL.2.2.trans inf_le_left)
    rw [Nat.cast_mul]
    exact Ideal.span_singleton_le_span_singleton.2 (dvd_mul_left _ _)
  have hiso := (GlobalTheory.zh_isotropic_and_half_isotropic GlobalTheory.firstFiveLaws.1 E H Dw l Xo _ (xOf y) n Λ (A.k * N) hU
    hkN.pos hsub).1
  obtain ⟨hff, -, hhom⟩ := GlobalTheory.PushIntegral.map_pushL_mem_FFV E H Dw l c n Λ w P hP T io A.k A.ga
    (isUnit_of_coprime hl A.cop) A.unitary A.into
  have hkN0 : ((A.k * N : ℕ) : c.F) ^ P.totalDegree ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hkN.pos.ne')
  obtain ⟨z, hz1, hz2⟩ := GlobalTheory.T.sum_hv_primary_kernel_alt E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl (A.k * N)
    (A.k ^ 2) (N ^ 2) A.k₁ A.p A.q ((A.k : 𝓞 E) • A.g) hkN hsim (mul_pow _ _ _) (A.cop.pow_left 2) hR A.cop₁
    (by rw [Matrix.smul_mul, A.gq, smul_smul]; congr 1; push_cast; ring) J a hinj ha'
    (fun i i' ε hε => hiso (a i) (a i') ε (hZ i) (hZ i') fun b => by rw [← Nat.cast_pow]; exact hε b)
    (fun b => pl (F₀ b)) (fun i b => pl (F (π i) b))
    (fun b => .pull (N ^ 2) (A.k ^ 2) _ (A.k : 𝓞 E) (F₀ b) _ (hre b)
      (one_or_four_le hN)
      A.odd.pow (nat_mul_bar A.k) hlev (hpl _))
    (fun b u hu huN => hmv u _ _ (by rw [pow_two, pow_mul, huN, one_pow]) (hfix b _
      (hu.imp fun j hj => by rw [pow_right_comm, hj, one_pow]) (by rw [← pow_mul, huN])))
    (fun i b => hmv _ _ _ ((hZ i).1 b) (by rw [← hπ]; exact hF _ _))
    P (((A.k * N : ℕ) : c.F) ^ P.totalDegree)⁻¹ hP.1
    (by rw [A.prod, hhom, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hkN0, map_one, _root_.one_mul]; exact hff)
  have hch : ∀ i, hv Xo c nab y.1 ((A.k * N) ^ 2) (fun b => pl (F (π i) b)) P =
      io (nrm Dw c w (A.k : 𝓞 E)) * hv Xo c nab y.1 (N ^ 2) (F (π i)) P := fun i =>
    _root_.GlobalTheory.PlaceInt.hv_pulls E H Dw l Xo c hst nab hnab T.Fr y.1 (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) _ (nat_mul_bar A.k) hlev n
      (F (π i)) _ (fun b => hpl _) w P hP.1
  obtain ⟨hi1, hi2, -⟩ := GlobalTheory.LatticeIndex.latidx E H Dw l c n Λ N M ℓ hU hL hp A
  have hcnt := _root_.GlobalTheory.card_kills_primary E H Dw l Xo T.Fr (xOf y) ℓ hp n A.q ((N : 𝓞 E) • A.g) A.k₁ (N ^ 2) A.cop₁
    (pow_pos hN.pos 2) (by rw [Matrix.smul_mul, A.gq, smul_smul]; congr 1; push_cast; ring) hR
  rw [card_kills Xo A.p A.q a hinj ha', hcnt, hi1, Finset.sum_congr rfl fun i _ => hch i, ← Finset.mul_sum,
    Equiv.sum_comp π fun i => hv Xo c nab y.1 (N ^ 2) (F i) P] at hz2
  have hδ : 0 ≤ nval T.V e (io s * io (∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) := by
    rw [← map_mul]; exact hs A
  have hz3 : ((-ρ : ℝ) : EReal) ≤ nval T.V e (io s * io (∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) * z) := by
    rw [nval_mul]
    calc ((-ρ : ℝ) : EReal) = 0 + ((-ρ : ℝ) : EReal) := (zero_add _).symm
      _ ≤ _ := add_le_add hδ hz1
  clear hδ
  generalize io (∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) = δ at hz2 hz3
  have u2 := un_ordProj (K := T.Fr) hp hl hi2
  have u3 := un_nrm (Dw := Dw) c T io hl A.cop w
  have u4 := (un_of_coprime (K := T.Fr) hl A.cop).pow P.totalDegree
  rw [← ((u2.mul u3.inv).mul u4).nval e _] at hz3
  convert hz3 using 2
  have h3 := u3.ne
  have h4 := u4.ne
  have h5 : (N : T.Fr) ^ P.totalDegree ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN.pos.ne')
  simp only [map_mul, map_inv₀, map_pow io, map_natCast, Nat.cast_mul, mul_pow] at hz2 ⊢
  generalize (∑ i, hv Xo c nab y.1 (N ^ 2) (F i) P) = Sm at *
  generalize io (nrm Dw c w (A.k : 𝓞 E)) = ν at *
  generalize (A.k : T.Fr) ^ P.totalDegree = κ at *
  generalize (N : T.Fr) ^ P.totalDegree = ξ at *
  generalize io s = sg at *
  generalize ((Λ.mIdx N (Dw.p + Dw.q) : ℕ) : T.Fr)⁻¹ = im at *
  generalize ((ℓ ^ (Λ.mIdx N (Dw.p + Dw.q)).factorization ℓ : ℕ) : T.Fr) = L at *
  have h6 : L * im * ν⁻¹ * κ * (sg * δ * z) = sg * (im * ν⁻¹ * κ) * (L * δ * z) := by ring
  rw [h6, ← hz2]
  field_simp

theorem bound_of_coprime_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (Λ : GenLat E n) (N M : ℕ), Λ.Unimod → Λ.LevOK N M → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmL c Λ w → ∀ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo (xOf y) z → (∀ b, tp b ^ (N ^ 2) = 1) → (∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) → AllRat Xo (xOf y) (N ^ 2) → (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ b, tp b ^ m = 1) → ∀ s : c.F, (∀ A : GlobalTheory.PlaceInt.Adapt Λ N ℓ, 0 ≤ nval T.V e (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ))) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (s * (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) * ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  intro E _ _ _ H Dw l Xo c _ hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl Λ N M hU hL P hP z tp F hz hg
    htp hF hR ⟨m', hm', htm⟩ s hs
  letI := io.toAlgebra
  obtain ⟨J, J', _, _, a, a', σ, hinj, ha, ⟨m, hm, ham⟩, hσ, -⟩ :=
    _root_.GlobalTheory.isotropic_primary_decomposition E H Dw l Xo T.Fr (xOf y) n Λ N M ℓ hU hL hp z hz hg
  rw [← Equiv.sum_comp σ, Fintype.sum_prod_type_right, Finset.mul_sum]
  refine GlobalTheory.ShortPrime.le_nval_sum _ _ _ _ fun i' _ => ?_
  choose F₀ h1 h2 h3 using fun b => GlobalTheory.ShortPrime.exists_base Xo hL.1 (sOf1 y) (a' i' b) (tp b) (ham i' b).2 (htp b)
    hm hm' (ham i' b).1 (htm b)
  refine isotropicLPart_shortSeries_bound_mul Xo c hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl Λ N M hU hL P hP hR J a
    hinj ha F₀ (fun i b => sqN Xo N (F (σ (i, i')) b)) h1 h2 (fun i b => ?_) s hs
  obtain ⟨h4, h5⟩ := (ha _).1 ⟨i, rfl⟩
  exact h3 b _ _ (h5 b) (h4.1 b) (hσ i i' b ▸ hF _ b)

end Coprime
end GlobalTheory.SupFull
end
end

