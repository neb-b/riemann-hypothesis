module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import GroundTheory.GlobalFields.Adele.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0795
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealLowestKTypeOfExtremalVectorCase
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0816
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0736
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0814
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralUnfoldMirabolic
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate Matrix

namespace GlobalTheory.ZUnfTheta

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem continuous_secRow {n : ℕ} :
    Continuous (fun y : Fin n → Cinf E => secRow y) := by
  refine continuous_matrix fun i j => ?_
  simp only [secRow, Matrix.of_apply]
  split_ifs
  · exact continuous_apply j
  · exact continuous_const

theorem continuousOn_secInv {n : ℕ} :
    ContinuousOn (fun y : Fin n → Cinf E => secInv y) {y | IsUnit (secRow y).det} := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h1 : ∀ y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det},
        ((secInv y.1 : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = (secRow y.1)⁻¹ := fun y => by
      rw [secInv, dite_eq_left (show IsUnit (secRow y.1).det from y.2), Matrix.coe_units_inv]
      rfl
    have hc : Continuous fun y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow y.1 :=
      continuous_secRow.comp continuous_subtype_val
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hinv : ContinuousAt Ring.inverse (secRow y.1).det := by
      have := NormedRing.inverse_continuousAt y.2.unit
      simpa using this
    have h2 : ContinuousAt (fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => (secRow z.1)⁻¹) y :=
      (continuousAt_matrix_inv _ hinv).comp (f := fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow z.1)
        hc.continuousAt
    convert h2 using 1
    funext z
    exact h1 z
  · have h1 : ∀ y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det},
        (((secInv y.1)⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = secRow y.1 := fun y => by
      rw [secInv, dite_eq_left (show IsUnit (secRow y.1).det from y.2), inv_inv]
      rfl
    convert (continuous_secRow.comp continuous_subtype_val :
      Continuous fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow z.1) using 1
    funext z
    exact h1 z

variable {m : ℕ}

theorem isClosed_natLat (N : ℕ) : IsClosed (natLat E N) := by
  have h : natLat E N =
      (fun u : Af E => (N : Af E) * u) '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [h]
  exact ((GroundTheory.Global.isCompact_integralFiniteAdeles E).image (continuous_const.mul continuous_id)).isClosed

theorem continuous_lastRow : Continuous fun g : GA E (m + 1) => GlobalTheory.ZEul.lastRow g :=
  continuous_pi fun j => (Units.continuous_val (M := Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))).matrix_elem (Fin.last m) j

theorem continuous_yInfRow : Continuous fun g : GA E (m + 1) => fun i => pInf E (GlobalTheory.ZEul.lastRow g i) :=
  continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp continuous_lastRow)

theorem measurable_mulSec :
    Measurable fun g : GA E (m + 1) => g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) := by
  have hy := continuous_yInfRow (E := E) (m := m)
  set s := {g : GA E (m + 1) | IsUnit (secRow fun i => pInf E (GlobalTheory.ZEul.lastRow g i)).det} with hsdef
  have hs : IsOpen s := Units.isOpen.preimage ((continuous_secRow.comp hy).matrix_det)
  refine measurable_of_restrict_of_restrict_compl hs.measurableSet ?_ ?_
  · have hc : ContinuousOn (fun g : GA E (m + 1) =>
        g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) s :=
      continuousOn_id.mul (GlobalTheory.ConstTermSmooth.continuous_infGL.comp_continuousOn
        (continuousOn_secInv.comp hy.continuousOn fun g hg => hg))
    exact hc.restrict.measurable
  · convert (measurable_subtype_coe : Measurable (Subtype.val : (sᶜ : Set (GA E (m + 1))) → GA E (m + 1))) using 1
    funext g
    have hg : ¬ IsUnit (secRow fun i => pInf E (GlobalTheory.ZEul.lastRow g.1 i)).det := g.2
    show g.1 * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g.1 i)) = g.1
    rw [secInv, dite_eq_right hg, map_one, mul_one]

theorem measurable_integrand {φ φ' : GA E (m + 1) → ℂ} (hφ : Measurable φ) (hφ' : Measurable φ')
    {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : Continuous Φ) (N : ℕ) (x : ℝ) :
    Measurable fun g : GA E (m + 1) => Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) := by
  have hh := measurable_mulSec (E := E) (m := m)
  have hy := continuous_yInfRow (E := E) (m := m)
  have hI : Measurable fun g : GA E (m + 1) => indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) := by
    have hS : IsClosed {g : GA E (m + 1) | ∀ i : Fin (m + 1),
        GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => (isClosed_natLat N).preimage
        (((continuous_snd : Continuous (GlobalTheory.RSJ.pFin E)).comp ((continuous_apply i).comp continuous_lastRow)).sub
          continuous_const)
    unfold indN
    exact Measurable.ite hS.measurableSet measurable_const measurable_const
  have hD : Continuous fun g : GA E (m + 1) => (detPow E (m + 1) x g : ℂ) := by
    unfold detPow chiDet
    exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.comp
      ((GlobalTheory.HeckeGal.Model.absPow E x).2.1.comp Matrix.GeneralLinearGroup.continuous_det)))
  unfold Psi
  exact ((((hφ.comp hh).mul (Complex.continuous_conj.measurable.comp (hφ'.comp hh))).mul
    (hΦ.measurable.comp hy.measurable)).mul hI).mul hD.measurable

end GlobalTheory.ZUnfTheta

set_option synthInstance.maxHeartbeats 200000 in
theorem GlobalTheory.ZUnfTheta.zint_eq_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ →
    ∀ φ φ' : GA E (m + 1) → ℂ, Measurable φ → Measurable φ' → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ γ g, φ' (ratGL E (m + 1) γ * g) = φ' g) → ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), Continuous Φ → ∀ x : ℝ,
    ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ →
    Zint μ 𝓕 φ φ' Φ N x = ∫ g in 𝓕P, Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) ∂μ := by
  intro E _ _ _ m μ _ 𝓕 𝓕P h𝓕 h𝓕P φ φ' hφm hφ'm hφ hφ' N Φ hΦ x hfin
  set l : Fin (m + 1) := Fin.last m with hl
  let F : GA E (m + 1) → (Fin (m + 1) → Ad E) → ℂ := fun g y => Psi φ φ' Φ N g y * (detPow E (m + 1) x g : ℂ)
  have hv : (Pi.single l 1 : Fin (m + 1) → E) ≠ 0 := fun h0 => by simpa using congrFun h0 l
  have hP' : ∀ γ : GL (Fin (m + 1)) E,
      γ ∈ mirU E (m + 1) m ↔ (Pi.single l 1 : Fin (m + 1) → E) ᵥ* γ.val = Pi.single l 1 := fun γ => by
    rw [mem_mirU_last, Matrix.single_one_vecMul, funext_iff]
    simp only [Pi.single_apply, Matrix.row]
    exact Iff.rfl
  have he : ∀ g : GA E (m + 1),
      (algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin (m + 1) → E)) ᵥ* g.val = GlobalTheory.ZEul.lastRow g := fun g => by
    have h1 : algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin (m + 1) → E) = Pi.single l 1 := by
      funext j
      simp only [Function.comp_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [h1, Matrix.single_one_vecMul]
    rfl
  have hF : ∀ γ g y, F (ratGL E (m + 1) γ * g) y = F g y := fun γ g y => by
    simp only [F, Psi, mul_assoc (ratGL E (m + 1) γ) g, hφ, hφ', GlobalTheory.RSJ.Model.detPow_mul,
      GlobalTheory.RSJ.Model.detPow_ratGL, one_mul]
  have hm : Measurable fun g => F g (GlobalTheory.ZEul.lastRow g) := GlobalTheory.ZUnfTheta.measurable_integrand hφm hφ'm hΦ N x
  have h𝓕P' : IsFundamentalDomain ((mirU E (m + 1) m).map (ratGL E (m + 1))) 𝓕P μ := h𝓕P
  have hlin := GlobalTheory.ThetaUnfold.lintegral_tsum_vecMul μ hv hP' h𝓕 h𝓕P' (fun g y => ‖F g y‖ₑ)
    (fun γ g y => by simp only [hF]) (by simp only [he]; exact hm.enorm.aemeasurable)
  have hfin' : ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0},
      ‖F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖ₑ ∂μ ≠ ⊤ := by
    rw [hlin]
    simpa only [he] using hfin
  obtain ⟨-, -, -, hint⟩ := GlobalTheory.ThetaUnfold.integral_tsum_vecMul μ hv hP' h𝓕 h𝓕P' F hF
    (by simp only [he]; exact hm.aestronglyMeasurable) hfin'
  simp only [he] at hint
  unfold Zint thetaSum
  rw [← hint]
  congr 1
  funext g
  rw [← tsum_mul_right]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatHeckeRealRd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie.HkRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem evK_hkFR {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL ((j : ℕ) + 1)))
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) hL) (k : ℕ) (P : PlE D.host) (R : Finset (GA D (Wc D j))) (s : ℂ)
    (hR : ∀ x : S.WL ((j : ℕ) + 1), evW YS v₀ j (hL k P x) = s • heckeLin (Wc D j) R (evW YS v₀ j x))
    (y : NX.Fm S i ((j : ℕ) + 1) b) :
    evK YS v₀ hρ i j b (NX.hkFR S i ((j : ℕ) + 1) b hL hs k P y) = s • heckeLin (Wc D j) R (evK YS v₀ hρ i j b y) := by
  induction y using TensorProduct.induction_on with
  | zero => erw [LinearMap.map_zero, map_zero, map_zero, smul_zero]
  | add y z hy hz => erw [LinearMap.map_add, map_add, hy, hz, map_add, map_add, smul_add]
  | tmul a f0 =>
    have e1 : NX.hkFR S i ((j : ℕ) + 1) b hL hs k P (a ⊗ₜ f0) =
        a ⊗ₜ (((hL k P).restrictScalars S.Ks).restrict (p := (S.A ((j : ℕ) + 1)).WK) (q := (S.A ((j : ℕ) + 1)).WK)
          fun x hx => hs k P x hx) f0 := rfl
    erw [e1, evK_tmul, evK_tmul]
    change ρ.e i b a • evW YS v₀ j (hL k P f0.1) = _
    rw [hR, map_smul, smul_comm]

end GlobalTheory.SeriesTie.HkRat

namespace GlobalTheory.SeriesTie.HkRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem evW_reads (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hR : GlobalTheory.ExportPin.Reads Rl cG S YS hL)
    (j : Fin D.R.m) (k : ℕ) (P : PlE D.host) (hPs : IsSplitPl D.host P)
    (hso : Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E))) (hk : k ≤ D.R.r) (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j)))
    (hα : IsHeckeAt (Wc D j) P k α) (hdc : Bridge.IsDC (levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R)
    (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₀ j (hL ((j : ℕ) + 1) k P x) =
      ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
        heckeLin (Wc D j) R (evW YS v₀ j x) := by
  have h := congrArg (fun F => F (v₀ j (sg0 D A3.A))) (hR j k P hPs hso hk α R hα hdc x)
  exact h

end GlobalTheory.SeriesTie.HkRat

namespace GlobalTheory.SeriesTie.HkRat
open GlobalTheory.SeriesTie.Setup

theorem ratHecke_realRd : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), RealPin Rl cG ρ → ChrEq (Rl.mu0 ((j : ℕ) + 1)) (Rl.C.mu0 j) → (∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E))) → ∀ hL : ∀ n, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL n), NX.HeckeStabR S ((j : ℕ) + 1) (hL ((j : ℕ) + 1)) → GlobalTheory.ExportPin.Reads Rl cG S YS hL → RatHecke (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hp hchr hsplit hL hs hR k P hk f
  obtain ⟨hk1, hkr, hPs, hPS0⟩ := hk
  have hso := hsplit P hPs hPS0
  have hPg : Bridge.SplitOff P (((ρ.B i j b).G.Pg : Finset _) : Set (Pl D.host.E)) :=
    _root_.GlobalTheory.SplitOffS0.main hρ i _ (fun P' hP' => by
      obtain ⟨k', hk'⟩ := hρ.Pg i j b P' hP'
      exact D.ntw.placesOver_subset_exceptional i k' hk') P hPs hPS0
  have hdQ : Bridge.SplitOff P (((ρ.B i j b).de.Q : Finset _) : Set (Pl D.host.E)) :=
    _root_.GlobalTheory.SplitOffS0.main hρ i _ (fun P' hP' => by
      rw [hρ.delta i j b] at hP'
      exact D.ntw.primes_subset_exceptional i (mem_half.1 hP').1) P hPs hPS0
  by_cases hd : ∃ α R z, ρ.IsHeckeDatum i j b k P α R z
  swap
  · exact ⟨0, fun α R z d => absurd ⟨α, R, z, d⟩ hd⟩
  obtain ⟨α₀, R₀, z₀, d₀⟩ := hd
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.DeltaRange.delta_value_mem_range hρ i j b z₀
  have hde : ∀ α R z, ρ.IsHeckeDatum i j b k P α R z → (((ρ.B i j b).de.chi z : Circle) : ℂ) = ρ.e i b a :=
    fun α R z d => by
      rw [ha, _root_.GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α z (hp.delta i j b) (hρ.base i j b).de.unram (hρ.base i j b).de.split hdQ d.elt d.det,
        _root_.GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α₀ z₀ (hp.delta i j b) (hρ.base i j b).de.unram (hρ.base i j b).de.split hdQ d₀.elt d₀.det]
  have hchr' : ChrEq (ρ.B i j b).mu0 (Rl.C.mu0 j) := by rw [hp.mu0 i j b]; exact hchr
  have hmu0 : ∀ α R z, ρ.IsHeckeDatum i j b k P α R z →
      (((ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k :=
    fun α R z d => _root_.GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α z hchr' (hρ.base i j b).unram
      ((hρ.base i j b).places.split.elim fun _ h => h.2.2.mono h.1) hPg d.elt d.det
  refine ⟨a⁻¹ • (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm
    (NX.hkFR S i ((j : ℕ) + 1) b (hL _) hs k P (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)), ?_⟩
  rcases eq_or_ne ν 0 with rfl | hν
  · intro α R z d
    rw [realRd_apply, realRd_apply YS v₀ hρ i j b 0 f, inv_zero, zero_smul, zero_smul, map_zero]
  rw [heckeAt_realRd YS v₀ hρ i j b hν]
  intro α R z d
  have hdc := d.reps
  rw [_root_.GlobalTheory.SeriesTie.levK_eq_levG_triv Rl hp i j b] at hdc
  have key := evK_hkFR YS v₀ hρ i j b (hL _) hs k P R _
    (evW_reads YS v₀ hL hR j k P hPs hso hkr α R d.elt hdc) (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
  funext x
  rw [Setup.hecke_apply, map_smulₛₗ]
  change ρ.e i b a⁻¹ * ((1 : ℂ)⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2
    ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm _))) x = _ * _ *
      ∑ γ ∈ R, ((1 : ℂ)⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) (x * γ)
  rw [LinearEquiv.apply_symm_apply, key]
  simp only [inv_one, one_smul, Pi.smul_apply, smul_eq_mul, heckeLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Base.mu, MonoidHom.mul_apply, Circle.coe_mul, hmu0 α R z d, hde α R z d, map_inv₀]
  rw [show normV P = Nat.card (kP P) from rfl, D.sp.V_rank _ (Nat.le_add_left _ _) j.2]
  simp only [one_mul]
  ring

end GlobalTheory.SeriesTie.HkRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealLow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.RealLowPf

theorem realLow : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, RealLow R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hP i t
  exact _root_.GlobalTheory.RawLift.RealLowRed.realLow_of_ext D G Pl0 T A Ks R F hL hP i t (GlobalTheory.T.fockCoefficient_extremal_eq_discreteSeries D G Pl0 T A Ks R F hL hP i t)

end GlobalTheory.RawLift.RealLowPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

noncomputable section
namespace GlobalTheory.RSPole

def schurDir (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑' l : {l : Fin n → ℕ // Antitone l},
    ENNReal.ofReal (‖GlobalTheory.JSW.schurAt l.1 α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x)))

def eulD {I : Type} (q : I → ℕ) {n : ℕ} (α : I → Fin n → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∏' w, schurDir (q w) (α w) x

def thetaZ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (μ : Measure (GA E a)) (𝓕 : Set (GA E a))
    (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (x : ℝ) : ℂ :=
  ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ φ' Φ J η g
      ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
    ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ

end GlobalTheory.RSPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatIntegrableMomentsStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_integrable_moments : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (F : (Fin m → Ad E) → ℂ),
    F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin m) →
    (∃ L : Set (Fin m → Af E), IsCompact L ∧ ∀ x, F x ≠ 0 → (fun i => pFin E (x i)) ∈ L) ∧
    ∀ k : ℕ, Integrable (fun x => ‖F x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E) := by
  first | exact @GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments | exact GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments | (intros; apply GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesRay
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cmp.SeriesRay

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke

variable {D : D7}

section Forms

variable {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)

theorem sum_mem_intForms (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) {m : ℕ} (x : Fin m → C.d.c₂.F)
    (hx : ∀ k, ∀ la ∈ S, la.valuation C.d.c₂.F (x k) ≤ 1) (φ : Fin m → GA D (T.V j σ) → ℂ) (hφ : ∀ k, φ k ∈ C.intForms a n S) :
    (∑ k, C.σ₂ (x k) • φ k) ∈ C.intForms a n S := by
  choose f hf e using hφ
  refine ⟨∑ k, x k • f k, ⟨⟨sum_mem fun k _ => Submodule.smul_mem _ _ (hf k).1.1, ?_⟩, fun la hla v hv => ?_⟩, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      exact sum_mem fun k _ => by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (hf k).1.2
  · have hV := isVal_valSet la v hv
    exact GlobalTheory.IdemInt.nonneg_sum hV _ _ fun k _ => GlobalTheory.IdemInt.nonneg_smul hV (hx k la hla) ((hf k).2 la hla v hv)
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [← e, Cover.rd, map_sum, map_smulₛₗ, Finset.smul_sum, RingHom.id_apply]
      exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

end Forms

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))



section Data

variable {T}

variable {R i}

end Data

section First

variable {T R i κ}

variable {hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i} {v₀ : (R.MW i (sg0 D A)).Vec} {u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ}
  {c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W} {ka : ℂ} {J : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}


end First

end GlobalTheory.Cmp.SeriesRay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLatticeRationalFormMemLocalUnitBall
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_locBall_of_mem_MK : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f : NX.FmK S ((j : ℕ) + 1), (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK → f ∈ locBall YS fw iC b j := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j f hf
  intro z
  obtain ⟨hwk, hb⟩ := ((YS.fi j).mkK _).1 hf
  obtain ⟨T, io, k, hk, y, u, hy, hu, hval⟩ := PtC.exists_valC z (wtA (κ j)) (κ j).n
  obtain ⟨e, ho⟩ := GlobalTheory.ReadingOver.overLa_placeAt _ _ (embC YS iC b) T io k hk
  let v : T0.PtM ((j : ℕ) + 1) (placeC YS iC b) :=
    ⟨vAtV (PtV.mk (cls := algCls (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c) (PY := Unit) (lies := fun _ _ _ _ => True)
      (placeC YS iC b) ho y hy () trivial), ⟨_, rfl⟩⟩
  obtain ⟨w, hw⟩ := (fw.pt j (placeC YS iC b)).surjective v
  have h1 := hb (placeC YS iC b) w
  have e1 : (⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1, hwk⟩ : (Rl.FW j).WK) = fw.e j (cuspOf YS fw j f) :=
    Subtype.ext (e_cuspOf YS fw j f).symm
  rw [e1, fw.nrm_eq, hw] at h1
  have h2 := (T0.nrmM_le_one_iff _ _ v _).1 h1
  have h3 := (GlobalTheory.GoodPtsModel.inV_iff_nval T ho.1 (evI y (cuspOf YS fw j f : T0.R ((j : ℕ) + 1)))).2 h2
  rw [hval _ (cuspOf_mem_sec YS fw j f), norm_mul, hu, one_mul]
  exact (hk.int _).2 h3

end GlobalTheory.GeoTie
end
end

