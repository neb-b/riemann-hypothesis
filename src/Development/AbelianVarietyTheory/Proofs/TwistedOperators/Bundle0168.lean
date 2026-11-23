module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameInteg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SplitFrameColumn

theorem intAE_mul {D : D7} {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, c, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, d, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, c * d, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; push_cast; rfl
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem comm_mem_intAf_iff {D : D7} (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      z ∈ intAE D := by
  constructor
  · intro hs
    have hs' : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z ∈
        Subring.closure (Set.range (fun x : Formalism.UG.intOE D.host.E => (x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∪
        Set.range (fun y : Formalism.UG.intAd D.host.F => (1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F))) := hs
    suffices h : ∀ s ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE D.host.E => (x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∪
        Set.range (fun y : Formalism.UG.intAd D.host.F => (1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F))),
        (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm s ∈ intAE D by
      simpa using h _ hs'
    have hone : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by rw [map_one]; exact one_mem _
    intro s hs
    induction hs using Subring.closure_induction with
    | mem s hs =>
      rcases hs with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩
      · exact AddSubgroup.subset_closure ⟨1, hone, c, rfl⟩
      · refine AddSubgroup.subset_closure ⟨a, fun w => ha w, 1, ?_⟩
        simp
    | zero => rw [map_zero]; exact zero_mem _
    | one => rw [map_one]; exact AddSubgroup.subset_closure ⟨1, hone, 1, by simp [Algebra.TensorProduct.one_def]⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact intAE_mul hx hy
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      rw [Algebra.TensorProduct.comm_tmul]
      have hx : (x : D.host.E) ⊗ₜ[D.host.F] a =
          ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hx]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨(x : D.host.E), ⟨x, rfl⟩⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem toEAf_finEmb {D : D7} (t : EAf D) : toEAf D (GlobalTheory.AdelicLatMove.finEmb D t) = t := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | tmul x α => rfl

theorem latHat_iff_hatL {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) ↔
      (fun i => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact GlobalTheory.AdelicLatMove.pure_mem_hatL Λ a (fun w => ha w) x hx
    | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
    | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx
  · intro hz
    have key : ∀ w ∈ AddSubgroup.closure (GlobalTheory.AdelicLatMove.pureSet (D := D) Λ),
        (fun i => (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm (w i)) ∈
          Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) := by
      intro w hw
      induction hw using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨α, hα, x, hx, rfl⟩ := hw
        exact AddSubgroup.subset_closure ⟨α, fun u => hα u, x, hx, rfl⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
      | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx
    have := key _ (GlobalTheory.AdelicLatMove.mem_closure_of_mem_hatL Λ _ hz)
    simpa only [AlgEquiv.symm_apply_apply] using this

theorem frame_column : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (EAf D)), IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ ∀ i, Valued.v ((((frCo φ β)⁻¹ : GL (Fin V.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdA φ (y k)) i) ≤ 1 := by
  intro D V Λ β _ hβ v φ e he y
  obtain ⟨hπ, hE, -, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  set u : Fin V.rank → EAf D := (β⁻¹).1 *ᵥ fun k => toEAf D (y k) with hu
  have hsw : (fun k => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (e * y k))) =
      toEAf D e • fun k => toEAf D (y k) := funext fun k => (toEAf D).map_mul e (y k)
  have hfe : ∀ t : EAf D, toEAf D (GlobalTheory.AdelicLatMove.finEmb D t) = t := toEAf_finEmb
  rw [latHat_iff_hatL, hβ, hsw, Matrix.mulVec_smul]
  refine forall_congr' fun i => ?_
  have h1 : (toEAf D e • u) i = toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (u i)) := by
    rw [map_mul, hfe]; rfl
  have h2 : rdA φ (GlobalTheory.AdelicLatMove.finEmb D (u i)) =
      ((((frCo φ β)⁻¹ : GL (Fin V.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdA φ (y k)) i) := by
    rw [← hE, hfe, hu, RingHom.map_mulVec]
    unfold frCo
    rw [← map_inv]
    congr 1
    funext k
    exact hE (y k)
  rw [h1, show toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (u i)) =
      Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (e * GlobalTheory.AdelicLatMove.finEmb D (u i))) from rfl,
    comm_mem_intAf_iff, hπ.2.2.2, GlobalTheory.SplitHecke.isInt_Ov, HeightOneSpectrum.mem_adicCompletionIntegers, h2]

end GlobalTheory.SplitFrameColumn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceWeilRepLatticeVacuumCharacter
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv


open GlobalTheory.SplitScalar GlobalTheory.SplitHecke in
theorem om_latVac_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e, IsSplitIdem D e → ∀ g h, Formalism.L2.Theta.SuppAt e S g → Formalism.L2.Theta.SuppAt e T h → (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • f := by
  intro D ψ S T ΛS ΛT χS χT om hW hS hT e he g h hg hh hlat x y hx hy f hf hv

  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ

  obtain ⟨hdual, -, -⟩ := _root_.GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hW.std hS hT
  have hdd : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1 := fun u hu u' hu' =>
    (hdual u (GlobalTheory.SplitScalar.latO_fin hu)).1 hu u' hu'
  have he' : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hst : ∀ u ∈ Λ, cA D e • u ∈ Λ := GlobalTheory.SplitScalar.idem_smul_mem he'.1
  have hst' : ∀ u ∈ Λ, cA D (cA D e) • u ∈ Λ := by
    rw [GlobalTheory.DualPairCheck.cA_cA]; exact GlobalTheory.SplitScalar.idem_smul_mem he.1

  have hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1 :=
    fun y hy hyn => GlobalTheory.SplitScalar.exists_dual_half he hdual hst hy hyn
  have hd' : ∀ y, IsHalf (cA D e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf e l ∧ ψ (symplO S T l y) ≠ 1 := by
    intro y hy hyn
    have hex := GlobalTheory.SplitScalar.exists_dual_half he' hdual hst' hy hyn
    rwa [GlobalTheory.DualPairCheck.cA_cA] at hex

  have hback : ∀ w, actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := fun w => by
    simpa using GlobalTheory.SplitHecke.actO_inv_actO g⁻¹ h⁻¹ w
  have hmem : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ Λ ↔ w ∈ Λ := fun w => by
    have hw := hlat (actO S T g⁻¹ h⁻¹ w)
    rwa [hback] at hw

  have hR : ∀ u ∈ ({0} : Finset (WO S T)), actO S T g⁻¹ h⁻¹ u ∈ Λ ∧ IsHalf e u := by
    intro u hu
    rw [Finset.mem_singleton] at hu
    subst hu
    exact ⟨(hmem 0).2 (zero_mem _), GlobalTheory.SplitScalar.isHalf_zero e⟩
  have hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ Λ → IsHalf e w → ∃! v, v ∈ ({0} : Finset (WO S T)) ∧ w - v ∈ Λ := by
    intro w hw _
    refine ⟨0, ⟨Finset.mem_singleton_self _, by simpa using (hmem w).1 hw⟩, ?_⟩
    rintro v ⟨hv0, -⟩
    exact Finset.mem_singleton.1 hv0
  have hle : ∀ w ∈ Λ, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ Λ := fun w hw _ => (hmem w).2 hw
  obtain ⟨r, hr, hom⟩ := GlobalTheory.SplitHecke.om_eq_smul_sum hW he hdd hd hd' hg hh hx hy hR hRu hle
  have key : om (g, h) f = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) • f := by
    have hk := hom f hf (fun u hu hue => hv.2 e he u hu hue) (fun u hu hue => hv.2 (cA D e) he' u hu hue)
    rwa [Finset.sum_singleton, GlobalTheory.WeilVacMove.heisO_zero] at hk

  by_cases hf0 : f = 0
  · subst hf0
    simp
  obtain ⟨htop, hlc, hsc, ht2, hdisc, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI := htop
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI := hdisc
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, h1⟩, hN⟩ :=
    GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratL T S) K hK hcov
  haveI := hμ
  have hper := GlobalTheory.WeilVacMove.norm_periodic hW.std hf
  obtain ⟨N, hNf⟩ := hN f hf.cont hper
  obtain ⟨-, -, hI, -⟩ := hNf μ 𝓕 hμ h𝓕
  have hu := hW.om_unit μ 𝓕 hμ h𝓕 (g, h) f hf
  rw [key] at hu
  have hpt : ∀ w, ‖(((r : ℂ) * (splitFacO χS χT x y : ℂ)) • f) w‖ₑ ^ 2 =
      ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖ₑ ^ 2 * ‖f w‖ₑ ^ 2 := fun w => by
    rw [Pi.smul_apply, smul_eq_mul, enorm_mul (a := (r : ℂ) * (splitFacO χS χT x y : ℂ)), mul_pow]
  simp_rw [hpt] at hu
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top), hI, h1, one_mul] at hu
  have hN0 : (N : ENNReal) ≠ 0 := by
    intro hz
    apply hf0
    have h0 : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = 0 := by rw [hI, hz, mul_zero]
    rw [lintegral_eq_zero_iff' (hf.cont.measurable.enorm.pow_const 2).aemeasurable] at h0
    apply GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 f hf.cont hper
    filter_upwards [h0] with w hw
    simpa using hw
  have hnorm : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hs1 : ‖(splitFacO χS χT x y : ℂ)‖ = 1 := by
      first
        | exact Circle.norm_coe _
        | exact Circle.abs_coe _
        | simp
    rw [hs1, mul_one]
  have hr1 : r = 1 := by
    have hc : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖₊ ^ 2 = 1 := by
      rw [enorm_eq_nnnorm] at hu
      have hN0' : N ≠ 0 := fun hz => hN0 (by rw [hz]; rfl)
      have h2 : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖₊ ^ 2 * N = 1 * N := by
        rw [one_mul]; exact_mod_cast hu
      exact mul_right_cancel₀ hN0' h2
    have hc' : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖ ^ 2 = 1 := by
      rw [← coe_nnnorm]
      exact_mod_cast hc
    rw [hnorm] at hc'
    nlinarith
  rw [key, hr1]
  simp

end GlobalTheory.VecInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceCmHostAdeles
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacClosed

open GlobalTheory.MixModel.HypDec

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def uniOnX (d : HypDec S S₀ ρ) : Set (GA D S) :=
  {g | mt S g ⬝ d.jX = d.jX ⬝ blockX d g ∧ (∀ i j : Fin ρ, j < i → blockX d g i j = 0) ∧ ∀ i, blockX d g i i = 1}

theorem t2Space_cm_host_adeles : T2Space (AE D) := by
  haveI : T2Space (Mx D 1 1) := (lattice_Mx D 1 1).2.2.2.1
  exact @T2Space.of_injective_continuous _ _ _ _ this (fun a : AE D => (Matrix.of fun _ _ => a : Mx D 1 1))
    (fun a b h => congrFun (congrFun h 0) 0) (continuous_pi fun _ => continuous_pi fun _ => continuous_id)

theorem isClosed_uniOnX (d : HypDec S S₀ ρ) : IsClosed (uniOnX d) := by
  haveI : T2Space (AE D) := t2Space_cm_host_adeles
  have hm := GlobalTheory.MixModel.continuous_mt (D := D) S
  have hb : Continuous fun g : GA D S => blockX d g := continuous_const.matrix_mul (hm.matrix_mul continuous_const)
  have e1 : {g : GA D S | ∀ i j : Fin ρ, j < i → blockX d g i j = 0} =
      ⋂ i : Fin ρ, ⋂ j : Fin ρ, ⋂ (_ : j < i), {g | blockX d g i j = 0} := by ext; simp only [Set.mem_setOf_eq, Set.mem_iInter]
  have e2 : {g : GA D S | ∀ i : Fin ρ, blockX d g i i = 1} = ⋂ i : Fin ρ, {g | blockX d g i i = 1} := by ext; simp only [Set.mem_setOf_eq, Set.mem_iInter]
  have c1 : IsClosed {g : GA D S | ∀ i j : Fin ρ, j < i → blockX d g i j = 0} := by
    rw [e1]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply j).comp ((continuous_apply i).comp hb)) continuous_const
  have c2 : IsClosed {g : GA D S | ∀ i : Fin ρ, blockX d g i i = 1} := by
    rw [e2]
    exact isClosed_iInter fun i => isClosed_eq ((continuous_apply i).comp ((continuous_apply i).comp hb)) continuous_const
  exact (isClosed_eq (hm.matrix_mul continuous_const) (continuous_const.matrix_mul hb)).inter (c1.inter c2)

theorem mem_uniOnX_of (d : HypDec S S₀ ρ) {g : GA D S} {u : GL (Fin ρ) (AE D)} (hu : u ∈ upperUni ρ (AE D))
    (h : mt S g ⬝ d.jX = d.jX ⬝ u.1) : g ∈ uniOnX d := by
  have hb : blockX d g = u.1 := by rw [blockX, h, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
  refine ⟨by rw [hb]; exact h, fun i j hij => ?_, fun i => ?_⟩
  · rw [hb]; exact (hu i j).1 hij
  · rw [hb]; exact (hu i i).2

def uniOnXSub (d : HypDec S S₀ ρ) : Subgroup (GA D S) where
  carrier := {g | ∃ u ∈ UX D ρ, mt S g ⬝ d.jX = d.jX ⬝ u.1}
  one_mem' := ⟨1, one_mem _, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  mul_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨v, hv, hb⟩
    exact ⟨u * v, mul_mem hu hv, by
      rw [mt_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h1 : mt S a⁻¹ ⬝ d.jX ⬝ u.1 = d.jX := by
      rw [Matrix.mul_assoc, ← ha, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    calc mt S a⁻¹ ⬝ d.jX = mt S a⁻¹ ⬝ d.jX ⬝ (u.1 ⬝ (u⁻¹).1) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX ⬝ (u⁻¹).1 := by rw [← Matrix.mul_assoc, h1]

def uniUnit (U : Mx D ρ ρ) (h0 : ∀ i j : Fin ρ, j < i → U i j = 0) (h1 : ∀ i, U i i = 1) : GL (Fin ρ) (AE D) :=
  Matrix.nonsingInvUnit U (by
    rw [Matrix.det_of_upperTriangular (fun i j (h : j < i) => h0 i j h)]
    simp [h1])

theorem uniUnit_val (U : Mx D ρ ρ) (h0 : ∀ i j : Fin ρ, j < i → U i j = 0) (h1 : ∀ i, U i i = 1) :
    (uniUnit U h0 h1).1 = U := rfl

theorem uniUnit_mem (U : Mx D ρ ρ) (h0 : ∀ i j : Fin ρ, j < i → U i j = 0) (h1 : ∀ i, U i i = 1) :
    uniUnit U h0 h1 ∈ upperUni ρ (AE D) := fun i j => ⟨h0 i j, h1 i⟩

theorem flagN_le (d : HypDec S S₀ ρ) : flagN d ≤ uniOnXSub d := by
  show Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro g ⟨hX, -⟩
  choose a ha1 ha2 using hX
  let A : Mx D ρ ρ := Matrix.of fun j i => a i j
  have hcol : subOne S g ⬝ d.jX = d.jX ⬝ A := by
    ext k i
    exact congrFun (ha2 i) k
  have h0 : ∀ i j : Fin ρ, j < i → (1 + A) i j = 0 := fun i j h => by
    simp only [Matrix.add_apply, A, Matrix.of_apply, Matrix.one_apply_ne h.ne', ha1 j i h.le, add_zero]
  have h1 : ∀ i, (1 + A) i i = 1 := fun i => by
    simp only [Matrix.add_apply, A, Matrix.of_apply, Matrix.one_apply_eq, ha1 i i le_rfl, add_zero]
  refine ⟨uniUnit (1 + A) h0 h1, uniUnit_mem _ h0 h1, ?_⟩
  rw [uniUnit_val, Matrix.mul_add, Matrix.mul_one, ← hcol, GlobalTheory.MixModel.HypDec.subOne_mul, add_sub_cancel]

theorem jacGrp_le (d : HypDec S S₀ ρ) : jacGrp d ≤ uniOnXSub d := by
  refine sup_le (flagN_le d) ?_
  rintro _ ⟨h, rfl⟩
  exact ⟨1, one_mem _, by rw [wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩


set_option maxHeartbeats 2000000 in
theorem mem_jacGrp_of_fix (d : HypDec S S₀ ρ) {g : GA D S} (hg : mt S g ⬝ d.jX = d.jX) : g ∈ jacGrp d := by
  have hU : adj (mt S g) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S ⬝ d.j0 := cancel₃ (mt_unitary S g) d.j0
  have hY : d.pY ⬝ (mt S g ⬝ d.j0) = 0 := by
    have h1 : adj d.jX ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = adj (mt S g ⬝ d.jX) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) := by rw [hg]
    rw [d.pY_eq, Matrix.mul_assoc, h1, adj_mul, Matrix.mul_assoc, hU, d.wittDecomp_gram_X_anisotropic]
  obtain ⟨b, hb⟩ : ∃ b, d.pX ⬝ (mt S g ⬝ d.j0) = b := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, d.p0 ⬝ (mt S g ⬝ d.j0) = A := ⟨_, rfl⟩
  have hdec : mt S g ⬝ d.j0 = d.jX ⬝ b + d.j0 ⬝ A := by
    have he : (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY) ⬝ (mt S g ⬝ d.j0) = (1 : Mx D S.rank S.rank) ⬝ (mt S g ⬝ d.j0) := by rw [d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hY, hb, hA, Matrix.mul_zero, add_zero] at he
    exact he.symm
  have hAu : adj A * (gA S₀ * A) = gA S₀ := by
    have h1 : adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S₀ := by
      rw [adj_mul, Matrix.mul_assoc, hU, d.gram_00]
    rw [hdec] at h1
    simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, cancel₃ d.gram_XX, cancel₃ d.wittDecomp_gram_X_anisotropic,
      cancel₃ d.gram_0X, cancel₃ d.gram_00, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at h1
    exact h1
  obtain ⟨h, hAh⟩ : ∃ h : GA D S₀, mt S₀ h = A := ⟨ofMat S₀ A hAu, rfl⟩
  have hAi : A ⬝ mt S₀ h⁻¹ = mt S₀ 1 := by rw [← hAh, ← mt_mul, mul_inv_cancel]
  have hi : (d.emb0 h)⁻¹ = d.emb0 h⁻¹ := (map_inv d.emb0 h).symm
  have hm0 : mt S (g * d.emb0 h⁻¹) = mt S g ⬝ mt S (d.emb0 h⁻¹) := mt_mul S _ _
  have he0 : mt S (d.emb0 h⁻¹) ⬝ d.j0 = d.j0 ⬝ mt S₀ h⁻¹ := d.wittDecomp_anisotropicEmbedding_inclAnisotropic h⁻¹
  have heX : mt S (d.emb0 h⁻¹) ⬝ d.jX = d.jX := d.wittDecomp_anisotropicEmbedding_inclX h⁻¹
  have hj : d.j0 ⬝ mt S₀ (1 : GA D S₀) = d.j0 := by rw [mt_one, Matrix.mul_one]
  have hn0' : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 := by
    have s1 : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = (mt S g ⬝ d.j0) ⬝ mt S₀ h⁻¹ := by
      rw [hi, hm0, Matrix.mul_assoc, he0, Matrix.mul_assoc]
    have s2 : (d.jX ⬝ b + d.j0 ⬝ A) ⬝ mt S₀ h⁻¹ = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ (A ⬝ mt S₀ h⁻¹) :=
      (Matrix.add_mul (d.jX ⬝ b) (d.j0 ⬝ A) (mt S₀ h⁻¹)).trans
        (congrArg₂ (· + ·) (Matrix.mul_assoc d.jX b (mt S₀ h⁻¹)) (Matrix.mul_assoc d.j0 A (mt S₀ h⁻¹)))
    have s3 : d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ (A ⬝ mt S₀ h⁻¹) = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 :=
      (congrArg (fun M : Mx D S₀.rank S₀.rank => d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ M) hAi).trans (congrArg (fun M : Mx D S.rank S₀.rank => d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + M) hj)
    exact s1.trans ((congrArg (fun M : Mx D S.rank S₀.rank => M ⬝ mt S₀ h⁻¹) hdec).trans (s2.trans s3))
  have hn0 : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = d.j0 + d.jX ⬝ (b ⬝ mt S₀ h⁻¹) := hn0'.trans (add_comm _ _)
  have hnX' : mt S (g * (d.emb0 h)⁻¹) ⬝ d.jX = d.jX := by
    rw [hi, hm0, Matrix.mul_assoc, heX, hg]
  have hnX : mt S (g * (d.emb0 h)⁻¹) ⬝ d.jX = d.jX ⬝ (1 : GL (Fin ρ) (AE D)).1 := by
    rw [Units.val_one, Matrix.mul_one]; exact hnX'
  have hn : g * (d.emb0 h)⁻¹ ∈ flagN d := d.mem_NFlag one_mem_upperUni hnX hn0
  have hm : g * (d.emb0 h)⁻¹ * d.emb0 h ∈ jacGrp d :=
    mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)
  rwa [inv_mul_cancel_right] at hm

theorem uniOnX_subset (d : HypDec S S₀ ρ) : uniOnX d ⊆ jacGrp d := by
  rintro g ⟨hX, h0, h1⟩
  set u := uniUnit (blockX d g) h0 h1
  have hl : d.levi u ∈ flagN d := d.levi_mem_NFlag (uniUnit_mem _ h0 h1)
  have hf : mt S ((d.levi u)⁻¹ * g) ⬝ d.jX = d.jX := by
    rw [← map_inv, mt_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, levi_jX, Matrix.mul_assoc,
      show (u⁻¹).1 ⬝ blockX d g = 1 from Units.inv_mul u, Matrix.mul_one]
  have := mul_mem (Subgroup.mem_sup_left (T := d.emb0.range) hl) (mem_jacGrp_of_fix d hf)
  rwa [mul_inv_cancel_left] at this

theorem jacGrp_eq (d : HypDec S S₀ ρ) : (jacGrp d : Set (GA D S)) = uniOnX d := by
  refine Set.Subset.antisymm (fun g hg => ?_) (uniOnX_subset d)
  obtain ⟨u, hu, h⟩ := jacGrp_le d hg
  exact mem_uniOnX_of d hu h

end GlobalTheory.JacClosed

namespace GlobalTheory

theorem jacGrp_isClosed : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), IsClosed (jacGrp d : Set (GA D S)) := by
  intro D S S₀ ρ d
  rw [GlobalTheory.JacClosed.jacGrp_eq]
  exact GlobalTheory.JacClosed.isClosed_uniOnX d

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlaceDatumBlockTriangularMove
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

theorem collect_factors {ι : Type} (s : Finset ι) (A B p q : ι → ℂˣ) (u v : ℂ)
    (h : (∏ i ∈ s, (((q i : ℂˣ) : ℂ) * ((p i : ℂˣ) : ℂ)⁻¹)) * u =
      ((∏ i ∈ s, A i : ℂˣ) : ℂ) * ((∏ i ∈ s, B i : ℂˣ) : ℂ)⁻¹ * v) :
    u = ((∏ i ∈ s, (A i * (B i)⁻¹ * (p i * (q i)⁻¹)) : ℂˣ) : ℂ) * v := by

  have hne : (∏ i ∈ s, (((q i : ℂˣ) : ℂ) * ((p i : ℂˣ) : ℂ)⁻¹)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _))
  have hu : u = (∏ i ∈ s, (((q i : ℂˣ) : ℂ) * ((p i : ℂˣ) : ℂ)⁻¹))⁻¹ *
      (((∏ i ∈ s, A i : ℂˣ) : ℂ) * ((∏ i ∈ s, B i : ℂˣ) : ℂ)⁻¹ * v) := by
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hu]
  push_cast [Units.coe_prod]
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv, inv_inv]
  ring

theorem omegaG_blockTri_move : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, G PP ∈ blockTri (blkOf r t) ∧ H PP ∈ blockTri (blkOf r t) ∧ upperLeftBlock ha (G PP) = upperLeftBlock hb (H PP)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Pg, ((∏ c ∈ Finset.range k, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (G PP))) * (∏ c ∈ Finset.range (k + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (H PP)))⁻¹ * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹)) : ℂˣ) : ℂ) * omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) y := by
  intro D a b r t k ha hb hak hbk Pg Q χ ξ G H hGH y

  have hlaw := _root_.GlobalTheory.StepLaw.TypeDatum.omegaG_law D a b r t k ha hb hak hbk Pg Q χ ξ G H y
    (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val)
    (fun PP hP => (hGH PP hP).1) (fun PP hP => (hGH PP hP).2.1) (fun PP hP => (hGH PP hP).2.2)
    (fun _ _ => rfl)
  exact collect_factors Pg
    (fun PP => ∏ c ∈ Finset.range k, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (G PP)))
    (fun PP => ∏ c ∈ Finset.range (k + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (H PP)))
    (fun PP => χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)))
    (fun PP => χ (k + 1) PP (Matrix.GeneralLinearGroup.det (G PP))) _ _ hlaw

end GlobalTheory.StepLaw
end

