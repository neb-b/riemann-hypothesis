module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0085
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalReductionUnitary
section
open Matrix Filter Topology Set
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.RadicalReductionUnitary

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD Formalism.FourierDecayAlt.P.NFRadRedL

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {k r : ℕ}

theorem inv_eq_ring_inverse (A : Q.Mx k r) : A⁻¹ = Ring.inverse A := by
  first
    | exact Matrix.nonsing_inv_eq_ringInverse A
    | exact Matrix.nonsing_inv_eq_ring_inverse A

def lieU (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Q.Mx k r) where
  carrier := {X | InLieW k r z X}
  zero_mem' := ⟨⟨by simp, fun a _ => ⟨by simp, by simp⟩⟩, by simp⟩
  add_mem' := by
    rintro X Y ⟨⟨hX1, hX2⟩, hX3⟩ ⟨⟨hY1, hY2⟩, hY3⟩
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
        show Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y) =
          (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) by abel, hX1, hY1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).1, (hY2 a ha).1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).2, (hY2 a ha).2, add_zero]
    · rw [Matrix.add_mulVec, hX3, hY3, add_zero]
  smul_mem' := by
    rintro c X ⟨⟨hX1, hX2⟩, hX3⟩
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_smul]
      simp only [RCLike.star_def, RCLike.conj_ofReal]
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).2, smul_zero]
    · rw [Matrix.smul_mulVec, hX3, smul_zero]

theorem cinv_eq (g : Q.Mx k r) : cinv g = Ring.inverse (g + 1) * (g - 1) := by
  rw [cinv, inv_eq_ring_inverse]

theorem cinv_contDiffAt {g : Q.Mx k r} (hu : IsUnit (g + 1)) : ContDiffAt ℝ ∞ cinv g := by
  have h1 : ContDiffAt ℝ ∞ (fun x : Q.Mx k r => Ring.inverse (x + 1)) g := by
    obtain ⟨u, hu⟩ := hu
    have : ContDiffAt ℝ ∞ Ring.inverse (u : Q.Mx k r) := contDiffAt_ringInverse ℝ u
    rw [hu] at this
    exact this.comp g (contDiffAt_id.add contDiffAt_const)
  have h2 : ContDiffAt ℝ ∞ (fun x : Q.Mx k r => x - 1) g := contDiffAt_id.sub contDiffAt_const
  have : (cinv : Q.Mx k r → Q.Mx k r) = fun x => Ring.inverse (x + 1) * (x - 1) := funext cinv_eq
  rw [this]
  exact h1.mul h2

theorem two_mul_half : ((1 : Q.Mx k r) + 1) * ((1 / 2 : ℂ) • 1) = 1 := by
  rw [mul_smul_comm, mul_one, ← two_smul ℂ (1 : Q.Mx k r), smul_smul]
  norm_num

theorem half_mul_two : ((1 / 2 : ℂ) • (1 : Q.Mx k r)) * (1 + 1) = 1 := by
  rw [smul_mul_assoc, one_mul, ← two_smul ℂ (1 : Q.Mx k r), smul_smul]
  norm_num

def twoU (k r : ℕ) : (Q.Mx k r)ˣ := ⟨1 + 1, (1 / 2 : ℂ) • 1, two_mul_half, half_mul_two⟩

theorem cinv_hasFDerivAt_one :
    HasFDerivAt (cinv : Q.Mx k r → Q.Mx k r) (ContinuousLinearMap.mul ℝ (Q.Mx k r) ((1 / 2 : ℂ) • 1)) 1 := by
  have hinv : Ring.inverse ((1 : Q.Mx k r) + 1) = (1 / 2 : ℂ) • 1 := Ring.inverse_unit (twoU k r)
  have h1 := (hasFDerivAt_ringInverse (𝕜 := ℝ) (twoU k r)).comp (1 : Q.Mx k r)
    ((hasFDerivAt_id (𝕜 := ℝ) (1 : Q.Mx k r)).add_const 1)
  have h2 : HasFDerivAt (fun x : Q.Mx k r => x - 1) (ContinuousLinearMap.id ℝ (Q.Mx k r)) 1 :=
    (hasFDerivAt_id (1 : Q.Mx k r)).sub_const 1
  have h3 := h1.mul' h2
  have hfun : (cinv : Q.Mx k r → Q.Mx k r) =
      (fun x : Q.Mx k r => Ring.inverse (id x + 1)) * (fun x : Q.Mx k r => x - 1) := by
    funext x; rw [cinv_eq]; rfl
  rw [hfun]
  refine h3.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun h => ?_
  simp [hinv]
  change ((2 : ℂ)⁻¹ • (1 : Q.Mx k r)) * h = (2 : ℂ)⁻¹ • h
  rw [smul_mul_assoc, one_mul]

private theorem exp_mulVec_eq_self_of_mulVec_eq_zero {X : Q.Mx k r} {v : Fin (2 * r + k + 1) → ℂ} (hv : X *ᵥ v = 0) :
    NormedSpace.exp X *ᵥ v = v := by
  let Lv : Q.Mx k r →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    { toFun := fun A => A *ᵥ v
      map_add' := fun A B => Matrix.add_mulVec A B v
      map_smul' := fun c A => Matrix.smul_mulVec c A v }
  let Lc := LinearMap.toContinuousLinearMap Lv
  have hs : Summable (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • X ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) X
  have hpow : ∀ n : ℕ, (X ^ (n + 1)) *ᵥ v = 0 := fun n => by
    rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have key : Lc (∑' n : ℕ, ((n.factorial : ℂ))⁻¹ • X ^ n) =
      ∑' n : ℕ, Lc (((n.factorial : ℂ))⁻¹ • X ^ n) := Lc.map_tsum hs
  simp only [Lc, LinearMap.coe_toContinuousLinearMap', Lv, LinearMap.coe_mk, AddHom.coe_mk] at key
  rw [NormedSpace.exp_eq_tsum ℂ]
  simp only
  rw [key, tsum_eq_single 0]
  · simp
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Matrix.smul_mulVec, hpow, smul_zero]

private theorem exp_mem_uwset_of_inLieW {z : Fin (2 * r + k + 1) → ℂ} {X : Q.Mx k r} (hX : InLieW k r z X) :
    NormedSpace.exp X ∈ UWset k r z := by
  obtain ⟨hX1, hX2⟩ := hX
  have h1 : (1 : Q.Mx k r) ∈ Glev k r (Fin.last r) := by
    simp [Glev, UH]
  have h := Formalism.FourierDecayAlt.P.LeftDerivativeCurves.lcurve_lev h1 hX1 1
  simp only [Complex.ofReal_one, one_smul, mul_one, Glev, Set.mem_setOf_eq] at h
  simp only [UWset, Set.mem_setOf_eq]
  exact ⟨h.1, fun a => h.2 a (by simp), exp_mulVec_eq_self_of_mulVec_eq_zero hX2⟩

theorem locLogOp (z : Fin (2 * r + k + 1) → ℂ) :
    ∃ O : Set (Q.Mx k r), IsOpen O ∧ (1 : Q.Mx k r) ∈ O ∧ ∃ Λ : Q.Mx k r → Q.Mx k r, ContDiffOn ℝ ∞ Λ O ∧
      ∀ g ∈ O, g ∈ UWset k r z → InLieW k r z (Λ g) ∧ NormedSpace.exp (Λ g) = g := by
  classical

  let L := lieU k r z
  haveI : FiniteDimensional ℝ (Q.Mx k r) := inferInstance
  haveI : CompleteSpace L := (Submodule.complete_of_finiteDimensional L).completeSpace_coe
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective L.subtype (Submodule.ker_subtype L)
  let P : Q.Mx k r →L[ℝ] L := LinearMap.toContinuousLinearMap p
  have hP : ∀ Y : L, P (Y : Q.Mx k r) = Y := fun Y => by
    show p (L.subtype Y) = Y
    rw [← LinearMap.comp_apply, hp, LinearMap.id_apply]
  have hPmem : ∀ x, InLieW k r z x → (P x : Q.Mx k r) = x := fun x hx => by
    have := hP ⟨x, hx⟩
    rw [this]

  let Φ : L → L := fun Y => (2 : ℝ) • P (cinv (NormedSpace.exp (Y : Q.Mx k r)))
  have hu1 : IsUnit ((1 : Q.Mx k r) + 1) := ⟨twoU k r, rfl⟩
  have he0 : NormedSpace.exp ((0 : L) : Q.Mx k r) = 1 := by simp
  have hexp : ∀ x : Q.Mx k r, ContDiffAt ℝ ∞ (NormedSpace.exp : Q.Mx k r → Q.Mx k r) x :=
    fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hΦc : ∀ Y : L, IsUnit (NormedSpace.exp (Y : Q.Mx k r) + 1) → ContDiffAt ℝ ∞ Φ Y := by
    intro Y hY
    have a1 : ContDiffAt ℝ ∞ (fun Y : L => NormedSpace.exp (Y : Q.Mx k r)) Y :=
      (hexp _).comp Y L.subtypeL.contDiff.contDiffAt
    have a0 : ContDiffAt ℝ ∞ (cinv : Q.Mx k r → Q.Mx k r) (NormedSpace.exp (Y : Q.Mx k r)) :=
      cinv_contDiffAt (k := k) (r := r) hY
    have a2 : ContDiffAt ℝ ∞ ((cinv : Q.Mx k r → Q.Mx k r) ∘ fun Y : L => NormedSpace.exp (Y : Q.Mx k r)) Y :=
      ContDiffAt.comp (g := (cinv : Q.Mx k r → Q.Mx k r)) (f := fun Y : L => NormedSpace.exp (Y : Q.Mx k r)) Y a0 a1
    exact (P.contDiff.contDiffAt.comp Y a2).const_smul (2 : ℝ)
  have hΦ0c : ContDiffAt ℝ ∞ Φ 0 := hΦc 0 (by rw [he0]; exact hu1)
  have hΦ0d : HasFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ L : L ≃L[ℝ] L) : L →L[ℝ] L) 0 := by
    have hE : HasFDerivAt (fun Y : L => NormedSpace.exp (Y : Q.Mx k r))
        ((1 : Q.Mx k r →L[ℝ] Q.Mx k r).comp L.subtypeL) 0 := by
      convert HasFDerivAt.comp_continuousLinearMap L.subtypeL (0 : L)
        (hasFDerivAt_exp_zero (𝕂 := ℝ)) using 1 <;> rfl
    have hC : HasFDerivAt (cinv : Q.Mx k r → Q.Mx k r)
        (ContinuousLinearMap.mul ℝ (Q.Mx k r) ((1 / 2 : ℂ) • 1))
        (NormedSpace.exp ((0 : L) : Q.Mx k r)) := by
      rw [he0]; exact cinv_hasFDerivAt_one
    have h := ((P.hasFDerivAt).comp (0 : L) (hC.comp (0 : L) hE)).const_smul (2 : ℝ)
    refine HasFDerivAt.congr_fderiv h ?_
    refine ContinuousLinearMap.ext fun Y => ?_
    have hh : ((1 / 2 : ℂ) • (1 : Q.Mx k r)) * (Y : Q.Mx k r) = (1 / 2 : ℝ) • (Y : Q.Mx k r) := by
      rw [smul_mul_assoc, one_mul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      norm_num
    change (2 : ℝ) • P (((1 / 2 : ℂ) • (1 : Q.Mx k r)) * (Y : Q.Mx k r)) = Y
    rw [hh, P.map_smul, hP, smul_smul]
    norm_num
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let f := ContDiffAt.toOpenPartialHomeomorph Φ hΦ0c hΦ0d hn
  have hfc : (f : L → L) = Φ := rfl

  have hU : ∀ᶠ Y : L in 𝓝 (0 : L), IsUnit (NormedSpace.exp (Y : Q.Mx k r) + 1) := by
    have hc : ContinuousAt (fun Y : L => NormedSpace.exp (Y : Q.Mx k r) + 1) 0 :=
      (((hexp _).continuousAt).comp L.subtypeL.continuous.continuousAt).add continuousAt_const
    have h0 : IsUnit (NormedSpace.exp ((0 : L) : Q.Mx k r) + 1) := by rw [he0]; exact hu1
    exact hc.eventually_mem (Units.isOpen.mem_nhds h0)
  have hD : ∀ᶠ Y : L in 𝓝 (0 : L), fderiv ℝ Φ Y ∈
      Set.range (ContinuousLinearEquiv.toContinuousLinearMap : (L ≃L[ℝ] L) → L →L[ℝ] L) := by
    have hcont : ContinuousAt (fderiv ℝ Φ) 0 := (hΦ0c.fderiv_right (m := 0) (by simp)).continuousAt
    exact hcont.eventually_mem (ContinuousLinearEquiv.isOpen.mem_nhds
      ⟨ContinuousLinearEquiv.refl ℝ L, hΦ0d.fderiv.symm⟩)
  obtain ⟨V, hVsub, hVo, hV0⟩ := eventually_nhds_iff.mp (hU.and hD)
  have hsym : ∀ a ∈ f.target ∩ f.symm ⁻¹' V, ContDiffAt ℝ ∞ f.symm a := by
    rintro a ⟨ha, haV⟩
    obtain ⟨hu, e, he⟩ := hVsub _ haV
    have hcd := hΦc _ hu
    have hd : HasFDerivAt Φ (e : L →L[ℝ] L) (f.symm a) := by
      rw [show (e : L →L[ℝ] L) = fderiv ℝ Φ (f.symm a) from he]
      exact (hcd.differentiableAt (by simp)).hasFDerivAt
    exact f.contDiffAt_symm ha (by rw [hfc]; exact hd) (by rw [hfc]; exact hcd)

  let w : Q.Mx k r → L := fun g => (2 : ℝ) • P (cinv g)
  have hw : ∀ g : Q.Mx k r, IsUnit (g + 1) → ContDiffAt ℝ ∞ w g := fun g hg =>
    ((P.contDiff.contDiffAt).comp g (cinv_contDiffAt (k := k) (r := r) hg)).const_smul (2 : ℝ)
  have hGU : IsOpen {g : Q.Mx k r | IsUnit (g + 1)} :=
    Units.isOpen.preimage (continuous_id.add continuous_const)
  have hT : IsOpen (f.target ∩ f.symm ⁻¹' V) := f.isOpen_inter_preimage_symm hVo
  have hwc : ContinuousOn w {g : Q.Mx k r | IsUnit (g + 1)} := fun g hg =>
    (hw g hg).continuousAt.continuousWithinAt
  have hΦ00 : Φ 0 = 0 := by simp [Φ, cinv_one]
  have hw1 : w 1 = 0 := by simp [w, cinv_one]
  refine ⟨{g : Q.Mx k r | IsUnit (g + 1)} ∩ w ⁻¹' (f.target ∩ f.symm ⁻¹' V),
    hwc.isOpen_inter_preimage hGU hT, ⟨hu1, ?_⟩, fun g => ((f.symm (w g) : L) : Q.Mx k r), ?_, ?_⟩
  · have h0t : Φ 0 ∈ f.target := ContDiffAt.image_mem_toOpenPartialHomeomorph_target hΦ0c hΦ0d hn
    have h0s : (0 : L) ∈ f.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hΦ0c hΦ0d hn
    rw [hΦ00] at h0t
    refine ⟨?_, ?_⟩
    · show w 1 ∈ f.target
      rw [hw1]; exact h0t
    · show f.symm (w 1) ∈ V
      rw [hw1, ← hΦ00, ← hfc, f.left_inv h0s]
      exact hV0
  · intro g hg
    exact (L.subtypeL.contDiff.contDiffAt.comp g ((hsym (w g) hg.2).comp g (hw g hg.1))).contDiffWithinAt
  · intro g hg hgU
    set Y := f.symm (w g) with hYdef
    have hY : InLieW k r z (Y : Q.Mx k r) := Y.2
    refine ⟨hY, ?_⟩
    obtain ⟨huY, -⟩ := hVsub _ hg.2.2
    have h1 : Φ Y = w g := f.right_inv hg.2.1
    have hdg : IsUnit (g + 1).det := (Matrix.isUnit_iff_isUnit_det _).mp hg.1
    have hdY : IsUnit (NormedSpace.exp (Y : Q.Mx k r) + 1).det := (Matrix.isUnit_iff_isUnit_det _).mp huY
    have h2 : P (cinv (NormedSpace.exp (Y : Q.Mx k r))) = P (cinv g) :=
      smul_right_injective L (two_ne_zero' ℝ) h1
    have h3 := congrArg Subtype.val h2
    rw [hPmem _ (cinv_lie (exp_mem_uwset_of_inLieW hY) hdY), hPmem _ (cinv_lie hgU hdg)] at h3
    exact cinv_inj hdY hdg h3

end Formalism.FourierDecayAlt.P.RadicalReductionUnitary
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport
section
namespace Formalism.FourierDecayAlt.P.PBJ

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

section rw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rw_vanish_GV {O : Set (Mat k r)} (hO : IsOpen O) {f : Mat k r → E}
    (h : ∀ g ∈ O, g ∈ GV k r → f g = 0) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ g ∈ O, g ∈ GV k r → Rw w f g = 0
  | [], _ => h
  | X :: w, hw => by
    intro g hg hgG
    have ih := rw_vanish_GV hO h w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    have hX : inLie k r X := hw X List.mem_cons_self
    show RdV X (Rw w f) g = 0
    unfold RdV
    have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
      (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
    have h0 : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 ∈ O := by
      simp only; rw [Formalism.FourierDecayAlt.P.B5.curve_zero]; exact hg
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ O :=
      hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
    have e : (fun t : ℝ => Rw w f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hev] with t ht
      exact ih _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)
    rw [e.deriv_eq]; simp

end rw

section op

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem opApply_eq_zero (Θ : DiffOp k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r)
    (h : ∀ T ∈ Θ, Rw T.word F g = 0) : opApply Θ F g = 0 := by
  unfold opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
  rw [h T hT, map_zero]

theorem ckOn_opApply_list (UU : Set (Mat k r)) (F : Mat k r → (Wq →L[ℂ] Wp))
    (hF : CkOn ⊤ (GV k r) F) (hs : closure {g | g ∈ GV k r ∧ F g ≠ 0} ⊆ UU) :
    ∀ Θ : DiffOp k r Wp Wq, (∀ T ∈ Θ, CkOn ⊤ UU T.coef) →
      (∀ T ∈ Θ, closure {g | g ∈ GV k r ∧ Rw T.word F g ≠ 0} ⊆ UU) → CkOn ⊤ (GV k r) (opApply Θ F)
  | [], _, _ => by
    have e : opApply ([] : DiffOp k r Wp Wq) F = fun _ => 0 := by funext g; simp [opApply]
    rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero
  | T :: Θ, hc, hsu => by
    have e : opApply (T :: Θ) F = fun g => T.coef g (Rw T.word F g) + opApply Θ F g := by
      funext g; simp [opApply]
    rw [e]
    refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add ?_ (ckOn_opApply_list UU F hF hs Θ (fun T' hT' => hc T' (List.mem_cons_of_mem _ hT'))
      (fun T' hT' => hsu T' (List.mem_cons_of_mem _ hT')))
    exact Formalism.FourierDecayAlt.P.B5.ckOn_coef (hc T List.mem_cons_self)
      (Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_Rw_top hF T.word_lie) (hsu T List.mem_cons_self)

end op

end Formalism.FourierDecayAlt.P.PBJ

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

theorem theta_compact_support : Formalism.FourierDecayAlt.KB.ThetaCpt := by
  intro Wp Wq _ _ _ _ _ _ P p F w e Cb hDD hF hw
  obtain ⟨nf, fib, o, κ, Dop, _, hIn, _, _, hΘeq⟩ := hDD w hw e
  obtain ⟨hFs, ⟨R, hR⟩, ε, hε, hεF⟩ := hF
  have hGc : Continuous (Gf P.k P.r p.T.base.z p.T.base.z') := Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _

  have hv1 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat P.k P.r | Gf P.k P.r p.T.base.z p.T.base.z' g < ε}, g ∈ GV P.k P.r →
      Rw T.word F g = 0 := fun T _ =>
    PBJ.rw_vanish_GV (isOpen_lt hGc continuous_const)
      (fun g hg hgG => by by_contra hne; exact absurd (hεF g hgG hne) (not_le.2 hg)) T.word T.word_lie
  have hv2 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat P.k P.r | R < gN g}, g ∈ GV P.k P.r → Rw T.word F g = 0 := fun T _ =>
    PBJ.rw_vanish_GV (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous)
      (fun g hg hgG => by by_contra hne; exact absurd (hR g hgG hne) (not_le.2 hg)) T.word T.word_lie
  have hcl : IsClosed {g : Mat P.k P.r | g ∈ GV P.k P.r ∧ ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g} :=
    Formalism.FourierDecayAlt.P.B5.GV_closed.inter (isClosed_le continuous_const hGc)
  have hsub : {g : Mat P.k P.r | g ∈ GV P.k P.r ∧ ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g} ⊆
      C6.domL p.T.base ∅ := fun g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2, by simp⟩
  have hsF : closure {g | g ∈ GV P.k P.r ∧ F g ≠ 0} ⊆ C6.domL p.T.base ∅ := by
    refine subset_trans (closure_minimal ?_ hcl) hsub
    intro g hg; exact ⟨hg.1, hεF g hg.1 hg.2⟩
  have hsT : ∀ T ∈ Dop, closure {g | g ∈ GV P.k P.r ∧ Rw T.word F g ≠ 0} ⊆ C6.domL p.T.base ∅ := by
    intro T hT
    refine subset_trans (closure_minimal ?_ hcl) hsub
    intro g hg
    refine ⟨hg.1, ?_⟩
    by_contra hlt
    exact hg.2 (hv1 T hT g (not_le.1 hlt) hg.1)
  refine ⟨opApply Dop F, ⟨?_, ⟨R, ?_⟩, ε, hε, ?_⟩, fun g hg => hΘeq F g hg, ?_⟩
  · exact PBJ.ckOn_opApply_list _ F hFs hsF Dop (fun T hT => (hIn.1 T hT).1) hsT
  · intro g hgG hne
    by_contra hlt
    exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv2 T hT g (not_le.1 hlt) hgG)
  · intro g hgG hne
    by_contra hlt
    exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g (not_le.1 hlt) hgG)
  · intro a
    show D.vecV p.T.base p.ν' p.m₀ _ a = D.vecV p.T.base p.ν' p.m₀ _ a
    unfold D.vecV
    split_ifs with h1 h2
    · have hγ := h2.choose_spec
      have hG : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h2.choose := by
        rw [← Formalism.FourierDecayAlt.P.ptG_spec _ _ _ _ a _ h1.1 hγ.2.1]; exact h1.2
      rw [Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae p.T.base h2.choose _ (p.Θ.Θ w e F) (opApply Dop F) 1 ?_, one_smul]
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS p.T.base] with q hq
      rw [one_smul]
      simp only [D.orbIntegrand, rho]
      rw [hΘeq F _ ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem p.T.base hq hγ.1,
        by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs p.T.base hq]; exact hG, by simp⟩]
    · rfl
    · rfl

end Formalism.FourierDecayAlt.P
end

