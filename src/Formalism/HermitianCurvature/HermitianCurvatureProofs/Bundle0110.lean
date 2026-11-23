module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0103
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliCoordinates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSection
public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRcLin
section
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {i : Fin (r + 1)}

theorem lie_rsmul {X : Q.Mx k r} (hX : Q.inLieLev k r i X) (x : ℝ) : Q.inLieLev k r i (x • X) := by
  unfold Formalism.FourierDecayAlt.Q.inLieLev at hX ⊢
  obtain ⟨h1, h2⟩ := hX
  have hs : ∀ v : Fin (2 * r + k + 1) → ℂ, (x • X) *ᵥ v = x • (X *ᵥ v) := fun v => by
    ext j
    simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc, mul_assoc]
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · rw [hs, (h2 a ha).1, smul_zero]
  · rw [hs, (h2 a ha).2, smul_zero]

private theorem inLieLev_add {X Y : Q.Mx k r} (hX : Q.inLieLev k r i X) (hY : Q.inLieLev k r i Y) :
    Q.inLieLev k r i (X + Y) := by
  unfold Formalism.FourierDecayAlt.Q.inLieLev at hX hY ⊢
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
      show Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y) =
        (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) by abel, hX.1, hY.1, add_zero]
  · rw [Matrix.add_mulVec, (hX.2 a ha).1, (hY.2 a ha).1, add_zero]
  · rw [Matrix.add_mulVec, (hX.2 a ha).2, (hY.2 a ha).2, add_zero]

theorem glc_lin {Z Z' : Q.Mx k r} (hZ : GLc k r Z) (hZ' : GLc k r Z') (a : ℂ) : GLc k r (a • Z + Z') := by
  unfold GLc at *
  obtain ⟨h1, h2⟩ := hZ
  obtain ⟨h1', h2'⟩ := hZ'
  have hI : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hsa : star a = (a.re : ℂ) - (a.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have ha : a = (a.re : ℂ) + (a.im : ℂ) * Complex.I := (Complex.re_add_im a).symm
  have e1 : hpart1 (Hpk k r) (a • Z + Z') =
      a.re • hpart1 (Hpk k r) Z + (-a.im) • hpart2 (Hpk k r) Z + hpart1 (Hpk k r) Z' := by
    unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    first | ring | (ring_nf; simp only [Complex.I_sq]; ring)
  have e2 : hpart2 (Hpk k r) (a • Z + Z') =
      a.im • hpart1 (Hpk k r) Z + a.re • hpart2 (Hpk k r) Z + hpart2 (Hpk k r) Z' := by
    unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination (-(a.im : ℂ) * Z i j / 2 + (a.im : ℂ) * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) i j / 2) * Complex.I_sq
  rw [e1, e2]
  exact ⟨inLieLev_add (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h1',
    inLieLev_add (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h2'⟩

private theorem hermitian_halves_smul_add (Z Z' : Q.Mx k r) (a : ℂ) :
    hpart1 (Hpk k r) (a • Z + Z') =
      a.re • hpart1 (Hpk k r) Z + (-a.im) • hpart2 (Hpk k r) Z + hpart1 (Hpk k r) Z' ∧
    hpart2 (Hpk k r) (a • Z + Z') =
      a.im • hpart1 (Hpk k r) Z + a.re • hpart2 (Hpk k r) Z + hpart2 (Hpk k r) Z' := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hsa : star a = (a.re : ℂ) - (a.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have ha : a = (a.re : ℂ) + (a.im : ℂ) * Complex.I := (Complex.re_add_im a).symm
  constructor
  · unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  · unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination (-(a.im : ℂ) * Z i j / 2 + (a.im : ℂ) * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) i j / 2) * Complex.I_sq

private theorem rdV_real_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Q.Mx k r → E)
    (X g : Q.Mx k r) (s : ℝ) : RdV (s • X) f g = (s : ℂ) • RdV X f g := by
  have hx : ∀ t : ℝ, (t : ℂ) • (s • X) = ((s * t : ℝ) : ℂ) • X := fun t => by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
    ring
  unfold Formalism.REAL.RdV
  simp only [hx]
  have key := deriv_comp_mul_left s (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) 0
  simp only [mul_zero] at key
  rw [key, Complex.coe_smul]

private theorem gLc_zero : GLc k r (0 : Q.Mx k r) := by
  unfold GLc Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2 Formalism.FourierDecayAlt.Q.inLieLev
  simp

private theorem rc_zero_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Q.Mx k r → E) (g : Q.Mx k r) :
    Rc (0 : Q.Mx k r) f g = 0 := by
  unfold Rc Formalism.REAL.RdV Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
  simp

private theorem rc_smul_add_of_smoothLev_of_gLc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}
    {f : Q.Mx k r → E} (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r}
    (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) {Z Z' : Q.Mx k r} (hZ : GLc k r Z) (hZ' : GLc k r Z') (a : ℂ) :
    Rc (a • Z + Z') f g = a • Rc Z f g + Rc Z' f g := by
  obtain ⟨e1, e2⟩ := hermitian_halves_smul_add Z Z' a
  have hz := hZ
  have hz' := hZ'
  unfold GLc at hz hz'
  obtain ⟨h1, h2⟩ := hz
  obtain ⟨h1', h2'⟩ := hz'
  unfold Rc
  rw [e1, e2,
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h1',
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (lie_rsmul h1 _) (lie_rsmul h2 _),
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h2',
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (lie_rsmul h1 _) (lie_rsmul h2 _)]
  simp only [rdV_real_smul, Complex.ofReal_neg]
  have haI : a * Complex.I = (a.re : ℂ) * Complex.I - a.im := by
    apply Complex.ext <;> simp
  rw [smul_add a, smul_smul a Complex.I, haI,
    show a • RdV (hpart1 (Hpk k r) Z) f g = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • RdV (hpart1 (Hpk k r) Z) f g by
      rw [Complex.re_add_im]]
  module

theorem rc_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)} {f : Q.Mx k r → E}
    (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) :
    ∃ L : Q.Mx k r →ₗ[ℂ] E, ∀ Z, GLc k r Z → Rc Z f g = L Z := by
  let S : Submodule ℂ (Q.Mx k r) :=
    { carrier := {Z | GLc k r Z}
      add_mem' := fun {Z Z'} hZ hZ' => by simpa using glc_lin hZ hZ' 1
      zero_mem' := gLc_zero
      smul_mem' := fun c Z hZ => by simpa using glc_lin hZ gLc_zero c }
  let f0 : S →ₗ[ℂ] E :=
    { toFun := fun Z => Rc (Z : Q.Mx k r) f g
      map_add' := fun Z Z' => by simpa using rc_smul_add_of_smoothLev_of_gLc hf hg Z.2 Z'.2 1
      map_smul' := fun c Z => by simpa [rc_zero_left] using rc_smul_add_of_smoothLev_of_gLc hf hg Z.2 gLc_zero c }
  obtain ⟨L, hL⟩ := LinearMap.exists_extend f0
  exact ⟨L, fun Z hZ => (LinearMap.congr_fun hL ⟨Z, hZ⟩).symm⟩

theorem radial_coefficient_linearity : RcLin := by
  unfold RcLin
  intro k r E _ _ D f _ hf g hg a Z Z' hZ hZ'
  obtain ⟨L, hL⟩ := rc_linear hf hg
  rw [hL _ (glc_lin hZ hZ' a), hL Z hZ, hL Z' hZ', map_add (f := _), map_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRcSmooth
section
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_coefficient_smoothness : RcSmooth := by
  intro k r E _ _ D f f' _ hf hf' Z hZ
  refine ⟨?_, ?_, ?_⟩
  · exact Qx2.smooth_add (Qx2.rd_smooth hf hZ.1) (Qx2.smooth_smul (Qx2.rd_smooth hf hZ.2) Complex.I)
  · intro a g hg
    have e : (fun x => a • f x + f' x) = fun x => f' x + a • f x := by
      funext x
      exact add_comm _ _
    show RdV _ (fun x => a • f x + f' x) g + Complex.I • RdV _ (fun x => a • f x + f' x) g =
      a • (RdV _ f g + Complex.I • RdV _ f g) + (RdV _ f' g + Complex.I • RdV _ f' g)
    rw [e, Qx2.rd_lin hf' hf a hg hZ.1, Qx2.rd_lin hf' hf a hg hZ.2, smul_add, smul_add, smul_comm Complex.I a]
    abel
  · intro E' _ _ L g hg
    show RdV _ (fun x => L (f x)) g + Complex.I • RdV _ (fun x => L (f x)) g = L (RdV _ f g + Complex.I • RdV _ f g)
    have e1 : RdV (hpart1 (Hpk k r) Z) (fun y => L (f y)) g = L (RdV _ f g) := Qx5.ntw_rd L hZ.1 f hf g hg
    have e2 : RdV (hpart2 (Hpk k r) Z) (fun y => L (f y)) g = L (RdV _ f g) := Qx5.ntw_rd L hZ.2 f hf g hg
    rw [e1, e2, map_add (f := _), map_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRightCov
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

theorem rdV_rightCov {k r : ℕ} {z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} (hπ : IsCRepOn (UWset k r z') π') (hc : ContinuousOn π' (UWset k r z'))
    {D : Set (Q.Mx k r)} {F : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hF : ∀ h ∈ UWset k r z', ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (g * h) = (F g).comp (π' h))
    {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) {X : Q.Mx k r} (hX : P.QrD.InLieW k r z' X) :
    RdV X F g = (F g).comp (P.QrD.dOp π' X) := by
  have key : ∀ t : ℝ, F (g * NormedSpace.exp ((t : ℂ) • X)) = (F g).comp (π' (NormedSpace.exp ((t : ℂ) • X))) :=
    fun t => hF _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) g hg
  unfold Formalism.REAL.RdV
  simp only [key]
  let L : (Wq →L[ℂ] Wq) →L[ℝ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wq Wp (F g)).restrictScalars ℝ
  have hL : ∀ A, L A = (F g).comp A := fun A => rfl
  have hd : HasDerivAt (fun t : ℝ => L (π' (NormedSpace.exp ((t : ℂ) • X)))) (L (P.QrD.dOp π' X)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 (Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hπ hc hX)
  simp only [hL] at hd
  exact hd.deriv

theorem right_covariance_holds : RightCov := by
  intro k r z' Wp Wq _ _ _ _ _ _ π' hπ hc _ D F _ _ _ hF g hg A hA
  refine ⟨⟨hA.1.1, hA.2.1⟩, ?_⟩
  unfold Rc P.QrD.ecOp
  rw [rdV_rightCov hπ hc hF hg hA.1, rdV_rightCov hπ hc hF hg hA.2]
  ext v
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPSecDeriv
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SD

theorem hasDeriv_form {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) {γ : ℝ → Matrix (Fin n) (Fin n) ℂ}
    {g γ' : Matrix (Fin n) (Fin n) ℂ} (h0 : γ 0 = g) (h : ∀ a b, HasDerivAt (fun t => γ t a b) (γ' a b) 0)
    (i j : Fin n) :
    HasDerivAt (fun t => ((γ t)ᴴ * H * γ t) i j) ((γ'ᴴ * H * g + gᴴ * H * γ') i j) 0 := by
  have hγ : ∀ a b, γ 0 a b = g a b := fun a b => by rw [h0]
  have key : ∀ a b, HasDerivAt (fun t => star (γ t a i) * H a b * γ t b j)
      (star (γ' a i) * H a b * g b j + star (g a i) * H a b * γ' b j) 0 := by
    intro a b
    have h1 : HasDerivAt (fun t => star (γ t a i) * H a b * γ t b j)
        (star (γ' a i) * H a b * γ 0 b j + star (γ 0 a i) * H a b * γ' b j) 0 :=
      (((h a i).star).mul_const (H a b)).mul (h b j)
    rw [hγ a i, hγ b j] at h1
    exact h1
  have hs := HasDerivAt.sum (u := Finset.univ) fun b _ =>
    HasDerivAt.sum (u := Finset.univ) fun a _ => key a b
  simp only [Finset.sum_fn] at hs
  have e1 : (fun t => ((γ t)ᴴ * H * γ t) i j) =
      fun t => ∑ b, ∑ a, star (γ t a i) * H a b * γ t b j := by
    funext t
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  have e2 : (γ'ᴴ * H * g + gᴴ * H * γ') i j =
      ∑ b, ∑ a, (star (γ' a i) * H a b * g b j + star (g a i) * H a b * γ' b j) := by
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
      Finset.sum_add_distrib]
  rw [e1, e2]
  exact hs

variable {k r : ℕ}

theorem lie_of_curve {μ : ℂ → Q.Mx k r} {ζ : ℂ} {D : ℂ →L[ℝ] Q.Mx k r} (hD : HasFDerivAt μ D ζ)
    (hG : ∀ᶠ w in 𝓝 ζ, μ w ∈ Q.Glev k r (Fin.last r)) (v : ℂ) :
    Q.inLieLev k r (Fin.last r) ((μ ζ)⁻¹ * D v) := by
  have hℓ : HasDerivAt (fun t : ℝ => ζ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ζ
  have hγ : HasDerivAt (fun t : ℝ => μ (ζ + t • v)) (D v) 0 := by
    have hD' : HasFDerivAt μ D (ζ + (0 : ℝ) • v) := by simpa using hD
    exact hD'.comp_hasDerivAt (0 : ℝ) hℓ
  have hent : ∀ a b, HasDerivAt (fun t : ℝ => μ (ζ + t • v) a b) (D v a b) 0 := by
    intro a b
    exact hasDerivAt_pi.1 (hasDerivAt_pi.1 hγ a) b
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), μ (ζ + t • v) ∈ Q.Glev k r (Fin.last r) := by
    have ht : Tendsto (fun t : ℝ => ζ + t • v) (𝓝 0) (𝓝 ζ) := by
      simpa using hℓ.continuousAt.tendsto
    exact ht.eventually hG
  have hU : (μ ζ)ᴴ * Hpk k r * μ ζ = Hpk k r := hG.self_of_nhds.1
  have hder : (D v)ᴴ * Hpk k r * μ ζ + (μ ζ)ᴴ * Hpk k r * D v = 0 := by
    ext i j
    have h1 := hasDeriv_form (Hpk k r) (γ := fun t : ℝ => μ (ζ + t • v)) (g := μ ζ) (γ' := D v)
      (by simp) hent i j
    have h2 : HasDerivAt (fun t : ℝ => ((μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v)) i j) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (Hpk k r i j)).congr_of_eventuallyEq (hev.mono fun t ht => by
        show ((μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v)) i j = Hpk k r i j
        rw [show (μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v) = Hpk k r from ht.1])
    exact h1.unique h2
  have hH : (Hpk k r).det ≠ 0 := by
    have h1 := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h1
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hdet : IsUnit (μ ζ).det := by
    have h2 := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    refine isUnit_iff_ne_zero.2 fun h0 => hH ?_
    rw [h0, mul_zero] at h2
    exact h2.symm
  have hgi : μ ζ * (μ ζ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have e1 : ((μ ζ)⁻¹)ᴴ * Hpk k r = Hpk k r * μ ζ := by
    calc ((μ ζ)⁻¹)ᴴ * Hpk k r = ((μ ζ)⁻¹)ᴴ * ((μ ζ)ᴴ * Hpk k r * μ ζ) := by rw [hU]
      _ = (μ ζ * (μ ζ)⁻¹)ᴴ * Hpk k r * μ ζ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * μ ζ := by rw [hgi, Matrix.conjTranspose_one, Matrix.one_mul]
  have e2 : Hpk k r * (μ ζ)⁻¹ = (μ ζ)ᴴ * Hpk k r := by
    calc Hpk k r * (μ ζ)⁻¹ = (μ ζ)ᴴ * Hpk k r * μ ζ * (μ ζ)⁻¹ := by rw [hU]
      _ = (μ ζ)ᴴ * Hpk k r := by rw [Matrix.mul_assoc, hgi, Matrix.mul_one]
  have hvec : ∀ w : Fin (2 * r + k + 1) → ℂ, (∀ᶠ t in 𝓝 (0 : ℝ), μ (ζ + t • v) *ᵥ w = w) →
      D v *ᵥ w = 0 := by
    intro w hw
    funext q
    have hd : HasDerivAt (fun t : ℝ => (μ (ζ + t • v) *ᵥ w) q) ((D v *ᵥ w) q) 0 := by
      simp only [Matrix.mulVec, dotProduct]
      first
      | exact HasDerivAt.sum fun p _ => (hent q p).mul_const (w p)
      | exact HasDerivAt.fun_sum fun p _ => (hent q p).mul_const (w p)
    have hc : HasDerivAt (fun t : ℝ => (μ (ζ + t • v) *ᵥ w) q) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (w q)).congr_of_eventuallyEq (hw.mono fun t ht => by
        show (μ (ζ + t • v) *ᵥ w) q = w q
        rw [ht])
    exact hd.unique hc
  unfold Q.inLieLev
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc (Hpk k r), e2,
      ← Matrix.mul_assoc]
    exact hder
  · rw [← Matrix.mulVec_mulVec, hvec _ (hev.mono fun t ht => (ht.2 a ha).1), Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, hvec _ (hev.mono fun t ht => (ht.2 a ha).2), Matrix.mulVec_zero]

end SD

theorem section_derivative_holds : SecDeriv := by
  intro k r z z' hk hz hz' hT hT' ζ hζ
  have hsec := TheSec.theSection_isSection k r z z' hk hz hz' hT hT'
  have hA : IsOpen {w : ℂ | Tz k r z * Tz k r z' < Complex.normSq w} :=
    isOpen_lt continuous_const Complex.continuous_normSq
  have hcd : ContDiffOn ℝ ∞ (mu0 k r z z') {w : ℂ | Tz k r z * Tz k r z' < Complex.normSq w} :=
    NFRadRedA.muZ_contDiffOn hsec
  have hdiff : DifferentiableAt ℝ (mu0 k r z z') ζ :=
    (hcd.differentiableOn (by simp)).differentiableAt (hA.mem_nhds hζ)
  obtain ⟨D, hD⟩ : ∃ D : ℂ →L[ℝ] Q.Mx k r, HasFDerivAt (mu0 k r z z') D ζ := ⟨_, hdiff.hasFDerivAt⟩
  have hG : ∀ᶠ w in 𝓝 ζ, mu0 k r z z' w ∈ Q.Glev k r (Fin.last r) := by
    filter_upwards [hA.mem_nhds hζ] with w hw
    exact NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hw)
  have hg : mu0 k r z z' ζ ∈ Q.Glev k r (Fin.last r) := hG.self_of_nhds
  have hX := SD.lie_of_curve hD hG
  have hrow : ∀ i, HasFDerivAt (fun w => mu0 k r z z' w i) ((ContinuousLinearMap.proj i).comp D) ζ :=
    hasFDerivAt_pi'.1 hD
  have hent : ∀ i j v, fderiv ℝ (fun w => mu0 k r z z' w i j) ζ v = D v i j := by
    intro i j v
    have h := (hasFDerivAt_pi'.1 (hrow i)) j
    rw [h.fderiv]
    rfl
  have hs1 : D ((1 / 2 : ℝ) • (1 : ℂ)) = (1 / 2 : ℝ) • D 1 := map_smul D _ _
  have hs2 : D ((-(1 / 2) : ℝ) • Complex.I) = (-(1 / 2) : ℝ) • D Complex.I := map_smul D _ _
  have hs3 : D ((1 / 2 : ℝ) • Complex.I) = (1 / 2 : ℝ) • D Complex.I := map_smul D _ _
  have e1 : etaZ k r z z' ζ = (mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • (1 : ℂ)) +
      Complex.I • ((mu0 k r z z' ζ)⁻¹ * D ((-(1 / 2) : ℝ) • Complex.I)) := by
    unfold etaZ
    rw [← Matrix.mul_smul, ← Matrix.mul_add, hs1, hs2]
    congr 1
    ext i j
    simp only [Matrix.of_apply, NF.dZ, hent, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  have e2 : etaZb k r z z' ζ = (mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • (1 : ℂ)) +
      Complex.I • ((mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • Complex.I)) := by
    unfold etaZb
    rw [← Matrix.mul_smul, ← Matrix.mul_add, hs1, hs3]
    congr 1
    ext i j
    simp only [Matrix.of_apply, NF.dZb, hent, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  obtain ⟨p1, p2⟩ := Qx5.hpart_unique (hX ((1 / 2 : ℝ) • (1 : ℂ))) (hX ((-(1 / 2) : ℝ) • Complex.I))
  obtain ⟨q1, q2⟩ := Qx5.hpart_unique (hX ((1 / 2 : ℝ) • (1 : ℂ))) (hX ((1 / 2 : ℝ) • Complex.I))
  rw [← e1] at p1 p2
  rw [← e2] at q1 q2
  have hmem : mu0 k r z z' ζ ∈ Q.Glev k r (Fin.last r) ∩ Dp k r z z' := by
    refine ⟨hg, ?_⟩
    show 0 < Complex.normSq (Q.zetaL k r z z' (Fin.last r) (NF.muZ k r (TheSec.theSection k r z z') ζ)) -
      Tz k r z * Tz k r z'
    rw [NFRadRedA.zeta_muZ hz hz' hsec hζ]
    linarith
  refine ⟨⟨by rw [p1]; exact hX _, by rw [p2]; exact hX _⟩, ⟨by rw [q1]; exact hX _, by rw [q2]; exact hX _⟩, hmem, ?_⟩
  intro E _ _ F hF
  obtain ⟨U, F', hU, hgU, hFc, he⟩ := hF _ hmem
  have hd : DifferentiableAt ℝ F' (mu0 k r z z' ζ) :=
    (hFc.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hR : ∀ v, RdV ((mu0 k r z z' ζ)⁻¹ * D v) F (mu0 k r z z' ζ) = fderiv ℝ F' (mu0 k r z z' ζ) (D v) := by
    intro v
    have h := (Qx2.hasDeriv_ext hU hgU hg (hX v) hd he).deriv
    rw [← Matrix.mul_assoc, FrameEntries.mul_inv_uh hg.1, Matrix.one_mul] at h
    exact h
  have hC : HasFDerivAt (fun w => F (mu0 k r z z' w)) ((fderiv ℝ F' (mu0 k r z z' ζ)).comp D) ζ := by
    refine (hd.hasFDerivAt.comp ζ hD).congr_of_eventuallyEq ?_
    filter_upwards [hG, hD.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)] with w h1 h2
    exact he _ h2 h1
  constructor
  · unfold Rc dZV
    rw [p1, p2, hR, hR, hC.fderiv, hs1, hs2]
    simp only [ContinuousLinearMap.comp_apply, map_smul]
    rw [← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    module
  · unfold Rc dZbV
    rw [q1, q2, hR, hR, hC.fderiv, hs1, hs3]
    simp only [ContinuousLinearMap.comp_apply, map_smul]
    rw [← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    module

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TLPlanAsm
section
namespace Formalism.FourierDecayAlt.TL

open Finset MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

open Classical

theorem act_e1Vec {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ}
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (M : Wd.SlopeTestRemainingChoices S (Q.Pr (Q.RadSp k r z z' π π'))) (Φ : Q.RadSp k r z z' π π') (e : Wd.Ix S) :
    P5.act M (Top.firstStateVector Φ) e = (M e e1).1 Φ := by
  unfold P5.act Top.firstStateVector
  rw [Finset.sum_eq_single (fun _ => 0)]
  · simp only [if_true]
    rfl
  · intro b _ hb
    rw [if_neg hb, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end

end Formalism.FourierDecayAlt.TL
end

