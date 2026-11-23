module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0017
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0018

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CauchyRiemannDerivativeEq
section
noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.SiegelWeilFormula

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def toC (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ) (hL : ∀ v, L (Complex.I • v) = Complex.I * L v) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ where
  toFun := L
  map_add' := L.map_add
  map_smul' c v := by
    have hv : c • v = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
      conv_lhs => rw [← Complex.re_add_im c]
      ring
    rw [hv, map_add L, L.map_smul, L.map_smul, hL, RingHom.id_apply, smul_eq_mul]
    simp only [Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  cont := L.cont

theorem cauchy_riemann_derivative_eq (A : M2 n) (Φ : M2 n → ℂ) (x : M2 n) (d1 d2 : ℂ)
    (h1 : HasDerivAt (fun t : ℝ => Φ (x * II.cE (Z1 A) t)) d1 0)
    (h2 : HasDerivAt (fun t : ℝ => Φ (x * II.cE (Z2 A) t)) d2 0) : rC A Φ x = d1 + Complex.I * d2 := by
  have key : ∀ E : M2 n, (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • E))) = fun t : ℝ => Φ (x * II.cE E t) := by
    intro E; funext t; simp only [II.cE, Complex.coe_smul]
  change deriv (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • Z1 A))) 0 +
    Complex.I * deriv (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • Z2 A))) 0 = _
  rw [key, key, h1.deriv, h2.deriv]

theorem crLem_of (hsec : LocSec) (hfib : Fib) (ha : CauchyRiemannFacts) : CRLem := by
  intro n m e φ Φ Ω hΩ hGΩ hΦ hΦφ hlaw hrC
  classical
  have hF0 : ∀ y : GR n, F0 m 0 e y ≠ 0 := by
    intro y
    rw [ha.1]
    unfold holomorphicScalarSection
    exact mul_ne_zero (zpow_ne_zero _ (det_ne_zero_of_inG y.2)) (zpow_ne_zero _ (AbsSt.detU1 n y).1)
  set H : Matrix (Fin n) (Fin n) ℂ → ℂ := fun Z =>
    if h : ∃ y : GR n, zOfE (mR y) = Z then φ h.choose / F0 m 0 e h.choose else 0 with hHdef
  have hH : ∀ y : GR n, φ y = F0 m 0 e y * H (zOfE (mR y)) := by
    intro y
    have hex : ∃ y' : GR n, zOfE (mR y') = zOfE (mR y) := ⟨y, rfl⟩
    simp only [hHdef, dif_pos hex]
    have hz : zOfE (mR hex.choose) = zOfE (mR y) := hex.choose_spec
    have hk := hfib n hex.choose y hz
    have hkK : (hex.choose⁻¹ * y) ∈ AbsSt.KR n := hk
    have e1 : y = hex.choose * (hex.choose⁻¹ * y) := by group
    have h1 : φ y = φ hex.choose * F0 m 0 e (hex.choose⁻¹ * y) := by
      conv_lhs => rw [e1]
      exact hlaw _ _ hk
    have h2 : F0 m 0 e y = F0 m 0 e hex.choose * F0 m 0 e (hex.choose⁻¹ * y) := by
      conv_lhs => rw [e1]
      exact ((AbsSt.mult n m 0 e).1 _ _ hkK).1
    rw [h1, h2]
    field_simp [hF0 hex.choose]
  refine ⟨fun Z => H (Matrix.of Z), ?_, fun y => ?_⟩
  swap
  · simp only [↓reduceIte]
    exact hH y
  intro Z0' hZ0
  set Z0 : Matrix (Fin n) (Fin n) ℂ := Matrix.of Z0' with hZ0def
  obtain ⟨s, hs, hsd⟩ := hsec n Z0 hZ0
  obtain ⟨hxG, hxd, hxz⟩ := hs.self_of_nhds
  set x0 := s Z0 with hx0
  set y0 := toGR x0 hxG with hy0
  have hu1 : (u1 x0).det ≠ 0 := (AbsSt.detU1 n y0).1
  obtain ⟨hzd, hFd, hlow, hsig, hW⟩ := ha.2 n x0 hxd hu1
  have hFx0 : holomorphicScalarSection m e x0 ≠ 0 := by
    have := hF0 y0
    rwa [ha.1] at this
  have heq : H =ᶠ[𝓝 Z0] fun Z => Φ (s Z) * (holomorphicScalarSection m e (s Z))⁻¹ := by
    filter_upwards [hs] with Z hZ
    obtain ⟨hG, -, hzZ⟩ := hZ
    have h1 := hH (toGR (s Z) hG)
    rw [mR_toGR, hzZ, ← hΦφ (toGR (s Z) hG), mR_toGR] at h1
    have h2 : F0 m 0 e (toGR (s Z) hG) = holomorphicScalarSection m e (s Z) := by rw [ha.1, mR_toGR]
    have h4 : holomorphicScalarSection m e (s Z) ≠ 0 := by rw [← h2]; exact hF0 _
    rw [← div_eq_mul_inv, eq_div_iff h4, mul_comm, ← h2, ← h1]
  have hΦd : DifferentiableAt ℝ Φ x0 :=
    (hΦ.contDiffAt (hΩ.mem_nhds (hGΩ hxG))).differentiableAt (by simp)
  have hsd' : DifferentiableAt ℝ s Z0 := hsd.differentiableAt one_ne_zero
  have hFr : DifferentiableAt ℝ (holomorphicScalarSection m e) x0 := (hFd m e).restrictScalars ℝ
  have hzr : DifferentiableAt ℝ zOfE x0 := hzd.restrictScalars ℝ
  have hR : DifferentiableAt ℝ (fun Z => Φ (s Z) * (holomorphicScalarSection m e (s Z))⁻¹) Z0 :=
    (hΦd.comp Z0 hsd').mul ((hFr.comp Z0 hsd').inv hFx0)
  have hHd : DifferentiableAt ℝ H Z0 := hR.congr_of_eventuallyEq heq
  set L := fderiv ℝ H Z0 with hLdef
  have hHd' : DifferentiableAt ℝ H (zOfE x0) := by rw [hxz]; exact hHd

  have key : ∀ Q : Matrix (Fin n) (Fin n) ℂ,
      L (Complex.I • (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)))) =
        Complex.I * L (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q))) := by
    intro Q
    set g : M2 n → ℂ := fun x => holomorphicScalarSection m e x * H (zOfE x) with hg
    have hcurve : ∀ E : M2 n, sig E = E → ∀ t : ℝ, Φ (x0 * II.cE E t) = g (x0 * II.cE E t) := by
      intro E hE t
      have hp : InG (x0 * II.cE E t) := inG_mul hxG (inG_cE hE t)
      have := hH (toGR _ hp)
      rw [mR_toGR, ha.1, mR_toGR] at this
      rw [← hΦφ (toGR _ hp), mR_toGR] at this
      exact this
    have hr : rC (lowQ Q) Φ x0 = 0 := hrC y0 Q
    have hder : ∀ E : M2 n, sig E = E → HasDerivAt (fun t : ℝ => Φ (x0 * II.cE E t))
        (fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * E) * H Z0 + holomorphicScalarSection m e x0 * L (fderiv ℂ zOfE x0 (x0 * E))) 0 := by
      intro E hE
      have hc : HasDerivAt (fun t : ℝ => x0 * II.cE E t) (x0 * E) 0 :=
        (II.mulL x0).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (II.cE_hasDerivAt0 E)
      have hc0 : x0 * II.cE E 0 = x0 := by rw [II.cE_zero, Matrix.mul_one]
      have hFc : HasDerivAt (fun t : ℝ => holomorphicScalarSection m e (x0 * II.cE E t)) (fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * E)) 0 := by
        have h : HasFDerivAt (holomorphicScalarSection m e) ((fderiv ℂ (holomorphicScalarSection m e) x0).restrictScalars ℝ) (x0 * II.cE E 0) := by
          rw [hc0]; exact (hFd m e).hasFDerivAt.restrictScalars ℝ
        exact h.comp_hasDerivAt (0 : ℝ) hc
      have hzc : HasDerivAt (fun t : ℝ => zOfE (x0 * II.cE E t)) (fderiv ℂ zOfE x0 (x0 * E)) 0 := by
        have h : HasFDerivAt zOfE ((fderiv ℂ zOfE x0).restrictScalars ℝ) (x0 * II.cE E 0) := by
          rw [hc0]; exact hzd.hasFDerivAt.restrictScalars ℝ
        exact h.comp_hasDerivAt (0 : ℝ) hc
      have hHc : HasDerivAt (fun t : ℝ => H (zOfE (x0 * II.cE E t))) (L (fderiv ℂ zOfE x0 (x0 * E))) 0 := by
        have h : HasFDerivAt H L (zOfE (x0 * II.cE E 0)) := by
          rw [hc0, hxz]; exact hHd.hasFDerivAt
        exact h.comp_hasDerivAt (0 : ℝ) hzc
      have hprod := hFc.mul hHc
      rw [hc0, hxz] at hprod
      refine hprod.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      exact hcurve E hE t
    rw [cauchy_riemann_derivative_eq (lowQ Q) Φ x0 _ _ (hder _ (conj_real_part_fixed _)) (hder _ (conj_imaginary_part_fixed _))] at hr
    have hsum : ∀ (D : M2 n →L[ℂ] Matrix (Fin n) (Fin n) ℂ), D (x0 * Z1 (lowQ Q)) + Complex.I • D (x0 * Z2 (lowQ Q)) =
        D (x0 * lowQ Q) := by
      intro D
      rw [← D.map_smul, ← map_add D, ← Matrix.mul_smul, ← Matrix.mul_add, real_add_imaginary_part]
    have hsum' : ∀ (D : M2 n →L[ℂ] ℂ), D (x0 * Z1 (lowQ Q)) + Complex.I * D (x0 * Z2 (lowQ Q)) =
        D (x0 * lowQ Q) := by
      intro D
      rw [← smul_eq_mul Complex.I (D _), ← D.map_smul, ← map_add D, ← Matrix.mul_smul, ← Matrix.mul_add, real_add_imaginary_part]
    have hsumF : fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * Z1 (lowQ Q)) + Complex.I * fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * Z2 (lowQ Q)) =
        0 := (hsum' _).trans ((hlow Q).2 m e)
    have hsumZ := hsum (fderiv ℂ zOfE x0)
    rw [(hlow Q).1] at hsumZ
    have hv1 : fderiv ℂ zOfE x0 (x0 * Z1 (lowQ Q)) = -(Complex.I • fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q))) :=
      eq_neg_of_add_eq_zero_left hsumZ
    rw [hv1, map_neg] at hr
    have hr2 : holomorphicScalarSection m e x0 * (-L (Complex.I • fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q))) +
        Complex.I * L (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)))) = 0 := by
      rw [← hr]
      linear_combination (-(H Z0)) * hsumF
    rcases mul_eq_zero.1 hr2 with h | h
    · exact absurd h hFx0
    · linear_combination -h

  have hsurj : ∀ v : Matrix (Fin n) (Fin n) ℂ, ∃ Q, fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)) = v := by
    intro v
    have hWu : IsUnit (WM x0).det := isUnit_iff_ne_zero.2 (hW hxG)
    have hUu : IsUnit (u1 x0).det := isUnit_iff_ne_zero.2 hu1
    refine ⟨((-(2 * Complex.I)) • ((WM x0)⁻¹ * v * u1 x0))ᴴ, ?_⟩
    rw [Z2, Matrix.mul_smul, map_smul, Matrix.mul_sub, map_sub, (hlow _).1, hsig, Matrix.conjTranspose_conjTranspose,
      zero_sub]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_neg, smul_smul]
    have : WM x0 * ((WM x0)⁻¹ * v * u1 x0) * (u1 x0)⁻¹ = v := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hWu, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hUu, Matrix.mul_one]
    rw [this]
    ext i j
    simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
    field_simp
  have hLC : ∀ v, L (Complex.I • v) = Complex.I * L v := by
    intro v
    obtain ⟨Q, hQ⟩ := hsurj v
    have := key Q
    rw [hQ] at this
    exact this
  have hC : HasFDerivAt H (toC L hLC) Z0 :=
    hasFDerivAt_of_restrictScalars ℝ hHd.hasFDerivAt (by ext; rfl)
  have hC' : DifferentiableAt ℂ H Z0 := hC.differentiableAt
  exact (hC'.comp Z0' (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv.differentiableAt).differentiableWithinAt

end PositivityTheory.Rg.Sw.HSt.CR
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolomorphicSectionLoweringInvariant
section
noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fderiv_line_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : M2 n → E} {x : M2 n}
    (hf : DifferentiableAt ℂ f x) (v : M2 n) (hc : ∀ τ : ℂ, f (x + τ • v) = f x) : fderiv ℂ f x v = 0 := by
  have hl : HasDerivAt (fun τ : ℂ => x + τ • v) v 0 :=
    (((hasDerivAt_id' (0:ℂ)).smul_const v).const_add x).congr_deriv (one_smul ℂ v)
  have h1 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℂ) hl (by simp)
  have h2 : HasDerivAt (f ∘ fun τ : ℂ => x + τ • v) 0 0 := by
    have e : (f ∘ fun τ : ℂ => x + τ • v) = fun _ => f x := funext fun τ => hc τ
    rw [e]
    exact hasDerivAt_const _ _
  exact h1.unique h2

theorem line_low (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) :
    x + τ • (x * lowQ Q) = x * mX 1 (τ • Q) 0 1 := by
  rw [mX_low, lowQ_smul, mul_add, mul_one, Matrix.mul_smul]

theorem zOfE_low (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) : zOfE (x * mX 1 Q 0 1) = zOfE x := by
  rw [zOfE_eq, zOfE_eq, first_cayley_block_mul_block, Nm_mX]; simp

theorem holomorphic_section_lowering_invariant (m : ℕ) (e : ℤ) (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) : holomorphicScalarSection m e (x * mX 1 Q 0 1) = holomorphicScalarSection m e x := by
  unfold holomorphicScalarSection
  simp only [Matrix.det_mul, det_mX_low, first_cayley_block_mul_block, mul_one, mul_zero, add_zero]

theorem fderiv_zOfE_low (x : M2 n) (h : (u1 x).det ≠ 0) (Q : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℂ zOfE x (x * lowQ Q) = 0 :=
  fderiv_line_zero (da_zOfE x h) _ fun τ => by rw [line_low, zOfE_low]

theorem fderiv_F0E_low (m : ℕ) (e : ℤ) (x : M2 n) (h0 : x.det ≠ 0) (h : (u1 x).det ≠ 0)
    (Q : Matrix (Fin n) (Fin n) ℂ) : fderiv ℂ (holomorphicScalarSection m e) x (x * lowQ Q) = 0 :=
  fderiv_line_zero (da_F0E m e x h0 h) _ fun τ => by rw [line_low, holomorphic_section_lowering_invariant]

theorem low_blocks (R : Matrix (Fin n) (Fin n) ℂ) :
    lowQ R = fromBlocks ((-1 / 2 : ℂ) • R) ((Complex.I / 2) • R) ((Complex.I / 2) • R) ((1 / 2 : ℂ) • R) := by
  rw [lowQ_eq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

def raiseR (S : Matrix (Fin n) (Fin n) ℂ) : M2 n := mX 1 0 S 1 - 1

private theorem Cm_mul_Cmi : Cm n * Cmi n = 1 := by
  unfold Cm Cmi
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem raise_eq (S : Matrix (Fin n) (Fin n) ℂ) : raiseR S = Cm n * fromBlocks 0 0 S 0 * Cmi n := by
  have hinv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_right_inv Cm_mul_Cmi
  have hb : (fromBlocks 1 0 S 1 : M2 n) = fromBlocks 0 0 S 0 + 1 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
    simp
  unfold raiseR mX
  rw [hinv, hb, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Cm_mul_Cmi, add_sub_cancel_right]

theorem raise_blocks (S : Matrix (Fin n) (Fin n) ℂ) :
    raiseR S = fromBlocks ((-1 / 2 : ℂ) • S) ((-Complex.I / 2) • S) ((-Complex.I / 2) • S) ((1 / 2 : ℂ) • S) := by
  rw [raise_eq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem sig_fromBlocks (A B C D : Matrix (Fin n) (Fin n) ℂ) :
    sig (fromBlocks A B C D) = fromBlocks (-Dᴴ) Bᴴ Cᴴ (-Aᴴ) := by
  rw [sig_eq]
  unfold JJ
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem sig_low (R : Matrix (Fin n) (Fin n) ℂ) : sig (lowQ R) = raiseR Rᴴ := by
  rw [low_blocks, raise_blocks, sig_fromBlocks]
  simp only [Matrix.conjTranspose_smul]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply] <;> ring_nf <;> simp [Complex.conj_I] <;> ring_nf

theorem raiseR_smul (c : ℂ) (S : Matrix (Fin n) (Fin n) ℂ) : raiseR (c • S) = c • raiseR S := by
  rw [raise_blocks, raise_blocks, Matrix.fromBlocks_smul]
  congr 1 <;> exact smul_comm _ _ _

theorem line_raise (x : M2 n) (S : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) :
    x + τ • (x * raiseR S) = x * mX 1 0 (τ • S) 1 := by
  have : mX 1 0 (τ • S) 1 = 1 + raiseR (τ • S) := by rw [raiseR]; abel
  rw [this, raiseR_smul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]

end PositivityTheory.Rg.Sw.HSt.CR
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IntegralTsumSupp
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

theorem ιK_apply (k : KR n) : ιK n k = mR (k : GR n) := rfl

theorem continuous_fzG (hS : SecFz) (w : ℂ) : Continuous fun Y : GR n => fz m e w (mR Y) := by
  have h1 : (fun Y : GR n => fz m e w (mR Y)) = fun Y => F0 m 0 e Y * ((hLoc Y : ℝ) : ℂ) ^ w :=
    funext fun Y => hS n m e w Y
  rw [h1]
  refine (Vac.continuous_weight_factor detU1 m 0 e).mul ?_
  refine Continuous.cpow (Complex.continuous_ofReal.comp (Vac.continuous_hLoc detU1)) continuous_const fun Y => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (Vac.hLoc_pos detU1 Y)

theorem integral_tsum_supp {X : Type} [MeasurableSpace X] {ν : Measure X} {ι' : Type} (F : ι' → X → ℂ) (u : ι' → ℝ)
    (hu : Summable u) (hu0 : ∀ q, 0 ≤ u q) (bd : X → ℝ) (hbd : Integrable bd ν)
    (hF : ∀ q x, ‖F q x‖ ≤ u q * bd x) (hFm : ∀ q, AEStronglyMeasurable (F q) ν) :
    Summable (fun q => ∫ x, F q x ∂ν) ∧ ∫ x, ∑' q, F q x ∂ν = ∑' q, ∫ x, F q x ∂ν := by
  have hFi : ∀ q, Integrable (F q) ν := fun q =>
    Integrable.mono' (hbd.const_mul (u q)) (hFm q) (ae_of_all _ (hF q))
  have hIn : ∀ q, ‖∫ x, F q x ∂ν‖ ≤ u q * ∫ x, bd x ∂ν := by
    intro q
    calc ‖∫ x, F q x ∂ν‖ ≤ ∫ x, u q * bd x ∂ν := norm_integral_le_of_norm_le (hbd.const_mul (u q)) (ae_of_all _ (hF q))
      _ = u q * ∫ x, bd x ∂ν := integral_const_mul _ _
  refine ⟨Summable.of_norm_bounded (hu.mul_right _) hIn, ?_⟩
  have hF0 : ∀ q, q ∉ Function.support u → ∀ x, F q x = 0 := by
    intro q hq x
    have h0 : u q = 0 := Function.notMem_support.mp hq
    have := hF q x
    rw [h0, zero_mul] at this
    exact norm_le_zero_iff.mp this
  have : Countable (Function.support u) := hu.countable_support.to_subtype
  have hL : ∀ x, ∑' q, F q x = ∑' s : Function.support u, F s x := by
    intro x
    refine (tsum_subtype_eq_of_support_subset (f := fun q => F q x) ?_).symm
    intro q hq
    by_contra h
    exact hq (hF0 q h x)
  have hN : ∀ q, ∫ x, ‖F q x‖ ∂ν ≤ u q * ∫ x, bd x ∂ν := by
    intro q
    calc ∫ x, ‖F q x‖ ∂ν ≤ ∫ x, u q * bd x ∂ν :=
          integral_mono (hFi q).norm (hbd.const_mul (u q)) (hF q)
      _ = u q * ∫ x, bd x ∂ν := integral_const_mul _ _
  have hsumn : Summable fun s : Function.support u => ∫ x, ‖F s x‖ ∂ν :=
    Summable.of_nonneg_of_le (fun s => integral_nonneg fun _ => norm_nonneg _) (fun s => hN s)
      ((hu.subtype _).mul_right _)
  simp_rw [hL]
  rw [← integral_tsum_of_summable_integral_norm (F := fun (s : Function.support u) x => F s x) (fun s => hFi s) hsumn]
  refine tsum_subtype_eq_of_support_subset (f := fun q => ∫ x, F q x ∂ν) ?_
  intro q hq
  by_contra h
  exact hq (by simp only [hF0 q h, integral_zero])

end PositivityTheory.Rg.Sw.HSt.FarP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ReConjMulLe
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.FL

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw.LVs.II (cE cE_hasDerivAt0 cE_add cE_zero cE_continuous mulL mulL_apply)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem fz_curve {X x : M2 n} (hX : IsLie X) (hx : InG x) (m : ℕ) (e : ℤ) (w : ℂ) (s : ℝ) :
    fz m e w (x * cE X s) = (x * cE X s).det ^ e * (u1 (x * cE X s)).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 (x * cE X s)).det) : ℝ) : ℂ) * (-w)) := by
  have hg : InG (x * cE X s) := inG_mul hx (inG_cE hX s)
  have hd := det_first_cayley_block_ne_zero hg
  have hmul : (u1 (x * cE X s)).det * (ub1 (x * cE X s)).det =
      ((Complex.normSq (u1 (x * cE X s)).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_adjoint hg, Matrix.det_conjTranspose]
    exact Complex.mul_conj _
  have hpos : (0 : ℝ) < Complex.normSq (u1 (x * cE X s)).det := Complex.normSq_pos.mpr hd
  unfold fz
  rw [hmul, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), Complex.ofReal_log hpos.le]

theorem fz_deriv {X x : M2 n} (hX : IsLie X) (hx : InG x) (m : ℕ) (e : ℤ) (w : ℂ) :
    ∃ R : ℂ, HasDerivAt (fun s : ℝ => fz m e w (x * cE X s)) R 0 ∧
      ‖R‖ ≤ ‖fz m e w x‖ * (|(e : ℝ)| * ‖rD X x‖ + ((m : ℝ) + 2 * ‖w‖) * ‖rA X x‖) := by
  have hd0 : det x ≠ 0 := (isUnit_det_of_InG hx).ne_zero
  have ha0 : (u1 x).det ≠ 0 := det_first_cayley_block_ne_zero hx
  have hfun : (fun s : ℝ => fz m e w (x * cE X s)) = fun s : ℝ =>
      (x * cE X s).det ^ e * (u1 (x * cE X s)).det ^ (-(m : ℤ)) *
        Complex.exp (((Real.log (Complex.normSq (u1 (x * cE X s)).det) : ℝ) : ℂ) * (-w)) :=
    funext fun s => fz_curve hX hx m e w s
  have hf0 : fz m e w x = (det x) ^ e * (u1 x).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 x).det) : ℝ) : ℂ) * (-w)) := by
    have h := fz_curve hX hx m e w 0
    rw [cE_zero, mul_one] at h
    exact h
  have hD : HasDerivAt (fun s : ℝ => det (x * cE X s))
      ((fderiv ℂ (fun y : M2 n => det y) x) (x * X)) 0 :=
    curve_deriv (fun y : M2 n => det y) cd_det X x
  have hA : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)) 0 :=
    curve_deriv (fun y : M2 n => (u1 y).det) cd_detu1 X x
  have hD0 : det (x * cE X 0) = det x := by rw [cE_zero, mul_one]
  have hA0 : (u1 (x * cE X 0)).det = (u1 x).det := by rw [cE_zero, mul_one]
  have hzD : HasDerivAt (fun z : ℂ => z ^ e) (↑e * det x ^ (e - 1)) (det (x * cE X 0)) := by
    rw [hD0]
    exact hasDerivAt_zpow e (det x) (Or.inl hd0)
  have hzA : HasDerivAt (fun z : ℂ => z ^ (-(m : ℤ)))
      (↑(-(m : ℤ)) * (u1 x).det ^ (-(m : ℤ) - 1)) ((u1 (x * cE X 0)).det) := by
    rw [hA0]
    exact hasDerivAt_zpow _ _ (Or.inl ha0)
  have hDz := hzD.comp (0 : ℝ) hD
  have hAz := hzA.comp (0 : ℝ) hA
  have hre : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det.re)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)).re 0 := by
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    exact h2
  have him : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det.im)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)).im 0 := by
    have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    exact h2
  have hN := ((hre.mul hre).add (him.mul him)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => Complex.normSq_apply (u1 (x * cE X s)).det)
  have hNne : Complex.normSq (u1 (x * cE X 0)).det ≠ 0 := by
    rw [hA0]
    exact (Complex.normSq_pos.mpr ha0).ne'
  have hL := hN.log hNne
  have hE := (hL.ofReal_comp.mul_const (-w)).cexp
  have hfin := (hDz.mul hAz).mul hE
  rw [hfun]
  refine ⟨_, hfin, ?_⟩
  simp only [hA0, hD0, Function.comp_apply]
  have hd' : (fderiv ℂ (fun y : M2 n => det y) x) (x * X) = rD X x * det x := by
    unfold rD
    field_simp
  have ha' : (fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X) = rA X x * (u1 x).det := by
    unfold rA
    field_simp
  have bound : ‖(det x ^ e * (u1 x).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 x).det) : ℝ) : ℂ) * (-w))) *
      ((e : ℂ) * rD X x + (-(m : ℂ)) * rA X x + ((2 * (rA X x).re : ℝ) : ℂ) * (-w))‖ ≤
      ‖fz m e w x‖ * (|(e : ℝ)| * ‖rD X x‖ + ((m : ℝ) + 2 * ‖w‖) * ‖rA X x‖) := by
    rw [norm_mul, hf0]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    refine norm_add₃_le.trans ?_
    have h1 : |(rA X x).re| ≤ ‖rA X x‖ := Complex.abs_re_le_norm _
    have h2 : 0 ≤ ‖w‖ := norm_nonneg _
    simp only [norm_mul, norm_neg, Complex.norm_intCast, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_two]
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  convert bound using 2
  rw [hd', ha']
  have hq : ((rA X x * (u1 x).det).re * (u1 x).det.re + (u1 x).det.re * (rA X x * (u1 x).det).re +
      ((rA X x * (u1 x).det).im * (u1 x).det.im + (u1 x).det.im * (rA X x * (u1 x).det).im)) /
      Complex.normSq (u1 x).det = 2 * (rA X x).re := by
    have hn : Complex.normSq (u1 x).det ≠ 0 := (Complex.normSq_pos.mpr ha0).ne'
    rw [div_eq_iff hn, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im]
    ring
  rw [hq]
  simp only [Pi.mul_apply, Function.comp_apply, cE_zero, mul_one]
  rw [zpow_sub_one₀ hd0, zpow_sub_one₀ ha0]
  push_cast
  field_simp

end PositivityTheory.Rg.Sw.HSt.FL
end
end

