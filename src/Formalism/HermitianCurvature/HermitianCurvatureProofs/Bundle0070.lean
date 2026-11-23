module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactlySupportedBanachModel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0026
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeakToStrongSmoothnessReal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCellsOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0021

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddScalBound
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def regE (D : B.RealPlaceData k r Wp Wq) (ε : ℝ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ ε ≤ Gf k r D.z D.z' g}

theorem regE_sub (D : B.RealPlaceData k r Wp Wq) (ε : ℝ) : regE D ε ⊆ B.GV k r := fun _ hg => hg.1

theorem scal_bound_of_ubl (D : B.RealPlaceData k r Wp Wq) (φ : B.Mat k r → ℂ) (e γ : ℕ) (Bg : ℝ)
    (hBg : (e : ℝ) + γ ≤ Bg) (ε : ℝ)
    (h0 : ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖φ g‖ ≤ C0) (hU : ∀ n : ℕ, UBL φ (regE D ε) n e γ) (m : ℕ) :
    ∃ C : ℝ, ∀ u w : List (B.Mat k r),
      (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g → ‖B.dLR u w φ g‖ ≤ C * B.gN g ^ (Bg * m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    obtain ⟨C0, hC0⟩ := h0
    refine ⟨C0, fun u w _ _ hl g hg hgε => ?_⟩
    have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu hw
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    exact hC0 g ⟨hg, hgε⟩
  · obtain ⟨⟨C, hC0, hUB⟩, -⟩ := hU m
    refine ⟨C, fun u w hu hw hl g hg hgε => ?_⟩
    have hA : admitted m (wL u ++ wR w) := ⟨u, w, hu, hw, hl, rfl⟩
    have hb := hUB _ hA g ⟨hg, hgε⟩
    rw [dLR_eq]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    have h1 : 1 ≤ B.gN g := gN_ge_one hg
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le h1
    rw [len_LR]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hl' : ((u.length + w.length : ℕ) : ℝ) ≤ m := by exact_mod_cast hl
    have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have hγ : (0 : ℝ) ≤ γ := Nat.cast_nonneg _
    push_cast at hl' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hl' hγ, mul_le_mul_of_nonneg_left hm1 he,
      mul_le_mul_of_nonneg_right hBg (by linarith : (0 : ℝ) ≤ m)]

theorem dlast_pos (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) {g : B.Mat k r} (hg : ε ≤ Gf k r D.z D.z' g) :
    ε ≤ Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1))) :=
  Formalism.FourierDecayAlt.P.gram_function_last_minor k r D.z D.z' D.T_pos.le D.T'_pos.le g ε hg

theorem dlast_ne (D : B.RealPlaceData k r Wp Wq) {g : B.Mat k r} (hg : g ∈ B.GPos D) :
    Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0 := by
  intro h
  have := dlast_pos D hg.2 (le_refl _)
  rw [h, map_zero] at this
  linarith [hg.2]

theorem open_dlast (z z' : Fin (2 * r + k + 1) → ℂ) :
    IsOpen {g : B.Mat k r | Dmin k r z z' g (Fin.last (r + 1)) ≠ 0} :=
  isOpen_ne_fun (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' _).continuous continuous_const

theorem ckOn_phiR (D : B.RealPlaceData k r Wp Wq) : B.CkOn ⊤ (B.GPos D) (phiR k r D.z D.z') := by
  intro g₀ hg₀
  refine ⟨{g : B.Mat k r | Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0}, phiR k r D.z D.z', open_dlast D.z D.z',
    dlast_ne D hg₀, ?_, fun _ _ _ => rfl⟩
  have h0 := Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin (k := k) (r := r) D.z D.z' ⟨r, by omega⟩
  have h1 := Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin (k := k) (r := r) D.z D.z' (Fin.last (r + 1))
  refine (h0.contDiffOn.mul (h1.contDiffOn.inv (fun x hx => hx))).congr (fun x _ => ?_)
  simp [phiR, div_eq_mul_inv]

theorem ckOn_phiD (D : B.RealPlaceData k r Wp Wq) : B.CkOn ⊤ (B.GPos D) (phiD k r D.z D.z') := by
  intro g₀ hg₀
  refine ⟨{g : B.Mat k r | Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0}, phiD k r D.z D.z', open_dlast D.z D.z',
    dlast_ne D hg₀, ?_, fun _ _ _ => rfl⟩
  have h1 := Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin (k := k) (r := r) D.z D.z' (Fin.last (r + 1))
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => (starRingEnd ℂ) (Dmin k r D.z D.z' g (Fin.last (r + 1)))) :=
    Complex.conjCLE.contDiff.comp h1
  refine (h1.contDiffOn.mul (h2.contDiffOn.inv (fun x hx => by simpa using hx))).congr (fun x _ => ?_)
  simp [phiD, div_eq_mul_inv]

theorem phiR_le (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) :
    ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖phiR k r D.z D.z' g‖ ≤ C0 := by
  set T := Tz k r D.z * Tz k r D.z' with hT
  have hT0 : 0 < T := mul_pos D.T_pos D.T'_pos
  refine ⟨1 + 1 / T, fun g hg => ?_⟩
  have hG := hg.2
  have h1 := dlast_pos D hε hG
  have hpos : 0 < Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1))) := lt_of_lt_of_le hε h1
  unfold Gf at hG
  set a := Complex.normSq (Dmin k r D.z D.z' g ⟨r, by omega⟩)
  set b := Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1)))
  have hsq : ‖phiR k r D.z D.z' g‖ ^ 2 = a / b := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [phiR, Complex.normSq_div]
    rfl
  have hle : a / b ≤ 1 / T := by
    rw [div_le_div_iff₀ hpos hT0]
    nlinarith
  have hx := norm_nonneg (phiR k r D.z D.z' g)
  nlinarith [sq_nonneg (‖phiR k r D.z D.z' g‖ - 1)]

theorem phiD_le (D : B.RealPlaceData k r Wp Wq) (ε : ℝ) :
    ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖phiD k r D.z D.z' g‖ ≤ C0 := by
  refine ⟨1, fun g _ => ?_⟩
  simp only [phiD, norm_div, Complex.norm_conj]
  exact div_self_le_one _

theorem ubl_phiR (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    UBL (phiR k r D.z D.z') (regE D ε) n r (r + 1) := by
  have hP0 : U.IsPolyDeg r (fun g : B.Mat k r => Dmin k r D.z D.z' g ⟨r, by omega⟩) :=
    Formalism.FourierDecayAlt.P.minor_polynomial_property k r D.z D.z' ⟨r, by omega⟩
  have hP1 : U.IsPolyDeg (r + 1) (fun g : B.Mat k r => Dmin k r D.z D.z' g (Fin.last (r + 1))) := by
    have := Formalism.FourierDecayAlt.P.minor_polynomial_property k r D.z D.z' (Fin.last (r + 1))
    simpa using this
  have ha := ubl_poly hP0 (regE D ε) (regE_sub D ε) n (r + 1)
  have hb := ubl_invpow hP1 (regE_sub D ε) hε (fun g hg => dlast_pos D hε hg.2) 1 n
  have hm := ubl_mul (regE_sub D ε) ha hb
  have e : phiR k r D.z D.z' = fun g => Dmin k r D.z D.z' g ⟨r, by omega⟩ *
      (Dmin k r D.z D.z' g (Fin.last (r + 1)))⁻¹ ^ 1 := by
    funext g; simp [phiR, div_eq_mul_inv]
  rw [e]
  simpa using hm

theorem ubl_phiD (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    UBL (phiD k r D.z D.z') (regE D ε) n (r + 1) (r + 1) := by
  have hP1 : U.IsPolyDeg (r + 1) (fun g : B.Mat k r => Dmin k r D.z D.z' g (Fin.last (r + 1))) := by
    have := Formalism.FourierDecayAlt.P.minor_polynomial_property k r D.z D.z' (Fin.last (r + 1))
    simpa using this
  have hP2 := Formalism.FourierDecayAlt.P.CutMP.jdh_pd_star hP1
  have ha := ubl_poly hP1 (regE D ε) (regE_sub D ε) n (r + 1)
  have hb := ubl_invpow hP2 (regE_sub D ε) hε
    (fun g hg => by simpa [Complex.star_def] using dlast_pos D hε hg.2) 1 n
  have hm := ubl_mul (regE_sub D ε) ha hb
  have e : phiD k r D.z D.z' = fun g => Dmin k r D.z D.z' g (Fin.last (r + 1)) *
      (star (Dmin k r D.z D.z' g (Fin.last (r + 1))))⁻¹ ^ 1 := by
    funext g; simp [phiD, div_eq_mul_inv]
  rw [e]
  simpa using hm

end

theorem scalar_transfer_bound_holds : JAScalBound := by
  refine ⟨2, by norm_num, ?_⟩
  intro k r Wp Wq _ _ _ _ D Bg hBg
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  refine ⟨⟨ckOn_phiR D, fun ε hε m => ?_⟩, ⟨ckOn_phiD D, fun ε hε m => ?_⟩⟩
  · exact scal_bound_of_ubl D _ r (r + 1) Bg (by push_cast; linarith) ε (phiR_le D hε)
      (fun n => ubl_phiR D hε n) m
  · exact scal_bound_of_ubl D _ (r + 1) (r + 1) Bg (by push_cast; linarith) ε (phiD_le D ε)
      (fun n => ubl_phiD D hε n) m

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableEquivOps
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.QuantumDeterminants.WeylGroupFacts

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section aux

variable {k r : ℕ}

def pOf (a b c d : B.Mat k r) : B.SS k r :=
  ((Matrix.of.symm a, Matrix.of.symm b), (Matrix.of.symm c, Matrix.of.symm d))

theorem level_zero_iff (g : B.Mat k r) : g ∈ Q.Glev k r 0 ↔ g ∈ B.GV k r := by
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem mat_inv_one : (1 : B.Mat k r)⁻¹ = 1 := by
  simp

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem rho_pOf (D : B.RealPlaceData k r Wp Wq) (a b c d : B.Mat k r) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.rho D (pOf a b c d) F = fun x => (D.π a).comp ((F (a⁻¹ * b⁻¹ * x * d * c)).comp (D.π' c⁻¹)) := by
  funext x
  simp only [B.rho, B.sgs, pOf, Equiv.apply_symm_apply]

end aux

theorem equivariant_operators_holds : EquivOps := by
  intro hE k r Wp Wq _ _ _ _ _ D O P hDom hloc hsmul hsm hcomm J hJ
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  have hext : ∀ g₀ ∈ B.GV k r, g₀ ∈ O → ∃ (f : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set (B.Mat k r)),
      B.CkOn ⊤ (B.GV k r) f ∧ HasCompactSupport f ∧ tsupport f ⊆ O ∧ IsOpen U ∧ g₀ ∈ U ∧
        ∀ x ∈ U, x ∈ B.GV k r → f x = J x :=
    fun g₀ hg hO => hE k r (Wq →L[ℂ] Wp) O J hDom.1 hS g₀ hg hO
  have one_N : (1 : B.Mat k r) ∈ Q.Nlev k r 0 := ⟨mem_n_one, (level_zero_iff _).2 uh_one⟩
  have one_S : ∀ z, (1 : B.Mat k r) ∈ Q.Slev k r z 0 :=
    fun z => ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, one_N, by simp⟩
  have hπ1 : D.π 1 = 1 := D.π_rep.1
  have hπ'1 : D.π' 1 = 1 := D.π'_rep.1
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro g₀ hg₀
    have hgG := (level_zero_iff g₀).1 hg₀.1
    obtain ⟨f, U, hf, _, hfO, hUo, hgU, hfJ⟩ := hext g₀ hgG hg₀.2
    obtain ⟨U', F, hU', hgU', hF, hFe⟩ := hsm f hf hfO g₀ hg₀
    refine ⟨U ∩ U', F, hUo.inter hU', ⟨hgU, hgU'⟩, hF.mono Set.inter_subset_right, ?_⟩
    intro x hx hxG
    rw [← hFe x hx.2 hxG]
    exact hloc U J f hUo (fun y hy hyG => (hfJ y hy hyG).symm) x hx.1 ((level_zero_iff x).1 hxG)
  ·
    intro g hg n hn
    have hgG := (level_zero_iff g).1 hg.1
    have hnN : n ∈ Formalism.QuantumDeterminants.Nset k r := hn.1
    have hnG : n ∈ B.GV k r := hnN.1
    have hng : n * g ∈ O := by
      have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z, n, hn, by simp⟩ 1 (one_S D.z')
      simpa using this
    have hngG : n * g ∈ B.GV k r := uh_mul hnG hgG
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hngU1, hf1J⟩ := hext (n * g) hngG hng
    have hp : D.inSS (pOf 1 n⁻¹ 1 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z
      · exact mem_n_inv hnN
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'
      · exact mem_n_one
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf 1 n⁻¹ 1 1) F = fun x => F (n * x) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [Matrix.nonsing_inv_nonsing_inv n (isUnit_of_uh hnG), mat_inv_one, hπ1, hπ'1]
      ext v
      simp
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    beta_reduce at hc
    have e1 : P f1 (n * g) = P J (n * g) := hloc U1 f1 J hU1 hf1J (n * g) hngU1 hngG
    have hV : IsOpen ((fun x : B.Mat k r => n * x) ⁻¹' U1 ∩ O) :=
      (hU1.preimage (continuous_const.matrix_mul continuous_id)).inter hDom.1
    have e2 : P (fun x => f1 (n * x)) g = P (Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd n • J) g := by
      refine hloc _ _ _ hV ?_ g ⟨hngU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J (n * x) hx.1 (uh_mul hnG hxG), Pi.smul_apply]
      exact hL x ⟨(level_zero_iff x).2 hxG, hx.2⟩ n hn
    rw [← e1, ← hc, e2, hsmul _ J g hgG]
  ·
    intro g hg n hn
    have hgG := (level_zero_iff g).1 hg.1
    have hnN : n ∈ Formalism.QuantumDeterminants.Nset k r := hn.1
    have hnG : n ∈ B.GV k r := hnN.1
    have hgn : g * n ∈ O := by
      have := hDom.2 g hg 1 (one_S D.z) n ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z', n, hn, by simp⟩
      simpa using this
    have hgnG : g * n ∈ B.GV k r := uh_mul hgG hnG
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hgnU1, hf1J⟩ := hext (g * n) hgnG hgn
    have hp : D.inSS (pOf 1 1 1 n) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z
      · exact mem_n_one
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'
      · exact hnN
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf 1 1 1 n) F = fun x => F (x * n) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [mat_inv_one, hπ1, hπ'1]
      ext v
      simp
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    beta_reduce at hc
    have e1 : P f1 (g * n) = P J (g * n) := hloc U1 f1 J hU1 hf1J (g * n) hgnU1 hgnG
    have hV : IsOpen ((fun x : B.Mat k r => x * n) ⁻¹' U1 ∩ O) :=
      (hU1.preimage (continuous_id.matrix_mul continuous_const)).inter hDom.1
    have e2 : P (fun x => f1 (x * n)) g = P (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd n • J) g := by
      refine hloc _ _ _ hV ?_ g ⟨hgnU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J (x * n) hx.1 (uh_mul hxG hnG), Pi.smul_apply]
      exact hR x ⟨(level_zero_iff x).2 hxG, hx.2⟩ n hn
    rw [← e1, ← hc, e2, hsmul _ J g hgG]
  ·
    intro g hg h hh h' hh'
    have hgG := (level_zero_iff g).1 hg.1
    have hhG : h ∈ B.GV k r := hh.1
    have hh'G : h' ∈ B.GV k r := hh'.1
    have hu := isUnit_of_uh hhG
    have hu' := isUnit_of_uh hh'G
    have hhg : h * g * h' ∈ O := by
      have := hDom.2 g hg h ⟨h, hh, 1, one_N, by simp⟩ h' ⟨h', hh', 1, one_N, by simp⟩
      simpa using this
    have hhgG : h * g * h' ∈ B.GV k r := uh_mul (uh_mul hhG hgG) hh'G
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hhgU1, hf1J⟩ := hext (h * g * h') hhgG hhg
    have hp : D.inSS (pOf h⁻¹ 1 h' 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact uw_inv hh
      · exact mem_n_one
      · exact hh'
      · exact mem_n_one
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf h⁻¹ 1 h' 1) F =
        fun x => (D.π h⁻¹).comp ((F (h * x * h')).comp (D.π' h'⁻¹)) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [Matrix.nonsing_inv_nonsing_inv h hu, mat_inv_one]
      simp [Matrix.mul_assoc]

    have eL : (D.π h⁻¹).comp (D.π h) = 1 := by
      rw [← D.π_rep.2 _ (uw_inv hh) _ hh, Matrix.nonsing_inv_mul h hu, hπ1]
    have eL' : (D.π h).comp (D.π h⁻¹) = 1 := by
      rw [← D.π_rep.2 _ hh _ (uw_inv hh), Matrix.mul_nonsing_inv h hu, hπ1]
    have eR : (D.π' h').comp (D.π' h'⁻¹) = 1 := by
      rw [← D.π'_rep.2 _ hh' _ (uw_inv hh'), Matrix.mul_nonsing_inv h' hu', hπ'1]
    have eR' : (D.π' h'⁻¹).comp (D.π' h') = 1 := by
      rw [← D.π'_rep.2 _ (uw_inv hh') _ hh', Matrix.nonsing_inv_mul h' hu', hπ'1]
    have eLv : ∀ w, D.π h⁻¹ (D.π h w) = w := fun w => by simpa using congrArg (fun L => L w) eL
    have eL'v : ∀ w, D.π h (D.π h⁻¹ w) = w := fun w => by simpa using congrArg (fun L => L w) eL'
    have eRv : ∀ w, D.π' h' (D.π' h'⁻¹ w) = w := fun w => by simpa using congrArg (fun L => L w) eR
    have eR'v : ∀ w, D.π' h'⁻¹ (D.π' h' w) = w := fun w => by simpa using congrArg (fun L => L w) eR'
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    have e1 : P f1 (h * g * h') = P J (h * g * h') := hloc U1 f1 J hU1 hf1J _ hhgU1 hhgG
    have hV : IsOpen ((fun x : B.Mat k r => h * x * h') ⁻¹' U1 ∩ O) :=
      (hU1.preimage ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)).inter hDom.1
    have e2 : P (fun x => (D.π h⁻¹).comp ((f1 (h * x * h')).comp (D.π' h'⁻¹))) g = P J g := by
      refine hloc _ _ _ hV ?_ g ⟨hhgU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J _ hx.1 (uh_mul (uh_mul hhG hxG) hh'G), hU x ⟨(level_zero_iff x).2 hxG, hx.2⟩ h hh h' hh']
      ext v
      simp [eLv, eRv]
    rw [e2] at hc
    beta_reduce at hc
    rw [e1] at hc

    rw [hc]
    ext v
    simp [eL'v, eR'v]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRho
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho

noncomputable section

def nrmW (k r : ℕ) (z a : Fin (2 * r + k + 1) → ℂ) : ℝ :=
  (herm (Hpk k r) (SSn.prWv k r z a) (SSn.prWv k r z a)).re

section spec

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

def PRhoSpec (P : M.Par) (z : Fin (2 * P.r + P.k + 1) → ℂ) (π : B.Mat P.k P.r → (Wp →L[ℂ] Wp))
    (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp)) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Pr ρ) {a | 1 / 4 < nrmW P.k P.r z a}) ∧
  (∀ h ∈ UWset P.k P.r z, ∀ ρ a, Pr ρ (h *ᵥ a) = (π h).comp ((Pr ρ a).comp (π h⁻¹))) ∧
  ∀ a, 0 < nrmW P.k P.r z a →
    (∀ ρ (c : ℂ), c ≠ 0 → Pr ρ (c • a) = Pr ρ a) ∧
    (∀ ρ x y, inner ℂ (Pr ρ a x) y = inner ℂ x (Pr ρ a y)) ∧
    (∀ ρ ρ', (Pr ρ a).comp (Pr ρ' a) = if ρ = ρ' then Pr ρ a else 0) ∧
    ∀ ρ (x : Wp), Pr ρ a x = x ↔
      ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [z, SSn.prWv P.k P.r z a] Fr →
        ∀ w : ℂ, Q.capRep P.k P.r π Fr w x = M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • x

end spec

def PRhoExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∃ Pr, PRhoSpec P Bs.z Bs.π Pr

section ctx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def Hyp (Cc : ℝ) (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  BuiltOW Cc S T f χ ν' m₀ top A₀ ∧ IsFrame S T v e ∧ IsGauge S T v e ∧ IsGaugeQQ S T v e

end ctx

def GaugeLines : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    Hyp Cc S T f χ ν' m₀ top A₀ v e → 2 ≤ S.G.k →
    ∀ ζ : ℂ, (D.parOf S v).TT < Complex.normSq ζ → ∀ (ρ : M.Ty (D.parOf S v))
      (Fr : Fin (S.G.k - 1) → Fin (2 * S.G.r + S.G.k + 1) → ℂ),
      Q.IsFrameOf S.G.k S.G.r [(T v).base.z, SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ] Fr →
      ∀ (w : ℂ) (x : Wq (S.pl v)),
        Q.capRep S.G.k S.G.r (T v).base.π Fr w (e ρ ζ x) =
          M.xC (D.parOf S v) ρ (w - ((S.G.k : ℂ) - 2) / 2) • e ρ ζ x

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace
section
namespace Formalism.FourierDecayAlt.P

theorem coordinate_sizes_in_norm : Formalism.FourierDecayAlt.U.SliceCoordinateSizes :=
  coordinate_sizes_of_parts slice_membership block3_apply_embedding aux_statement_17 hat_z_on_slice level_determinant_z

theorem norm_decay_in_coordinates : Formalism.FourierDecayAlt.U.CoordinateDecay :=
  norm_decay_of_coordinate_sizes coordinate_sizes_in_norm

theorem phi_pointwise_bound : Formalism.FourierDecayAlt.U.PointwiseIntegralBound :=
  phi_bound_of_parts slice_membership derivative_cost_bound norm_decay_in_coordinates weight_integrability

theorem theorem_u : Formalism.FourierDecayAlt.U.TheoremU :=
  theorem_u_of_parts phi_pointwise_bound phi_support_determinant weak_to_strong_smoothness

theorem phi_support_level_function : Formalism.FourierDecayAlt.U.PhiSuppG :=
  phi_support_level_of_parts level_function_slice level_determinant_z hat_z_on_slice

theorem corollary_u2_germ_hypothesis : Formalism.FourierDecayAlt.U.GermExpansionHypothesis :=
  corollary_u2_of_parts theorem_u corollary_u1_truncated_alt star_projection budget_second_corollary
    thresholds_second_corollary phi_support_level_function

theorem germ_expansion_applies : Formalism.FourierDecayAlt.U.UseGerm :=
  germ_expansion_of_parts germ_rate det_weyl_matrix corollary_u2_germ_hypothesis derivative_bound_of_decay
    power_matching scale_matching

theorem germ_expansion_top_level : Formalism.FourierDecayAlt.U.UseGermTop :=
  germ_top_level_of_parts germ_rate det_weyl_matrix top_cells derivative_bound_of_decay

end Formalism.FourierDecayAlt.P
end

