module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0078
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0087
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0160
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0159
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0070
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0161
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0103
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothHermitianRankTwo
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0153
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GeometryEquivarianceEmbedding
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAtGq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomUBL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0152
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0090

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLocal
section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gTSSLocal_of_radT : GTCLRadT → GTSSLocal := by
  intro hT Wp Wq _ _ _ _ _ _ P Bs X d hG e he _
  obtain ⟨hP, hk, hC, -⟩ := id hG
  have hX : ∀ (Y : ℂ) (a b : Fin 2), SliceLoc P Bs (X.t Y a b) := fun Y a b =>
    second_shift_slice_derivative Wp Wq P Bs hP _ (hT Wp Wq P Bs hP hk hC X Y a b)
  exact second_shift_matrix_form Wp Wq P Bs X d hG e he
    (second_shift_slice_operator Wp Wq P Bs X d hG hX)

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGraded
section
open Formalism.FourierDecayAlt MeasureTheory NumberField

open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.Gr

noncomputable section

section cls

variable {r : ℕ} {TT : ℝ}

def smM (m : ℕ∞) : WithTop ℕ∞ := ((m : ℕ∞) : WithTop ℕ∞)

end cls

section jets

variable {r : ℕ} {TT : ℝ}


end jets

section ord

variable {r : ℕ} {TT : ℝ}

end ord

section En

variable (P : M.Par) (m : ℕ∞)

end En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def FFlM {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (m : ℕ∞) (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (i : Fin (r + 1)) (Dm : Set (Q.Mx k r)) : Set (Q.Mx k r → (Wq →L[ℂ] Wp)) :=
  {J | (∀ g₀ ∈ Q.Glev k r i ∩ Dm, ∃ (U : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)),
      IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ (smM m) F U ∧ ∀ g ∈ U, g ∈ Q.Glev k r i → J g = F g) ∧
    Q.LeftEq k r z i Dm J ∧ Q.RightEq k r z' i Dm J ∧
    ∀ g ∈ Q.Glev k r i ∩ Dm, ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset k r z',
      J (h * g * h') = (π h).comp ((J g).comp (π' h'))}

section place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

end place

end

end Formalism.FourierDecayAlt.P.CutMP.Gr
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddScalProof
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.CutMP.JA.BStar Formalism.FourierDecayAlt.P.MAx2.Adj Formalism.FourierDecayAlt.P.MAx1.An Formalism.QuantumDeterminants
open scoped ComplexConjugate Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section deriv

variable {k r : ℕ} {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F'] [NormedSpace ℂ F']

theorem ldV_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) (X : B.Mat k r) (f : B.Mat k r → F) :
    B.LdV X (fun g => L (f g)) = fun g => L (B.LdV X f g) := by
  funext g
  unfold B.LdV
  exact P.JCTx6.Pos.deriv_cle_comp L L' hL (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0

theorem rdV_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) (X : B.Mat k r) (f : B.Mat k r → F) :
    Formalism.REAL.RdV X (fun g => L (f g)) = fun g => L (Formalism.REAL.RdV X f g) := by
  funext g
  unfold Formalism.REAL.RdV
  exact P.JCTx6.Pos.deriv_cle_comp L L' hL (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

theorem rw_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) :
    ∀ (v : List (B.Mat k r)) (f : B.Mat k r → F), B.Rw v (fun g => L (f g)) = fun g => L (B.Rw v f g)
  | [], _ => rfl
  | X :: v, f => by
    show Formalism.REAL.RdV X (B.Rw v fun g => L (f g)) = fun g => L (Formalism.REAL.RdV X (B.Rw v f) g)
    rw [rw_rl L L' hL v f, rdV_rl L L' hL X]

theorem dLR_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) (w : List (B.Mat k r)) :
    ∀ (u : List (B.Mat k r)) (f : B.Mat k r → F), B.dLR u w (fun g => L (f g)) = fun g => L (B.dLR u w f g)
  | [], f => rw_rl L L' hL w f
  | X :: u, f => by
    show B.LdV X (B.dLR u w fun g => L (f g)) = fun g => L (B.LdV X (B.dLR u w f) g)
    rw [dLR_rl L L' hL w u f, ldV_rl L L' hL X]

theorem dLR_conj (u w : List (B.Mat k r)) (f : B.Mat k r → ℂ) :
    B.dLR u w (fun g => conj (f g)) = fun g => conj (B.dLR u w f g) :=
  dLR_rl (Complex.conjCLE : ℂ →L[ℝ] ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) (fun y => by simp) w u f

theorem dLR_smulc (A : F) (u w : List (B.Mat k r)) (f : B.Mat k r → ℂ) :
    B.dLR u w (fun g => f g • A) = fun g => B.dLR u w f g • A := by
  by_cases hA : A = 0
  · subst hA; simp only [smul_zero]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_zero u w
  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ A (norm_ne_zero_iff.2 hA)
  have hn : ((‖A‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hA
  let L : ℂ →L[ℝ] F := ((ContinuousLinearMap.id ℂ ℂ).smulRight A).restrictScalars ℝ
  let L' : F →L[ℝ] ℂ := ((((‖A‖ : ℝ) : ℂ))⁻¹ • ℓ).restrictScalars ℝ
  have hL : ∀ y, L' (L y) = y := fun y => by
    simp only [L, L', ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, map_smul, hℓ, smul_eq_mul]
    field_simp
    norm_cast
  exact dLR_rl L L' hL w u f

end deriv

theorem scalar_conjugation_transfer : JAScalConj := by
  intro k r Wp Wq _ _ _ _ D Bg φ hφ
  refine ⟨fun g₀ hg₀ => ?_, fun ε hε m => ?_⟩
  · obtain ⟨U, φ', hU, hg, hφ', he⟩ := hφ.1 g₀ hg₀
    refine ⟨U, fun g => conj (φ' g), hU, hg, ?_, fun g hgU hgG => by simp only; rw [he g hgU hgG]⟩
    exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hφ'
  · obtain ⟨C, hC⟩ := hφ.2 ε hε m
    refine ⟨C, fun u w hu hw hl g hg hG => ?_⟩
    rw [dLR_conj, Complex.norm_conj]
    exact hC u w hu hw hl g hg hG

section real

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem scal_real (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')
    (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hFr : IsFrame S T v e) (Cb : ℝ)
    (φ : B.Mat S.G.k S.G.r → ℂ) (hφ : ScalOK (T v).base (Cb * ((S.G.r : ℝ) + 1)) φ)
    (hinv : ∀ p, (T v).base.inSS p → ∀ g, φ (B.sgs p g) = φ g)
    (β : (DQ (D.parOf S v)).R)
    (hval : ∀ (q : MA.E (D.parOf S v).r) (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
      φ (B.gq (T v).base q) = evD (D.parOf S v) ⟨q, hq⟩ β) :
    BddReal S T v e Cb (Matrix.scalar (M.Ty (D.parOf S v)) ((DQ (D.parOf S v)).fnP β (cjD (D.parOf S v) β))) := by
  have hφc := scalar_conjugation_transfer _ _ _ _ (T v).base _ φ hφ
  refine SSn.real_to_bounded_holds E Wp Wq S T v hPl e Cb
    (fun g => φ g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (fun g => conj (φ g) • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (fun ρ π q => if ρ = π then evD (D.parOf S v) q β else 0) _ hFr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · intro x A B'
    simp only [B.hsInner, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      P.TBBx2.Tri.hsVec_smul, inner_smul_left, inner_smul_right, Complex.conj_conj]
  · intro g₀ hg₀
    obtain ⟨U, φ', hU, hg, hφ', he⟩ := hφ.1 g₀ hg₀
    exact ⟨U, fun g => φ' g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), hU, hg,
      hφ'.smul contDiffOn_const, fun g hgU hgG => by simp only; rw [he g hgU hgG]⟩
  · intro g₀ hg₀
    obtain ⟨U, φ', hU, hg, hφ', he⟩ := hφc.1 g₀ hg₀
    exact ⟨U, fun g => φ' g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), hU, hg,
      hφ'.smul contDiffOn_const, fun g hgU hgG => by
        show conj (φ g) • _ = φ' g • _
        rw [show conj (φ g) = φ' g from he g hgU hgG]⟩
  · intro p hp g _ X
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hinv p hp g,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro p hp g _ X
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hinv p hp g,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro ε hε m
    obtain ⟨C, hC⟩ := hφ.2 ε hε m
    refine ⟨C, fun u w hu hw hl g hg hG => ?_⟩
    rw [dLR_smulc]
    exact (norm_smul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans
      (hC u w hu hw hl g hg hG))
  · intro ε hε m
    obtain ⟨C, hC⟩ := hφc.2 ε hε m
    refine ⟨C, fun u w hu hw hl g hg hG => ?_⟩
    rw [dLR_smulc]
    exact (norm_smul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans
      (hC u w hu hw hl g hg hG))
  · intro q hq ρ π
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, P.TBBx2.Tri.hsVec_smul,
      inner_smul_right, (hFr.2 q.2 hq.2).2.1 ρ π, hval q hq]
    split_ifs <;> simp
  · intro ρ π
    by_cases h : ρ = π
    · subst h
      exact ⟨β, by rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq], fun q => by simp⟩
    · refine ⟨0, ?_, fun q => by simp [h]⟩
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, cjD_zero, multiplierPair_zero]

end real

section main

theorem phiR_sgs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p)
    (g : B.Mat k r) : phiR k r D.z D.z' (B.sgs p g) = phiR k r D.z D.z' g := by
  unfold phiR; rw [P.BigCellZetaMinors.dmin_sgs D hp, P.BigCellZetaMinors.dmin_sgs D hp]

theorem phiD_sgs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p)
    (g : B.Mat k r) : phiD k r D.z D.z' (B.sgs p g) = phiD k r D.z D.z' g := by
  unfold phiD; rw [P.BigCellZetaMinors.dmin_sgs D hp]

theorem dmin_gq {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ}
    (hq : q ∈ JF.QDom k r D.z D.z') :
    Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ = ∏ a, q.1 a ∧
      Dmin k r D.z D.z' (B.gq D q) (Fin.last (r + 1)) = q.2 * ∏ a, q.1 a := by
  have h1 : Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ = ∏ a, q.1 a := by
    have := (bigCellMinors k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem).1 (Fin.last r)
    simp only [Fin.val_last] at this
    rw [show B.gq D q = bigCell k r q.1 (D.μsec q.2) from rfl, this]
    exact Finset.prod_congr (by ext a; simp) fun _ _ => rfl
  refine ⟨h1, ?_⟩
  have hz := P.BigCellZetaMinors.zeta_gq D hq
  have hne : Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ ≠ 0 := by
    rw [h1]; exact Finset.prod_ne_zero_iff.2 fun a _ => hq.1 a
  unfold zeta at hz
  rw [← hz, ← h1, div_mul_cancel₀ _ hne]

theorem bounded_scalar_transfer_holds : JABddScal := by
  obtain ⟨K, hK0, hK⟩ := scalar_transfer_bound_holds
  refine ⟨K, hK0, fun Cc Cb _ hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr _ hL b hb => ?_⟩
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hT : Tz S.G.k S.G.r (T v).base.z = S.T := hPl.2.2.2.1
  have hT' : Tz S.G.k S.G.r (T v).base.z' = S.T' := hPl.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' = (D.parOf S v).TT := by
    rw [hT, hT']; rfl
  have hTpos : 0 < (D.parOf S v).TT := by
    rw [← hTT]; exact mul_pos (T v).base.T_pos (T v).base.T'_pos
  have hT0 := hTpos.le
  have hQD : ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun q hq => ⟨hq.1, by rw [hTT]; exact hq.2⟩
  have hBg : K * ((S.G.r : ℝ) + 1) ≤ Cb * ((S.G.r : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hCb (by positivity)
  obtain ⟨hR, hD⟩ := hK S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base _ hBg
  have hRc := scalar_conjugation_transfer _ _ _ _ (T v).base _ _ hR
  have hDc := scalar_conjugation_transfer _ _ _ _ (T v).base _ _ hD
  obtain ⟨-, -, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, -, -, -, -, -⟩ := hL

  have vR : ∀ q (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
      phiR S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) = (q.2)⁻¹ := fun q hq => by
    have hz' := P.BigCellZetaMinors.zeta_gq (T v).base (hQD q hq)
    unfold zeta at hz'
    unfold phiR
    rw [← hz', inv_div]
  have vD : ∀ q (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
      phiD S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) =
        (∏ a, q.1 a) * q.2 * ((conj q.2)⁻¹ * ∏ a, (conj (q.1 a))⁻¹) := fun q hq => by
    have h := (dmin_gq (T v).base (hQD q hq)).2
    have hz0 : q.2 ≠ 0 := BStar.z_ne hT0 ⟨q, hq⟩
    have hc0 : ∀ a, q.1 a ≠ 0 := hq.1
    unfold phiD
    rw [h, map_mul, map_prod, Finset.prod_inv_distrib, div_eq_mul_inv, mul_inv]
    ring
  rcases hb with rfl | rfl | rfl | rfl
  · rw [BStar.rep_zi hzi, ← BStar.cjD_izi hT0]
    refine scal_real S T v hPl e hFr Cb _ hR (fun p hp g => phiR_sgs _ hp g) _ fun q hq => ?_
    rw [vR q hq, BStar.evD_inv _ hT0, coordE_vz]
  · rw [BStar.rep_zbi hzbi, ← BStar.cjD_izbi hT0]
    refine scal_real S T v hPl e hFr Cb _ hRc (fun p hp g => by simp only [phiR_sgs _ hp g]) _ fun q hq => ?_
    simp only
    rw [vR q hq, BStar.evD_inv _ hT0, coordE_vzb, map_inv₀]
  · have e1 : L.D * L.Dbi = Matrix.scalar (M.Ty (D.parOf S v))
        ((DQ (D.parOf S v)).fnP (βD (D.parOf S v)) (βDb (D.parOf S v))) := by
      rw [LevelData.D, LevelData.Dbi, rep_Dr hc, zeta_eq_scalar_matrix hz, rep_zbi hzbi, rep_Drbi hcbi, scalar_mul_fnP,
        scalar_mul_fnP, scalar_mul_fnP]; rfl
    rw [e1, ← BStar.cjD_βD hT0]
    refine scal_real S T v hPl e hFr Cb _ hD (fun p hp g => phiD_sgs _ hp g) _ fun q hq => ?_
    rw [vD q hq]
    simp only [βD, map_mul, map_prod, evaluation_of_coordinate_variable, BStar.evD_inv _ hT0, coordE_vc, coordE_vcb, coordE_vz, coordE_vzb]
  · have e2 : L.Db * L.Di = Matrix.scalar (M.Ty (D.parOf S v))
        ((DQ (D.parOf S v)).fnP (βDb (D.parOf S v)) (βD (D.parOf S v))) := by
      rw [LevelData.Db, LevelData.Di, rep_Drb hcb, rep_zb hzb, rep_zi hzi, rep_Dri hci, scalar_mul_fnP,
        scalar_mul_fnP, scalar_mul_fnP]; rfl
    rw [e2, ← BStar.cjD_βDb hT0]
    refine scal_real S T v hPl e hFr Cb _ hDc (fun p hp g => by simp only [phiD_sgs _ hp g]) _ fun q hq => ?_
    simp only
    rw [vD q hq, ← BStar.cjD_βD hT0, evD_cjD]
    simp only [βD, map_mul, map_prod, evaluation_of_coordinate_variable, BStar.evD_inv _ hT0, coordE_vc, coordE_vcb, coordE_vz, coordE_vzb]

end main

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdj
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAGroupAdj_of_jComm (h : GA.GAJComm) : JAGroupAdj :=
  GA.jAGroupAdj_of_leaves GA.graded_truncation_action_holds h GA.group_action_pairing_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPCoreAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

theorem glc_single (k r : ℕ) (a b : Fin (k + 1)) : GLc k r (Matrix.single (wI k r a) (wI k r b) 1) := by
  have hm : mdim k r (Fin.last r) = k + 1 := by simp [mdim]
  have h := Formalism.FourierDecayAlt.P.Qx2.hpart_lev (k := k) (r := r) (Fin.last r) (Fin.cast hm.symm a) (Fin.cast hm.symm b)
  have ea : posL k r (Fin.last r) (Fin.cast hm.symm a) = wI k r a := by
    ext; simp [posL, wI, Fin.val_last]; omega
  have eb : posL k r (Fin.last r) (Fin.cast hm.symm b) = wI k r b := by
    ext; simp [posL, wI, Fin.val_last]; omega
  rw [ea, eb] at h
  exact h

theorem radSp_smoothLev {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} (Φ : Q.RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    Q.SmoothLev k r (Fin.last r) (Dp k r z z') ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := Φ.2.2.1 (c, g₀) ⟨hc, hg₀.1, hg₀.2⟩
  refine ⟨{g | (c, g) ∈ U}, fun g => F (c, g), hU.preimage (continuous_const.prodMk continuous_id), hxU, ?_, ?_⟩
  · exact hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun g hg => hg)
  · intro g hg hgl
    exact hΦ (c, g) hg hgl

theorem psv_congr {TT : ℝ} {V : Type*} [AddCommGroup V] [Module ℂ V] {f g : ℂ → V} (hf : PSV TT f)
    (h : ∀ ζ : ℂ, TT < Complex.normSq ζ → g ζ = f ζ) : PSV TT g := by
  obtain ⟨n, a, v, ha, hfe⟩ := hf
  exact ⟨n, a, v, ha, fun ζ hζ => by rw [h ζ hζ]; exact hfe ζ hζ⟩

theorem psv_sum {TT : ℝ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (hadd : ∀ f g : ℂ → V, PSV TT f → PSV TT g → PSV TT (fun ζ => f ζ + g ζ)) (h0 : PSV TT (fun _ => (0 : V)))
    {ι : Type*} (s : Finset ι) (F : ι → ℂ → V) (hF : ∀ i ∈ s, PSV TT (F i)) :
    PSV TT (fun ζ => ∑ i ∈ s, F i ζ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert a s ha ih =>
    have := hadd _ _ (hF a (Finset.mem_insert_self a s)) (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))
    refine psv_congr this fun ζ _ => ?_
    simp [Finset.sum_insert ha]

theorem radial_polynomial_of_truncation : CorePolyOfCut := by
  intro hT hW hC Wp Wq _ _ _ _ _ _ P Bs hpl hk hsec Φ X₀ hX c hc Y
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  obtain ⟨n, κ, w, hκ, hw, hid⟩ := hT P.k P.r Bs.z Bs.z' Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Y
  rw [hTz] at hκ
  have hsm := radSp_smoothLev Φ hc
  have hwords : ∀ i, PSV P.TT (fun ζ =>
      wordR (w i) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ)) := by
    intro i
    refine hW Wp Wq P Bs hpl hk hsec Φ X₀ hX c hc (w i) (fun Z hZ => ?_)
    obtain ⟨a, b, rfl⟩ := hw i Z hZ
    exact glc_single P.k P.r a b
  have hTT : 0 < P.TT := by rw [← hTz]; exact mul_pos Bs.T_pos Bs.T'_pos
  obtain ⟨-, -, -, -, -, -, -, hV⟩ := hC P.TT hTT
  obtain ⟨hadd, hsmul, -, -, hconst⟩ := hV (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp)
  have hsum := psv_sum hadd (hconst 0) Finset.univ
    (fun i ζ => κ i ζ • wordR (w i) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ))
    (fun i _ => hsmul _ _ (hκ i) (hwords i))
  refine psv_congr hsum fun ζ hζ => ?_
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by rw [hTz]; exact hζ
  have := hid (Wq →L[ℂ] Wp) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) hsm ζ hζ'
  simp only [mu0] at this
  rw [hsec]
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeom
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem second_shift_geometry_holds : SSn.SSnGeom :=
  SSn.Geom.geometry_assembly_holds SSn.Geom.geometry_smoothness_holds SSn.Geom.geometry_equivariance_first_vector SSn.Geom.geometry_equivariance_embedding
    SSn.Geom.geometry_at_level_function SSn.Geom.geometry_boundedness_at_zero SSn.Geom.geometry_unipotent_bound_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSmoothCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ellreg

variable {d : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

end ellreg

def lieOf {k r : ℕ} (Sx : Set (B.Mat k r)) : Set (B.Mat k r) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Sx}

def OmQ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {g | 0 < Gf k r z z' g ∧ ∀ a : Fin r, Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def SymbolNil : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ g ∈ B.GV k r, g ∈ OmQ k r z z' → ∀ ξ : B.Mat k r, B.inLie k r ξ → IsNilpotent ξ →
      (∀ X ∈ lieOf (Sset k r z), (Matrix.trace (ξ * X)).re = 0) →
      (∀ X ∈ lieOf (Sset k r z'), (Matrix.trace (ξ * (g * X * g⁻¹))).re = 0) →
      ξ = 0

theorem lieOf_mono {k r : ℕ} {A B' : Set (B.Mat k r)} (h : A ⊆ B') : lieOf A ⊆ lieOf B' :=
  fun _ hX t => h (hX t)

theorem UWset_sub_Sset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : UWset k r z ⊆ Sset k r z :=
  fun h hh => ⟨h, hh, 1, (nSubgroup k r).1, by simp⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JfS
end

