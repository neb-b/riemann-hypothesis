module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointCornerScaledSingleComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0169
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensityOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0133
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0252
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UwClosedSubgroup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0167
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0200
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0232
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0250
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0253
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0249
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0018
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBPts
section
open Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section heads

theorem ptDiag_ne {h : C.LPt} {j : ℕ} (hh : D.IsLocPt h j) (a : Fin (D.ptSize h)) : D.ptDiag h a ≠ 0 :=
  Formalism.FourierDecayAlt.P.PBJ.Asm.ptScal_ne h hh.1 a a.isLt

theorem zxH_det_ne {h : C.LPt} {j : ℕ} (hh : D.IsLocPt h j) (v : XH h) : (zxH h j hh.2 v).det ≠ 0 := by
  unfold zxH
  rw [Matrix.det_reindex_self, Matrix.det_mul]
  exact mul_ne_zero (LeftFubiniLemmas.lh_unit _ v).ne_zero (Formalism.FourierDecayAlt.P.PBM.hMat_det_ne _ _ (ptDiag_ne hh))

theorem cdOn_mat {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {m n : Type} [Fintype m] [Fintype n]
    {f : X → Matrix m n ℂ} {s : Set X} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => f x a b) s) : ContDiffOn ℝ ∞ f s :=
  contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => h a b

theorem cd_lowW_entry {p : ℕ} (σ : Equiv.Perm (Fin p)) (a b : Fin p) :
    ContDiff ℝ ∞ (fun v : U.LW σ → ℂ => U.lowW σ v a b) := by
  unfold U.lowW
  simp only [Matrix.add_apply, Matrix.of_apply]
  refine contDiff_const.add ?_
  split_ifs
  · exact contDiff_apply ℝ (fun _ => ℂ) _
  · exact contDiff_const

theorem cd_zxH_entry (h : C.LPt) (j : ℕ) (hs : D.ptSize h = j) (a b : Fin j) :
    ContDiff ℝ ∞ (fun v : XH h => zxH h j hs v a b) := by
  unfold zxH LeftFubiniLemmas.lhOf
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  refine ContDiff.sum fun c _ => ContDiff.mul ?_ contDiff_const
  refine ContDiff.sum fun c' _ => ContDiff.mul ?_ contDiff_const
  refine ContDiff.sum fun c'' _ => ContDiff.mul contDiff_const ?_
  exact cd_lowW_entry _ _ _

end heads

section curve

theorem cd_det {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} (M : X → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ a b, ContDiff ℝ ∞ (fun x => M x a b)) : ContDiff ℝ ∞ (fun x => (M x).det) := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact contDiff_const.mul (contDiff_prod fun i _ => h (σ i) i)

theorem cd_inv_entry {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} (M : X → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ a b, ContDiff ℝ ∞ (fun x => M x a b)) (hd : ∀ x, (M x).det ≠ 0) (a b : Fin n) :
    ContDiff ℝ ∞ (fun x => (M x)⁻¹ a b) := by
  have e : ∀ x, (M x)⁻¹ a b = ((M x).det)⁻¹ * (M x).adjugate a b := by
    intro x
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  simp only [e]
  refine ContDiff.mul ((cd_det M h).inv hd) ?_
  simp only [Matrix.adjugate_apply]
  refine cd_det _ fun c d => ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact h _ _

theorem cd_zxHct_inv_entry (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (a b : Fin j) :
    ContDiff ℝ ∞ (fun v : XH h => ((zxH h j hh.2 v)ᴴ)⁻¹ a b) := by
  refine cd_inv_entry (fun v => (zxH h j hh.2 v)ᴴ) (fun c d => ?_) (fun v => ?_) a b
  · simp only [Matrix.conjTranspose_apply]
    exact Formalism.FourierDecayAlt.P.PBG.contDiff_starC.comp (cd_zxH_entry h j hh.2 d c)
  · rw [Matrix.det_conjTranspose]
    exact star_ne_zero.2 (zxH_det_ne hh v)

end curve

section curve2

theorem cd_zfull_entry (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (a b : Fin (j + 1)) :
    ContDiff ℝ ∞ (fun q : XH h × ℂ => zfull (zxH h j hh.2 q.1) q.2 a b) := by
  simp only [zfull_apply]
  split_ifs
  · exact (cd_zxH_entry h j hh.2 _ _).comp contDiff_fst
  · exact contDiff_snd
  · exact contDiff_const

theorem cdOn_zfullInv_entry (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (a b : Fin (j + 1)) :
    ContDiffOn ℝ ∞ (fun q : XH h × ℂ => ((zfull (zxH h j hh.2 q.1) q.2)ᴴ)⁻¹ a b) (Set.univ ×ˢ {τ | τ ≠ 0}) := by
  have e : ∀ q ∈ (Set.univ ×ˢ {τ : ℂ | τ ≠ 0} : Set (XH h × ℂ)),
      ((zfull (zxH h j hh.2 q.1) q.2)ᴴ)⁻¹ a b = zfull ((zxH h j hh.2 q.1)ᴴ)⁻¹ (star q.2)⁻¹ a b := by
    intro q hq
    rw [zfull_conjTranspose_inv (zxH_det_ne hh q.1) hq.2]
  refine ContDiffOn.congr ?_ e
  simp only [zfull_apply]
  split_ifs
  · exact ((cd_zxHct_inv_entry h j hh _ _).comp contDiff_fst).contDiffOn
  · intro q hq
    have hτ : star q.2 ≠ 0 := star_ne_zero.2 hq.2
    have h1 := (contDiffAt_inv ℂ (n := ∞) hτ).restrict_scalars ℝ
    exact (h1.comp q ((Formalism.FourierDecayAlt.P.PBG.contDiff_starC.comp contDiff_snd).contDiffAt)).contDiffWithinAt
  · exact contDiffOn_const

theorem curveSmooth : CurveSmooth := by
  intro k r j hj h hh γ
  refine cdOn_mat fun p' q' => ?_
  obtain ⟨P, rfl⟩ := cast_eB_surj (k := k) hj p'
  obtain ⟨Q, rfl⟩ := cast_eB_surj (k := k) hj q'
  simp only [level_point_eq_block_three, LeftFubiniLemmas.castM_apply', Fin.cast_cast, Fin.cast_eq_self, Ux3.block3_apply]
  rcases P with ((a | a) | a) <;> rcases Q with ((b | b) | b) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply] <;>
    first
    | exact contDiffOn_const
    | (simp only [Matrix.mul_apply]
       refine ContDiffOn.sum fun c _ => ?_
       first
       | exact (cdOn_zfullInv_entry h j hh _ _).mul contDiffOn_const
       | exact contDiffOn_const.mul (cd_zfull_entry h j hh _ _).contDiffOn)

end curve2

section pts

theorem dmin_mMap_hi {k J ρ : ℕ} (z z' : Fin (2 * (J + ρ) + k + 1) → ℂ) (hz : inWb k (J + ρ) z)
    (hz' : inWb k (J + ρ) z') (Z : Matrix (Fin J) (Fin J) ℂ) (γ : B.Mat k ρ) (l : ℕ) (hl : l ≤ ρ + 1) :
    Dmin k (J + ρ) z z' (U.mMap k J ρ Z γ) ⟨J + l, by omega⟩ =
      Z.det * Dmin k ρ (U.lowV k J ρ z) (U.lowV k J ρ z') γ ⟨l, by omega⟩ := by
  have hZ : Zhat k (J + ρ) z z' (U.mMap k J ρ Z γ) =
      Matrix.reindex (Ux3.eC J ρ) (Ux3.eC J ρ)
        (Matrix.fromBlocks Z 0 0 (Zhat k ρ (U.lowV k J ρ z) (U.lowV k J ρ z') γ)) := by
    unfold U.mMap
    rw [Ux3.z_hat_of_block3 z z' hz hz', Formalism.QuantumDeterminants.Zhat_eq]
    congr 1
    simp [← Matrix.mul_assoc, Ux3.wMat_mul_self]
  unfold Dmin
  rw [hZ]
  exact Ux3.minor_blocks _ _ l hl _

theorem gf_castM {k a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) :
    Gf k b z z' (D.castM e g) = Gf k a (D.castV e.symm z) (D.castV e.symm z') g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem dmin_castM' {k a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) (l : ℕ)
    (hl : l < b + 2) :
    Dmin k b z z' (D.castM e g) ⟨l, hl⟩ = Dmin k a (D.castV e.symm z) (D.castV e.symm z') g ⟨l, by omega⟩ := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem lowV_base {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {k r : ℕ} (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r)
    (e : j + 1 + (r - (j + 1)) = r) :
    U.lowV k (j + 1) (r - (j + 1)) (D.castV e.symm T.base.z) = (T.bs (j + 1)).z ∧
      U.lowV k (j + 1) (r - (j + 1)) (D.castV e.symm T.base.z') = (T.bs (j + 1)).z' := by
  unfold D.LevTower.base
  rw [← T.z_lev (j + 1) hj, ← T.z'_lev (j + 1) hj, castV_castV', castV_castV']
  exact ⟨Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _, Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _⟩
where
  castV_castV' {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (v : Fin (2 * a + k + 1) → ℂ) :
      D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by
    subst h1 h2; rfl

theorem pts : Pts := by
  intro Wp Wq _ _ _ _ _ _ P p j hj h hh γ hγ hΩ v
  have hZ := zxH_det_ne hh v
  refine ⟨hZ, fun τ hτ => ?_⟩
  set Z := zxH h j hh.2 v
  have e : j + 1 + (P.r - (j + 1)) = P.r := by omega
  have hz := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z_mem
  have hz' := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z'_mem
  obtain ⟨hl1, hl2⟩ := lowV_base p.T j hj e
  have hdf : (zfull Z τ).det ≠ 0 := by rw [zfull_det]; exact mul_ne_zero hZ hτ
  have hx : x0 P.k P.r j hj Z τ γ = D.castM e (U.mMap P.k (j + 1) (P.r - (j + 1)) (zfull Z τ) γ) := rfl
  refine ⟨fun l hl1' hl2' => ?_, ?_⟩
  · by_cases hlj : l.val = j
    · have := (Formalism.FourierDecayAlt.P.CutHL.leading_minors_at_base_point P.k P.r j hj p.T.base.z p.T.base.z' Z τ γ hZ hτ hγ).1
      have hl : l = ⟨j, by omega⟩ := Fin.ext hlj
      rw [hl, this]; exact hZ
    · obtain ⟨l', hl'⟩ : ∃ l', l.val = j + 1 + l' := ⟨l.val - (j + 1), by omega⟩
      have hl : l = ⟨j + 1 + l', by omega⟩ := Fin.ext hl'
      rw [hl, hx, dmin_castM' e, dmin_mMap_hi _ _ hz hz' _ _ l' (by omega), hl1, hl2]
      refine mul_ne_zero hdf ?_
      exact hΩ.1 ⟨l', by omega⟩ (by simp; omega)
  · rw [hx, gf_castM e]
    have hG := Formalism.FourierDecayAlt.P.level_function_slice P.k (j + 1) (P.r - (j + 1)) _ _ hz hz' 0 0 (zfull Z τ) γ
    rw [LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at hG
    rw [hG, hl1, hl2]
    exact mul_pos (Complex.normSq_pos.2 hdf) hΩ.2

end pts

section head

theorem leading_block_of_base_point {k r j : ℕ} (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (e : r = j + (r - j)) : U.Zh k j (r - j) (D.castM e (x0 k r j hj Z τ γ)) = Z := by
  ext a b
  unfold U.Zh x0
  rw [LeftFubiniLemmas.castM_apply', LeftFubiniLemmas.castM_apply']
  simp only [Fin.cast_cast]
  have key : ∀ q : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1), q.val = 2 * (j + (r - j)) + k - a.val →
      q = U.eB k (j + 1) (r - (j + 1)) (Sum.inr ⟨j - a.val, by omega⟩) := by
    intro q hq; ext; rw [Ux3.block_index_last_val]; simp only [Fin.val_mk]; omega
  rw [key (Fin.cast _ _) (by simp), LeftFubiniLemmas.embedding_map_apply_last_block, dite_eq_left (by simp only [Fin.val_cast]; omega), zfull_apply,
    dite_eq_left (by simp only [Fin.val_rev, Fin.val_cast, Fin.val_mk]; omega)]
  congr 1 <;> ext <;> simp only [Fin.val_rev, Fin.val_cast, Fin.val_mk] <;> omega

end head

end Formalism.FourierDecayAlt.P.CutHB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLAsm
section
namespace Formalism.FourierDecayAlt.P.CutHL

theorem headLetter_of_rest (hL : LeftActionRuleAtBasePoint) (hT : TorusDirectionAtBasePoint) (hSL : ConjugateActionRuleAtBasePoint) (hST : ConjugateTorusDirectionAtBasePoint)
    (hPP : PlusPosOfParts) (hPZ : PlusZeroOfParts) (hMP : MinusPosOfParts) (hMZ : MinusZeroOfParts) :
    LevelPointCoordinates.HeadLetter :=
  headLetter_of_open hL hT hSL hST frozen_X_identity frozen_V_identity hPP hPZ hMP hMZ

end Formalism.FourierDecayAlt.P.CutHL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAAll
section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem jDCapA_of_inv_toda (hI : JDACapInv) (hT : JDACapToda) (hTv : JDACapTodaV) : JDCapA :=
  jDCapA_of_grp (jDAGrp_of_parts capelli_representation_holds hI hT hTv)

theorem jDCapA_of_inv_todaV (hI : JDACapInv) (hTv : JDACapTodaV) : JDCapA :=
  jDCapA_of_inv_toda hI jda_capelli_toda_proof hTv

theorem jDCapA_of_todaV (hTv : JDACapTodaV) : JDCapA := jDCapA_of_inv_todaV capelli_invariance_criterion hTv

theorem capelli_minors_holds : JDCapA := jDCapA_of_todaV jda_capelli_toda_mirror_proof

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMKTop
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMK

theorem psi_cast {k a b : ℕ} (e : a = b) (v : Fin (2 * a + k + 1) → ℂ) (c : ℂ) (g : B.Mat k a) :
    psi k b (D.castV e v) c (D.castM e g) = psi k a v c g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem top_construction : TopMk := by
  intro hC Wp Wq _ _ _ _ _ _ P p
  have hT := p.hT
  have hr : P.r ≤ P.r := le_rfl
  have e0 : P.r + (P.r - P.r) = P.r := by omega
  have hρ : P.r - P.r = 0 := Nat.sub_self _
  obtain ⟨b, hbs, hbc, hκL, hκR⟩ := Formalism.FourierDecayAlt.P.CutEX.MkTopBump.bump_exists (k := P.k) (p := P.r) (ρ := P.r - P.r)
    (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).z_mem (p.T.bs P.r).z'_mem
  obtain ⟨β, hβs, hβi, hβK⟩ := Formalism.FourierDecayAlt.P.CutEXMT.top_truncation_construction P.r
  refine ⟨b, b, β, kapL (p.T.bs P.r).z b * kapR (p.T.bs P.r).z' b, hbs, hbc, hbs, hbc, mul_ne_zero hκL hκR, hβs,
    ?_, ?_⟩
  · intro K hK hKU
    obtain ⟨K', hK', hK'1, hK'2⟩ := hβK (Mt P.k (P.r - P.r)) K hK (fun q hq => (hKU hq).1)
    refine ⟨K', hK', fun q hq => ?_, hK'2⟩
    obtain ⟨hd, q₀, hq₀, he⟩ := hK'1 q hq
    exact ⟨hd, he ▸ (hKU hq₀).2⟩
  · intro Φ hΦL hΦU Z y hZ hy
    have hyG : (Matrix.of y : B.Mat P.k (P.r - P.r)) ∈ B.GV P.k (P.r - P.r) :=
      (Formalism.FourierDecayAlt.P.CutEX.MkCptPf.glev_last_iff hρ _).1 hy
    have hz : p.T.base.z' = D.castV e0 (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z') := (p.T.z'_lev P.r hr).symm
    have hpsi : ∀ u : G.UT P.r → ℂ, CutEX.psiU p (G.upper u) =
        psi P.k (P.r + (P.r - P.r)) (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z') cStd
          (U.muP P.k P.r (P.r - P.r) (G.upper u)) := by
      intro u
      unfold CutEX.psiU
      rw [hz]
      exact psi_cast e0 _ _ _
    have key := hC P.k P.r (P.r - P.r) P.r Wp Wq e0 hρ (p.T.bs P.r) p.T.base (p.T.z'_lev P.r hr)
      (p.T.π'_lev P.r hr) (hT P.r hr).1 (hT P.r hr).2.1 (Formalism.FourierDecayAlt.P.PBM.tower_haarW' p.T hT P.r hr e0)
      (hT P.r hr).2.2 (hT 0 (Nat.zero_le _)).2.2 b b β Φ hbs.continuous hbc hbs.continuous hbc Z hZ
      (hβi Z hZ).1 (hβi Z hZ).2 y hyG (fun h1 hh1 h2 hh2 => hΦL Z y hy h1 hh1 h2 hh2)
      (fun u y' hy' => by
        rw [hΦU Z y' (G.upper u) hZ ((Formalism.FourierDecayAlt.P.CutEX.MkCptPf.glev_last_iff hρ _).2 hy')
          (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.upper_isUpUni u), hpsi u])
    exact key

theorem mkTop_of_avgs (hR : RightAvg) (hL : LeftAvg) : CutEX.MkTop := mkTop_of_leaves hR hL top_construction

end Formalism.FourierDecayAlt.P.CutMK
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEBTCls
section
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

section BTClsPf

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem opClos_op (X : ActualOps k r z z' π π') (l : Fin r) (B : Submodule ℂ (RadSp k r z z' π π')) (j : Fin 6) :
    ∀ Φ ∈ OpClos X l B, X.op l j Φ ∈ OpClos X l B := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨js, Ψ, hΨ, rfl⟩ := hx
    exact Submodule.subset_span ⟨j :: js, Ψ, hΨ, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem act_mem_of_entSub {S : Type} [Fintype S] [DecidableEq S] (C : Submodule ℂ (RadSp k r z z' π π'))
    (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : M ∈ entSub (presAlg C)) (u : Ix S → RadSp k r z z' π π')
    (hu : ∀ b, u b ∈ C) (b : Ix S) : act M u b ∈ C := by
  exact Formalism.FourierDecayAlt.P5.HerA.act_mem_pres M (fun a c => hM a c) u hu b

end BTClsPf

theorem boundary_torus_closure : BTCls := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ l _ u hu
  have hAL := hD.2.2.1
  have hop : ∀ (j : Fin 6) (Φ : (RadSp P.k P.r z z' π π')), Φ ∈ (ClsE S P z z' π π' X L st l0 D l) → X.op l j Φ ∈ (ClsE S P z z' π π' X L st l0 D l) :=
    fun j Φ hΦ => opClos_op X l _ j Φ hΦ
  have hmk : ∀ i j : Fin 6, mkP (X.op l i) (X.op l j) ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := fun i j =>
    (show (∀ Φ ∈ (ClsE S P z z' π π' X L st l0 D l), (mkP (X.op l i) (X.op l j)).1 Φ ∈ (ClsE S P z z' π π' X L st l0 D l)) ∧
        ∀ Φ ∈ (ClsE S P z z' π π' X L st l0 D l), (mkP (X.op l i) (X.op l j)).2.unop Φ ∈ (ClsE S P z z' π π' X L st l0 D l) from
      ⟨fun Φ hΦ => hop i Φ hΦ, fun Φ hΦ => hop j Φ hΦ⟩)
  have hmkneg : ∀ i j : Fin 6, mkP (X.op l i) (-X.op l j) ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := fun i j =>
    (show (∀ Φ ∈ (ClsE S P z z' π π' X L st l0 D l), (mkP (X.op l i) (-X.op l j)).1 Φ ∈ (ClsE S P z z' π π' X L st l0 D l)) ∧
        ∀ Φ ∈ (ClsE S P z z' π π' X L st l0 D l), (mkP (X.op l i) (-X.op l j)).2.unop Φ ∈ (ClsE S P z z' π π' X L st l0 D l) from
      ⟨fun Φ hΦ => hop i Φ hΦ, fun Φ hΦ => by
        show (-X.op l j) Φ ∈ (ClsE S P z z' π π' X L st l0 D l)
        rw [LinearMap.neg_apply]
        exact Submodule.neg_mem _ (hop j Φ hΦ)⟩)
  have hp : L.p l ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := by rw [hAL.1 l]; exact hmkneg 0 3
  have hc : L.c l ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := by rw [hAL.2.2.1 l]; exact hmk 1 4
  have hci : L.ci l ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := by rw [hAL.2.2.2.1 l]; exact hmk 2 5
  have hconv : ∀ M : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π')),
      M ∈ Formalism.FourierDecayAlt.P5.matSub (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra (Ix S) →
        M ∈ Formalism.FourierDecayAlt.P5.HerA.entSub (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)) := fun M h => h
  have hins : ∀ (a : S) (M : M2 (Pr (RadSp P.k P.r z z' π π'))), (∀ i j, M i j ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)) →
      ins a (lift0 M : M2 (SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π')))) ∈
        Formalism.FourierDecayAlt.P5.matSub (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra (Ix S) := by
    intro a M hM
    apply Formalism.FourierDecayAlt.P5.ins_mem
    have h : ∀ (i j : Fin 2) (p q : Ix S), ((lift0 M : M2 (SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π')))) i j) p q ∈
        (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra := by
      intro i j p q
      simp only [lift0, Matrix.map_apply, io, Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs
      · exact hM i j
      · exact Subalgebra.zero_mem _
    exact h
  refine ⟨fun le b => ?_, fun le b => ?_, fun a i j b => ?_⟩
  · refine act_mem_of_entSub _ _ (hconv _ (hins le.intersection_update_fsHerm_neg_one _ ?_)) u hu b
    intro i j
    split_ifs
    · exact Formalism.FourierDecayAlt.P5.Ts_mem (T := (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra) (site L l) le.pt
        hp hc hci i j
    · exact star_mem
        (Formalism.FourierDecayAlt.P5.Ts_mem (T := (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra) (site L l) le.pt
          hp hc hci i j)
  · refine act_mem_of_entSub _ _ (hconv _ (hins le.intersection_update_fsHerm_neg_one _ ?_)) u hu b
    intro i j
    split_ifs
    · exact Formalism.FourierDecayAlt.P5.HerA.matrix_two_entries_mem (zero_mem _) (neg_mem (star_mem hci)) (star_mem hc)
        (add_mem (algebraMap_mem _ _) (star_mem hp)) i j
    · exact Formalism.FourierDecayAlt.P5.HerA.matrix_two_entries_mem (zero_mem _) (neg_mem hci) hc
        (add_mem (algebraMap_mem _ _) hp) i j
  · exact act_mem_of_entSub _ _
      (hconv _ (Formalism.FourierDecayAlt.P5.eU_mem (C := (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra) a i j)) u hu b

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEIbTInv
section
open Matrix Formalism.FourierDecayAlt.Wd

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

namespace IbTInvPf

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem plus_inv (σ : Site A) (hW : YangianSpanCharacter.T.WeylRel σ.p σ.c σ.ci) (Y : K) (hY : star Y = Y) :
    (!![0, -star σ.ci; star σ.c, algebraMap K A (Y + 1) + star σ.p] : M2 A) * (Ts σ Y)ᴴ = 1 := by
  have hs := congrArg star hW.2.2
  simp only [star_mul, star_add] at hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ts, YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · rw [← star_mul, hW.1, star_one]
  · rw [← algebraMap_star_comm, hY, mul_add, add_mul, add_mul, one_mul, hs, Algebra.commutes]
    abel
  · rw [← star_mul, hW.2.1, star_one]

theorem minus_inv (σ : Site A) (hW : YangianSpanCharacter.T.WeylRel σ.p σ.c σ.ci) (Y : K) :
    (!![0, -σ.ci; σ.c, algebraMap K A (Y - 1) + σ.p] : M2 A) * ((Ts σ Y).map star)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ts, YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · exact hW.2.1
  · rw [mul_add, add_mul, sub_mul, one_mul, hW.2.2, Algebra.commutes]
    abel
  · exact hW.1

theorem lift_zero_one : (lift0 (1 : M2 A) : M2 (SlopeTestRemainingChoices S A)) = 1 := by
  unfold lift0
  ext i j
  rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [io]

theorem ivlet_mul_star (σ : Site A) (hW : YangianSpanCharacter.T.WeylRel σ.p σ.c σ.ci) (l : Letter K S)
    (hl : star l.pt = l.pt) : ivlet σ l * star (vlet σ l) = 1 := by
  unfold ivlet vlet
  rw [Formalism.FourierDecayAlt.P.Wd1.ins_star _ _ (Formalism.FourierDecayAlt.P.Wd7.freeOf2_lift _ _),
    ← Formalism.FourierDecayAlt.P.Wd1.ins_mul _ _ _ (Formalism.FourierDecayAlt.P.Wd7.freeOf2_lift _ _), Formalism.FourierDecayAlt.P.Wd7.liftMatrix_conjTranspose,
    ← Formalism.FourierDecayAlt.P.Wd7.lift_reduction_mul]
  cases hpl : l.plus
  · simp only [Bool.false_eq_true, ite_false]
    rw [minus_inv σ hW l.pt, lift_zero_one, Formalism.FourierDecayAlt.P.Wd1.ins_one]
  · simp only [ite_true]
    rw [plus_inv σ hW l.pt hl, lift_zero_one, Formalism.FourierDecayAlt.P.Wd1.ins_one]

theorem ibT_mul_star (σ : Site A) (hσ : IsSite σ) :
    ∀ w : List (Letter K S), (∀ l ∈ w, star l.pt = l.pt) → ibT σ w * star (bT σ w) = 1
  | [], _ => by simp [ibT, bT]
  | l :: w, h => by
    have hw := ibT_mul_star σ hσ w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    rw [ibT, bT, star_mul, mul_assoc, ← mul_assoc (ibT σ w), hw, one_mul,
      ivlet_mul_star σ hσ.1 l (h l (by simp))]

end IbTInvPf

theorem boundary_torus_invariance : IbTInv := by
  intro K A S _ _ _ _ _ _ _ _ σ w hσ hw
  exact IbTInvPf.ibT_mul_star σ hσ w hw

end Formalism.FourierDecayAlt.P.CutSE
end
end

