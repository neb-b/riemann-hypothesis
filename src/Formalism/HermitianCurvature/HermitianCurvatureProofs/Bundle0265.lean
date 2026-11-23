module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0258
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0250
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0251
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0262
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0264
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0259
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0263
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothTruncationInduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0260
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0232
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterpolationInverseMatrixSumIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0191

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBFinal
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

theorem headBridge_of_rest (hPr : ProperDomP) (hW : WordSmooth) (h1 : Side1) : LevelPointCoordinates.HeadBridge :=
  headBridge_of Formalism.FourierDecayAlt.P.rules_eq hW pts curveSmooth (supp_of Formalism.FourierDecayAlt.P.letters_pass_partial_bessel hPr)
    (Formalism.FourierDecayAlt.P.SliceIntegralLemmas.side_zero_of_local_properness hPr) h1 Formalism.FourierDecayAlt.P.one_variable_letters_under_integral

end Formalism.FourierDecayAlt.P.CutHB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDGqRes
section
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_group_residue : RDGqRes := by
  intro k r Wp Wq _ _ _ _ _ _ D q hq
  obtain ⟨hq1, hq2⟩ := hq
  have hsec := (D.sec.2 q.2 hq2).1
  have hU : B2.embWb k r (D.μsec q.2) ∈ B2.UWb k r :=
    TwoByOneBlock.emb_mem_UWb (k := k) (r := r) hsec
  have hv := TwoByOneBlock.sec_vec D.z_mem D.z'_mem D.sec hq2
  refine ⟨(q.1, B2.embWb k r (D.μsec q.2)), ?_, ?_⟩
  · refine ⟨hq1, ⟨hU.1, fun a _ => hU.2 a⟩, ?_⟩
    show 0 < Complex.normSq (zetaL k r D.z D.z' (Fin.last r) (B2.embWb k r (D.μsec q.2))) - Tz k r D.z * Tz k r D.z'
    have hz : zetaL k r D.z D.z' (Fin.last r) (B2.embWb k r (D.μsec q.2)) = q.2 := by
      unfold zetaL fvec
      simpa using hv.2.2
    rw [hz]
    linarith
  · refine ⟨((∏ a : Fin r, if (a : ℕ) < ((Fin.last r : Fin (r + 1)) : ℕ) then ‖q.1 a‖ ^ (Mdim k r a - 1) else 1 : ℝ) : ℂ), ?_, ?_⟩
    · rw [Complex.ofReal_ne_zero]
      refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
      split_ifs
      · exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hq1 a))
      · exact one_ne_zero
    · intro J _
      have hcell : wCell k r (Fin.last r) q.1 * B2.embWb k r (D.μsec q.2) = B.gq D q := by
        rw [Rad.wCell_last_eq]
        exact ((TwoByOneBlock.bigCellFactor k r q.1 (D.μsec q.2)).1).symm
      unfold resG
      rw [hcell]

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDOpFF
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutSE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem level_zero_inter_big_cell_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Q.Glev k r 0 ∩ JF.Om k r z z' = Q.Glev k r 0 ∩ Q.OmPlus k r z z' := by
  ext g
  constructor
  · rintro ⟨h1, _, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h1.1, h2⟩

theorem ffl_om_eq (k r : ℕ) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) :
    Q.FFl k r z z' π π' 0 (JF.Om k r z z') = Q.FFl k r z z' π π' 0 (Q.OmPlus k r z z') := by
  unfold Q.FFl Q.SmoothLev Q.LeftEq Q.RightEq
  simp only [level_zero_inter_big_cell_eq]

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS in
theorem radial_operator_function_field : RDOpFF := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hSm hC J hJ
  rw [ffl_om_eq] at hJ ⊢
  have hDom : Q.IsDom k r D.z D.z' 0 (Q.OmPlus k r D.z D.z') :=
    Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus D.z_mem D.z'_mem
  have hPos : ∀ g ∈ Q.OmPlus k r D.z D.z', g ∈ B.GV k r → g ∈ B.GPos D := fun g hg hgG => ⟨hgG, hg.2⟩
  have hG' := germ_operators_holds k r Wp Wq Θ
  have hsupp : ∀ f' : B.Mat k r → (Wq →L[ℂ] Wp), tsupport f' ⊆ Q.OmPlus k r D.z D.z' →
      B.SuppIn (B.GPos D) f' := by
    intro f' hs x hx
    have hxG : x ∈ B.GV k r :=
      (Formalism.FourierDecayAlt.P.B5.GV_closed (k := k) (r := r)).closure_subset_iff.2 (by exact fun y hy => hy.1) hx
    have hxT : x ∈ tsupport f' := closure_mono (by exact fun y hy => hy.2) hx
    exact hPos x (hs hxT) hxG
  constructor
  · refine equivariant_operators_holds extension_locality_holds _ _ _ _ D (Q.OmPlus k r D.z D.z') (B.opApply Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).1) (fun c f₁ g _ => (hG'.2 c f₁ g).1)
      (fun f₁ hf hs => (smooth_operators_holds _ _ _ _ D Θ _ hDom.1 hPos hSm f₁ hf hs).1) ?_ J hJ
    intro f₁ hf _ _ p hp g hg hgG
    exact hC p hp f₁ (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hf) g (hPos g hg hgG)
  · refine equivariant_operators_holds extension_locality_holds _ _ _ _ D (Q.OmPlus k r D.z D.z') (B.opAdj Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).2) (fun c f₁ g _ => (hG'.2 c f₁ g).2)
      (fun f₁ hf hs => (smooth_operators_holds _ _ _ _ D Θ _ hDom.1 hPos hSm f₁ hf hs).2) ?_ J hJ
    intro f₁ hf hc hs p hp g hg hgG
    exact adjoint_commutation_holds _ _ _ _ D Θ hSm hC f₁ hf hc (hsupp f₁ hs) p hp g (hPos g hg hgG)

end Formalism.FourierDecayAlt.P.CutSE
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDResRad
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem rdb_glev0_inter_om (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Q.Glev k r 0 ∩ JF.Om k r z z' = Q.Glev k r 0 ∩ Q.OmPlus k r z z' := by
  ext g
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h1.1, h2⟩

theorem rdb_ffl_om_eq (k r : ℕ) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) :
    Q.FFl k r z z' π π' 0 (JF.Om k r z z') = Q.FFl k r z z' π π' 0 (Q.OmPlus k r z z') := by
  simp only [Q.FFl, Q.SmoothLev, Q.LeftEq, Q.RightEq, rdb_glev0_inter_om]

private theorem conjTranspose_mul_H_mul_preserved_of_preserved {n : ℕ} (H a b : Matrix (Fin n) (Fin n) ℂ)
    (ha : a.conjTranspose * H * a = H) (hb : b.conjTranspose * H * b = H) :
    (a * b).conjTranspose * H * (a * b) = H := by
  rw [Matrix.conjTranspose_mul]
  calc b.conjTranspose * a.conjTranspose * H * (a * b)
      = b.conjTranspose * (a.conjTranspose * H * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = H := by
        rw [ha, hb]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem radial_residue_formula : RDResRad := by
  classical
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD J hJ
  have hz := hD.1.2.1
  have hz' := hD.1.2.2.1
  rw [rdb_ffl_om_eq] at hJ
  obtain ⟨hS, -, -, hE⟩ := hJ
  have huh : ∀ a b : Mx P.k P.r, a ∈ UH (Hpk P.k P.r) → b ∈ UH (Hpk P.k P.r) →
      a * b ∈ UH (Hpk P.k P.r) :=
    fun a b ha hb => conjTranspose_mul_H_mul_preserved_of_preserved _ a b ha hb
  have hcell : ∀ c ∈ OmX P.r, wCell P.k P.r (Fin.last P.r) c ∈ UH (Hpk P.k P.r) := by
    intro c hc
    refine List.prod_induction _ huh ?_ ?_
    · show (1 : Mx P.k P.r).conjTranspose * Hpk P.k P.r * 1 = Hpk P.k P.r
      simp
    · intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      exact Qx3.weyl_cell_mem_unitary a (hc a)
  have hcomm : ∀ (c : Fin P.r → ℂ) (h : Mx P.k P.r), h ∈ UWset P.k P.r z →
      Commute (wCell P.k P.r (Fin.last P.r) c) h := by
    intro c h hh
    refine Commute.list_prod_left _ _ ?_
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact Qx3.w1_commute_of_mem_Glev a (c a) ⟨hh.1, fun b _ => hh.2.1 b⟩
  have hin : ∀ x ∈ DomR P.k P.r z z',
      wCell P.k P.r (Fin.last P.r) x.1 * x.2 ∈ Glev P.k P.r 0 ∩ OmPlus P.k P.r z z' :=
    fun x hx => ⟨Rad.glev0 (huh _ _ (hcell _ hx.1) hx.2.1.1),
      Rad.wCell_mem_omPlus hz hz' hx.1 hx.2.1 hx.2.2⟩
  let Φ0 : Fn P.k P.r (Wq →L[ℂ] Wp) := fun c g =>
    if (c, g) ∈ DomR P.k P.r z z' then resG P.k P.r (Fin.last P.r) J c g else 0
  have hmem : Φ0 ∈ RadSp P.k P.r z z' π π' := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact if_neg hx
    · intro x₀ hx₀
      obtain ⟨U, F, hU, hxU, hF, hag⟩ :=
        Rad.sf_resG hS x₀ ⟨hx₀.1, (hin x₀ hx₀).2⟩ hx₀.2.1
      refine ⟨U ∩ (Prod.fst ⁻¹' OmX P.r ∩ Prod.snd ⁻¹' {g | 0 < GGl P.k P.r z z' g}), F,
        hU.inter (((Qx3.isOpen_OmX _).preimage continuous_fst).inter
          (isOpen_lt continuous_const ((Qx5.GGl_continuous _ _ _ _).comp continuous_snd))),
        ⟨hxU, hx₀.1, hx₀.2.2⟩, hF.mono Set.inter_subset_left, ?_⟩
      intro x hx hg
      have hxD : x ∈ DomR P.k P.r z z' := ⟨hx.2.1, hg, hx.2.2⟩
      show (if (x.1, x.2) ∈ DomR P.k P.r z z' then _ else _) = _
      rw [if_pos hxD]
      exact hag x hx.1 hg
    · intro x hx h hh h' hh'
      have hx' := Rad.domR_uw hx hh hh'
      show (if (x.1, h * x.2 * h') ∈ DomR P.k P.r z z' then _ else _) =
        π h ∘SL (if (x.1, x.2) ∈ DomR P.k P.r z z' then _ else _) ∘SL π' h'
      rw [if_pos hx', if_pos hx]
      simp only [resG]
      rw [show wCell P.k P.r (Fin.last P.r) x.1 * (h * x.2 * h') =
          h * (wCell P.k P.r (Fin.last P.r) x.1 * x.2) * h' by
        simp only [← mul_assoc, (hcomm x.1 h hh).eq]]
      rw [hE _ (hin x hx) h hh h' hh']
      simp [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  refine ⟨⟨Φ0, hmem⟩, fun x hx => ?_⟩
  show (if (x.1, x.2) ∈ DomR P.k P.r z z' then _ else _) = _
  rw [if_pos hx]

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDStartCoord
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_start_coordinates : RDStartCoord := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  obtain ⟨-, -, hL, hQ, -⟩ := hD
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  have ht : ∀ Y (a b : Fin 2) l (i : Fin 6), Commute (X.t Y a b) (X.op l i) :=
    fun Y a b l i => Formalism.FourierDecayAlt.P.NFx1.TC.t_op_comm X Y a b l i
  intro Y a b l x hx
  have hm : Commute (X.QQ Y a b) x := by
    rw [Formalism.FourierDecayAlt.P.NFx3.QQ_apply]
    simp only [coordOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 0) (ht (star Y) b a l 3).neg_right
    · rw [hpb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 3) (ht (star Y) b a l 0).neg_right
    · rw [hc l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 1) (ht (star Y) b a l 4)
    · rw [hci l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 2) (ht (star Y) b a l 5)
    · rw [hcb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 4) (ht (star Y) b a l 1)
    · rw [hcbi l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 5) (ht (star Y) b a l 2)
  rw [hQ Y, Matrix.smul_apply]
  exact hm.smul_left _

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDWaveFF
section
open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section WaveFF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem rdb_one_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, (nSubgroup k r).1, by simp⟩

theorem rdb_n_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {n : Mx k r} (hn : n ∈ Nlev k r 0) : n ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, n, hn.1, by simp⟩

theorem rdb_h_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {h : Mx k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, (nSubgroup k r).1, by simp⟩

theorem rdb_fsv_dmin_contDiff (z z' : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (h1 : 1 < r + 2) :
    ContDiff ℝ ∞ (fun g : Mx k r => fsv s (Dmin k r z z' g ⟨1, h1⟩)) := by
  have e : (fun g : Mx k r => fsv s (Dmin k r z z' g ⟨1, h1⟩)) = fun g =>
      Complex.exp (Formalism.FourierDecayAlt.P.PBFV.phaseL s (Formalism.FourierDecayAlt.P.JCx2.mnLinHerm (fvec k r z' 0) (fvec k r z 0)) g) :=
    funext fun g => Formalism.FourierDecayAlt.P.PBFV.fsv_dmin_one s z z' g h1
  rw [e]
  exact Complex.contDiff_exp.comp (ContinuousLinearMap.contDiff _)

theorem rdb_wvG_mem_FFl {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (s : ℂ)
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ FFl k r z z' π π' 0 Dm) : wvG z z' s J ∈ FFl k r z z' π π' 0 Dm := by
  have h1 : 1 < r + 2 := by omega
  have inv : ∀ {a b : Mx k r}, a ∈ Sset k r z → b ∈ Sset k r z' → ∀ g : Mx k r,
      Dmin k r z z' (a * g * b) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ :=
    fun ha hb g => dInv k r z z' hz hz' _ ha _ hb g _
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFJ⟩ := hS g₀ hg₀
    refine ⟨U, fun g => fsv s (Dmin k r z z' g ⟨1, h1⟩) • F g, hU, hgU,
      (rdb_fsv_dmin_contDiff z z' s h1).contDiffOn.smul hF, fun g hgU hgG => ?_⟩
    show fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g = _
    rw [hFJ g hgU hgG]
  · intro g hg n hn
    have e : Dmin k r z z' (n * g) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ := by
      have := inv (rdb_n_mem_Sset z hn) (rdb_one_mem_Sset z') g
      simpa using this
    show fsv s (Dmin k r z z' (n * g) ⟨1, h1⟩) • J (n * g) = _ • (fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g)
    rw [e, hL g hg n hn, smul_comm]
  · intro g hg n hn
    have e : Dmin k r z z' (g * n) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ := by
      have := inv (rdb_one_mem_Sset z) (rdb_n_mem_Sset z' hn) g
      simpa using this
    show fsv s (Dmin k r z z' (g * n) ⟨1, h1⟩) • J (g * n) = _ • (fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g)
    rw [e, hR g hg n hn, smul_comm]
  · intro g hg h hh h' hh'
    show fsv s (Dmin k r z z' (h * g * h') ⟨1, h1⟩) • J (h * g * h') =
      (π h).comp ((fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g).comp (π' h'))
    rw [inv (rdb_h_mem_Sset z hh) (rdb_h_mem_Sset z' hh') g, hU g hg h hh h' hh',
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end WaveFF

theorem radial_wave_function_field : RDWaveFF := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hr s hD J hJ
  have hz : inWb P.k P.r z := hD.1.2.1
  have hz' : inWb P.k P.r z' := hD.1.2.2.1
  have h1 : 1 < P.r + 2 := by omega
  refine ⟨rdb_wvG_mem_FFl hz hz' s hJ, fun x hx => ?_⟩
  simp only [resG, wvG]
  rw [Formalism.FourierDecayAlt.P.PBFV.first_minor_cell_eq_coord hz hz' hr x.1 hx.2.1 h1]
  exact smul_comm _ _ _

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDWaveRad
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
open scoped ComplexConjugate

section PairSub

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem rdw_sub_fst (a b : Pr V) : (a - b).1 = a.1 - b.1 := rfl
theorem rdw_sub_snd (a b : Pr V) : (a - b).2.unop = a.2.unop - b.2.unop := rfl

end PairSub

theorem radial_wave_radial : RDWaveRad := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hr s hD Wv Wv' hW hW'
  obtain ⟨-, -, hL, hQ, -⟩ := hD
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hG, hGi, -⟩ := hL
  obtain ⟨hWave, hWc, hWci, hWp⟩ := waveSiteAll Wp Wq P z z' π π' X L hL' ⟨0, hr⟩ s Wv Wv' hW hW'
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hop : ∀ (l : Fin P.r) i (Φ : RadSp P.k P.r z z' π π'),
      (X.op l i Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) = crd (opL l i) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) :=
    fun l i Φ => X.op_apply l i Φ
  have hcomm : ∀ (W : Module.End ℂ (RadSp P.k P.r z z' π π')) (u : ℂ → ℂ),
      (∀ (Φ : RadSp P.k P.r z z' π π') c g, (W Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        u (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      ∀ i : Fin 6, (i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5) → Commute W (X.op ⟨0, hr⟩ i) := by
    intro W u hWu i hi
    show W * X.op ⟨0, hr⟩ i = X.op ⟨0, hr⟩ i * W
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, hWu, hop, crd]
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp only [opL, cOp, ciOp, cbOp, cbiOp] <;> exact smul_comm _ _ _
  have hoth : ∀ (t : ℂ) (W : Module.End ℂ (RadSp P.k P.r z z' π π')),
      (∀ (Φ : RadSp P.k P.r z z' π π') c g, (W Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        fsv t (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      ∀ l : Fin P.r, l ≠ ⟨0, hr⟩ → ∀ i : Fin 6, Commute W (X.op l i) :=
    fun t W hWt l hl i => mulOp_comm_op X W t ⟨0, hr⟩ hWt hl i
  refine ⟨hWave, hWc, hWci, ?_, ?_, hWp, ?_, ?_, ?_, ?_⟩
  · rw [hcb]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hcomm Wv _ hW1 4 (by decide)) (hcomm Wv' _ hW2 1 (by decide))
  · rw [hcbi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hcomm Wv _ hW1 5 (by decide)) (hcomm Wv' _ hW2 2 (by decide))
  · rw [hpb, hcb]
    refine pr_ext ?_ ?_
    · change X.op ⟨0, hr⟩ 3 * Wv = Wv * X.op ⟨0, hr⟩ 3 -
        algebraMap ℂ _ (starRingEnd ℂ s) * Wv * X.op ⟨0, hr⟩ 4
      apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
      obtain ⟨hd, h0⟩ := radSp_regular Φ g c
      simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
        Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, hop, crd, hW1, opL]
      have e := pbOp_fsv_smul (-s) ⟨0, hr⟩ _ c hd h0
      simp only [neg_neg] at e
      rw [e]
      simp only [cbOp, map_neg]
      module
    · change Wv' * (-X.op ⟨0, hr⟩ 0) = (-X.op ⟨0, hr⟩ 0) * Wv' -
        X.op ⟨0, hr⟩ 1 * Wv' * algebraMap ℂ _ (starRingEnd ℂ (starRingEnd ℂ s))
      apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
      obtain ⟨hd, h0⟩ := radSp_regular Φ g c
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
        Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_smul, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, hop,
        crd, hW2, opL]
      rw [pOp_fsv_smul (-s) ⟨0, hr⟩ _ c hd h0]
      simp only [cOp, Complex.conj_conj]
      module
  · intro l hl x hx
    simp only [coordOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 0) (hoth (-s) Wv' hW2 l hl 3).neg_right
    · rw [hpb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 3) (hoth (-s) Wv' hW2 l hl 0).neg_right
    · rw [hc l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 1) (hoth (-s) Wv' hW2 l hl 4)
    · rw [hci l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 2) (hoth (-s) Wv' hW2 l hl 5)
    · rw [hcb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 4) (hoth (-s) Wv' hW2 l hl 1)
    · rw [hcbi l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 5) (hoth (-s) Wv' hW2 l hl 2)
  · have hf : ∀ j : Fin 6, Commute Wv (X.fn j) ∧ Commute Wv' (X.fn j) := fun j =>
      ⟨TwistedTransfer.mulOp_comm_fn X Wv _ hW j, TwistedTransfer.mulOp_comm_fn X Wv' _ hW' j⟩
    intro x hx
    simp only [Fr.zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hz]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 0).1 (hf 2).2
    · rw [hzi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 1).1 (hf 3).2
    · rw [hzb]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 2).1 (hf 0).2
    · rw [hzbi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 3).1 (hf 1).2
    · rw [hG]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 4).1 (hf 4).2
    · rw [hGi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 5).1 (hf 5).2
  · intro Y a b
    rw [hQ Y, Matrix.smul_apply, Formalism.FourierDecayAlt.P.NFx3.QQ_apply]
    exact (Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (comm_xt_of_fsv_smul_endomorphism X Wv s ⟨0, hr⟩ hW1 Y a b)
      (comm_xt_of_fsv_smul_endomorphism X Wv' (-s) ⟨0, hr⟩ hW2 (star Y) b a)).smul_right _

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialOperatorLocality
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem radial_operator_locality : RDOpLocal := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ f₁ f₂ h g hg
  have hO := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus (k := k) (r := r) D.z D.z'
  have h' : ∀ x ∈ B.GV k r, x ∈ Q.OmPlus k r D.z D.z' → f₁ x = f₂ x := fun x hx hxO => h x ⟨hx, hxO⟩
  exact ⟨Formalism.FourierDecayAlt.P.CutMP.JA.LocOp.opApply_congr_GV Θ hO h' g hg.1 hg.2,
    Formalism.FourierDecayAlt.P.CutMP.JA.LocOp.opAdj_congr_GV Θ hO h' g hg.1 hg.2⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

