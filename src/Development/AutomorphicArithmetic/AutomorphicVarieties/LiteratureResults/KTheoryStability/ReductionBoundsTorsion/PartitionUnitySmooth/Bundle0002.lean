module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.DiagForm

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.BQRSingle
section
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL PositivityTheory.KB PositivityTheory.KB.SmoothPartitionUnityBasic.BasicAux
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private theorem b_qR_single {L : Type} [Field L] [NumberField L] {N : ℕ} [DecidableEq (InfinitePlace L)]
    (h : HS L N) (w : InfinitePlace L) (x : Fin N → ℂ) :
    qR h (Pi.single w x) = (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  unfold qR
  rw [Finset.sum_eq_single w (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
    (fun hw => absurd (Finset.mem_univ w) hw), Pi.single_eq_same]

private theorem b_cl_at {L : Type} [Field L] [NumberField L] {N : ℕ} {δ : ℝ} {h k : HS L N}
    (hcl : Cl δ h k) (w : InfinitePlace L) (x : Fin N → ℂ) :
    |(star x ⬝ᵥ (mat k w *ᵥ x)).re - (star x ⬝ᵥ (mat h w *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  classical
  have := hcl (Pi.single w x)
  rwa [b_qR_single, b_qR_single] at this

private theorem b_toR_ne {L : Type} [Field L] [NumberField L] {N : ℕ} {v : Lat L N} (hv : v ≠ 0) :
    toR v ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hv
  obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
  intro h0
  have := congrFun (congrFun h0 w) a
  simp only [toR, Pi.zero_apply] at this ha
  apply ha
  simpa [embO] using this

private theorem b_qR_pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N} (hh : h ∈ Pos L N)
    {z : VR L N} (hz : z ≠ 0) : 0 < qR h z := by
  obtain ⟨c, hc, hev⟩ := UpperTheory.V.KT.lowbd L N h hh
  have h1 := hev.self_of_nhds z
  have : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2 : 0 < ‖z‖ ^ 2 := by positivity
  nlinarith

private theorem b_emb_val {L : Type} [Field L] [NumberField L] {N : ℕ} (γ : Gm L N) (w : InfinitePlace L) :
    (((emb L N γ) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  ext i j
  simp [emb, toP, toK, embO, Matrix.GeneralLinearGroup.map_apply]

private theorem b_ginv {L : Type} [Field L] [NumberField L] {N : ℕ} (γ : Gm L N) (w : InfinitePlace L) :
    ((((emb L N γ) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  rw [← b_emb_val, map_inv, Pi.inv_apply]

private theorem b_transp {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → ℂ) :
    star z ⬝ᵥ (Mᵀ *ᵥ z) = star (star z) ⬝ᵥ (M *ᵥ star z) := by
  rw [star_star, mulVec_transpose, dotProduct_comm (star z), ← dotProduct_mulVec]

theorem pf_Basic : Basic := by
  intro L _ _ N hN
  classical
  refine ⟨?p1, ?p2, ?p3, ?p4, ?p5, ?p6⟩
  · intro h hh
    have hfin : ∀ B : ℝ, {v : Lat L N | q h v ≤ B}.Finite := fun B => by
      obtain ⟨S, hS, hev⟩ := UpperTheory.V.KT.locfin L N h hh B
      refine hS.subset fun v hv => ?_
      by_contra hvS
      exact absurd hv (not_le.2 (hev.self_of_nhds v hvS))
    have hpos : ∀ v : Lat L N, v ≠ 0 → 0 < q h v := fun v hv => b_qR_pos hh (b_toR_ne hv)
    obtain ⟨v0, hv0⟩ : ∃ v0 : Lat L N, v0 ≠ 0 := by
      refine ⟨Pi.single (⟨0, hN⟩ : Fin N) 1, fun h0 => ?_⟩
      have := congrFun h0 ⟨0, hN⟩
      simp at this
    obtain ⟨vm, ⟨hvm0, -⟩, hvm⟩ := Set.exists_min_image {v : Lat L N | v ≠ 0 ∧ q h v ≤ q h v0}
      (fun v => q h v) ((hfin (q h v0)).subset fun v hv => hv.2) ⟨v0, hv0, le_rfl⟩
    have mlow : ∀ v : Lat L N, v ≠ 0 → q h vm ≤ q h v := fun v hv => by
      by_cases hle : q h v ≤ q h v0
      · exact hvm v ⟨hv, hle⟩
      · exact (hvm v0 ⟨hv0, le_rfl⟩).trans (not_le.1 hle).le
    haveI : Nonempty {y : Lat L N // y ≠ 0} := ⟨⟨v0, hv0⟩⟩
    have hlam : lam h = q h vm := by
      unfold lam
      refine le_antisymm (ciInf_le ⟨q h vm, ?_⟩ (⟨vm, hvm0⟩ : {y : Lat L N // y ≠ 0}))
        (le_ciInf fun y => mlow y.1 y.2)
      rintro _ ⟨y, rfl⟩
      exact mlow y.1 y.2
    refine ⟨by rw [hlam]; exact hpos vm hvm0, fun v hv => by rw [hlam]; exact mlow v hv,
      ⟨vm, hvm0, hlam.symm⟩, fun w => ?_, hfin⟩
    exact (hh w).inv.transpose
  · intro γ h v
    simp only [q, qR, ac, mat_actL, smul_lat, toR_mulVec, b_ginv]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  · intro γ
    let γt : Gm L N := ⟨(γ : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ, ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ,
      by rw [← transpose_mul, Units.inv_mul, transpose_one],
      by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
    refine ⟨γt⁻¹, fun h hh => HS_ext fun w => ?_⟩
    simp only [dualH, mat_mkHS, ac, mat_actL, b_ginv, inv_inv]
    have hT : ((γt : Matrix (Fin N) (Fin N) (𝓞 L))).map (embO w) =
        ((γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w))ᵀ := by
      ext i j; rfl
    rw [hT]
    set M := (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hM
    set G := ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hG
    have hMG : M * G = 1 := by
      rw [hM, hG, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have hGinv : G⁻¹ = M := Matrix.inv_eq_left_inv hMG
    have hCT : Mᴴᵀ = Mᵀᴴ := by ext i j; simp
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hGinv, ← conjTranspose_nonsing_inv, hGinv,
      transpose_mul, transpose_mul, hCT]
  · intro δ hδ hδ2 h hh k hcl
    have hat := fun w x => b_cl_at hcl w x
    have hk : k ∈ Pos L N := fun w => by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos (mat_herm k w) (by
        intro x hx
        have h1 := (Complex.pos_iff.1 ((hh w).dotProduct_mulVec_pos hx)).1
        have h2 := (abs_le.1 (hat w x)).1
        exact Complex.pos_iff.2 ⟨by nlinarith, (herm_im _ (mat_herm k w) x).symm⟩)
    refine ⟨hk, fun z => ?_⟩
    have per : ∀ w, |(star (z w) ⬝ᵥ (mat (dualH k) w *ᵥ z w)).re -
        (star (z w) ⬝ᵥ (mat (dualH h) w *ᵥ z w)).re| ≤
        2 * δ * (star (z w) ⬝ᵥ (mat (dualH h) w *ᵥ z w)).re := by
      intro w
      simp only [dualH, mat_mkHS]
      rw [b_transp, b_transp]
      have i1 := invmono (mat h w) (mat k w) (hh w) (hk w) (1 - δ) (by linarith)
        (fun x => by have := (abs_le.1 (hat w x)).1; rw [sub_mul, one_mul]; linarith) (star (z w))
      have i2 := invmono (mat k w) (mat h w) (hk w) (hh w) (1 + δ)⁻¹ (by positivity)
        (fun x => by
          rw [inv_mul_le_iff₀ (by linarith)]
          have := (abs_le.1 (hat w x)).2
          rw [add_mul, one_mul]; linarith) (star (z w))
      have hD := re_nonneg_psd (hh w).inv.posSemidef (star (z w))
      have i2' := mul_le_mul_of_nonneg_left i2 (by linarith : (0 : ℝ) ≤ 1 + δ)
      rw [← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul] at i2'
      refine abs_le.2 ⟨by nlinarith [mul_nonneg hδ hD], by nlinarith [mul_nonneg hδ hD]⟩
    unfold qR
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => per w)
  · intro δ hδ h hh k hcl w u v
    have hat := fun x => b_cl_at hcl w x
    have hA : (mat k w - mat h w).IsHermitian := (mat_herm k w).sub (mat_herm h w)
    have hb : ∀ x : Fin N → ℂ, |(star x ⬝ᵥ ((mat k w - mat h w) *ᵥ x)).re| ≤
        δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
      intro x; rw [sub_mulVec, dotProduct_sub, Complex.sub_re]; exact hat x
    have := csq _ _ hA (hh w).posSemidef δ hδ hb u v
    rw [sub_mulVec, dotProduct_sub] at this
    have ha := re_nonneg_psd (hh w).posSemidef u
    have hb' := re_nonneg_psd (hh w).posSemidef v
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg δ) ha) hb']
  · obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional (𝕜 := ℝ) (HSsub L N)
    have hent : ∀ w a b, ContDiff ℝ (⊤ : ℕ∞) (fun h : HS L N => mat h w a b) := fun w a b => by
      have e : (fun h : HS L N => mat h w a b) =
          (fun x : InfinitePlace L → Fin N → Fin N → ℂ => x w a b) ∘ (HSsub L N).subtypeL := rfl
      rw [e]
      exact (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id w) a) b).comp
        (HSsub L N).subtypeL.contDiff
    have hF : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun h : HS L N => ((dualH h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ)) (Pos L N) := by
      refine contDiffOn_pi' fun w => contDiffOn_pi' fun a => contDiffOn_pi' fun b => ?_
      intro h hh
      have hdet : (mat h w).det ≠ 0 := ((hh w).det_pos).ne'
      exact (cd_inv (fun h : HS L N => mat h w) (fun i j => hent w i j) b a h hdet).contDiffWithinAt
    have e : (dualH : HS L N → HS L N) =
        fun h => P ((dualH h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ) := by
      funext h; exact (hP (dualH h)).symm
    rw [e]
    exact P.contDiff.comp_contDiffOn hF

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GProdScale
section
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL PositivityTheory.KB PositivityTheory.KB.SmoothPartitionUnityBasic.BasicAux PositivityTheory.KB.SmoothPartitionUnityBasic.LipschitzAlgebraNorm
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

section GNrmHelpers

set_option linter.unusedSectionVars false

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private def gP (h : HS L N) : ℝ := ∏ w : InfinitePlace L, ((mat h w).det.re) ^ w.mult

private theorem g_qR_single [DecidableEq (InfinitePlace L)]
    (h : HS L N) (w : InfinitePlace L) (x : Fin N → ℂ) :
    qR h (Pi.single w x) = (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  unfold qR
  rw [Finset.sum_eq_single w (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
    (fun hw => absurd (Finset.mem_univ w) hw), Pi.single_eq_same]

private theorem g_cl_at {δ : ℝ} {h k : HS L N}
    (hcl : Cl δ h k) (w : InfinitePlace L) (x : Fin N → ℂ) :
    |(star x ⬝ᵥ (mat k w *ᵥ x)).re - (star x ⬝ᵥ (mat h w *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  classical
  have := hcl (Pi.single w x)
  rwa [g_qR_single, g_qR_single] at this

private theorem g_qR_smul (c : ℝ) (h : HS L N) (z : VR L N) : qR (c • h) z = c * qR h z := by
  rw [← evR_apply, map_smul, evR_apply, smul_eq_mul]

private theorem g_det_pos {h : HS L N} (hh : h ∈ Pos L N) (w : InfinitePlace L) : 0 < (mat h w).det.re :=
  (Complex.pos_iff.1 (hh w).det_pos).1

private theorem g_gP_pos {h : HS L N} (hh : h ∈ Pos L N) : 0 < gP h :=
  Finset.prod_pos fun w _ => pow_pos (g_det_pos hh w) _

private theorem g_prod_scale (c : ℝ) (f : InfinitePlace L → ℝ) :
    ∏ w : InfinitePlace L, (c ^ N * f w) ^ w.mult = c ^ (N * Module.finrank ℚ L) * ∏ w, f w ^ w.mult := by
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← pow_mul]

private theorem g_det_smul (r : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) : (r • M).det.re = r ^ N * M.det.re := by
  have : r • M = (r : ℂ) • M := by ext i j; simp [Complex.real_smul]
  rw [this, det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

private theorem g_gP_smul (r : ℝ) (h : HS L N) : gP (r • h) = r ^ (N * Module.finrank ℚ L) * gP h := by
  unfold gP
  simp only [mat_smul, g_det_smul]
  exact g_prod_scale r _

private theorem g_emb_val (γ : Gm L N) (w : InfinitePlace L) :
    (((emb L N γ) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  ext i j
  simp [emb, toP, toK, embO, Matrix.GeneralLinearGroup.map_apply]

private theorem g_ginv (γ : Gm L N) (w : InfinitePlace L) :
    ((((emb L N γ) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  rw [← g_emb_val, map_inv, Pi.inv_apply]

private theorem g_gP_ac (γ : Gm L N) (h : HS L N) : gP (actL (emb L N γ) h) = gP h := by
  unfold gP
  set u : L := algebraMap (𝓞 L) L ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).det with hu
  have hw : ∀ w : InfinitePlace L, (mat (actL (emb L N γ) h) w).det.re = w u ^ 2 * (mat h w).det.re := by
    intro w
    rw [mat_actL, g_ginv, det_mul, det_mul, det_conjTranspose]
    have e : (((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w)).det = w.embedding u := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [e]
    have e2 : star (w.embedding u) * (mat h w).det * w.embedding u =
        ((Complex.normSq (w.embedding u) : ℝ) : ℂ) * (mat h w).det := by
      rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]; ring
    rw [e2, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq]
  simp only [hw, mul_pow, Finset.prod_mul_distrib]
  have hn : |Algebra.norm ℚ u| = 1 := by
    have := NumberField.Units.norm L (Matrix.GeneralLinearGroup.det (γ⁻¹ : Gm L N))
    simpa [hu, Matrix.GeneralLinearGroup.val_det_apply] using this
  have hu1 : ∏ w : InfinitePlace L, (w u ^ 2) ^ w.mult = 1 := by
    rw [show (∏ w : InfinitePlace L, (w u ^ 2) ^ w.mult) = (∏ w : InfinitePlace L, w u ^ w.mult) ^ 2 by
      rw [← Finset.prod_pow]; refine Finset.prod_congr rfl fun w _ => ?_; rw [← pow_mul, ← pow_mul, mul_comm]]
    rw [InfinitePlace.prod_eq_abs_norm]
    rw [hn, Rat.cast_one, one_pow]
  rw [hu1, one_mul]

private theorem g_ent (w : InfinitePlace L) (a b : Fin N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun h : HS L N => mat h w a b) := by
  have e : (fun h : HS L N => mat h w a b) =
      (fun x : InfinitePlace L → Fin N → Fin N → ℂ => x w a b) ∘ (HSsub L N).subtypeL := rfl
  rw [e]
  exact (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id w) a) b).comp (HSsub L N).subtypeL.contDiff

private theorem g_gP_cd : ContDiff ℝ (⊤ : ℕ∞) (gP : HS L N → ℝ) := by
  unfold gP
  refine contDiff_prod fun w _ => ContDiff.pow ?_ _
  have := Complex.reCLM.contDiff.comp (cd_det (k := (⊤ : ℕ∞)) (fun h : HS L N => mat h w) (fun i j => g_ent w i j))
  simpa [Function.comp_def] using this

end GNrmHelpers

theorem pf_GNrm : GNrm := by
  intro hB L _ _ N hN
  classical
  obtain ⟨-, -, -, h4, -, -⟩ := hB L N hN
  have hd : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hNd : (0 : ℝ) < (N : ℝ) * (Module.finrank ℚ L : ℝ) := mul_pos (Nat.cast_pos.2 hN) (Nat.cast_pos.2 hd)
  set a : ℝ := ((N : ℝ) * (Module.finrank ℚ L : ℝ))⁻¹ with ha
  have ha0 : 0 < a := inv_pos.2 hNd
  have hNa : ((N * Module.finrank ℚ L : ℕ) : ℝ) * a = 1 := by
    rw [ha, Nat.cast_mul, mul_inv_cancel₀ hNd.ne']
  have hpow : ∀ c : ℝ, 0 ≤ c → (c ^ (N * Module.finrank ℚ L)) ^ a = c := fun c hc => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc, hNa, Real.rpow_one]
  refine ⟨fun h => (gP h ^ (-a)) • h, 3, by norm_num, ?c1, ?c2, ?c3, ?c4, ?c5, ?c6⟩
  · have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun h : HS L N => gP h ^ (-a)) (Pos L N) := fun h hh =>
      ((g_gP_cd (L := L) (N := N)).contDiffAt.rpow_const_of_ne (g_gP_pos hh).ne').contDiffWithinAt
    exact hs.smul (contDiff_id.contDiffOn (s := Pos L N))
  · intro h hh
    exact ⟨_, Real.rpow_pos_of_pos (g_gP_pos hh) _, rfl⟩
  · intro γ h hh
    dsimp only
    rw [ac, ac, g_gP_ac, map_smul]
  · intro r hr h hh
    dsimp only
    rw [g_gP_smul, Real.mul_rpow (by positivity) (g_gP_pos hh).le, smul_smul]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, mul_neg, hNa, Real.rpow_neg_one]
    field_simp
  · intro r hr h hh
    have hq : ∀ (c : ℝ) (k : HS L N) (y : Lat L N), q (c • k) y = c * q k y := fun c k y => by
      rw [← ev_apply, map_smul, ev_apply, smul_eq_mul]
    have hlam : ∀ (c : ℝ), 0 < c → ∀ k : HS L N, lam (c • k) = c * lam k := fun c hc k => by
      unfold lam
      simp only [hq]
      rw [Real.mul_iInf_of_nonneg hc.le]
    have hdual : dualH (r • h) = r⁻¹ • dualH h := HS_ext fun w => by
      simp only [dualH, mat_mkHS, mat_smul]
      have hdet : IsUnit (mat h w).det := (Matrix.isUnit_iff_isUnit_det _).1 (hh w).isUnit
      rw [Matrix.inv_eq_left_inv (B := r⁻¹ • (mat h w)⁻¹) (by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
          Matrix.nonsing_inv_mul _ hdet]), transpose_smul]
    unfold lamD
    rw [hdual, hlam r hr, hlam r⁻¹ (inv_pos.2 hr), mul_mul_mul_comm, mul_inv_cancel₀ hr.ne', one_mul]
  · intro δ hδ hδ4 h hh k hcl
    have hk : k ∈ Pos L N := (h4 δ hδ (by linarith) h hh k hcl).1
    have hat := fun w x => g_cl_at hcl w x
    have h1δ : 0 < 1 - δ := by linarith
    have hup : ∀ w, (mat k w).det.re ≤ (1 + δ) ^ N * (mat h w).det.re := fun w =>
      detMono _ _ (hh w) (hk w).posSemidef (1 + δ) (by linarith) (fun x => by
        have := (abs_le.1 (hat w x)).2; rw [add_mul, one_mul]; linarith)
    have hlo : ∀ w, (1 - δ) ^ N * (mat h w).det.re ≤ (mat k w).det.re := fun w => by
      have h0 := detMono _ _ (hk w) (hh w).posSemidef (1 - δ)⁻¹ (inv_pos.2 h1δ) (fun x => by
        rw [le_inv_mul_iff₀ h1δ]
        have := (abs_le.1 (hat w x)).1; rw [sub_mul, one_mul]; linarith)
      have := mul_le_mul_of_nonneg_left h0 (pow_nonneg h1δ.le N)
      rwa [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h1δ.ne', one_pow, one_mul] at this
    have hPup : gP k ≤ (1 + δ) ^ (N * Module.finrank ℚ L) * gP h := by
      unfold gP
      rw [← g_prod_scale]
      exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg (g_det_pos hk w).le _)
        (fun w _ => pow_le_pow_left₀ (g_det_pos hk w).le (hup w) _)
    have hPlo : (1 - δ) ^ (N * Module.finrank ℚ L) * gP h ≤ gP k := by
      unfold gP
      rw [← g_prod_scale]
      exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg (mul_nonneg (pow_nonneg h1δ.le N) (g_det_pos hh w).le) _)
        (fun w _ => pow_le_pow_left₀ (mul_nonneg (pow_nonneg h1δ.le N) (g_det_pos hh w).le) (hlo w) _)
    have hPh := g_gP_pos hh
    have hPk := g_gP_pos hk
    have hA2 : gP k ^ a ≤ (1 + δ) * gP h ^ a := by
      have := Real.rpow_le_rpow hPk.le hPup ha0.le
      rwa [Real.mul_rpow (by positivity) hPh.le, hpow _ (by linarith)] at this
    have hA1 : (1 - δ) * gP h ^ a ≤ gP k ^ a := by
      have := Real.rpow_le_rpow (by positivity) hPlo ha0.le
      rwa [Real.mul_rpow (by positivity) hPh.le, hpow _ h1δ.le] at this
    intro z
    dsimp only
    rw [g_qR_smul, g_qR_smul, Real.rpow_neg hPk.le, Real.rpow_neg hPh.le]
    have hH : 0 ≤ qR h z := Finset.sum_nonneg fun w _ => re_nonneg_psd (hh w).posSemidef (z w)
    exact lipAlg δ _ _ _ _ hδ hδ4 (Real.rpow_pos_of_pos hPh a) hA1 hA2 hH (hcl z)

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.PfDerB
section
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL PositivityTheory.KB PositivityTheory.KB.SmoothPartitionUnityBasic.DerivationBounds Filter Topology

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private theorem d_rel {L : Type} [Field L] [NumberField L] {N : ℕ} (g : Gp L N) (h : HS L N)
    (z : VR L N) (w : InfinitePlace L) :
    star (z w) ⬝ᵥ (mat (actL g h) w *ᵥ z w) =
      star ((((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *ᵥ z w) ⬝ᵥ
        (mat h w *ᵥ ((((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *ᵥ z w)) := by
  rw [mat_actL, star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]

private theorem d_key {L : Type} [Field L] [NumberField L] {N : ℕ} (x : Gp L N) (v : HS L N) (z : VR L N) :
    |qR (actL x v) z| ≤ N * ‖v‖ * qR (actL x (one L N).1) z := by
  unfold qR
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [d_rel, d_rel]
  have h1 : mat (one L N).1 w = 1 := rfl
  rw [h1, one_mulVec]
  refine quad_bd N (mat v w) ‖v‖ (norm_nonneg _) (fun a b => ?_) _
  exact ((norm_le_pi_norm (v.1 w a) b).trans (norm_le_pi_norm (v.1 w) a)).trans
    ((norm_le_pi_norm v.1 w).trans le_rfl)

theorem pf_DerB : DerB := by
  intro L _ _ N φ x B ε hB hε hd hl
  set p := actL x (one L N).1 with hp
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [ContinuousLinearMap.comp_apply]
  set u := actL x v with hu
  have hline : HasDerivAt (fun t : ℝ => φ (p + t • u)) ((fderiv ℝ φ p) u) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => p + t • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p
    have hD : HasFDerivAt φ (fderiv ℝ φ p) (p + (0 : ℝ) • u) := by
      simpa using hd.hasFDerivAt
    exact hD.comp_hasDerivAt (0 : ℝ) h1
  have hlim := hline.tendsto_slope_zero_right.norm
  set K : ℝ := N * ‖v‖ with hK
  have hK0 : 0 ≤ K := by positivity
  refine le_of_tendsto hlim ?_
  have hmem : Set.Ioo (0 : ℝ) (ε / (K + 1)) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hmem] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hδε : K * t ≤ ε := by
    have : (K + 1) * t < ε := by rwa [lt_div_iff₀ (by positivity), mul_comm] at ht1
    nlinarith
  have hcl : Cl (K * t) p (p + t • u) := by
    intro z
    have e : qR (p + t • u) z = qR p z + t * qR u z := by
      rw [← evR_apply, map_add (f := _), map_smul, evR_apply, evR_apply, smul_eq_mul]
    rw [e, add_sub_cancel_left, abs_mul, abs_of_pos ht0]
    have := d_key x v z
    rw [← hu, ← hp] at this
    nlinarith
  have hb := hl (K * t) (by positivity) hδε _ hcl
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul, norm_mul, norm_inv, Real.norm_eq_abs,
    abs_of_pos ht0]
  rw [inv_mul_le_iff₀ ht0]
  nlinarith

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

