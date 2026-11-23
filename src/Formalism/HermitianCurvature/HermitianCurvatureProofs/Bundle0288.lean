module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0283
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTypeNormMeas
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTrNormKB
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section aux

variable {P : M.Par}

theorem nf_evQ_toSm_le (u : MA.Qp P.r P.TT → ℂ) (q : MA.Qp P.r P.TT) : ‖MA.evQ P (MA.toSm P u) q‖ ≤ ‖u q‖ := by
  unfold MA.evQ MA.toSm
  split_ifs with h
  · exact le_rfl
  · simp

theorem nf_wq_eq (k r : ℕ) (T T' : ℝ) (x : (Fin r → ℂ) × ℂ) (hx : T * T' ≤ Complex.normSq x.2) :
    MA.wq k x (T * T') = (∏ l : Fin r, Complex.normSq (x.1 l)) * bcWeight k r T T' x := by
  unfold MA.wq bcWeight
  rw [if_pos hx, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  have hl : MA.Mdim k r l - 1 = (Formalism.QuantumDeterminants.Mdim k r l - 2) + 1 := by
    have := l.2
    unfold MA.Mdim Formalism.QuantumDeterminants.Mdim
    omega
  rw [hl, pow_mul, ← Complex.normSq_eq_norm_sq, pow_succ, mul_comm]

end aux

theorem trace_norm_bound_constant_one : NFTrNormKB := by
  intro Wp Wq _ _ _ _ _ _ P p e he
  refine ⟨1, fun H c q hq hloc hG => ?_⟩
  have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
  have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  have hon : Orthonormal ℂ (fun ρ => B.hsVec (e ρ q.1.2)) := by
    rw [orthonormal_iff_ite]
    convert (he.2 q.1.2 hζ).2.1
  have hw0 : 0 ≤ MA.wq P.k q.1 P.TT := by
    unfold MA.wq
    exact mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (Complex.normSq_nonneg _) _)
      (pow_nonneg (sub_nonneg.2 hζ.le) _)
  have hterm : ∀ ρ, ‖MA.evQ P (trJKB p e (B.JF p.T.base H) ρ) q‖ ^ 2 ≤
      MA.wq P.k q.1 P.TT *
        ‖inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1)))‖ ^ 2 := by
    intro ρ
    have h1 := nf_evQ_toSm_le (P := P) (fun q : MA.Qp P.r P.TT =>
      ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1)))) q
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (le_of_eq ?_)
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hw0]
  have hsum : ∑ ρ, ‖MA.evQ P (trJKB p e (B.JF p.T.base H) ρ) q‖ ^ 2 ≤
      MA.wq P.k q.1 P.TT * ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1))‖ ^ 2 := by
    refine (Finset.sum_le_sum fun ρ _ => hterm ρ).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hon.sum_inner_products_le _) hw0
  have hwq : MA.wq P.k q.1 P.TT =
      (∏ l : Fin P.r, Complex.normSq (q.1.1 l)) * bcWeight P.k P.r P.T P.T' q.1 :=
    nf_wq_eq P.k P.r P.T P.T' q.1 hζ.le
  have hEw0 : 0 ≤ TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) := by
    rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p H hloc]
    positivity
  have hpt := pt_le p H c
  rw [hT, hT', ENNReal.ofReal_le_ofReal_iff hEw0] at hpt
  have hkey : bcWeight P.k P.r P.T P.T' q.1 * ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1))‖ ^ 2 ≤
      TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) := by
    unfold B.gq
    rw [hq]
    exact hpt
  have hprod : ∏ l : Fin P.r, Complex.normSq (q.1.1 l) = ∏ l : Fin P.r, Complex.normSq (c l.castSucc) := by
    rw [hq]
  calc ∑ ρ, ‖MA.evQ P (trJKB p e (B.JF p.T.base H) ρ) q‖ ^ 2
      ≤ (∏ l : Fin P.r, Complex.normSq (q.1.1 l)) *
          (bcWeight P.k P.r P.T P.T' q.1 * ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1))‖ ^ 2) := by
        rw [← mul_assoc, ← hwq]
        exact hsum
    _ ≤ (∏ l : Fin P.r, Complex.normSq (q.1.1 l)) * TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) :=
        mul_le_mul_of_nonneg_left hkey (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _)
    _ = 1 * (∏ l : Fin P.r, Complex.normSq (c l.castSucc)) *
          TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) := by
        rw [hprod, one_mul]

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTypeNormMeasV
section
namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory Matrix

noncomputable section

section vec

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

def gd (p : KB.Pl P Wp Wq) (d : Fin (P.r + 1) → ℂ) : B.Mat P.k P.r :=
  bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r)))

def wq (p : KB.Pl P Wp Wq) (d : Fin (P.r + 1) → ℂ) : Fin (2 * P.r + P.k + 1) → ℂ :=
  D.prW P.k P.r p.T.base.z (D.cofR p.T.base (gd p d))

theorem vDecomp (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (d : Fin (P.r + 1) → ℂ)
    (hd : ∀ a, d a ≠ 0) (hG : 0 < TBB.Gp p (TBB.bigPt P.r d)) :
    ∃ hA ∈ UWset P.k P.r p.T.base.z, ∃ hB ∈ UWset P.k P.r p.T.base.z', ∃ l : ℂ,
      p.V F (TBB.bigPt P.r d) = Formalism.FourierDecayAlt.P.Dx2.VV.CinL p.T.base hA hB (B.JF p.T.base F (gd p d)) ∧
      hA *ᵥ wq p d = l • (p.m₀ *ᵥ p.ν') ∧ l ≠ 0 := by
  have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt d hd
  have hG' : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt d) := hG
  have h' := Formalism.FourierDecayAlt.P.exists_isotropic_frame P.k P.r Wp Wq p.T.base p.ν' p.m₀ _ p.hF hl hG'
  have hV : p.V F (TBB.bigPt P.r d) = D.orbJ p.T.base h'.choose
      (D.muR p.T.base h'.choose (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d))) F := by
    show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt d) = _
    unfold D.vecV
    rw [dite_eq_left ⟨hl, hG'⟩, dite_eq_left h']
  obtain ⟨hγ, hZγ, hDγ⟩ := h'.choose_spec
  have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (d (Fin.last P.r)) :=
    Formalism.FourierDecayAlt.P.PBM.zeta_big _ d hG'
  have hc : ∀ a : Fin P.r, d a.castSucc ≠ 0 := fun a => hd _
  have hsec := p.T.base.sec.2 _ hζ
  have hγ' : gd p d ∈ B.GV P.k P.r := bigCellMem P.k P.r _ _ hc hsec.1
  have hZγ' : Zhat P.k P.r p.T.base.z p.T.base.z' (gd p d) = D.ptMatN (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) :=
    Formalism.FourierDecayAlt.P.PBM.zhat_bigCell_pt p.T.base d hζ
  have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ]; exact hG'
  have hpos' : 0 < Gf P.k P.r p.T.base.z p.T.base.z' (gd p d) := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ']; exact hG'
  obtain ⟨s, hs, s', hs', hγs⟩ := Formalism.FourierDecayAlt.P.fibre_orbit_description P.k P.r p.T.base.z p.T.base.z'
    ⟨p.T.base.k_pos, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base⟩
    _ hγ _ hγ' hpos (hZγ.trans hZγ'.symm)
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base) hs'
  have hlaw := Formalism.FourierDecayAlt.P.Dx2.VV.orbJ_pt p.T.base (Formalism.FourierDecayAlt.P.PBJ.bigPt d) hl hγ hZγ hpos hhA hnA hfA hhB hnB
    hfB F
  have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
    Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt d hd)
  obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) hl.2 hl.1
  rw [hw] at hmono
  obtain ⟨a, ha, hpr⟩ := hDγ.1
  have hdet : (Zhat P.k P.r p.T.base.z p.T.base.z' h'.choose).det ≠ 0 :=
    Formalism.FourierDecayAlt.P.determinant_nonzero P.k P.r p.T.base.z p.T.base.z' (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base)
      (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base) _ hpos
  refine ⟨hA, hhA, hB, hhB, (a : ℂ) * (Zhat P.k P.r p.T.base.z p.T.base.z' h'.choose).det, ?_, ?_,
    mul_ne_zero (by exact_mod_cast ha.ne') hdet⟩
  · rw [hV, ← hlaw]
    show _ = Formalism.FourierDecayAlt.P.Dx2.VV.CinL p.T.base hA hB (B.JF p.T.base F (gd p d))
    rw [← hγs, hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ' hpos' hnz (hZγ'.trans hmono) F]
  · have hZ1 := Formalism.FourierDecayAlt.P.Dx2.VV.zhat_conj p.T.base hhA hnA hfA hhB hnB hfB h'.choose
    have hcof := Formalism.FourierDecayAlt.P.Dx2.VV.cofR_conj p.T.base (sA := hA * nA)
      (Formalism.FourierDecayAlt.P.Dx2.VV.mul_fix hhB hfB) hZ1
    have hzz : herm (Hpk P.k P.r) p.T.base.z p.T.base.z ≠ 0 := by
      rw [Formalism.FourierDecayAlt.P.Dx2.DF.herm_self_alt]
      have := p.T.base.T_pos
      intro h
      have h2 := congrArg Complex.re h
      simp at h2; linarith
    have hsinv := Formalism.FourierDecayAlt.P.Dx2.VV.prW_sinv p.T.base.z_mem hzz hhA hnA
      (Formalism.FourierDecayAlt.P.Dx2.VV.cofR_free p.T.base h'.choose)
    unfold wq
    rw [hγs, hcof, hsinv, hpr, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1),
      Matrix.one_mulVec]

end vec

end

end Formalism.FourierDecayAlt.P.CutBP.TNM
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_TypeNormMeas_TC
section
namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Matrix

noncomputable section

section cov

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : B.Mat k r → (W →L[ℂ] W)}

theorem tc_dOp_conj (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {g : B.Mat k r}
    (hg : g ∈ UWset k r z) {X : B.Mat k r} (hX : P.QrD.InLieW k r z X)
    (hY : P.QrD.InLieW k r z (g * X * g⁻¹)) :
    (P.QrD.dOp π (g * X * g⁻¹)).comp (π g) = (π g).comp (P.QrD.dOp π X) := by
  have hiU := WeylGroupFacts.uh_inv hg.1
  have ug := WeylGroupFacts.isUnit_of_uh hg.1
  have key : ∀ t : ℝ, (π (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)))).comp (π g) =
      (π g).comp (π (NormedSpace.exp ((t : ℂ) • X))) := by
    intro t
    have hE := P.QrD.exp_uw hX t
    have hE' := P.QrD.exp_uw hY t
    have hconj : NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g = g * NormedSpace.exp ((t : ℂ) • X) := by
      have h := P.LeftDerivativeCurves.exp_swap hiU X t
      rw [Matrix.nonsing_inv_nonsing_inv _ ug] at h
      calc NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g
          = g * (g⁻¹ * NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) * g := by
            rw [← Matrix.mul_assoc g, Matrix.mul_nonsing_inv _ ug, Matrix.one_mul]
        _ = g * (NormedSpace.exp ((t : ℂ) • X) * g⁻¹) * g := by rw [h]
        _ = g * NormedSpace.exp ((t : ℂ) • X) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ug, Matrix.mul_one]
    rw [← hπ.2 _ hE' _ hg, ← hπ.2 _ hg _ hE, hconj]
  have hd1 := P.QrD.dOp_hasDeriv hπ hc hX
  have hd2 := P.QrD.dOp_hasDeriv hπ hc hY
  let L1 : (W →L[ℂ] W) →L[ℂ] (W →L[ℂ] W) := ContinuousLinearMap.compL ℂ W W W (π g)
  let L2 : (W →L[ℂ] W) →L[ℂ] (W →L[ℂ] W) := (ContinuousLinearMap.compL ℂ W W W).flip (π g)
  have h1 := (L1.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd1
  have h2 := (L2.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd2
  have hfun : ((L2.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)))) =
      ((L1.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) := by
    funext t
    exact key t
  rw [hfun] at h2
  exact h2.unique h1

theorem tc_inWb {g : B.Mat k r} (hg : g ∈ UWset k r z) {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) :
    inWb k r (g *ᵥ w) := by
  obtain ⟨hU, hme, hms, -⟩ := P.Dx2.VV.uw_parts hg
  exact P.Dx2.DF.m0_mulVec_mem_orthogonal g hU hme hms hw

theorem tc_ecOp_conj (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {g : B.Mat k r}
    (hg : g ∈ UWset k r z) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [z] Bs)
    (a b : Fin m) :
    (P.QrD.ecOp π (Q.unitB (Hpk k r) (fun a => g *ᵥ Bs a) a b)).comp (π g) =
      (π g).comp (P.QrD.ecOp π (Q.unitB (Hpk k r) Bs a b)) := by
  have ug := WeylGroupFacts.isUnit_of_uh hg.1
  have hgB : Q.IsFrameOf k r [z] (fun a => g *ᵥ Bs a) :=
    P.Topx1.vecw_frame_map hg.1 (fun w hw => tc_inWb hg hw) (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      exact ⟨1, z, by simp, by rw [hv, one_smul, hg.2.2]⟩) hB
  obtain ⟨e1, e2, e3⟩ := P.Topx1.vecw_conj_eq hg.1 ug Bs a b
  have lY := P.QrD.frame_lie hgB a b
  have lX := P.QrD.frame_lie hB a b
  rw [e1, e2, e3] at lY
  unfold P.QrD.ecOp
  rw [e1, e2, e3, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, tc_dOp_conj hπ hc hg lX.1 lY.1, tc_dOp_conj hπ hc hg lX.2 lY.2]

theorem tc_capRep_conj (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {g : B.Mat k r}
    (hg : g ∈ UWset k r z) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [z] Bs)
    (w : ℂ) (v : W) :
    Q.capRep k r π (fun a => g *ᵥ Bs a) w (π g v) = π g (Q.capRep k r π Bs w v) := by
  have hgB : Q.IsFrameOf k r [z] (fun a => g *ᵥ Bs a) :=
    P.Topx1.vecw_frame_map hg.1 (fun w hw => tc_inWb hg hw) (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      exact ⟨1, z, by simp, by rw [hv, one_smul, hg.2.2]⟩) hB
  unfold Q.capRep
  refine P.Topx1.vecw_qmF (π g).toLinearMap _ _ (fun i j y => ?_) id id w v
  have lY := P.QrD.frame_lie hgB i j
  have lX := P.QrD.frame_lie hB i j
  simp only [ContinuousLinearMap.coe_coe]
  rw [P.QrD.ecRep_eq hπ hc lY.1 lY.2, P.QrD.ecRep_eq hπ hc lX.1 lX.2]
  have h := congrArg (fun L : W →L[ℂ] W => L y) (tc_ecOp_conj hπ hc hg hB i j)
  simpa using h

end cov

theorem type_commutation_holds : TypeComm := by
  intro PP Wp _ _ _ π z e TP hπ hc hu hk hz hTz he hez hee g hg l hl ρ
  have ug := WeylGroupFacts.isUnit_of_uh hg.1
  have hgi : g⁻¹ ∈ UWset PP.k PP.r z := WeylGroupFacts.uw_inv hg
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hl
    have : e = 0 := by
      rw [← Matrix.one_mulVec e, ← Matrix.nonsing_inv_mul _ ug, ← Matrix.mulVec_mulVec, hl, Matrix.mulVec_zero]
    rw [this] at hee
    simp [herm] at hee
  have hli : g⁻¹ *ᵥ e = l⁻¹ • e := by
    calc g⁻¹ *ᵥ e = g⁻¹ *ᵥ (l⁻¹ • (l • e)) := by rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
      _ = l⁻¹ • (g⁻¹ *ᵥ (g *ᵥ e)) := by rw [hl, Matrix.mulVec_smul]
      _ = l⁻¹ • e := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ug, Matrix.one_mulVec]
  obtain ⟨Bs₀, hB₀⟩ := Formalism.FourierDecayAlt.P.Topx1.typ_frame_exists PP.k PP.r hk z e hz hTz he hez hee
  have hB₀z : Q.IsFrameOf PP.k PP.r [z] Bs₀ := Formalism.FourierDecayAlt.P.Topx1.vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB₀

  have keep : ∀ h ∈ UWset PP.k PP.r z, ∀ c : ℂ, c ≠ 0 → h *ᵥ e = c • e →
      ∀ v, TP.E ρ (π h (TP.E ρ v)) = π h (TP.E ρ v) := by
    intro h hh c hc0 hce v
    have hB1 : Q.IsFrameOf PP.k PP.r [z, e] (fun a => h *ᵥ Bs₀ a) :=
      Formalism.FourierDecayAlt.P.Topx1.vecw_frame_map hh.1 (fun w hw => tc_inWb hh hw) (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact ⟨1, v, by simp, by rw [one_smul, hh.2.2]⟩
        · exact ⟨c⁻¹, v, by simp, by rw [hce, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩) hB₀
    refine TP.full _ hB1 ρ _ fun w => ?_
    rw [tc_capRep_conj hπ hc hh hB₀z w, TP.eigen Bs₀ hB₀ ρ w v, map_smul]
  have kg := keep g hg l hl0 hl
  have kgi := keep g⁻¹ hgi l⁻¹ (inv_ne_zero hl0) hli

  let large₂ : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (π g : Wp →ₗ[ℂ] Wp), norm_map' := hu g hg }
  have hinn : ∀ x y, inner ℂ (π g x) (π g y) = inner ℂ x y := fun x y => large₂.inner_map_map x y
  have hgg : ∀ y, π g (π g⁻¹ y) = y := by
    intro y
    rw [← ContinuousLinearMap.comp_apply, ← hπ.2 _ hg _ hgi, Matrix.mul_nonsing_inv _ ug, hπ.1]
    rfl
  set E := TP.E ρ with hE
  have hEE : ∀ x, E (E x) = x - (x - E x) := by
    intro x; simp only [sub_sub_cancel]
    exact congrArg (fun L : Wp →L[ℂ] Wp => L x) (TP.idem ρ)
  have hker : ∀ y, E y = 0 → E (π g y) = 0 := by
    intro y hy
    have horth : ∀ u, inner ℂ (π g y) (E u) = 0 := by
      intro u
      calc inner ℂ (π g y) (E u) = inner ℂ (π g y) (π g (π g⁻¹ (E u))) := by rw [hgg]
        _ = inner ℂ y (π g⁻¹ (E u)) := hinn _ _
        _ = inner ℂ y (E (π g⁻¹ (E u))) := by rw [kgi u]
        _ = inner ℂ (E y) (π g⁻¹ (E u)) := (TP.selfAdj ρ _ _).symm
        _ = 0 := by rw [hy, inner_zero_left]
    have hidem : E (E (π g y)) = E (π g y) := congrArg (fun L : Wp →L[ℂ] Wp => L (π g y)) (TP.idem ρ)
    have h0 : inner ℂ (E (π g y)) (E (π g y)) = 0 := by
      rw [TP.selfAdj ρ, hidem, horth]
    exact inner_self_eq_zero.1 h0
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  have hidem : E (E x) = E x := congrArg (fun L : Wp →L[ℂ] Wp => L x) (TP.idem ρ)
  have hsplit : x = E x + (x - E x) := by abel
  have hy : E (x - E x) = 0 := by rw [map_sub, hidem, sub_self]
  conv_lhs => rw [hsplit, map_add (f := _), map_add (f := _), hker _ hy, add_zero, kg x]

end

end Formalism.FourierDecayAlt.P.CutBP.TNM
end

