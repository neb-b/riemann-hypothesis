module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0108
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0120
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0123
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0121
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0119
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0122
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCLat
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCBlk
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBBLiftV

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFKap
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

open Classical

theorem lagrange_all {T : Type} [Fintype T] (K : (T → ℂ) → Prop) (hc : ∀ c : ℂ, K fun _ => c)
    (hadd : ∀ f g, K f → K g → K (f + g)) (hmul : ∀ f g, K f → K g → K (f * g))
    (x : T → ℂ) (hx : K x) (hinj : Function.Injective x) : ∀ f, K f := by
  classical
  have hsum : ∀ (ι : Type) (s : Finset ι) (g : ι → T → ℂ), (∀ i ∈ s, K (g i)) → K (∑ i ∈ s, g i) := by
    intro ι s g
    refine Finset.induction_on s ?_ ?_
    · intro _
      rw [Finset.sum_empty]
      exact hc 0
    · intro a s ha ih hg
      rw [Finset.sum_insert ha]
      exact hadd _ _ (hg a (Finset.mem_insert_self a s)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
  have hprod : ∀ (ι : Type) (s : Finset ι) (g : ι → T → ℂ), (∀ i ∈ s, K (g i)) → K (∏ i ∈ s, g i) := by
    intro ι s g
    refine Finset.induction_on s ?_ ?_
    · intro _
      rw [Finset.prod_empty]
      exact hc 1
    · intro a s ha ih hg
      rw [Finset.prod_insert ha]
      exact hmul _ _ (hg a (Finset.mem_insert_self a s)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
  intro f
  have key : f = ∑ t, (fun _ : T => f t) *
      ∏ s ∈ Finset.univ.erase t, ((x + fun _ : T => -x s) * fun _ : T => (x t - x s)⁻¹) := by
    funext u
    simp only [Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Pi.add_apply]
    rw [Finset.sum_eq_single u]
    · rw [Finset.prod_eq_one, mul_one]
      intro s hs
      have hne : x u - x s ≠ 0 := sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hs) (hinj h).symm)
      rw [← sub_eq_add_neg, mul_inv_cancel₀ hne]
    · intro t _ htu
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm htu, Finset.mem_univ u⟩), mul_zero]
      rw [add_neg_cancel, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ u) h
  rw [key]
  exact hsum _ _ _ fun t _ => hmul _ _ (hc _) (hprod _ _ _ fun s _ => hmul _ _ (hadd _ _ hx (hc _)) (hc _))

section main

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GT

theorem quadratic_kappa_identity : GQKap := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hQ
  obtain ⟨hpl, hL, -, -, -⟩ := hA
  have hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT :=
    fun Φ ρ => radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  have hP : P.OK := hpl.1
  have hz := fun q => (sec_pt P Bs hpl q).2
  have hgg : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    show ((MA.coordQ (r := P.r) (TT := P.TT) M.vz : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q *
        ((MA.coordQ (r := P.r) (TT := P.TT) M.vzb : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q - (P.TT : ℂ) = _
    rw [coordQ_vz, coordQ_vzb]
  have hggv : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q ≠ 0 :=
    fun q => by rw [hgg]; exact gg_ne P q
  have hGG : ∀ q : MA.Qp P.r P.TT, ((Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) : ℝ) : ℂ) =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    rw [Complex.mul_conj]
    unfold Q.GGl
    rw [hz q, hpl.2.2.2.1, hpl.2.2.2.2.1]
    have hT : ((P.TT : ℝ) : ℂ) = (P.T : ℂ) * (P.T' : ℂ) := by
      show (((P.T * P.T' : ℝ)) : ℂ) = _
      push_cast; ring
    rw [hT]
    push_cast
    ring
  have hsc : ∀ (w : (MA.DQ P).Pr) (f : M.Ty P → MA.SmQ P.r P.TT),
      MA.actA P (MA.sc P (MA.DQ P) w) f = fun ρ => w.1 (f ρ) := VLem.actA_sc P
  have hGGi : Intw P Bs e d.L.GGi (MA.ggiA P (MA.DQ P)) := by
    intro Φ
    rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 5 (Ring.inverse (ggS P))
      (fun q => by rw [inverse_apply _ hggv]; exact inv_ne_zero (hggv q))
      (fun q => by rw [inverse_apply _ hggv, hgg]; show ((Q.GGl _ _ _ _ _ : ℝ) : ℂ)⁻¹ = _; rw [hGG q]) Φ).trans ?_
    exact (hsc ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ)).symm
  have hTT : 0 ≤ P.TT := (mul_pos hP.T_pos hP.T'_pos).le
  haveI : Fact ((MA.DQ P).Laws P.TT) := ⟨Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT⟩
  have hx : ∀ Y : ℝ, Intw P Bs e (d.κ fun ρ => M.xC P ρ (Y : ℂ)) (MA.kap P (MA.DQ P) fun ρ => M.xC P ρ (Y : ℂ)) := by
    intro Y
    have h1 := intw_mul hsm hGGi (hQ Y 1 1)
    have e1 : d.L.GGi * d.QQ (Y : ℂ) 1 1 = d.κ fun ρ => M.xC P ρ (Y : ℂ) := by
      show d.L.GGi * (d.L.GG * d.x (Y : ℂ)) = _
      rw [← mul_assoc, d.L.GGi_GG, one_mul]; rfl
    have e2 : MA.ggiA P (MA.DQ P) * MA.QQr P (MA.DQ P) (Y : ℂ) 1 1 = MA.kap P (MA.DQ P) fun ρ => M.xC P ρ (Y : ℂ) := by
      show MA.ggiA P (MA.DQ P) * (MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) (Y : ℂ)) = _
      rw [← mul_assoc, Formalism.FourierDecayAlt.P.MAx1.D5.ggi_gg, one_mul]; rfl
    rw [e1, e2] at h1; exact h1
  obtain ⟨Y₀, hinj⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hP
  refine lagrange_all (fun f => Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)) ?_ ?_ ?_ _ (hx Y₀) hinj
  · intro c
    have e1 : d.κ (fun _ => c) = algebraMap ℂ _ c := d.κ.commutes c
    have e2 : MA.kap P (MA.DQ P) (fun _ => c) = algebraMap ℂ _ c := (MA.kap P (MA.DQ P)).commutes c
    show Intw P Bs e (d.κ (fun _ => c)) (MA.kap P (MA.DQ P) (fun _ => c))
    rw [e1, e2]; exact intw_alg hsm c
  · intro f g hf hg
    show Intw P Bs e (d.κ (f + g)) (MA.kap P (MA.DQ P) (f + g))
    rw [map_add (f := _), map_add (f := _)]; exact intw_add hsm hf hg
  · intro f g hf hg
    show Intw P Bs e (d.κ (f * g)) (MA.kap P (MA.DQ P) (f * g))
    rw [map_mul, map_mul]; exact intw_mul hsm hf hg

end main

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FibreIntegralCells
section
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.FK

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ}

theorem gPoly_of (TT : ℝ) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    PBI.gPoly TT (Matrix.of (Matrix.of.symm M : G.Mat (r + 1))) = PBI.gPoly TT M := rfl

private theorem det_eq_one_of_lower_unitriangular' {m : ℕ} {L : Matrix (Fin m) (Fin m) ℂ} (h0 : ∀ i j, i < j → L i j = 0)
    (h1 : ∀ i, L i i = 1) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L (fun i j hij => h0 i j hij)]
  simp [h1]

private theorem det_eq_one_of_upper_unitriangular {m : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (h0 : ∀ i j, j < i → U i j = 0)
    (h1 : ∀ i, U i i = 1) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h0 i j hij)]
  simp [h1]

theorem gPoly_LU (TT : ℝ) {L M U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hL : L ∈ C2.LTset (r + 1))
    (hU : U ∈ C2.UTset (r + 1)) : PBI.gPoly TT (L * M * U) = PBI.gPoly TT M := by
  obtain ⟨hL0, hL1⟩ := hL
  obtain ⟨hU0, hU1⟩ := hU

  have hsub : (L * M * U).submatrix Fin.castSucc Fin.castSucc =
      L.submatrix Fin.castSucc Fin.castSucc * M.submatrix Fin.castSucc Fin.castSucc *
        U.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_castSucc,
      hL0 (Fin.castSucc i) (Fin.last r) (Fin.castSucc_lt_last i),
      hU0 (Fin.last r) (Fin.castSucc j) (Fin.castSucc_lt_last j), zero_mul, mul_zero, add_zero]
  have hL' : (L.submatrix Fin.castSucc Fin.castSucc).det = 1 :=
    det_eq_one_of_lower_unitriangular' (fun i j h => hL0 _ _ (Fin.castSucc_lt_castSucc_iff.mpr h)) (fun i => hL1 _)
  have hU' : (U.submatrix Fin.castSucc Fin.castSucc).det = 1 :=
    det_eq_one_of_upper_unitriangular (fun i j h => hU0 _ _ (Fin.castSucc_lt_castSucc_iff.mpr h)) (fun i => hU1 _)
  unfold PBI.gPoly
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_eq_one_of_lower_unitriangular' hL0 hL1,
    det_eq_one_of_upper_unitriangular hU0 hU1, hL', hU']
  simp

theorem gPoly_pt (TT : ℝ) (a : C.LPt) : PBI.gPoly TT (D.ptMatN a (r + 1)) = D.ptG TT r a := by
  have h : (D.ptMatN a (r + 1)).submatrix Fin.castSucc Fin.castSucc = D.ptMatN a r := by
    ext i j
    rfl
  unfold PBI.gPoly D.ptG
  rw [h]

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.FK

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.StabilizerDisintegration Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD

theorem fibre_integral_cells : PBI.FibIntCells := by
  intro Wp Wq _ _ _ _ _ _ P p
  set S := p.T.base with hS
  have hz : C2.StdZ P.k P.r S.z := ⟨S.z_mem, S.T_pos⟩
  have hz' : C2.StdZ P.k P.r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  obtain ⟨μ0, hμ0⟩ := exists_haar_stabilizer P.k P.r S.z hz
  obtain ⟨μ0', hμ0'⟩ := exists_haar_stabilizer P.k P.r S.z' hz'
  obtain ⟨c1, hc1, hN1⟩ := disintN P.k P.r S.z hz μ0 S.μN hμ0 S.haarN
  obtain ⟨c2, hc2, hN2⟩ := disintN P.k P.r S.z' hz' μ0' S.μN hμ0' S.haarN
  refine ⟨μ0, μ0', (((c1 * c2 : NNReal) : ℝ) : ℂ), hμ0, hμ0', ?_⟩
  intro sec hsec F hF a σ d ha hm
  obtain ⟨hw, hd0⟩ := Dx2.VV.ptMatN_monoP' a (P.r + 1) ha.2 ha.1
  set w := ha.2 ▸ D.ptPerm a with hwdef
  set d0 := ha.2 ▸ D.ptDiag a with hd0def
  obtain ⟨e, hemp, he⟩ := splitUT (P.r + 1) w
  have hPT := phiTopCoords (P.r + 1) σ w d d0 (Wq →L[ℂ] Wp)
    ((((c1 * c2 : NNReal) : ℝ) : ℂ) • PBI.phi0 S μ0 μ0' sec F) hd0 (hm.trans hw)
  rw [hPT]
  set TT := Tz P.k P.r S.z * Tz P.k P.r S.z' with hTT
  have hgP : ∀ Y : (C2.LPidx w → ℂ) × (G.UT (P.r + 1) → ℂ),
      PBI.gPoly TT (lowP w Y.1 * C2.monoP w d0 * G.upper Y.2) = D.ptG TT P.r a := by
    intro Y
    rw [FK.gPoly_LU TT (UC.lowerUnipotent_mem w Y.1).1 (UC.upper_mem Y.2), ← hw, FK.gPoly_pt]
  show D.vecV S p.ν' p.m₀ F a = _
  by_cases hG : 0 < D.ptG TT P.r a
  · obtain ⟨σ0, hE⟩ := Dx2.VV.exE S p.ν' p.m₀ p.hF a ha hG
    have hγe := hE.1
    have hZe := hE.2.1
    have hDe := hE.2.2.1
    set γ0 := p.m₀ * σ0 with hγ0
    have hV := isotropic_vectors_linear_indep P.k P.r Wp Wq S p.ν' p.m₀ F a ha γ0 p.hF hG hγe hZe hDe
    rw [hV]
    have hZw : Zhat P.k P.r S.z S.z' γ0 = C2.monoP w d0 := hZe.trans hw
    have hpos : 0 < Gf P.k P.r S.z S.z' γ0 := by
      rw [← ptG_spec P.k P.r S.z S.z' a _ ha hZe]; exact hG
    have hrel := relevant_points_holds P.k P.r Wp Wq S a γ0 ha hγe hZe
    obtain ⟨θ1, hθ1, hint1⟩ := CV.orbJConv_cpt S γ0 w d0 F hγe hrel hd0 hZw hpos hF
    have hex : ∃ θ, D.IsNormCut S γ0 (D.muR S γ0 w) θ ∧
        Integrable (fun q => θ q • D.orbIntegrand S γ0 F q) S.μSS := ⟨θ1, hθ1, hint1⟩
    unfold D.orbJ
    rw [dite_eq_left hex]
    obtain ⟨hθ, hint⟩ := hex.choose_spec
    obtain ⟨hI, hEq⟩ := OG.orb_int S hγe hd0 hZw hpos hrel e hemp he hμ0 hμ0' hc1 hc2 hN1 hN2 F _ hθ hint
    rw [hEq, OJ.cell_int S γ0 w hμ0 hμ0' F hI, RCLike.real_smul_eq_coe_smul (K := ℂ), ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    simp only [Pi.smul_apply]
    rw [smul_comm]
    congr 2
    have hZp : 0 < PBI.gPoly TT (Matrix.of (Matrix.of.symm (lowP w Y.1 * C2.monoP w d0 * G.upper Y.2) :
        G.Mat (P.r + 1))) := by
      rw [FK.gPoly_of, hgP Y]; exact hG
    unfold PBI.phi0
    rw [if_pos hZp]
    obtain ⟨hsG, hsZ, hsD⟩ := hsec.2 _ hZp
    have hv := lowPH_UT (w := w) Y.1
    have hu := UC.upper_mem Y.2
    have hZ1 : Zhat P.k P.r S.z S.z' ((C2.tauM P.k P.r S.z (lowP w Y.1)ᴴ)⁻¹ * γ0 *
        C2.tauM P.k P.r S.z' (G.upper Y.2)) = lowP w Y.1 * C2.monoP w d0 * G.upper Y.2 := by
      rw [Formalism.FourierDecayAlt.P.zhat_equivalence P.k P.r S.z S.z' hz hz' _ (A.n_in_S (A.tau_N hz hv)) _
          (A.n_in_S (A.tau_N hz' hu)) γ0,
        (Formalism.FourierDecayAlt.P.c2_tau_mem P.k P.r S.z hz _ hv).2.2, (Formalism.FourierDecayAlt.P.c2_tau_mem P.k P.r S.z' hz' _ hu).2.2,
        Matrix.conjTranspose_conjTranspose, hZw]
    symm
    exact FB.fib_indep S p.ν' p.m₀ p.hF a ha hG hE hμ0 hμ0' F hv hu hsG (hsZ.trans hZ1.symm) hsD
  · have h0 : D.vecV S p.ν' p.m₀ F a = 0 := by
      unfold D.vecV; rw [dite_eq_right (fun h => hG h.2)]
    rw [h0]
    symm
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun Y => ?_)
    simp only [Pi.smul_apply, Pi.zero_apply]
    unfold PBI.phi0
    rw [if_neg (by rw [FK.gPoly_of, hgP Y]; exact hG), smul_zero, smul_zero]

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroPointOver
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def levelZeroPointOver {k r : ℕ} (a : C.LPt) (hle : D.ptSize a ≤ r) (g : B.Mat k (r - D.ptSize a)) : B.Mat k r :=
  D.castM (by omega) (U.mMap k (D.ptSize a) (r - D.ptSize a) (U.hMat (D.ptPerm a) (D.ptDiag a)) g)

def LeftFubini : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (T : D.LevTower k r Wp Wq),
    D.TowerNormalised T → ∀ (j : ℕ) (hj : j ≤ r), 1 ≤ j → ∀ (a : C.LPt) (ha : D.IsLocPt a j),
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (ℓ : X → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) (sx : X → B.Mat k r),
      (∀ x, sx x ∈ Sset k r T.base.z) ∧
      ∀ g ∈ JF.Om k (r - j) (T.bs j).z (T.bs j).z', ∀ H : B.Mat k r → (Wq →L[ℂ] Wp),
        ContinuousOn H {x | x ∈ B.GV k r ∧ Dmin k r T.base.z T.base.z' x ⟨j, by omega⟩ ≠ 0} →
        (∃ R : ℝ, ∀ x ∈ B.GV k r, H x ≠ 0 → B.gN x ≤ R) →
        Integrable (fun x => ℓ x (PBG.Kr T.base H (sx x * levelZeroPointOver a (by rw [ha.2]; exact hj)
          (D.castM (by rw [ha.2]) g)))) μ ∧
        B.JF (T.bs j) (D.castF (by rw [ha.2]) (D.sliceAt k r T.base.z T.base.z' H a)) g =
          ∫ x, ℓ x (PBG.Kr T.base H (sx x * levelZeroPointOver a (by rw [ha.2]; exact hj) (D.castM (by rw [ha.2]) g))) ∂μ

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableEmbeddingLevM
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

def projM (y : Mt k (1 + ρ)) : Mt k ρ := fun a b => y ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩

theorem projM_levM (x : Mt k ρ) : projM (B2.levM k ρ x) = x := by
  funext a b
  simp only [projM, B2.levM, ιLev, Matrix.of_apply]
  rw [dite_eq_left ⟨by omega, by omega⟩, dite_eq_left ⟨by omega, by omega⟩]
  rfl

theorem continuous_levM : Continuous (B2.levM k ρ) := by
  exact Formalism.FourierDecayAlt.P.LongWeylElement.levM_cont k ρ

theorem continuous_projM : Continuous (projM (k := k) (ρ := ρ)) := by
  unfold projM
  fun_prop

theorem measurableEmbedding_levM : MeasurableEmbedding (B2.levM k ρ) := by
  refine MeasurableEmbedding.of_measurable_inverse continuous_levM.measurable ?_
    continuous_projM.measurable (fun x => projM_levM x)
  have hr : Set.range (B2.levM k ρ) = {y | B2.levM k ρ (projM y) = y} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      simp only [Set.mem_setOf_eq, projM_levM]
    · intro hy
      exact ⟨projM y, hy⟩
  rw [hr]
  exact (isClosed_eq (continuous_levM.comp continuous_projM) continuous_id).measurableSet

theorem zWeight_fin (T T' R : ℝ) :
    ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ) < ⊤ := by
  have hC : ∀ ζ ∈ Metric.closedBall (0 : ℂ) R,
      ENNReal.ofReal (B2.zWeight k T T' ζ) ≤ ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) := by
    intro ζ hζ
    apply ENNReal.ofReal_le_ofReal
    have hn : ‖ζ‖ ≤ R := by simpa using hζ
    have hns : Complex.normSq ζ ≤ R ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    simp only [B2.zWeight]
    split_ifs with h
    · apply pow_le_pow_left₀ (by linarith)
      linarith [neg_abs_le (T * T')]
    · positivity
  calc ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ)
      ≤ ∫⁻ _ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) :=
        setLIntegral_mono' measurableSet_closedBall hC
    _ = ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) * MeasureTheory.volume (Metric.closedBall (0 : ℂ) R) :=
        setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

section pair

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem pairAt_tr {t : ℂ} (ht : t ≠ 0) {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hmap : μs.map (B2.levM k ρ) = μ) (Φ Ψ : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (c : Fin ρ → ℂ) :
    P5.pairAt μs (trL ht z z' π π' Φ) (trL ht z z' π π' Ψ) c = P5.pairAt μ Φ Ψ (consC t c) := by
  subst hmap
  simp only [P5.pairAt]
  rw [measurableEmbedding_levM.integral_map]
  rfl

end pair

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCLoc
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def LocSup (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (n b : ℕ) (a : List C.Letter) (h : C.LPt) : Prop :=
  ∃ B : ℝ, ∀ t : ℂ, t ≠ 0 → ‖KB.gN S v ε (b + n - 1) a (h ++ [(n, t)]) (h ++ [(n, t)])‖ ≤ B

theorem psd_single_one {α : Type} (h : α) : TB.PSDOn ({h} : Finset α) (fun _ _ => (1 : ℂ)) := by
  unfold TB.PSDOn
  have hA : (Matrix.of fun (x y : ↥({h} : Finset α)) => (1 : ℂ)) =
      (Matrix.of fun (_ : ↥({h} : Finset α)) (_ : Unit) => (1 : ℂ)) *
        Matrix.conjTranspose (Matrix.of fun (_ : ↥({h} : Finset α)) (_ : Unit) => (1 : ℂ)) := by
    ext x y
    simp [Matrix.mul_apply]
  rw [hA]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem dlB_pos (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (b s : ℕ) : 0 < KB.dlB S b s := by
  have hd : (0 : ℝ) < ((|discr E| : ℤ) : ℝ) := by
    have := NumberField.discr_ne_zero E
    exact_mod_cast abs_pos.2 this
  have hrd : 0 < S6.rd E := Real.rpow_pos_of_pos hd _
  unfold KB.dlB D.deG
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  refine div_pos ?_ (div_pos two_pos (mul_pos hrd (pow_pos hg' 3)))
  first
  | exact pow_pos hrd _
  | exact zpow_pos hrd _
  | exact Real.rpow_pos_of_pos hrd _

theorem exists_word_of_admissible_at_place (S : C.HidaSetting E Wp Wq) {v : Fin S.f} {a : List C.Letter} (ha : D.AdmAt S v a) :
    ∃ w : S.W, w.1 v = a := ha

theorem locSup_one (S : C.HidaSetting E Wp Wq) (hI : KB.IntAll S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (b : ℕ)
    (hb : 1 ≤ b) (hbr : b ≤ S.G.r + 1) (a : List C.Letter) (ha : D.AdmAt S v a) (h : C.LPt)
    (hh : D.ptSize h = b - 1) : LocSup S v ε 1 b a h := by
  obtain ⟨w, hw⟩ := exists_word_of_admissible_at_place S ha
  obtain ⟨φ, -, hφ, ⟨Cφ, hCφ⟩, -⟩ := hI v ε hε b hb hbr w h h hh hh
  refine ⟨|Cφ| * ‖((S.sizeAt v a : ℝ) : ℂ)‖⁻¹, fun t ht => ?_⟩
  have hb1 : b + 1 - 1 = b := Nat.add_sub_cancel b 1
  unfold KB.gN
  rw [hb1, norm_div, div_eq_mul_inv, ← hw, ← hφ t ht]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
  have h1 : ((1 + ‖t‖) ^ 3)⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg t]))
  have h2 : 0 ≤ ((1 + ‖t‖) ^ 3)⁻¹ := inv_nonneg.2 (by positivity)
  calc ‖φ t‖ ≤ Cφ * ((1 + ‖t‖) ^ 3)⁻¹ := hCφ t
    _ ≤ |Cφ| * ((1 + ‖t‖) ^ 3)⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self _) h2
    _ ≤ |Cφ| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |Cφ| := mul_one _

theorem mL_one (K : ℕ) (L : ℝ) (σ : crystallineComparison.V 1) : crystallineComparison.mL K (fun _ => L) σ = crystallineComparison.mfac K L ‖σ 0‖ := by
  simp [crystallineComparison.mL]

theorem offdiag_bound {Z : Type} (w : Z → Z → ℂ) (a b : Z → Z → ℂ) (p : Z) (Y : Finset Z) (hp : p ∈ Y)
    (hB : KB.BlockPSD Y Y a w b) (Ba Bb : ℝ) (ha : (a p p).re ≤ Ba) (hb : (b p p).re ≤ Bb) :
    ‖w p p‖ ^ 2 ≤ Ba * Bb := by
  have hpsd := hB
  unfold KB.BlockPSD TB.PSDOn at hpsd
  let f : Fin 2 → ↥(Y.disjSum Y) := ![⟨Sum.inl p, by simp [hp]⟩, ⟨Sum.inr p, by simp [hp]⟩]
  have hs := hpsd.submatrix f
  have hdet := hs.det_nonneg
  have hd0 := hs.diag_nonneg (i := 0)
  have hd1 := hs.diag_nonneg (i := 1)
  rw [Matrix.det_fin_two] at hdet
  simp [f, Matrix.submatrix_apply] at hdet hd0 hd1
  rw [Complex.le_def] at hdet
  rw [Complex.nonneg_iff] at hd0 hd1
  have hw : ‖w p p‖ ^ 2 ≤ (a p p).re * (b p p).re := by
    have h3 := hdet.1
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, ← hd0.2, ← hd1.2] at h3
    nlinarith [h3]
  calc ‖w p p‖ ^ 2 ≤ (a p p).re * (b p p).re := hw
    _ ≤ Ba * Bb := mul_le_mul ha hb hd1.1 (le_trans hd0.1 ha)

end

end Formalism.FourierDecayAlt.P.PBC
end

