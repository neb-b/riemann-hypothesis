module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0178
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0163
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0174
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0055
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0177
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0168
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0114
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSquareIntegrableHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0170
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0162
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABStar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0057

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastMCastM
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem asm_omLong_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (β : ℂ) (Φ : G.Mat 1 → V) (z : ℂ) :
    G.OmLong β 0 Φ z = Φ (fun _ _ => z) := by
  unfold G.OmLong
  have : IsEmpty (G.UT (0 + 1)) := ⟨fun q => by have h := q.2; rw [Fin.lt_def] at h; omega⟩
  have hμ : G.muPi β (G.UT (0 + 1)) = Measure.dirac (fun q => isEmptyElim q) := Measure.pi_of_empty _ _
  rw [hμ, integral_dirac]
  have h1 : G.superSum (G.upper (fun q : G.UT (0 + 1) => isEmptyElim q)) = 0 := by
    simp [G.superSum]
  have h2 : (G.ptLong (0 + 1) z * G.upper (fun q : G.UT (0 + 1) => isEmptyElim q) : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.of fun _ _ => z := by
    ext i j
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    have hj : j = 0 := Fin.ext (by have := j.isLt; simp)
    subst hi hj
    simp [G.ptLong, G.wMat, G.upper, G.strictUpper, Matrix.mul_apply]
  rw [h1, h2]
  simp [G.psi]
  rfl

theorem asm_psi_cast {a b : ℕ} (h : a = b) (z : Fin (2 * a + k + 1) → ℂ) (cc : ℂ) (g : B.Mat k a) :
    psi k b (D.castV h z) cc (D.castM h g) = psi k a z cc g := by
  subst h; rw [P.JCTx5.castV_rfl, P.JCTx5.castM_rfl]

theorem asm_castM_mul {a b : ℕ} (h : a = b) (g g' : B.Mat k a) : D.castM h (g * g') = D.castM h g * D.castM h g' := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_castM_inv {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h g⁻¹ = (D.castM h g)⁻¹ := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_castM_castM {a b d : ℕ} (h1 : a = b) (h2 : b = d) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM (h1.trans h2) g := by
  subst h1; subst h2; rfl

theorem asm_castM_symm {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h.symm (D.castM h g) = g := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_lowV_lift (a ρ m r : ℕ) (hm : 1 + ρ = m) (h1 : a + m = r) (h5 : a + 1 + ρ = a + (1 + ρ))
    (er : r = a + 1 + ρ) (zj : Fin (2 * m + k + 1) → ℂ) :
    U.lowV k a (1 + ρ) (D.castV h5 (D.castV er (D.castV h1 (liftVec k a m zj)))) = D.castV hm.symm zj := by
  subst hm; subst h1
  funext i
  simp only [U.lowV, D.castV, liftVec, Fin.val_cast]
  rw [dite_eq_left (by omega)]
  congr 1; ext; simp

theorem asm_phiFun_lev {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {a r ρa ρb : ℕ} (e : ρa = ρb)
    (ha : r = a + 0 + ρa) (hb : r = a + 0 + ρb) (σ : Equiv.Perm (Fin a)) (d : Fin a → ℂ)
    (z0 z0' : Fin (2 * r + k + 1) → ℂ) (F0 : B.Mat k r → E) (g : B.Mat k ρa) :
    U.PhiFun (s := 0) k ρa σ d (D.castV ha z0) (D.castV ha z0') (D.castF ha.symm F0) (fun q => q.elim0) g =
      U.PhiFun (s := 0) k ρb σ d (D.castV hb z0) (D.castV hb z0') (D.castF hb.symm F0) (fun q => q.elim0)
        (D.castM e g) := by
  subst e; rw [P.JCTx5.castM_rfl]

theorem asm_bridge {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (a ρ1 ρ2 m r : ℕ) (e12 : ρ1 = ρ2) (e : ρ2 + 1 = m) (er : r = a + 1 + ρ1)
    (σ : Equiv.Perm (Fin a)) (d : Fin a → ℂ)
    (zb zb' : Fin (2 * r + k + 1) → ℂ) (zj zj' : Fin (2 * m + k + 1) → ℂ)
    (hzj : D.castV (show a + m = r by omega) (liftVec k a m zj) = zb)
    (hzj' : D.castV (show a + m = r by omega) (liftVec k a m zj') = zb')
    (Fb : B.Mat k r → E) (c : ℂ) (γ : B.Mat k ρ2)
    (zA zA' : Fin (2 * (a + 1 + ρ1) + k + 1) → ℂ) (hzA : zA = D.castV er zb) (hzA' : zA' = D.castV er zb')
    (FA : B.Mat k (a + 1 + ρ1) → E) (hFA : FA = D.castF er.symm Fb) (γ1 : B.Mat k ρ1)
    (hγ1 : γ1 = D.castM e12.symm γ) :
    ∫ yy : U.RC k 1 ρ1 × U.RC k 1 ρ1,
        (psi k (1 + ρ1) (U.lowV k a (1 + ρ1) (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA)) cStd
            (U.Rn k 1 ρ1 yy.1) *
          star (psi k (1 + ρ1) (U.lowV k a (1 + ρ1) (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA')) cStd
            (U.Rn k 1 ρ1 yy.2))) •
        U.PhiFun (p := a) (s := 0) k (1 + ρ1) σ d (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA)
          (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA') (D.castF (by omega : a + (1 + ρ1) = a + 1 + ρ1) FA)
          (fun q => q.elim0)
          ((U.Rn k 1 ρ1 yy.1)⁻¹ * U.mMap k 1 ρ1 (Matrix.of fun _ _ => c) γ1 * U.Rn k 1 ρ1 yy.2)
        ∂((U.muRC k 1 ρ1).prod (U.muRC k 1 ρ1)) =
      ∫ xx : U.RC k 1 ρ2 × U.RC k 1 ρ2,
        (psi k m zj cStd (rn1 e xx.1) * star (psi k m zj' cStd (rn1 e xx.2))) •
          U.PhiFun (p := a) (s := 0) k (r - a) σ d (D.castV (by omega : r = a + 0 + (r - a)) zb)
            (D.castV (by omega : r = a + 0 + (r - a)) zb') (D.castF (by omega : a + 0 + (r - a) = r) Fb)
            (fun q => q.elim0)
            (D.castM (by omega : m = r - a) ((rn1 e xx.1)⁻¹ * mc e c γ * rn1 e xx.2))
        ∂((U.muRC k 1 ρ2).prod (U.muRC k 1 ρ2)) := by
  subst e12; subst e; subst hzA; subst hzA'; subst hFA; subst hγ1; subst er
  rw [P.JCTx5.castM_rfl]
  refine integral_congr_ae (Filter.Eventually.of_forall fun xx => ?_)
  simp only [rn1, mc, P.JCTx5.castM_rfl]
  have hl := asm_lowV_lift (k := k) a ρ1 (ρ1 + 1) (a + 1 + ρ1) (by omega) (by omega) (by omega) rfl zj
  have hl' := asm_lowV_lift (k := k) a ρ1 (ρ1 + 1) (a + 1 + ρ1) (by omega) (by omega) (by omega) rfl zj'
  subst hzj; subst hzj'
  rw [hl, hl', ← asm_psi_cast (Nat.add_comm 1 ρ1) _ _ (U.Rn k 1 ρ1 xx.1),
    ← asm_psi_cast (Nat.add_comm 1 ρ1) _ _ (U.Rn k 1 ρ1 xx.2)]
  congr 1
  rw [← asm_castM_inv, ← asm_castM_mul, ← asm_castM_mul, asm_castM_castM]
  exact asm_phiFun_lev (by omega) _ _ σ d _ _ _ _

theorem asm_pointStepT (hPS : PointStep) : PointStepT := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h c hh hc hF γ hγ
  obtain ⟨hhb, rfl⟩ := hh
  have hc0 : c ≠ 0 := (hc.1 (1, c) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hP' : D.ptSize (h ++ [(1, c)]) = D.ptSize h + 1 := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h 1 c
  have hloc : D.IsLocPt (h ++ [(1, c)]) (D.ptSize (h ++ [(1, c)])) := ⟨hc.1, rfl⟩
  have hlocH : D.IsLocPt h (D.ptSize h) := ⟨hhb, rfl⟩
  have hle : D.ptSize (h ++ [(1, c)]) ≤ P.r := by omega
  have e2 : D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)])) = P.r := by omega
  have hFs : B.CkOn ⊤ (B.GV P.k (D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)])))) (D.castF e2 F) :=
    Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hF.1
  obtain ⟨R, hR⟩ := hF.2.1
  have hRs : ∀ g ∈ B.GV P.k (D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)]))), D.castF e2 F g ≠ 0 →
      B.gN g ≤ R := fun g hg hne => by
    have := hR _ (Formalism.FourierDecayAlt.P.PBE.castM_GV e2 hg) hne
    rwa [Formalism.FourierDecayAlt.P.PBE.gN_castM] at this
  have hγ' : D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ ∈
      B.GV P.k (P.r - D.ptSize (h ++ [(1, c)])) := Formalism.FourierDecayAlt.P.PBE.castM_GV _ hγ
  have hd0 : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hlocH.1 q q.2
  have hI := asm_gInt_int (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c hd0 hc0
    (D.castV e2.symm p.T.base.z) (D.castV e2.symm p.T.base.z') (D.castF e2 F) hFs R hRs _ hγ'
  have hS := Formalism.FourierDecayAlt.P.slice_measure_identity P.k P.r (Wq →L[ℂ] Wp) p.T.base.z p.T.base.z' F h (h ++ [(1, c)]) 0 c rfl hle
    (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ) hloc
    (integrable_slice_append_single p.T.base.z p.T.base.z' F h c hle hloc _ hI)
  rw [asm_omLong_zero] at hS
  have hPS' := hPS P.k (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) hd0 c hc0
    (D.castV (by omega) p.T.base.z) (D.castV (by omega) p.T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb _ _ p.T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb _ _ p.T.base.z'_mem)
    (Wq →L[ℂ] Wp) (D.castF (by omega) F)
    (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ)
    (integrable_unipotent_rank_one (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c _ _ _ _ hI)
  have hB := asm_bridge (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (P.r - (D.ptSize h + 1))
    (P.r - D.ptSize h) P.r (by omega) (by omega) (by omega) (D.ptPerm h) (D.ptDiag h) p.T.base.z p.T.base.z'
    (p.T.bs (D.ptSize h)).z (p.T.bs (D.ptSize h)).z' (p.T.z_lev _ (by omega)) (p.T.z'_lev _ (by omega)) F c γ
    _ _ rfl rfl _ rfl _ rfl
  have hπ : ((Real.pi ^ ((0 + 1) * 0 / 2) : ℝ) : ℂ) = 1 := by norm_num
  rw [hπ, one_smul] at hS
  refine ((show KB.slv p.T F (D.ptSize h + 1) hj [] (h ++ [(1, c)]) hc.2 (fun a => a.elim0) γ =
      D.sliceAt P.k P.r p.T.base.z p.T.base.z' F (h ++ [(1, c)])
        (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ) from rfl).trans
    (hS.trans (hPS'.trans (hB.trans ?_))))
  refine integral_congr_ae (Filter.Eventually.of_forall fun xx => ?_)
  dsimp only
  congr 1
  show _ = D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h (D.castM _ _)
  unfold D.sliceAt
  rw [dite_eq_left (by omega)]

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjFrom
section
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section smooth

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdV_global {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) :
    RdV X ψ = fun g => fderiv ℝ ψ g (g * X) := by
  funext g
  have hd : HasFDerivAt ψ (fderiv ℝ ψ (Formalism.FourierDecayAlt.P.B4.cv false X 0 g)) (Formalism.FourierDecayAlt.P.B4.cv false X 0 g) :=
    ((hψ.differentiable (by simp)) _).hasFDerivAt
  have h := hd.comp_hasDerivAt (0 : ℝ) (Formalism.FourierDecayAlt.P.B4.cv_hasDerivAt false X g)
  rw [Formalism.FourierDecayAlt.P.B4.cv_zero] at h
  exact h.deriv

theorem rdV_contDiff {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) : ContDiff ℝ ∞ (RdV X ψ) := by
  rw [rdV_global hψ X]
  exact (hψ.fderiv_right (m := ∞) (by simp)).clm_apply (Formalism.FourierDecayAlt.P.B4.mulR X).contDiff

theorem rw_contDiff {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) : ∀ w : List (B.Mat k r), ContDiff ℝ ∞ (B.Rw w ψ)
  | [] => hψ
  | X :: w => rdV_contDiff (rw_contDiff hψ w) X

theorem contDiff_listSum {ι : Type*} (f : ι → B.Mat k r → E) :
    ∀ L : List ι, (∀ i ∈ L, ContDiff ℝ ∞ (f i)) → ContDiff ℝ ∞ (fun g => (L.map fun i => f i g).sum)
  | [], _ => by simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : B.Mat k r => (0 : E)))
  | i :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h i (by simp)).add (contDiff_listSum f L fun j hj => h j (by simp [hj]))

theorem ckOn_of_contDiff {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) (m : ℕ∞) (UU : Set (B.Mat k r)) :
    B.CkOn m UU ψ :=
  fun _ _ => ⟨Set.univ, ψ, isOpen_univ, trivial,
    (hψ.of_le (by exact_mod_cast (le_top : m ≤ ⊤))).contDiffOn, fun _ _ _ => rfl⟩

theorem ckOn_sub_set {m : ℕ∞} {UU UU' : Set (B.Mat k r)} (h : UU' ⊆ UU) {f : B.Mat k r → E}
    (hf : B.CkOn m UU f) : B.CkOn m UU' f :=
  fun g hg => hf g (h hg)

end smooth

section pointwise

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem opAdj_capTh_contDiff (s Y : ℂ) {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (B.opAdj (capTh k r Wp Wq s Y) ψ) := by
  unfold B.opAdj
  refine contDiff_listSum (fun (T : B.DTerm k r Wp Wq) g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse
    (fun x => T.coefAdj x (ψ x)) g) _ fun T hT => ?_
  obtain ⟨c, w, rfl⟩ := mem_capOp s (capLw k r Y) hT
  refine (rw_contDiff ?_ _).const_smul _
  show ContDiff ℝ ∞ (fun x => (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (ψ x))
  simpa using hψ.const_smul (conj c)

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  have h := (Formalism.FourierDecayAlt.P.B5.hsL (Wp := Wp) (Wq := Wq)).map_smul c A
  rw [Formalism.FourierDecayAlt.P.B5.hsL_apply, Formalism.FourierDecayAlt.P.B5.hsL_apply] at h
  exact h

theorem hsVec_sub (A C : Wq →L[ℂ] Wp) : B.hsVec (A - C) = B.hsVec A - B.hsVec C := by
  have h := (Formalism.FourierDecayAlt.P.B5.hsL (Wp := Wp) (Wq := Wq)).map_sub A C
  rw [Formalism.FourierDecayAlt.P.B5.hsL_apply, Formalism.FourierDecayAlt.P.B5.hsL_apply, Formalism.FourierDecayAlt.P.B5.hsL_apply] at h
  exact h

theorem hs_sub_right (A C D : Wq →L[ℂ] Wp) : B.hsInner A (C - D) = B.hsInner A C - B.hsInner A D := by
  unfold B.hsInner
  rw [hsVec_sub, inner_sub_left]

theorem hsInner_smul_self (c : ℂ) (A : Wq →L[ℂ] Wp) :
    B.hsInner (c • A) A = c * ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [hsVec_smul, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp

theorem pt_of_int (hI : CapAdjInt) {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (B.GV k r) μ) (s Y : ℂ)
    {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {g₀ : B.Mat k r}
    (hg₀ : g₀ ∈ B.GV k r) :
    B.opAdj (capTh k r Wp Wq s Y) ψ g₀ = conj s • Q.CV k r (conj Y) ψ g₀ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  obtain ⟨L, hL, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r (conj Y)
  set Θ := capTh k r Wp Wq s Y
  set Ht : B.Mat k r → (Wq →L[ℂ] Wp) := fun g =>
    B.opAdj Θ ψ g - conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum with hHt
  have hCVg : ∀ g ∈ B.GV k r, Q.CV k r (conj Y) ψ g = (L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum :=
    fun g hg => hCV _ (B.GV k r) ψ (ckOn_of_contDiff hψ _ _) g hg hg
  have hS : ContDiff ℝ ∞ (fun g => (L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum) :=
    contDiff_listSum (fun cw g => cw.1 • B.Rw cw.2 ψ g) L fun cw _ => (rw_contDiff hψ _).const_smul _
  have hA : ContDiff ℝ ∞ (B.opAdj Θ ψ) := opAdj_capTh_contDiff s Y hψ
  have hHs : ContDiff ℝ ∞ Ht := hA.sub (hS.const_smul _)
  by_contra hne
  have hH0 : Ht g₀ ≠ 0 := by
    intro h0
    apply hne
    have := sub_eq_zero.1 h0
    rw [hCVg g₀ hg₀]
    exact this

  obtain ⟨β⟩ : Nonempty (ContDiffBump g₀) := ⟨⟨1, 2, one_pos, one_lt_two⟩⟩
  have hβs : ContDiff ℝ ∞ (fun g => ((β g : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp β.contDiff
  have hβc : HasCompactSupport (fun g => ((β g : ℝ) : ℂ)) :=
    β.hasCompactSupport.comp_left Complex.ofReal_zero
  set φ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => ((β g : ℝ) : ℂ) • Ht g with hφ
  have hφs : ContDiff ℝ ∞ φ := hβs.smul hHs
  have hφc : HasCompactSupport φ := hβc.smul_right
  have hInt := hI k r Wp Wq s Y μ hμ φ ψ hφs hφc hψ hψc

  have hcont1 : Continuous (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (B.opAdj Θ ψ (Matrix.of x))) :=
    Formalism.FourierDecayAlt.P.B5.hs_continuous.comp (hφs.continuous.prodMk hA.continuous)
  have hcs1 : HasCompactSupport (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (B.opAdj Θ ψ (Matrix.of x))) :=
    hφc.mono fun x hx h0 => hx (by show B.hsInner (φ x) _ = 0; rw [h0]; exact Formalism.FourierDecayAlt.P.B5.hs_zero_left _)
  have i1 := hcont1.integrable_of_hasCompactSupport (μ := μ) hcs1
  have hcont2 : Continuous (fun x : Mt k r => B.hsInner (φ (Matrix.of x))
      (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum)) :=
    Formalism.FourierDecayAlt.P.B5.hs_continuous.comp (hφs.continuous.prodMk (hS.const_smul _).continuous)
  have hcs2 : HasCompactSupport (fun x : Mt k r => B.hsInner (φ (Matrix.of x))
      (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum)) :=
    hφc.mono fun x hx h0 => hx (by show B.hsInner (φ x) _ = 0; rw [h0]; exact Formalism.FourierDecayAlt.P.B5.hs_zero_left _)
  have i2 := hcont2.integrable_of_hasCompactSupport (μ := μ) hcs2
  have hae2 : (fun x : Mt k r => B.hsInner (φ (Matrix.of x)) (conj s • Q.CV k r (conj Y) ψ (Matrix.of x))) =ᵐ[μ]
      fun x => B.hsInner (φ (Matrix.of x)) (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum) := by
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx
    rw [hCVg _ hx]
  rw [integral_congr_ae hae2] at hInt

  set h : Mt k r → ℝ := fun x => β (Matrix.of x) * ‖B.hsVec (Ht (Matrix.of x))‖ ^ 2 with hh
  have hpt : ∀ x : Mt k r, B.hsInner (φ (Matrix.of x)) (B.opAdj Θ ψ (Matrix.of x)) -
      B.hsInner (φ (Matrix.of x)) (conj s • (L.map fun cw => cw.1 • B.Rw cw.2 ψ (Matrix.of x)).sum) =
      ((h x : ℝ) : ℂ) := by
    intro x
    rw [← hs_sub_right]
    show B.hsInner (((β (Matrix.of x) : ℝ) : ℂ) • Ht (Matrix.of x)) (Ht (Matrix.of x)) = _
    rw [hsInner_smul_self]
    simp [hh]
  have hzero : ∫ x, ((h x : ℝ) : ℂ) ∂μ = 0 := by
    rw [← integral_congr_ae (Eventually.of_forall hpt), integral_sub i1 i2, hInt, sub_self]
  have hnn : 0 ≤ h := fun x => mul_nonneg (β.nonneg) (sq_nonneg _)
  have hcv : Continuous (fun x : B.Mat k r => B.hsVec (Ht x)) :=
    ((Formalism.FourierDecayAlt.P.B5.hsL (Wp := Wp) (Wq := Wq)).continuous.comp hHs.continuous).congr
      (fun x => Formalism.FourierDecayAlt.P.B5.hsL_apply _)
  have hcont : Continuous h := β.continuous.mul ((continuous_norm.comp hcv).pow 2)
  have hint : Integrable h μ := by
    have := (i1.sub i2).congr (Eventually.of_forall hpt)
    exact this.re.congr (Eventually.of_forall fun x => by simp)
  have hzero' : ∫ x, h x ∂μ = 0 := by
    have := hzero
    rw [integral_complex_ofReal] at this
    exact_mod_cast this
  have hae : h =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hnn hint).1 hzero'
  have hO : IsOpen {x : Mt k r | 0 < h x} := isOpen_lt continuous_const hcont
  have hg₀O : (g₀ : Mt k r) ∈ {x : Mt k r | 0 < h x} := by
    show 0 < β g₀ * ‖B.hsVec (Ht g₀)‖ ^ 2
    have h1 : β g₀ = 1 := β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)
    rw [h1, one_mul]
    have : B.hsVec (Ht g₀) ≠ 0 := fun h0 => hH0 (Formalism.FourierDecayAlt.P.JFxI.hsVec_injective (h0.trans (by
      rw [← Formalism.FourierDecayAlt.P.B5.hsL_apply, map_zero])))
    positivity
  have hpos := haar_open_pos hμ hO (g₀ := g₀) hg₀ hg₀O
  apply hpos
  have : {x : Mt k r | 0 < h x} ⊆ {x | h x ≠ 0} := fun x hx => (ne_of_gt hx)
  exact measure_mono_null this (by simpa [Filter.EventuallyEq, ae_iff] using hae)

end pointwise

theorem capacity_adjoint_from_integral : CapAdjFromInt := by
  intro hI k r Wp Wq _ _ _ _ _ _ s Y F hF g₀ hg₀
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨U, F', hU, hg₀U, hc, he⟩ := hF g₀ hg₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU g₀ hg₀U
  obtain ⟨β, hβin, hβout⟩ : ∃ β : ContDiffBump g₀, β.rIn = ε / 4 ∧ β.rOut = ε / 2 :=
    ⟨⟨ε / 4, ε / 2, by positivity, by linarith⟩, rfl, rfl⟩
  set ψ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => ((β g : ℝ) : ℂ) • F' g with hψ
  have hψs : ContDiff ℝ ∞ ψ := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact ((Complex.ofRealCLM.contDiff.comp β.contDiff).contDiffAt).smul
        ((hc.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast le_rfl))
    · have hx2 : ε ≤ dist x g₀ := by
        by_contra hlt
        exact hx (hball (Metric.mem_ball.2 (lt_of_not_ge hlt)))
      have hO : IsOpen {y : B.Mat k r | ε / 2 < dist y g₀} := isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have hev : ∀ᶠ y in 𝓝 x, β y = 0 := by
        filter_upwards [hO.mem_nhds (show ε / 2 < dist x g₀ by linarith)] with y hy
        exact β.zero_of_le_dist (by rw [hβout]; exact le_of_lt hy)
      refine contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (0 : Wq →L[ℂ] Wp)) ?_
      filter_upwards [hev] with y hy
      simp [hψ, hy]
  have hψc : HasCompactSupport ψ :=
    (β.hasCompactSupport.comp_left Complex.ofReal_zero).smul_right
  have hV : IsOpen (Metric.ball g₀ (ε / 4)) := Metric.isOpen_ball
  have hagree : ∀ x ∈ Metric.ball g₀ (ε / 4), x ∈ B.GV k r → F x = ψ x := by
    intro x hx hxG
    have h1 : β x = 1 := β.one_of_mem_closedBall (by rw [hβin]; exact Metric.ball_subset_closedBall hx)
    have hxU : x ∈ U := hball (Metric.ball_subset_ball (by linarith) hx)
    simp [hψ, h1, he x hxU hxG]
  have hg₀V : g₀ ∈ Metric.ball g₀ (ε / 4) := Metric.mem_ball_self (by positivity)
  have h1 := Formalism.FourierDecayAlt.P.JFxG.adj_local (capTh k r Wp Wq s Y) hV hagree g₀ hg₀V hg₀
  have h2 := Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r _ (Metric.ball g₀ (ε / 4)) F ψ (conj Y) hV
    (ckOn_sub_set Set.inter_subset_right (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF))
    (ckOn_of_contDiff hψs _ _) (fun x hx => hagree x hx.1 hx.2) g₀ ⟨hg₀V, hg₀⟩
  rw [h1, h2]
  exact pt_of_int hI hμ s Y hψs hψc hg₀

theorem capAdj_of_int (hI : CapAdjInt) : CapAdj := capacity_adjoint_from_integral hI

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjSCut
section
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def wsAdj {k r : ℕ} (L : List (ℂ × List (B.Mat k r))) (b : B.Mat k r → ℂ) (x : B.Mat k r) : ℂ :=
  (L.map fun cw => conj cw.1 * (-1 : ℂ) ^ cw.2.length * B.Rw cw.2.reverse b x).sum

def CapAdjScalar : Prop :=
  ∀ (k r : ℕ) (Y : ℂ) (μ : Measure (Mt k r)), B.IsHaarOn (B.GV k r) μ → ∀ a b : B.Mat k r → ℂ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b →
    (∫ x : Mt k r, a (Matrix.of x) * star (wsAdj (capLw k r Y) b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, a (Matrix.of x) * star (Q.CV k r (conj Y) b (Matrix.of x)) ∂μ

def CapAdjIntOfScalar : Prop := CapAdjScalar → CapAdjInt

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAQQ
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

def JAAssembleQQ : Prop :=
  JDHatOpQQ → JDHatBdd → JDJComm → JDCCLower → TransferSquareIntegrable → BoundedOperatorsSquareIntegrable → JABddOpQQ → JABddStar → JAIsAdj → JAPhiOp →
    JAStarOp → JAGroupAdj → JALocCC → JAFFStable → JAdjTrQQ

theorem jAdjTrQQ_of_leaves (hA : JAAssembleQQ) (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp)
    (h12 : JAGroupAdj) (h13 : JALocCC) (h14 : JAFFStable) : JAdjTrQQ :=
  hA h1 hat_bounded_decay_holds transfer_commutation_holds class_lower_decay_holds transfer_square_integrable_holds bounded_operators_square_integrable h7 transfer_star_bound_holds transfer_is_adjoint_holds phi_operator_transfer_holds h11
    h12 h13 h14

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQAsm
section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem jDecayTrQQ_of_open (h2 : JDHatOpQQ) : JDecayTrQQ := jDecayTrQQd_of_open h2

end Formalism.FourierDecayAlt.P.CutMP
end

