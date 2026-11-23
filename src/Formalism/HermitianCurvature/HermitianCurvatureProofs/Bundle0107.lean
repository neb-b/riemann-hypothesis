module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0104
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0089
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0101
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0103
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CastVMulVecLift
section
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section lift

variable {k : ℕ}

theorem frame_lift_list {i r' m : ℕ} (vs : List (Fin (2 * r' + k + 1) → ℂ)) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ)
    (h : IsFrameOf k r' vs Bs) :
    IsFrameOf k (i + r') (vs.map (liftVec k i r')) (fun c => liftVec k i r' (Bs c)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => (PI.QnLevBasicsW.level_group_isotropic_vector k i r' (Bs a) (h1 a)).1, fun a b => ?_, fun a x hx => ?_⟩
  · rw [PIQnLT.herm_liftVec]; exact h2 a b
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    rw [PIQnLT.herm_liftVec]
    exact h3 a v hv

theorem frame_lift_cast {i r' n m : ℕ} (hn : i + r' = n) (vs : List (Fin (2 * r' + k + 1) → ℂ))
    (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ) (h : IsFrameOf k r' vs Bs) :
    IsFrameOf k n (vs.map fun v => D.castV hn (liftVec k i r' v)) (fun c => D.castV hn (liftVec k i r' (Bs c))) := by
  subst hn
  simp only [JCTx5.castV_rfl]
  exact frame_lift_list vs Bs h

theorem capRep_lift_cast {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {i r' n m : ℕ} (hn : i + r' = n)
    (π0 : Mx k n → (Wp →L[ℂ] Wp)) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ) (w : ℂ) (v : Wp) :
    capRep k n π0 (fun c => D.castV hn (liftVec k i r' (Bs c))) w v =
      capRep k r' (fun y => π0 (D.castM hn (ιLev k i r' y))) Bs w v := by
  subst hn
  simp only [JCTx5.castV_rfl, JCTx5.castM_rfl]
  exact JCTx5.capRep_lift π0 Bs w v

theorem castV_mulVec_lift {i r' n : ℕ} (hn : i + r' = n) (M : B.Mat k r') (v : Fin (2 * r' + k + 1) → ℂ) :
    D.castM hn (ιLev k i r' M) *ᵥ D.castV hn (liftVec k i r' v) = D.castV hn (liftVec k i r' (M *ᵥ v)) := by
  subst hn
  simp only [JCTx5.castV_rfl, JCTx5.castM_rfl]
  exact PIQnLT.mulVec_liftVec M v

end lift

section types

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem tp_eigen_lev {P : M.Par} (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)) (hLF : PBI.LevFrame p ν'r m₀r)
    {Bs' : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    (hB : IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z', ν'r] Bs') (ρ : M.Ty P) (w : ℂ) (u : Wp) :
    capRep P.k (P.r - P.r) (p.T.bs P.r).π (fun a => m₀r *ᵥ Bs' a) w (p.TP.E ρ u) =
      M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • p.TP.E ρ u := by
  have hn : P.r + (P.r - P.r) = P.r := by omega
  obtain ⟨hν, hm, hbase⟩ := hLF
  have hB1 := Topx1.vecw_frame_fwd (p.T.bs P.r) hbase hB
  have hB2 := frame_lift_cast hn _ _ hB1
  have ez : D.castV hn (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) = p.T.base.z := p.T.z_lev P.r le_rfl
  have ee : D.castV hn (liftVec P.k P.r (P.r - P.r) (m₀r *ᵥ ν'r)) = p.m₀ *ᵥ p.ν' := by
    rw [← castV_mulVec_lift hn, hm, hν]
  simp only [List.map_cons, List.map_nil, ez, ee] at hB2
  have h := p.TP.eigen _ hB2 ρ w u
  rw [capRep_lift_cast hn] at h
  have hπ : (fun y => p.T.base.π (D.castM hn (ιLev P.k P.r (P.r - P.r) y))) = (p.T.bs P.r).π :=
    funext fun y => (p.T.π_lev P.r le_rfl y).symm
  rw [hπ] at h
  exact h

theorem aeval_intertwine (V : Wq →L[ℂ] Wp) (R : Module.End ℂ Wq) (Lf : Module.End ℂ Wp)
    (h : ∀ v, V (R v) = Lf (V v)) (p : Polynomial ℂ) : ∀ v, V (Polynomial.aeval R p v) = Polynomial.aeval Lf p (V v) := by
  induction p using Polynomial.induction_on with
  | C a => intro v; simp
  | add p q hp hq => intro v; simp [hp, hq]
  | monomial n a ih =>
    intro v
    have e1 : Polynomial.C a * Polynomial.X ^ (n + 1) = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
    have eR : Polynomial.aeval R (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval R (Polynomial.C a * Polynomial.X ^ n) * R := by rw [map_mul, Polynomial.aeval_X]
    have eL : Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n) * Lf := by rw [map_mul, Polynomial.aeval_X]
    rw [e1, eR, eL, Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem aeval_eigen (Lf : Module.End ℂ Wp) (x : Wp) (c : ℂ) (h : Lf x = c • x) (p : Polynomial ℂ) :
    Polynomial.aeval Lf p x = p.eval c • x := by
  induction p using Polynomial.induction_on with
  | C a => simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n a ih =>
    have e1 : Polynomial.C a * Polynomial.X ^ (n + 1) = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
    have eL : Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n) * Lf := by rw [map_mul, Polynomial.aeval_X]
    have ev : (Polynomial.C a * Polynomial.X ^ n * Polynomial.X).eval c =
        (Polynomial.C a * Polynomial.X ^ n).eval c * c := by rw [Polynomial.eval_mul, Polynomial.eval_X]
    rw [e1, eL, Module.End.mul_apply, h, map_smul, ih, smul_smul, ev, mul_comm]

theorem poly_types {P : M.Par} (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)) (hLF : PBI.LevFrame p ν'r m₀r)
    {Bs' : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    (hB : IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z', ν'r] Bs') (V : Wq →L[ℂ] Wp)
    (hV : PBI.GrpInt (p.T.bs P.r) ν'r m₀r V) (hex : ∑ ρ : M.Ty P, (p.TP.E ρ).comp V = V)
    (Y₀ : ℂ) (q : Polynomial ℂ) (v : Wq) :
    V (Polynomial.aeval (qdet (Qr.EB (p.T.bs P.r).π' Bs') (Y₀ + ((P.k : ℂ) - 2) / 2)) q v) =
      ∑ ρ : M.Ty P, q.eval (M.xC P ρ Y₀) • p.TP.E ρ (V v) := by
  set S := p.T.bs P.r
  have hbase := hLF.2.2
  have hBz' : IsFrameOf P.k (P.r - P.r) [S.z'] Bs' :=
    Topx1.vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  have hBz : IsFrameOf P.k (P.r - P.r) [S.z] (fun a => m₀r *ᵥ Bs' a) :=
    Topx1.vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (Topx1.vecw_frame_fwd S hbase hB)
  have hglR := Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k (P.r - P.r) (P.k - 1) S.z' S.π' Bs' ⟨S.π'_rep, S.π'_cont⟩ hBz'
  have hglL := Formalism.FourierDecayAlt.P.frame_general_linear Wp P.k (P.r - P.r) (P.k - 1) S.z S.π (fun a => m₀r *ᵥ Bs' a)
    ⟨S.π_rep, S.π_cont⟩ hBz
  set w0 : ℂ := Y₀ + ((P.k : ℂ) - 2) / 2
  have hint : ∀ v, V (qdet (Qr.EB S.π' Bs') w0 v) = qdet (Qr.EB S.π (fun a => m₀r *ᵥ Bs' a)) w0 (V v) := by
    intro v
    rw [← hglR.2, ← hglL.2]
    exact (PBI.gen_capRep_intertwine S hbase V hV hB w0 v).symm
  rw [aeval_intertwine V _ _ hint q v]
  conv_lhs => rw [← hex]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  refine aeval_eigen _ _ _ ?_ q
  rw [← hglL.2, tp_eigen_lev p ν'r m₀r hLF hB ρ w0 (V v)]
  congr 2
  ring

end types

end Formalism.FourierDecayAlt.P.DiagonalScalarMatrices
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMTB
section
noncomputable section

open Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

section cd

variable {m : ℕ}

theorem cd_det : ContDiff ℝ ∞ (fun M : Fin m → Fin m → ℂ => (Matrix.of M).det) := by
  simp only [Matrix.det_apply, Matrix.of_apply]
  refine ContDiff.sum fun σ _ => ?_
  refine ContDiff.const_smul _ ?_
  exact contDiff_prod fun i _ => by fun_prop

theorem cd_adj (i j : Fin m) : ContDiff ℝ ∞ (fun M : Fin m → Fin m → ℂ => (Matrix.of M).adjugate i j) := by
  have h : (fun M : Fin m → Fin m → ℂ => (Matrix.of M).adjugate i j) =
      (fun N : Fin m → Fin m → ℂ => (Matrix.of N).det) ∘
        (fun M : Fin m → Fin m → ℂ => fun a b => (Matrix.of M).updateRow j (Pi.single i 1) a b) := by
    funext M
    rw [Matrix.adjugate_apply]
    rfl
  rw [h]
  refine cd_det.comp ?_
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [Matrix.updateRow_apply, Matrix.of_apply]
  split_ifs <;> fun_prop

theorem cd_inv (i j : Fin m) :
    ContDiffOn ℝ ∞ (fun M : Fin m → Fin m → ℂ => (Matrix.of M)⁻¹ i j) {M | (Matrix.of M).det ≠ 0} := by
  have h1 : ContDiffOn ℝ ∞
      (fun M : Fin m → Fin m → ℂ => ((Matrix.of M).det)⁻¹ * (Matrix.of M).adjugate i j)
      {M | (Matrix.of M).det ≠ 0} :=
    (cd_det.contDiffOn.inv fun M hM => hM).mul (cd_adj i j).contDiffOn
  refine h1.congr fun M _ => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]

end cd

section wm

variable {n : ℕ}

theorem cd_gram (a b : Fin n) : ContDiff ℝ ∞ (fun Z : Fin n → Fin n → ℂ => gram (Matrix.of Z) a b) := by
  simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  refine ContDiff.sum fun k _ => ContDiff.mul ?_ (by fun_prop)
  exact Complex.conjCLE.contDiff.comp
    (by fun_prop : ContDiff ℝ ∞ fun Z : Fin n → Fin n → ℂ => Z k a)

private lemma det_gram_castLE_ne_zero_of_det_ne_zero (Z : Fin n → Fin n → ℂ) (hZ : (Matrix.of Z).det ≠ 0) (k : ℕ)
    (hk : k ≤ n) :
    (Matrix.of fun a b : Fin k => gram (Matrix.of Z) (Fin.castLE hk a) (Fin.castLE hk b)).det ≠ 0 := by
  set E : Matrix (Fin n) (Fin k) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id (Fin.castLE hk) with hE
  set A : Matrix (Fin n) (Fin k) ℂ := Matrix.of Z * E with hA
  have hA' : ∀ r a, A r a = Z r (Fin.castLE hk a) := by
    intro r a
    simp [hA, hE, Matrix.mul_apply, Matrix.one_apply]
  have hB : (Matrix.of fun a b : Fin k => gram (Matrix.of Z) (Fin.castLE hk a) (Fin.castLE hk b)) =
      Aᴴ * A := by
    ext a b
    simp only [Matrix.of_apply, gram, Matrix.mul_apply, Matrix.conjTranspose_apply, hA']
  rw [hB]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h1 : A *ᵥ v = 0 := by
    open scoped ComplexOrder in
    exact (Matrix.conjTranspose_mul_self_mulVec_eq_zero A v).1 hv
  have h2 : E *ᵥ v = 0 := by
    by_contra hne
    apply hZ
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨E *ᵥ v, hne, ?_⟩
    rw [Matrix.mulVec_mulVec, ← hA, h1]
  apply hv0
  funext a
  have := congrFun h2 (Fin.castLE hk a)
  simpa [hE, Matrix.mulVec, dotProduct, Matrix.one_apply, Fin.castLE_inj] using this

theorem cd_Wm (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun Z : Fin n → Fin n → ℂ => Wm (Matrix.of Z) i j) {Z | (Matrix.of Z).det ≠ 0} := by
  simp only [Wm, blkJ, colJ, Matrix.of_apply]
  by_cases hij : (i : ℕ) < j
  · simp only [dif_pos hij, Matrix.mulVec, dotProduct, Pi.neg_apply]
    have hg : ContDiff ℝ ∞ (fun Z : Fin n → Fin n → ℂ => fun a b : Fin j =>
        gram (Matrix.of Z) (Fin.castLE j.isLt.le a) (Fin.castLE j.isLt.le b)) :=
      contDiff_pi.2 fun a => contDiff_pi.2 fun b => cd_gram _ _
    refine ContDiffOn.neg (ContDiffOn.sum fun c _ => ContDiffOn.mul ?_ (cd_gram _ _).contDiffOn)
    exact (cd_inv (m := j) ⟨i, hij⟩ c).comp hg.contDiffOn fun Z hZ => det_gram_castLE_ne_zero_of_det_ne_zero Z hZ j j.isLt.le
  · simp only [dif_neg hij]
    split_ifs <;> exact contDiffOn_const

theorem cd_Sm (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun Z : Fin n → Fin n → ℂ => Sm (Matrix.of Z) i j) {Z | (Matrix.of Z).det ≠ 0} := by
  have hW : ContDiffOn ℝ ∞ (fun Z : Fin n → Fin n → ℂ => fun a b => Wm (Matrix.of Z) a b)
      {Z | (Matrix.of Z).det ≠ 0} :=
    contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => cd_Wm a b
  exact (cd_adj i j).comp_contDiffOn hW

end wm

end Formalism.FourierDecayAlt.P.CutEXMT
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvScal
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvScal

noncomputable section

theorem pl_monic (s : Finset ℕ) (f : ℕ → ℂ) : (∏ i ∈ s, (X + C (f i))).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_add_C (f i))

theorem pl_natDegree (s : Finset ℕ) (f : ℕ → ℂ) : (∏ i ∈ s, (X + C (f i))).natDegree = s.card := by
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C (f i))]
  simp [natDegree_X_add_C]

theorem pl_top (s : Finset ℕ) (f : ℕ → ℂ) : (∏ i ∈ s, (X + C (f i))).coeff s.card = 1 := by
  have h := (pl_monic s f).coeff_natDegree
  rwa [pl_natDegree] at h

theorem pl_next (s : Finset ℕ) (f : ℕ → ℂ) (hs : 0 < s.card) :
    (∏ i ∈ s, (X + C (f i))).coeff (s.card - 1) = ∑ i ∈ s, f i := by
  have h := nextCoeff_of_natDegree_pos (p := ∏ i ∈ s, (X + C (f i))) (by rw [pl_natDegree]; exact hs)
  rw [pl_natDegree] at h
  rw [← h, Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (f i))]
  simp [nextCoeff_X_add_C]

theorem pl_high (s : Finset ℕ) (f : ℕ → ℂ) {j : ℕ} (hj : s.card < j) : (∏ i ∈ s, (X + C (f i))).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [pl_natDegree]; exact hj)

theorem top2 (p : ℂ[X]) (N : ℕ) (h : p.natDegree < N + 2) (u : ℂ) :
    p.eval u = u ^ (N + 1) * p.coeff (N + 1) + u ^ N * p.coeff N + ∑ i ∈ Finset.range N, u ^ i * p.coeff i := by
  rw [eval_eq_sum_range' h, Finset.sum_range_succ, Finset.sum_range_succ]
  have : ∀ i, p.coeff i * u ^ i = u ^ i * p.coeff i := fun i => mul_comm _ _
  simp only [this]
  ring

theorem card_Icc_one (n : ℕ) : (Finset.Icc 1 n).card = n := by simp

theorem xC_leading_terms_alt (P : M.Par) (m : ℕ) (hm : P.k = m + 2) (ρ : M.Ty P) :
    ∃ c : ℕ → ℂ, ∀ u : ℂ, M.xC P ρ u = u ^ (P.k - 1) + (absTy P ρ : ℂ) * u ^ (P.k - 2) +
        ∑ i ∈ Finset.range (P.k - 2), u ^ i * c i := by
  have h1 : P.k - 1 = m + 1 := by omega
  have h2 : P.k - 2 = m := by omega
  let f : ℕ → ℂ := fun i => ((M.rho P ρ i : ℝ) : ℂ)
  refine ⟨fun i => (∏ i ∈ Finset.Icc 1 (m + 1), (X + C (f i))).coeff i, fun u => ?_⟩
  have hx : M.xC P ρ u = (∏ i ∈ Finset.Icc 1 (m + 1), (X + C (f i))).eval u := by
    rw [eval_prod]; unfold M.xC; rw [h1]; simp [f]
  rw [hx, top2 _ m (by rw [pl_natDegree, card_Icc_one]; omega) u, h1, h2]
  have ht := pl_top (Finset.Icc 1 (m + 1)) f
  have hn := pl_next (Finset.Icc 1 (m + 1)) f (by rw [card_Icc_one]; omega)
  rw [card_Icc_one] at ht hn
  rw [Nat.add_sub_cancel] at hn
  rw [ht, hn]
  have ha : (absTy P ρ : ℂ) = ∑ i ∈ Finset.Icc 1 (m + 1), f i := by
    simp only [absTy, h1, f]; push_cast; rfl
  rw [ha]; ring

theorem part_ex (P : M.Par) (m : ℕ) (hm : P.k = m + 2) (ρ : M.Ty P) (ex : Finset ℕ)
    (hex : ∃ l ∈ ex, l ∈ Finset.Icc 1 (P.k - 1)) :
    ∃ c : ℕ → ℂ, ∀ u : ℂ, M.xEx P ex ρ u = ∑ i ∈ Finset.range (P.k - 1), u ^ i * c i := by
  have h1 : P.k - 1 = m + 1 := by omega
  let f : ℕ → ℂ := fun i => ((M.rho P ρ i : ℝ) : ℂ)
  let s := Finset.Icc 1 (m + 1) \ ex
  have hs : s.card < m + 1 := by
    obtain ⟨l, hl, hlI⟩ := hex
    rw [h1] at hlI
    have hss : s ⊂ Finset.Icc 1 (m + 1) :=
      (Finset.ssubset_iff_of_subset Finset.sdiff_subset).2 ⟨l, hlI, by simp [s, hl]⟩
    have := Finset.card_lt_card hss
    rwa [card_Icc_one] at this
  refine ⟨fun i => (∏ i ∈ s, (X + C (f i))).coeff i, fun u => ?_⟩
  have hx : M.xEx P ex ρ u = (∏ i ∈ s, (X + C (f i))).eval u := by
    rw [eval_prod]; unfold M.xEx; rw [h1]; simp [f, s]
  rw [hx, eval_eq_sum_range' (by rw [pl_natDegree]; omega) u, h1]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem part_w (P : M.Par) (m : ℕ) (hm : P.k = m + 2) (ρ : M.Ty P) :
    ∃ c : ℕ → ℂ, ∀ u : ℂ, M.wC P ρ u = u ^ (P.k + 1) * (-(P.TT : ℂ)) +
        u ^ P.k * ((P.TT : ℂ) * ((absTy P ρ : ℂ) - 1 - sumU P)) + ∑ i ∈ Finset.range P.k, u ^ i * c i := by
  have h1 : P.k - 1 = m + 1 := by omega
  let fx : ℕ → ℂ := fun i => ((M.rho P ρ i : ℝ) : ℂ) + 1
  let xp := ∏ i ∈ Finset.Icc 1 (m + 1), (X + C (fx i))
  have hxp : M.coordinatePolynomial P ρ = xp := by unfold M.coordinatePolynomial; rw [h1]
  have xmon : xp.Monic := pl_monic _ _
  have xdeg : xp.natDegree = m + 1 := by rw [pl_natDegree, card_Icc_one]
  have xtop : xp.coeff (m + 1) = 1 := by
    have := pl_top (Finset.Icc 1 (m + 1)) fx; rwa [card_Icc_one] at this
  have xnext : xp.coeff m = ∑ i ∈ Finset.Icc 1 (m + 1), fx i := by
    have := pl_next (Finset.Icc 1 (m + 1)) fx (by rw [card_Icc_one]; omega)
    rwa [card_Icc_one, Nat.add_sub_cancel] at this
  have xhigh : xp.coeff (m + 2) = 0 := pl_high _ _ (by rw [card_Icc_one]; omega)
  let fa : ℕ → ℂ := fun i => 1 / 2 + (P.u i : ℂ)
  let fb : ℕ → ℂ := fun i => 1 / 2 + (P.u' i : ℂ)
  let pa := ∏ i ∈ Finset.Icc 1 (m + 2), (X + C (fa i))
  let pb := ∏ i ∈ Finset.Icc 1 (m + 2), (X + C (fb i))
  have hT : (-((P.T : ℂ) * (P.T' : ℂ))) = -(P.TT : ℂ) := by simp [M.Par.TT]
  have hq : M.qP P = C (-(P.TT : ℂ)) * (pa * pb) := by
    unfold M.qP; rw [hm, Finset.prod_mul_distrib, hT]
  have abmon : (pa * pb).Monic := (pl_monic _ _).mul (pl_monic _ _)
  have abdeg : (pa * pb).natDegree = 2 * m + 4 := by
    rw [(pl_monic _ _).natDegree_mul (pl_monic _ _), pl_natDegree, pl_natDegree, card_Icc_one]; ring
  have abtop : (pa * pb).coeff (2 * m + 4) = 1 := by rw [← abdeg]; exact abmon.coeff_natDegree
  have abnext : (pa * pb).coeff (2 * m + 3) =
      ∑ i ∈ Finset.Icc 1 (m + 2), fa i + ∑ i ∈ Finset.Icc 1 (m + 2), fb i := by
    have h := nextCoeff_of_natDegree_pos (p := pa * pb) (by rw [abdeg]; omega)
    rw [abdeg, show 2 * m + 4 - 1 = 2 * m + 3 by omega] at h
    rw [← h, (pl_monic _ _).nextCoeff_mul (pl_monic _ _),
      Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (fa i)),
      Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (fb i))]
    simp only [nextCoeff_X_add_C]
  let NS : ℂ[X] := ∑ l ∈ Finset.Icc 1 (m + 1), C ((M.Nrm P l ρ : ℝ) : ℂ) *
    ((∏ j ∈ (Finset.Icc 1 (m + 1)).erase l, (X + C ((M.rho P ρ j : ℝ) : ℂ))) *
      ∏ j ∈ (Finset.Icc 1 (m + 1)).erase l, (X + C (((M.rho P ρ j : ℝ) : ℂ) + 1)))
  have hw : M.wNum P ρ = M.qP P + NS := by unfold M.wNum; rw [h1]
  have nsdeg : NS.natDegree ≤ 2 * m + 2 := by
    apply natDegree_sum_le_of_forall_le
    intro l hl
    refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    have hc : ((Finset.Icc 1 (m + 1)).erase l).card = m := by
      rw [Finset.card_erase_of_mem hl, card_Icc_one]; omega
    have e1 := pl_natDegree ((Finset.Icc 1 (m + 1)).erase l) (fun j => ((M.rho P ρ j : ℝ) : ℂ))
    have e2 := pl_natDegree ((Finset.Icc 1 (m + 1)).erase l) (fun j => ((M.rho P ρ j : ℝ) : ℂ) + 1)
    rw [e1, e2, hc]; omega
  let c0 : ℂ := (P.TT : ℂ) * ((absTy P ρ : ℂ) - 1 - sumU P)
  let Q0 : ℂ[X] := C (-(P.TT : ℂ)) * X ^ (m + 3) + C c0 * X ^ (m + 2)
  let G : ℂ[X] := M.wNum P ρ - xp * Q0
  have e_xQ : xp * Q0 = C (-(P.TT : ℂ)) * (xp * X ^ (m + 3)) + C c0 * (xp * X ^ (m + 2)) := by
    simp only [Q0]; ring
  have c4a : (xp * X ^ (m + 3)).coeff (2 * m + 4) = 1 := by
    rw [show 2 * m + 4 = (m + 1) + (m + 3) by ring, coeff_mul_X_pow, xtop]
  have c4b : (xp * X ^ (m + 2)).coeff (2 * m + 4) = 0 := by
    rw [show 2 * m + 4 = (m + 2) + (m + 2) by ring, coeff_mul_X_pow, xhigh]
  have c3a : (xp * X ^ (m + 3)).coeff (2 * m + 3) = xp.coeff m := by
    rw [show 2 * m + 3 = m + (m + 3) by ring, coeff_mul_X_pow]
  have c3b : (xp * X ^ (m + 2)).coeff (2 * m + 3) = 1 := by
    rw [show 2 * m + 3 = (m + 1) + (m + 2) by ring, coeff_mul_X_pow, xtop]
  have Q0deg : (xp * Q0).natDegree ≤ 2 * m + 4 := by
    refine natDegree_mul_le.trans ?_
    rw [xdeg]
    have : Q0.natDegree ≤ m + 3 := (natDegree_add_le _ _).trans
      (max_le (natDegree_C_mul_X_pow_le _ _) ((natDegree_C_mul_X_pow_le _ _).trans (by omega)))
    omega
  have qdeg : (M.qP P).natDegree ≤ 2 * m + 4 := by
    rw [hq]; exact (natDegree_C_mul_le _ _).trans abdeg.le
  have hA : (absTy P ρ : ℂ) = ∑ i ∈ Finset.Icc 1 (m + 1), ((M.rho P ρ i : ℝ) : ℂ) := by
    simp only [absTy, h1]; push_cast; rfl
  have hS : sumU P = ∑ i ∈ Finset.Icc 1 (m + 2), (P.u i : ℂ) + ∑ i ∈ Finset.Icc 1 (m + 2), (P.u' i : ℂ) := by
    simp only [sumU, hm, Finset.sum_add_distrib]
  have Gdeg : G.natDegree ≤ 2 * m + 2 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp only [G, hw, coeff_sub, coeff_add]
    rw [coeff_eq_zero_of_natDegree_lt (p := NS) (by omega), add_zero]
    rcases (show N = 2 * m + 3 ∨ N = 2 * m + 4 ∨ 2 * m + 4 < N by omega) with h | h | h
    · subst h
      rw [e_xQ, coeff_add, coeff_C_mul, coeff_C_mul, c3a, c3b, xnext, hq, coeff_C_mul, abnext]
      simp only [fa, fb, fx, c0, hA, hS, Finset.sum_add_distrib, Finset.sum_const, card_Icc_one, nsmul_eq_mul]
      push_cast
      ring
    · subst h
      rw [e_xQ, coeff_add, coeff_C_mul, coeff_C_mul, c4a, c4b, hq, coeff_C_mul, abtop]; ring
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : (M.qP P).natDegree < N),
        coeff_eq_zero_of_natDegree_lt (by omega : (xp * Q0).natDegree < N)]; ring
  have hG := modByMonic_add_div G xp
  have hdiv : M.wNum P ρ /ₘ xp = Q0 + G /ₘ xp := by
    refine (div_modByMonic_unique (Q0 + G /ₘ xp) (G %ₘ xp) xmon ⟨?_, degree_modByMonic_lt _ xmon⟩).1
    calc G %ₘ xp + xp * (Q0 + G /ₘ xp) = xp * Q0 + (G %ₘ xp + xp * (G /ₘ xp)) := by ring
      _ = xp * Q0 + G := by rw [hG]
      _ = M.wNum P ρ := by simp only [G]; ring
  have Gq : (G /ₘ xp).natDegree < m + 2 := by rw [natDegree_divByMonic _ xmon, xdeg]; omega
  refine ⟨fun i => (G /ₘ xp).coeff i, fun u => ?_⟩
  unfold M.wC
  rw [hxp, hdiv, eval_add, eval_eq_sum_range' Gq u, hm]
  simp only [Q0, c0, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  have : ∀ i, (G /ₘ xp).coeff i * u ^ i = u ^ i * (G /ₘ xp).coeff i := fun i => mul_comm _ _
  simp only [this]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvScal

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem curvature_scalar_holds : GTCCurvScal := by
  intro P hk ρ
  obtain ⟨m, hm⟩ : ∃ m, P.k = m + 2 := ⟨P.k - 2, by omega⟩
  exact ⟨CurvScal.part_w P m hm ρ, CurvScal.xC_leading_terms_alt P m hm ρ, fun ex hex => CurvScal.part_ex P m hm ρ ex hex⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompDefs
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

abbrev Mb (k : ℕ) := Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ

def e0 (k r : ℕ) (X : Mb k) : Q.Mx k r := Em k r * X * (Em k r)ᵀ

def dnu (k : ℕ) (a b c : ℂ) : Mb k :=
  a • Matrix.single 0 0 1 + b • (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) +
    c • Matrix.single (Fin.last k) (Fin.last k) 1

def kap (T T' : ℝ) : ℂ := ((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ)

def nuI (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k := nu k (star (wZ T T' ζ)) (-sZ T T' ζ)

def H1 (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k :=
  nuI k T T' ζ * dnu k 0 ((2 * kap T T')⁻¹ * conj ζ * (sig (T * T') ζ)⁻¹) (-(kap T T')⁻¹)

def H2 (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k :=
  nuI k T T' ζ * dnu k (-(kap T T')⁻¹) ((2 * kap T T')⁻¹ * ζ * (sig (T * T') ζ)⁻¹) 0

def InL (k : ℕ) (C : Mb k) : Prop := ∀ i, C i (Fin.last k) = 0 ∧ C (Fin.last k) i = 0

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
end

