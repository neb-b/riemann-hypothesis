module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0259
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0258
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0145
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0183
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0238
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamJFDeriv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0254
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVZeroOfVanish

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDAsm
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem rd_iter_pow (hI : RDIdent) : RDHyp fun k r Wp Wq _ _ _ _ _ _ D =>
    ∀ (M : ℕ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F → NiceAll D F' →
      ∃ K : ℝ, ∀ s : ℂ, ‖s‖ ^ M * ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ K := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr M
  obtain ⟨Θ, hΘ, hid⟩ := hI Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  induction M with
  | zero =>
    intro F F' hF hF'
    obtain ⟨_, _, -, hFc, -⟩ := hF
    obtain ⟨_, _, -, hFc', -⟩ := hF'
    obtain ⟨K, hK⟩ := radial_boundedness P.k P.r Wp Wq D F F' hFc hFc'
    exact ⟨K, fun s => by simpa using hK s⟩
  | succ M ih =>
    intro F F' hF hF'
    obtain ⟨K1, hK1⟩ := ih (Θ 1 F) (Θ 0 F') (hΘ 1 F hF) (hΘ 0 F' hF')
    obtain ⟨K2, hK2⟩ := ih (Θ 3 F) (Θ 2 F') (hΘ 3 F hF) (hΘ 2 F' hF')
    refine ⟨K1 + K2, fun s => ?_⟩
    have e := hid s F F' hF hF'
    calc ‖s‖ ^ (M + 1) * ‖B.beta D (wvG D.z D.z' s F) F'‖
        = ‖s‖ ^ M * ‖s * B.beta D (wvG D.z D.z' s F) F'‖ := by rw [norm_mul, pow_succ]; ring
      _ = ‖s‖ ^ M * ‖B.beta D (wvG D.z D.z' s (Θ 1 F)) (Θ 0 F') -
            B.beta D (wvG D.z D.z' s (Θ 3 F)) (Θ 2 F')‖ := by rw [e]
      _ ≤ ‖s‖ ^ M * (‖B.beta D (wvG D.z D.z' s (Θ 1 F)) (Θ 0 F')‖ +
            ‖B.beta D (wvG D.z D.z' s (Θ 3 F)) (Θ 2 F')‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ K1 + K2 := by rw [mul_add]; exact add_le_add (hK1 s) (hK2 s)

theorem rd_pow_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) : (1 + x) ^ N ≤ 2 ^ N * (1 + x ^ N) := by
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + x ^ N) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hx N])
  · calc (1 + x) ^ N ≤ (2 * x) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * x ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + x ^ N) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem rd_decay (hI : RDIdent) : RDHyp fun k r Wp Wq _ _ _ _ _ _ D =>
    ∀ (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F → NiceAll D F' → ∀ n : ℕ,
      ∃ C : ℝ, ∀ s : ℂ, ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3)) := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr F F' hF hF' n
  have hp := rd_iter_pow hI Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  obtain ⟨K0, hK0⟩ := hp 0 F F' hF hF'
  obtain ⟨KN, hKN⟩ := hp (n + 3) F F' hF hF'
  refine ⟨2 ^ (n + 3) * (K0 + KN), fun s => ?_⟩
  have hx : 0 ≤ ‖s‖ := norm_nonneg _
  have hb : 0 ≤ ‖B.beta D (wvG D.z D.z' s F) F'‖ := norm_nonneg _
  have hb0 : ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ K0 := by simpa using hK0 s
  have hbN := hKN s
  have hpos : 0 < 1 + ‖s‖ := by linarith
  have main : (1 + ‖s‖) ^ (n + 3) * ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ 2 ^ (n + 3) * (K0 + KN) := by
    calc (1 + ‖s‖) ^ (n + 3) * ‖B.beta D (wvG D.z D.z' s F) F'‖
        ≤ 2 ^ (n + 3) * (1 + ‖s‖ ^ (n + 3)) * ‖B.beta D (wvG D.z D.z' s F) F'‖ :=
          mul_le_mul_of_nonneg_right (rd_pow_le _ hx _) hb
      _ = 2 ^ (n + 3) * (‖B.beta D (wvG D.z D.z' s F) F'‖ +
            ‖s‖ ^ (n + 3) * ‖B.beta D (wvG D.z D.z' s F) F'‖) := by ring
      _ ≤ 2 ^ (n + 3) * (K0 + KN) := mul_le_mul_of_nonneg_left (add_le_add hb0 hbN) (by positivity)
  have hr' : (1 + ‖s‖) ^ (-((n : ℝ) + 3)) = ((1 + ‖s‖) ^ (n + 3))⁻¹ := by
    rw [Real.rpow_neg hpos.le]
    congr 1
    rw [show ((n : ℝ) + 3) = ((n + 3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hr', ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith [main]

theorem radDecay_of_cut (hI : RDIdent) : RadDecay := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl ε G H hε hG hH Φ Ψ hΦ hΨ
    c hc n
  have hr : 0 < P.r := lt_of_le_of_lt (Nat.zero_le _) l.isLt
  have hl' : l = ⟨0, hr⟩ := Fin.ext hl
  have hl0 : l.castSucc = (0 : Fin (P.r + 1)) := Fin.ext (by simp [hl])
  obtain ⟨C', hC'⟩ := rd_decay hI Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr G H
    ⟨ε, hε, hG⟩ ⟨ε, hε, hH⟩ n
  subst hz hz' hπ hπ'
  obtain ⟨C1, -, hC1⟩ := radial_beta_identity P.k P.r Wp Wq D μ hD.2.1
  refine ⟨‖C1‖ * C', fun s Wv hW => ?_⟩
  have hwv := radial_wave_identity P.k P.r Wp Wq D hr ε s G
  have hΦ' : ∀ y ∈ DomR P.k P.r D.z D.z', ((Wv Φ : RadSp P.k P.r D.z D.z' D.π D.π') :
      Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 = resG P.k P.r (Fin.last P.r) (B.JF D (wvG D.z D.z' s G)) y.1 y.2 := by
    intro y hy
    rw [hW Φ y.1 y.2, hΦ y hy, hwv.2 y hy, hl']
  rw [hl0, hC1 (wvG D.z D.z' s G) H (Wv Φ) Ψ (hwv.1 hG).2.1 hH.2.1 hΦ' hΨ c, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC' s) (norm_nonneg _)

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHOpClosed
section
open scoped ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section opc

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem opc_cc_zero (j : ℕ) (hj : j + 1 ≤ P.r) (t : ℂ) (c : Fin (P.r - (j + 1)) → ℂ) :
    cc (P := P) j hj t c ⟨0, by omega⟩ = t := by
  unfold cc consC
  simp

theorem opc_cc_line (j : ℕ) (hj : j + 1 ≤ P.r) (t v : ℂ) (s : ℝ) (c : Fin (P.r - (j + 1)) → ℂ) :
    cc (P := P) j hj (t + (s : ℂ) * v) c =
      cc (P := P) j hj t c + s • (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ) := by
  funext l
  unfold cc consC
  by_cases hl : (l : ℕ) = 0
  · have e : l = ⟨0, by omega⟩ := Fin.ext hl
    simp [hl, Pi.single_apply, e, Complex.real_smul]
  · have hne : l ≠ ⟨0, by omega⟩ := fun h => hl (by rw [h])
    simp [hl, Pi.single_apply, hne]

theorem opc_mul (h2 : FamAlg) (h4 : RepLin) {T : D.LevTower P.k P.r Wp Wq}
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T) {j : ℕ} {hj : j + 1 ≤ P.r}
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ Ψ' : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    {G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)} (hG : GoodFam T j G) (hR : Rep T j hj Ψ G)
    (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {t | t ≠ 0})
    (hv : ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      (Ψ' : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
        m t • (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2)) :
    InC T j hj Ψ' := by
  refine ⟨fun t γ => m t • G t γ, (h2 Wp Wq P T j G G hG hG m hm).2, fun t ht x hx => ?_⟩
  rw [hv t ht x hx, hR t ht x hx]
  exact (h4 Wp Wq P T hP hT j hj hPs G G hG hG t ht (m t) x hx).2.symm

theorem opc_two (h2 : FamAlg) (h3 : FamDeriv) (h4 : RepLin) {T : D.LevTower P.k P.r Wp Wq}
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T) {j : ℕ} {hj : j + 1 ≤ P.r}
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ' : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    {G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)} (hG : GoodFam T j G)
    (m1 m2 : ℂ → ℂ) (hm1 : ContDiffOn ℝ ∞ m1 {t | t ≠ 0}) (hm2 : ContDiffOn ℝ ∞ m2 {t | t ≠ 0}) (v1 v2 : ℂ)
    (hv : ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      (Ψ' : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
        m1 t • resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v1 t)) x.1 x.2 +
        m2 t • resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v2 t)) x.1 x.2) :
    InC T j hj Ψ' := by
  have hd1 := h3 Wp Wq P T j G hG v1
  have hd2 := h3 Wp Wq P T j G hG v2
  have hA : GoodFam T j (fun t γ => m1 t • famP j G v1 t γ) := (h2 Wp Wq P T j _ _ hd1 hd1 m1 hm1).2
  have hB : GoodFam T j (fun t γ => m2 t • famP j G v2 t γ) := (h2 Wp Wq P T j _ _ hd2 hd2 m2 hm2).2
  refine ⟨fun t γ => m1 t • famP j G v1 t γ + m2 t • famP j G v2 t γ,
    (h2 Wp Wq P T j _ _ hA hB (fun _ => 1) contDiffOn_const).1, fun t ht x hx => ?_⟩
  have e0 := (h4 Wp Wq P T hP hT j hj hPs _ _ hA hB t ht 0 x hx).1
  have e1 := (h4 Wp Wq P T hP hT j hj hPs _ _ hd1 hd1 t ht (m1 t) x hx).2
  have e2 := (h4 Wp Wq P T hP hT j hj hPs _ _ hd2 hd2 t ht (m2 t) x hx).2
  rw [hv t ht x hx, ← e1, ← e2]
  exact e0.symm

theorem opc_fderiv (h5 : FamJFDeriv) (h6 : CellTie) (T : D.LevTower P.k P.r Wp Wq)
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T) (j : ℕ) (hj : j + 1 ≤ P.r)
    (hPj : IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) (hG : GoodFam T j G) (hR : Rep T j hj Ψ G)
    (t : ℂ) (ht : t ≠ 0) (x : (Fin (P.r - (j + 1)) → ℂ) × Mx P.k (P.r - (j + 1)))
    (hx : x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z') (v : ℂ) :
    fderiv ℝ (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) (cc j hj t x.1)
        (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v) =
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v t)) x.1 x.2 := by
  have hy := (h6 Wp Wq P T hP hT j hj hPj hPs t ht x hx).1
  obtain ⟨-, hs, -⟩ := Ψ.2
  obtain ⟨U, F, hU, hyU, hF, hΨF⟩ := hs _ hy
  have hg : gi j hj x.2 ∈ Glev P.k (P.r - j) (Fin.last _) := hy.2.1
  have hemb : Continuous fun c' : Fin (P.r - j) → ℂ => (c', gi j hj x.2) :=
    continuous_id.prodMk continuous_const
  have hev : (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) =ᶠ[𝓝 (cc j hj t x.1)]
      fun c' => F (c', gi j hj x.2) := by
    have hU' : ∀ᶠ c' in 𝓝 (cc j hj t x.1), (c', gi j hj x.2) ∈ U :=
      hemb.continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)
    filter_upwards [hU'] with c' hc'
    exact hΨF (c', gi j hj x.2) hc' hg
  have hFd : DifferentiableAt ℝ (fun c' => F (c', gi j hj x.2)) (cc j hj t x.1) :=
    ((hF.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)).comp (cc j hj t x.1)
      (differentiableAt_id.prodMk (differentiableAt_const _))
  have hφ := (hFd.congr_of_eventuallyEq hev).hasFDerivAt
  have hφ' : HasFDerivAt (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (fderiv ℝ (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) (cc j hj t x.1))
      (cc j hj t x.1 + (0 : ℝ) • (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ)) := by
    rw [zero_smul, add_zero]; exact hφ
  have hline := ((hasDerivAt_id (0 : ℝ)).smul_const
    (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ)).const_add (cc j hj t x.1)
  rw [one_smul] at hline
  have hcomp := hφ'.comp_hasDerivAt (0 : ℝ) hline
  have hJ := h5 Wp Wq P T hP hT j hj hPs G hG t ht x hx v
  have hc : Continuous fun s : ℝ => t + (s : ℂ) * v :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hne : ∀ᶠ s : ℝ in 𝓝 0, t + (s : ℂ) * v ≠ 0 :=
    hc.continuousAt.eventually_ne (by simpa using ht)
  have heq : ((fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) ∘
      fun s : ℝ => cc j hj t x.1 + id s • (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ))
      =ᶠ[𝓝 0] fun s : ℝ =>
        resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G (t + (s : ℂ) * v))) x.1 x.2 := by
    filter_upwards [hne] with s hs
    simp only [Function.comp, id]
    rw [← opc_cc_line]
    exact hR _ hs x hx
  exact hcomp.unique (hJ.congr_of_eventuallyEq heq)

end opc

theorem cutSH_opClosed_of (h2 : FamAlg) (h3 : FamDeriv) (h4 : RepLin) (h5 : FamJFDeriv) (h6 : CellTie) :
    OpClosed := by
  intro Wp Wq _ _ _ _ _ _ P T hP hT j hj hPj hPs X i Ψ hΨ
  obtain ⟨G, hG, hR⟩ := hΨ
  have hom : ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      cc j hj t x.1 ∈ OmX (P.r - j) := fun t ht x hx => (h6 Wp Wq P T hP hT j hj hPj hPs t ht x hx).1.1
  have hD := fun v t ht x hx => opc_fderiv h5 h6 T hP hT j hj hPj hPs Ψ G hG hR t ht x hx v
  have hid : ContDiff ℝ ∞ (fun t : ℂ => t) := contDiff_id
  have hst : ContDiff ℝ ∞ (fun t : ℂ => star t) := Complex.conjCLE.contDiff
  fin_cases i
  · refine opc_two h2 h3 h4 hP hT hPs hG (fun t => t / 2) (fun t => -(t * Complex.I / 2))
      (hid.div_const 2).contDiffOn ((hid.mul contDiff_const).div_const 2).neg.contDiffOn 1 Complex.I
      (fun t ht x hx => ?_)
    rw [X.op_apply]
    change pOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold pOp
    rw [if_pos (hom t ht x hx), opc_cc_zero]
    unfold wirt
    rw [hD 1 t ht x hx, hD Complex.I t ht x hx]
    module
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => t) hid.contDiffOn (fun t ht x hx => ?_)
    rw [X.op_apply]
    change cOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold cOp
    rw [opc_cc_zero]
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => t⁻¹) (hid.contDiffOn.inv fun t ht => ht)
      (fun t ht x hx => ?_)
    rw [X.op_apply]
    change ciOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold ciOp
    rw [opc_cc_zero]
  · refine opc_two h2 h3 h4 hP hT hPs hG (fun t => star t / 2) (fun t => star t * Complex.I / 2)
      (hst.div_const 2).contDiffOn ((hst.mul contDiff_const).div_const 2).contDiffOn 1 Complex.I
      (fun t ht x hx => ?_)
    rw [X.op_apply]
    change pbOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold pbOp
    rw [if_pos (hom t ht x hx), opc_cc_zero]
    unfold wirtBar
    rw [hD 1 t ht x hx, hD Complex.I t ht x hx]
    module
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => star t) hst.contDiffOn (fun t ht x hx => ?_)
    rw [X.op_apply]
    change cbOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold cbOp
    rw [opc_cc_zero]
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => (star t)⁻¹)
      (hst.contDiffOn.inv fun t ht => star_ne_zero.mpr ht) (fun t ht x hx => ?_)
    rw [X.op_apply]
    change cbiOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold cbiOp
    rw [opc_cc_zero]

end Formalism.FourierDecayAlt.P.CutSH

theorem Formalism.FourierDecayAlt.P.cutSH_opClosed_of (h2 : Formalism.FourierDecayAlt.P.CutSH.FamAlg) (h3 : Formalism.FourierDecayAlt.P.CutSH.FamDeriv)
    (h4 : Formalism.FourierDecayAlt.P.CutSH.RepLin) (h5 : Formalism.FourierDecayAlt.P.CutSH.FamJFDeriv) (h6 : Formalism.FourierDecayAlt.P.CutSH.CellTie) :
    Formalism.FourierDecayAlt.P.CutSH.OpClosed :=
  Formalism.FourierDecayAlt.P.CutSH.cutSH_opClosed_of h2 h3 h4 h5 h6

theorem Formalism.FourierDecayAlt.P.cutSH_opClosed_of_famJFDeriv (h5 : Formalism.FourierDecayAlt.P.CutSH.FamJFDeriv) : Formalism.FourierDecayAlt.P.CutSH.OpClosed :=
  Formalism.FourierDecayAlt.P.CutSH.cutSH_opClosed_of Formalism.FourierDecayAlt.P.CutSH.family_algebraic Formalism.FourierDecayAlt.P.family_derivative
    Formalism.FourierDecayAlt.P.CutSH.representation_linear h5 Formalism.FourierDecayAlt.P.CutSH.cell_compatibility

theorem Formalism.FourierDecayAlt.P.operator_class_closed : Formalism.FourierDecayAlt.P.CutSH.OpClosed :=
  Formalism.FourierDecayAlt.P.cutSH_opClosed_of_famJFDeriv Formalism.FourierDecayAlt.P.family_orbital_derivative_identity
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DetLowW
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBQ

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem kr_agree {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (l : Fin (r + 2)) (a : ℂ) (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp))
    (hH : ∀ g ∈ B.GV k r, Dmin k r Bs.z Bs.z' g l = a → H₁ g = H₂ g) (y : B.Mat k r) (hy : y ∈ B.GV k r)
    (hya : Dmin k r Bs.z Bs.z' y l = a) : PBG.Kr Bs H₁ y = PBG.Kr Bs H₂ y := by
  unfold PBG.Kr
  refine integral_congr_ae ?_
  filter_upwards [PBG.ae_inR Bs] with ξ hξ
  have hg : y * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hy hξ.2.1) hξ.1.1
  rw [hH _ hg (by rw [PBG.dmin_pR Bs hξ y l, hya])]

theorem pbT_agree (P : M.Par) (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r) (a : ℂ)
    (H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hH : ∀ g ∈ B.GV P.k P.r, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = a → H₁ g = H₂ g)
    (g : B.Mat P.k P.r) (hg : g ∈ B.GV P.k P.r)
    (hga : Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = a) :
    pbT p j (by omega) H₁ g = pbT p j (by omega) H₂ g := by
  unfold pbT
  have e : j + (P.r - j) = P.r := by omega
  rw [PartialBesselProperness.pbF_eq_TI, PartialBesselProperness.pbF_eq_TI]
  unfold PartialBesselProperness.TI
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [PartialBesselProperness.gI]
  split_ifs with hx
  · have hs : PartialBesselProperness.sE (p.T.bs j) e x ∈ Sset P.k P.r p.T.base.z := by
      have := PartialBesselProperness.sE_mem_S (p.T.bs j) e x
      rwa [p.T.z_lev j (by omega)] at this
    have hyG : PartialBesselProperness.sE (p.T.bs j) e x * g ∈ B.GV P.k P.r := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (PartialBesselProperness.sE_GV _ e x) hg
    have hyD : Dmin P.k P.r p.T.base.z p.T.base.z' (PartialBesselProperness.sE (p.T.bs j) e x * g) ⟨j + 1, by omega⟩ = a := by
      have := Formalism.QuantumDeterminants.diagonal_inverse_holds P.k P.r p.T.base.z p.T.base.z' p.T.base.z_mem p.T.base.z'_mem _ hs 1
        (Formalism.FourierDecayAlt.P.PBG.one_mem_Sset P.k P.r _) g ⟨j + 1, by omega⟩
      rw [Matrix.mul_one] at this
      rw [this, hga]
    rw [kr_agree p.T.base ⟨j + 1, by omega⟩ a H₁ H₂ hH _ hyG hyD]
  · rfl

def aVal (h : C.LPt) (t : ℂ) : ℂ := (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t

def CutOffStep : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)) (Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
    KB.CptCoef p.T.base Fc →
    (∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = aVal h t →
      Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g) →
    B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
      B.JF (p.T.bs j) (KB.slv p.T Fc j (by omega) [] h hh.2 fun a => a.elim0) (mLev P j hj t γ)

def CutOffExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (t : ℂ), D.IsLocPt (h ++ [(1, t)]) (j + 1) → ∀ e : Wd.Ix (Fin w.length),
    ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base Fc ∧
      ∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = aVal h t →
        Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g

theorem det_lowW {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : (U.lowW σ v).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [U.lowW]
  · intro a b hab
    simp only [U.lowW, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
    have hab' : a < b := hab
    rw [if_neg (ne_of_lt hab'), dite_eq_right (fun h => absurd h.1 (not_lt.mpr hab'.le)), add_zero]

theorem zxH_det (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (v : XH h) :
    (zxH h j hh.2 v).det = (U.hMat (D.ptPerm h) (D.ptDiag h)).det := by
  have hH : (U.hMat (D.ptPerm h) (D.ptDiag h)).det ≠ 0 :=
    Formalism.FourierDecayAlt.P.PBM.hMat_det_ne _ _ (CutHB.ptDiag_ne hh)
  have hw : IsUnit (U.wP (D.ptPerm h)) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    apply hH
    rw [U.hMat, Matrix.det_mul, h0, zero_mul]
  unfold zxH LeftFubiniLemmas.lhOf
  rw [Matrix.det_reindex_self, Matrix.det_mul, Matrix.det_conj hw, det_lowW, one_mul]

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

