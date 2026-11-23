module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle0002
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0256
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Formalism.LocalToGlobal.Columns.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitConstantsParameterConditionsLarge
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem Std.parConsts_pos {C : FC} (hC : Std C) : ∀ c ∈ C.P.list, 0 < c := by
  obtain ⟨hF, -, h1, h2, h3, h4, h5, -, -, -, -, h6, h7, -, hM, hL⟩ := hC
  obtain ⟨-, -, -, -, -, -, -, h8, -, -⟩ := hF
  simp only [FC.cLast, FC.cMid, List.forall_mem_cons] at hM hL
  obtain ⟨hCF, -⟩ := hM
  obtain ⟨a1, a2, a3, a4, a5, -, a6, a7, a8, a9, a10, a11, a12, a13, a14, -⟩ := hL
  have a4' : 0 < C.P.cLL := inv_pos.mp (lt_of_lt_of_le one_pos a4)
  simp only [PC.list, List.forall_mem_cons]
  refine ⟨?_, ?_, ?_, a4', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩ <;>
    linarith

theorem explicitConstants_parameterConditions_large :
    SzRow (fun C D L => HostArith D.host → ∃ P : ParameterChoice' D L, parConsts P = C.PK ∧ P.CnW = C.P.CnW) := by
  refine SzRow.imp (
    SzRow.and _root_.GlobalTheory.EX.szRow_primes_conductor <|
    SzRow.and GlobalTheory.EX.explicitChoice_rankK_lower_upper_bounds <|
    SzRow.and GlobalTheory.EX.szRow_rank_lower_bounds <|
    SzRow.and GlobalTheory.EX.szRow_logf <|
    SzRow.and _root_.GlobalTheory.EX.szRow_eta_bounds <|
    SzRow.and _root_.GlobalTheory.EX.szRow_eta_le_w <|
    SzRow.and _root_.GlobalTheory.EX.szRow_tops_band_bottoms <|
    SzRow.and GlobalTheory.EX.szRow_cloud_le <|
    SzRow.and GlobalTheory.EX.szRow_windowLength <|
    SzRow.and GlobalTheory.EX.szRow_exact <|
    SzRow.and GlobalTheory.EX.szRow_lowsFar <|
    SzRow.and _root_.GlobalTheory.EX.szRow_size_ratio <|
    SzRow.and GlobalTheory.EX.szRow_thinSize_ge <|
    SzRow.and _root_.GlobalTheory.EX.szRow_cloudUnit_lower <|
    SzRow.and _root_.GlobalTheory.EX.szRow_nodeGap <|
    SzRow.and _root_.GlobalTheory.EX.szRow_gap_fun_fN <|
    SzRow.and GlobalTheory.EX.szRow_sig_gaps <|
    SzRow.and GlobalTheory.EX.szRow_rbS <|
    SzRow.and GlobalTheory.T.sizes_b_add_Sc_add_etaSz_add_div_lt_lStar <|
    SzRow.and GlobalTheory.EX.szRow_card_words_le <|
    _root_.GlobalTheory.EX.szRow_typePrimes) ?_
  intro C cD ch D L hC _ h hA
  obtain ⟨⟨h_qd_pow, h_logq_ge, h_dlogL1_le, h_condE_le, h_pde_log⟩,
    ⟨h_k_low, h_k_up, h_R0_ge⟩,
    ⟨h_k_ge_m2L, h_k_ge_mx, h_klogk, h_flogk⟩,
    ⟨h_logf_le, h_log2f_le, h_loglogb, h_nW_ge⟩,
    ⟨h_eta_le, h_logeta, h_t_le_eta, h_teta, h_mteta⟩,
    ⟨h_mSeta, h_Neta, h_eta2, h_kS_le⟩,
    ⟨h_TT_card_le, h_rho_le, h_bT_le⟩,
    ⟨h_S_le, h_Del_le, h_logDel⟩,
    ⟨h_Lw_j, h_Lw_le, h_j0_le⟩,
    ⟨h_top_b1, h_cloud_le2, h_uk_extreme, h_em_win, h_nodes_gap, h_e_centred, h_e_parity, h_etaF_eq, h_pde_mod, h_pde_ne, h_ccK_log, h_ccK_le⟩,
    h_lows_far,
    ⟨h_X''_ratio, h_bm_le⟩,
    h_w''_ge,
    ⟨h_Del_ge, h_Del_count⟩,
    h_h0_ge,
    ⟨h_h0_fun, h_h0_fN⟩,
    h_sig_gaps,
    h_rbS,
    ⟨h_lstar1, h_lstar2⟩,
    h_words_le,
    h_g_Y⟩ := h
  have hp := hC.parConsts_pos
  simp only [PC.list, List.forall_mem_cons] at hp
  obtain ⟨p_CkLow, p_Ck6, p_CfL, p_cLL, p_CnW, p_Crho, p_CDelG, p_CLw, p_Cj0, p_Cw, p_cw, p_CDel, p_CCount, p_Ch0r, p_Ch0k, p_Ch0N, p_Cgap, p_CetaF, p_CY, p_CYL, p_Cpde, p_CccK, p_CF, -⟩ := hp
  exact ⟨
    { CkLow := C.P.CkLow, CkLow_pos := p_CkLow
      Ck6 := C.P.Ck6, Ck6_pos := p_Ck6
      CfL := C.P.CfL, CfL_pos := p_CfL
      cLL := C.P.cLL, cLL_pos := p_cLL
      CnW := C.P.CnW, CnW_pos := p_CnW
      Crho := C.P.Crho, Crho_pos := p_Crho
      CDelG := C.P.CDelG, CDelG_pos := p_CDelG
      CLw := C.P.CLw, CLw_pos := p_CLw
      Cj0 := C.P.Cj0, Cj0_pos := p_Cj0
      Cw := C.P.Cw, Cw_pos := p_Cw
      cw := C.P.cw, cw_pos := p_cw
      CDel := C.P.CDel, CDel_pos := p_CDel
      CCount := C.P.CCount, CCount_pos := p_CCount
      Ch0r := C.P.Ch0r, Ch0r_pos := p_Ch0r
      Ch0k := C.P.Ch0k, Ch0k_pos := p_Ch0k
      Ch0N := C.P.Ch0N, Ch0N_pos := p_Ch0N
      Cgap := C.P.Cgap, Cgap_pos := p_Cgap
      CetaF := C.P.CetaF, CetaF_pos := p_CetaF
      CY := C.P.CY, CY_pos := p_CY
      CYL := C.P.CYL, CYL_pos := p_CYL
      Cpde := C.P.Cpde, Cpde_pos := p_Cpde
      CccK := C.P.CccK, CccK_pos := p_CccK
      CF := C.P.CF, CF_pos := p_CF
      qd_pow := h_qd_pow
      logq_ge := h_logq_ge
      logDerivative_le_power := h_dlogL1_le
      condE_le := h_condE_le
      pde_log := h_pde_log
      k_low := h_k_low
      k_up := h_k_up
      radius_ge_sqrt_ratio := h_R0_ge
      k_ge_m2L := h_k_ge_m2L
      k_ge_mx := h_k_ge_mx
      klogk := h_klogk
      flogk := h_flogk
      logf_le := h_logf_le
      log_sq_conductor_le := h_log2f_le
      loglogb := h_loglogb
      nW_ge := h_nW_ge
      eta_le := h_eta_le
      logeta := h_logeta
      t_le_eta := h_t_le_eta
      teta := h_teta
      mteta := h_mteta
      mSeta := h_mSeta
      Neta := h_Neta
      eta2 := h_eta2
      kS_le := h_kS_le
      TT_card_le := h_TT_card_le
      rho_le := h_rho_le
      bT_le := h_bT_le
      S_le := h_S_le
      Del_le := h_Del_le
      logDel := h_logDel
      Lw_j := h_Lw_j
      Lw_le := h_Lw_le
      jetIndex_le_log := h_j0_le
      topPlace_first_bound := h_top_b1
      cloud_place_bound := h_cloud_le2
      uk_extreme := h_uk_extreme
      em_win := h_em_win
      nodes_gap := h_nodes_gap
      e_centred := h_e_centred
      e_mu := fun j => (h_e_parity j).num
      etaF_eq := h_etaF_eq
      pde_mod := h_pde_mod
      pde_ne := h_pde_ne
      ccK_log := h_ccK_log
      ccK_le := h_ccK_le
      lows_far := h_lows_far
      X''_ratio := h_X''_ratio
      bm_le := h_bm_le
      w''_ge := h_w''_ge
      Del_ge := h_Del_ge
      Del_count := h_Del_count
      h0_ge := h_h0_ge
      heightBound_ge_rank_cubic := h_h0_fun
      heightBound_ge_degree_power := h_h0_fN
      sig_gaps := h_sig_gaps
      rbS := h_rbS
      lstar1 := h_lstar1
      lstar2 := h_lstar2
      words_le := h_words_le
      g_Y := h_g_Y
      g_norm := hA.1
      g_mod := hA.2.1
      pde_split := hA.2.2.1
      level_split := hA.2.2.2 }, rfl, rfl⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgree
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
open GlobalTheory.IdealTransport GlobalTheory.InertSign GlobalTheory.ThetaLatImage

noncomputable section

namespace GlobalTheory.PeriodTransport

section Fields

variable {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E') {n a b : ℕ}

def vecT (n : ℕ) : (Fin n → E) ≃+ (Fin n → E') := AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv

theorem vecT_smul (r : 𝓞 E) (x : Fin n → E) : vecT e n (r • x) = RingOfIntegers.mapRingEquiv e r • vecT e n x :=
  funext fun i => map_smul_int e r (x i)

theorem trL_fg {N : Submodule (𝓞 E) (Fin n → E)} (h : N.FG) : (trL e N).FG := by
  obtain ⟨S, hS, rfl⟩ := Submodule.fg_def.1 h
  exact Submodule.fg_def.2 ⟨_, hS.image (vecT e n),
    (span_image_span (RingOfIntegers.mapRingEquiv e) (vecT e n) (vecT_smul e) S).symm⟩

theorem trL_span {N : Submodule (𝓞 E) (Fin n → E)} (h : Submodule.span E (N : Set (Fin n → E)) = ⊤) :
    Submodule.span E' (trL e N : Set (Fin n → E')) = ⊤ := by
  have h1 := span_image_span e (vecT e n) (fun r x => funext fun i => map_mul e r (x i)) (N : Set (Fin n → E))
  rw [h, Submodule.top_coe, Set.image_univ, (vecT e n).surjective.range_eq, Submodule.span_univ] at h1
  refine top_le_iff.1 (h1.le.trans (Submodule.span_mono ?_))
  exact Submodule.subset_span

def matT (a b : ℕ) : HomE E a b ≃+ Matrix (Fin b) (Fin a) E' :=
  (LinearMap.toMatrix' (R := E) (m := Fin b) (n := Fin a)).toAddEquiv.trans e.toAddEquiv.mapMatrix

theorem matT_apply (x : HomE E a b) (i : Fin b) (j : Fin a) : matT e a b x i j = e (x (Pi.single j 1) i) := by
  change e (LinearMap.toMatrix' x i j) = _
  rw [LinearMap.toMatrix'_apply]

theorem matT_smul (r : E) (x : HomE E a b) : matT e a b (r • x) = e r • matT e a b x := by
  ext i j
  simp [matT_apply]

theorem matT_smul_int (r : 𝓞 E) (x : HomE E a b) :
    matT e a b (r • x) = RingOfIntegers.mapRingEquiv e r • matT e a b x := by
  ext i j
  rw [Matrix.smul_apply, matT_apply, matT_apply, ← map_smul_int]
  rfl

theorem matT_mulVec (x : HomE E a b) (v : Fin a → E') :
    (fun i => e.symm ((matT e a b x).mulVec v i)) = x fun j => e.symm (v j) := by
  funext i
  rw [← LinearMap.toMatrix'_mulVec]
  simp [Matrix.mulVec, dotProduct, matT_apply]

theorem matT_carries (N : Submodule (𝓞 E) (Fin a → E)) (N' : Submodule (𝓞 E) (Fin b → E)) (x : HomE E a b) :
    (∀ v ∈ trL e N, (matT e a b x).mulVec v ∈ trL e N') ↔ ∀ y ∈ N, x y ∈ N' := by
  simp only [mem_trL, matT_mulVec]
  refine ⟨fun H y hy => ?_, fun H v hv => H _ hv⟩
  simpa using H (fun i => e (y i)) (by simpa using hy)

end Fields

variable {X : Fields} {D : D7} (s : Seam D X)

theorem sd_lat (hs : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (h : IsSdLat N) : StandardLatticesGL3.SD D (s.lat N) := by
  have hspan : Submodule.span X.E (N : Set (Sp X.E n)) = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro f hf
    let v : Sp X.E n := fun i => star (f (Pi.single i 1))
    have hpair : hStd X.E n v = f := by
      apply (Pi.basisFun X.E (Fin n)).ext
      intro i
      rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [hj]
      · simp
    have hline (r : X.E) : r • v ∈ N := by
      rw [← show dual (hStd X.E n) N = N from h.2, dualBasic_mem_dual]
      intro y hy
      have hy0 : hStd X.E n v y = 0 := by
        rw [hpair]
        exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
      have hz : hStd X.E n y v = 0 := by
        simpa [hy0] using ((hStd_isSymm (E := X.E) (n := n)).eq v y).symm
      simp [hz]
    have hv : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      let coord := (LinearMap.proj i : Sp X.E n →ₗ[X.E] X.E).restrictScalars (𝓞 X.E)
      have htop : N.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 X.E) X.E := Module.finite_def.mpr (htop ▸ h.1.fg.map coord)
      exact RingOfIntegers.not_isField X.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 X.E) X.E) (Field.toIsField X.E))
    rw [Submodule.mem_bot]
    simpa [hv] using hpair.symm
  refine (sd_iff D _).2 ⟨trL_fg s.iE h.1.fg, trL_span s.iE hspan, fun y => ?_⟩
  have key : ∀ x : Fin n → D.host.E, IntE D (hE D y x) ↔
      hStd X.E n (fun i => s.iE.symm (x i)) (fun i => s.iE.symm (y i)) ∈ (1 : Submodule (𝓞 X.E) X.E) := by
    intro x
    have e1 : hStd X.E n (fun i => s.iE.symm (x i)) (fun i => s.iE.symm (y i)) = s.iE.symm (hE D y x) := by
      apply s.iE.injective
      change s.iE (∑ i, star (s.iE.symm (x i)) * s.iE.symm (y i)) = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hs.2, RingEquiv.apply_symm_apply, hE, mul_comm]
    rw [e1, ← mem_one_iff, Submodule.mem_one]
    rfl
  have hm : ∀ x, x ∈ s.lat N ↔ (fun i => s.iE.symm (x i)) ∈ N := mem_trL s.iE N
  simp only [key, hm]
  conv_lhs => rw [← h.2, Formalism.L2.Col.mem_dual]
  refine ⟨fun H x hx => H _ hx, fun H x hx => ?_⟩
  simpa using H (fun i => s.iE (x i)) (by simpa using hx)

theorem mem_AA_iff {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (t : D.host.E) : t ∈ Iid D cc ↔ s.iE.symm t ∈ (ambOf s B χ cD).AA := by
  rw [← mem_trI]
  change _ ↔ t ∈ trI s.iE (Submodule.span _ _)
  rw [trI_span, Iid]
  congr! 2
  ext u
  constructor
  · rintro ⟨c, hc, a, ha, rfl⟩
    exact ⟨_, ⟨c, hc, a, ha, rfl⟩, s.iE.apply_symm_apply _⟩
  · rintro ⟨_, ⟨c, hc, a, ha, rfl⟩, rfl⟩
    exact ⟨c, hc, a, ha, s.iE.apply_symm_apply _⟩

theorem mem_RL_iff {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (z : Matrix (Fin b) (Fin a) D.host.E) :
    z ∈ RL D cc (s.lat N) (s.lat N') ↔ (matT s.iE a b).symm z ∈ perO (ambOf s B χ cD).AA N N' := by
  rw [← mem_span_image (RingOfIntegers.mapRingEquiv s.iE) (matT s.iE a b) (matT_smul_int s.iE), perO,
    span_image_span (RingOfIntegers.mapRingEquiv s.iE) (matT s.iE a b) (matT_smul_int s.iE), RL]
  congr! 2
  ext u
  constructor
  · rintro ⟨t, ht, A, hA, rfl⟩
    obtain ⟨x, rfl⟩ := (matT s.iE a b).surjective A
    refine ⟨_, ⟨_, (mem_AA_iff s B χ cD t).1 ht, x, (matT_carries s.iE N N' x).1 (mem_homL.1 hA), rfl⟩, ?_⟩
    rw [matT_smul, RingEquiv.apply_symm_apply]
  · rintro ⟨_, ⟨r, hr, x, hx, rfl⟩, rfl⟩
    exact ⟨s.iE r, (mem_AA_iff s B χ cD _).2 (by simpa using hr), _,
      mem_homL.2 ((matT_carries s.iE N N' x).2 hx), matT_smul _ _ _⟩

theorem seam_lattices : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → (∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N → StandardLatticesGL3.SD D (s.lat N)) ∧ ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : VCx X.Tau a b), z ∈ lam (ambOf s B χ cD) N N' ↔ (fun τ => z (s.iT.symm τ)) ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N') := by
  intro X D s cc δ B χ cD hs
  refine ⟨fun n N h => sd_lat s hs h, fun a b N N' z => ?_⟩
  have hpt : ∀ (x : HomE X.E a b) (τ : X.Tau), embH (X.embC s.σ₀) δ x τ =
      StandardLatticesGL3.pt D (TaylorLogMetric.tor0 D cc δ) δ (matT s.iE a b x) (s.iT τ) := by
    intro x τ
    funext i j
    rw [pt_apply, matT_apply, ← hs.1]
    rfl
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 := pt_mem_La (δ := δ) ((mem_RL_iff s B χ cD N N' (matT s.iE a b x)).2 (by simpa using hx)) 1
    rw [one_smul] at h1
    convert h1 using 1
    funext τ
    exact (hpt x _).trans (by rw [Equiv.apply_symm_apply])
  · intro h
    obtain ⟨w, hw, e⟩ := La_sub h
    refine ⟨_, (mem_RL_iff s B χ cD N N' w).1 hw, funext fun τ => (hpt _ τ).trans ?_⟩
    rw [AddEquiv.apply_symm_apply, ← e]
    exact congrArg z (s.iT.symm_apply_apply τ)

end GlobalTheory.PeriodTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem fc_large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem small_prime_lt (eps C8 : ℝ) (he : 0 < eps) (h8 : 1 ≤ C8) : ∃ x0 : ℝ, ∀ (s : Scale) (N q0 : ℝ), s.eps = eps → x0 ≤ s.x →
    0 < N → Real.log N ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 → q0 ≤ N ^ C8 → q0 < s.X' := by
  obtain ⟨x0, hx0⟩ := GlobalTheory.scale_poly_comparison eps (2 * C8) (1 / 2) he (by norm_num)
  refine ⟨x0, fun s N q0 hs hx hN hlog hq => ?_⟩
  have h := (hx0 s hs hx).2.2.2.2.2.2
  have hx1 := s.one_lt_alt
  have h1 : 1 ≤ s.x ^ (2 * C8) := Real.one_le_rpow hx1.le (by linarith)
  have hX : 1 < s.X' := Real.one_lt_exp_iff.2 (Real.rpow_pos_of_pos (by linarith) _)
  have h2 : s.X' ^ (1 / 2 : ℝ) < s.X' := by
    calc s.X' ^ (1 / 2 : ℝ) < s.X' ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hX (by norm_num)
      _ = s.X' := Real.rpow_one _
  have h3 : N ^ C8 ≤ Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) := by
    rw [Real.rpow_def_of_pos hN]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hlog (by linarith : (0 : ℝ) ≤ C8)
    linarith
  have h4 : Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) ≤
      Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) * s.x ^ (2 * C8) :=
    le_mul_of_one_le_right (Real.exp_pos _).le h1
  linarith

theorem X'_le_b (s : Scale) : s.X' ≤ s.b := by
  have := s.eps_pos
  exact Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith))

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWDelAtrIff
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.WeylLocOnePlace

theorem rhoVr_inv_coe {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n : ℕ} (lam : ι → DomWeight n) (B : GL (Fin n) E) (F : Formalism.L2.DIV.VV K lam) :
    (rhoVr emb lam B⁻¹ F).1 = actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 := by
  have e : (invTrK.comp (embGL emb)) B⁻¹ = (vlBdF emb (fun _ : ι => B))⁻¹ := by
    rw [map_inv]
    rfl
  show (rhoK lam ((invTrK.comp (embGL emb)) B⁻¹) F).1 = _
  rw [e]
  rfl

theorem mem_locW_delAtr_iff : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K)), (∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) → ∀ {n : ℕ} (lam lam' : ι → DomWeight n), (∀ τ, (lam τ).natW = (lam' τ).natW) → ∀ (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E M → ∀ (w : Pl.Pl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (M : Set (Fin n → E)) B → ∀ F : Formalism.L2.DIV.VV K lam, F ∈ locW Pl w (delAtr emb lam M) ↔ MvPolynomial.map σ (rhoVr emb lam B⁻¹ F).1 ∈ vlIntSpan σ Pl w lam' := by
  intro E K ι _ _ _ _ _ _ _ emb σ Pl pw hval n lam lam' hn M hM w B hB F
  have hbas : ∀ τ, IsBasisAt (pw w) (dualFr (tauLat emb τ M)) (vlBdF emb (fun _ : ι => B) τ) := fun τ =>
    pb_isBasisAt_dualFr (pw w) _ (tauLatticeLattice_holds E K ι n emb τ M hM).fg _
      (vl_isBasisAt_tauLat Pl pw hval emb τ w M B hB)
  have hlat : ∀ τ, Submodule.IsFullLattice K (dualFr (tauLat emb τ M)) := fun τ =>
    du_dualFr_lattice latticeBasisExists_holds _ (tauLatticeLattice_holds E K ι n emb τ M hM)
  have h0 : F ∈ locW Pl w (delAtr emb lam M) ↔ F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) :=
    vl_mem_span_intW_iff Pl pw hval w _ F
  have hmem : F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) ↔
      actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delStd K lam) := by
    have h1 : F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) ↔
        F.1 ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delP lam fun τ => dualFr (tauLat emb τ M)) := Iff.rfl
    rw [h1, (nablaDeltaLocal_holds K ι n lam _ hlat (pw w) _ hbas).2]
    constructor
    · rintro ⟨G, hG, hGF⟩
      have e : actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 = G := by
        rw [← hGF]
        show actP lam (vlBdF emb (fun _ : ι => B))⁻¹ (actP lam (vlBdF emb (fun _ : ι => B)) G) = G
        rw [← polyAction_mul, inv_mul_cancel, polyAction_one₂]
      rw [e]
      exact hG
    · intro h
      refine ⟨_, h, ?_⟩
      show actP lam (vlBdF emb (fun _ : ι => B)) (actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1) = F.1
      rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  rw [h0, hmem, rhoVr_inv_coe]
  constructor
  · intro h
    exact vl_map_mem_intSpan Pl pw hval σ w lam lam' hn h
  · intro h
    obtain ⟨G, hG, hGe⟩ := vl_exists_of_mem_intSpan Pl pw hval σ w lam lam' hn h
    have hG' : actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 = G :=
      (MvPolynomial.map_injective σ σ.injective hGe).symm
    rw [hG']
    exact hG

end GlobalTheory.WeylLocOnePlace
end
end

