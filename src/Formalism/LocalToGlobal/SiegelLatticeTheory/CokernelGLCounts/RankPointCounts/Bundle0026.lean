module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTiePl
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NinfConjIff
section
noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.KappaOffDiagonal

open Matrix

namespace Formalism.L2.SG.CovariantRepresentation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {n r : ℕ}

theorem hJ_unitary (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ) (hU : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.REAL.Jm ε)
    (x y : Fin n → ℂ) : hJ ε (P *ᵥ x) (P *ᵥ y) = hJ ε x y := by
  delta hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]

theorem fix_span (e : Fin r → Fin n → ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (he : ∀ a, Q *ᵥ e a = e a) (k : ℕ) :
    ∀ x ∈ spanLt e k, Q *ᵥ x = x := by
  delta spanLt
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    exact he a
  | zero => exact Matrix.mulVec_zero Q
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz]
  | smul c y _ hy => rw [Matrix.mulVec_smul, hy]

theorem inN_conj (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (P Q g : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (hU : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.REAL.Jm ε) (he : ∀ a, P *ᵥ e a = e a) (hz : P *ᵥ z = z)
    (hg : InN ε e z g) : InN ε e z (Q * g * P) := by
  have hQv' : ∀ v, Q *ᵥ (P *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  have hQv : ∀ v, P *ᵥ v = v → Q *ᵥ v = v := fun v hv =>
    calc Q *ᵥ v = Q *ᵥ (P *ᵥ v) := by rw [hv]
      _ = v := hQv' v
  have hQe : ∀ a, Q *ᵥ e a = e a := fun a => hQv (e a) (he a)
  have key : ∀ (v : Fin n → ℂ) (k : ℕ), P *ᵥ v = v → (g - 1) *ᵥ v ∈ spanLt e k →
      (Q * g * P - 1) *ᵥ v ∈ spanLt e k := by
    intro v k hv hw
    have h : (Q * g * P - 1) *ᵥ v = Q *ᵥ ((g - 1) *ᵥ v) := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_sub, hQv v hv]
    rw [h, fix_span e Q hQe k _ hw]
    exact hw
  obtain ⟨⟨h1a, h1b⟩, h2⟩ := hg
  refine ⟨⟨fun a => key (e a) a (he a) (h1a a), key z r hz h1b⟩, fun y hy => ?_⟩
  have hy' : ∀ a, hJ ε (e a) (P *ᵥ y) = 0 := fun a =>
    calc hJ ε (e a) (P *ᵥ y) = hJ ε (P *ᵥ e a) (P *ᵥ y) := by rw [he a]
      _ = hJ ε (e a) y := hJ_unitary ε P hU (e a) y
      _ = 0 := hy a
  have hw := h2 (P *ᵥ y) hy'
  have h : (Q * g * P - 1) *ᵥ y = Q *ᵥ ((g - 1) *ᵥ (P *ᵥ y)) := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, hQv' y]
  rw [h, fix_span e Q hQe r _ hw]
  exact hw

end Mat

section Grp

variable {D : D7} (X : HidaSetting D)

theorem fix_inv (s : X.B.I.Ginf) {v : InfinitePlace X.B.I.F} {x : Fin X.B.I.n → ℂ} (hx : uMat (s v) *ᵥ x = x) :
    uMat (s⁻¹ v) *ᵥ x = x := by
  have h1 : uMat (s⁻¹ v) * uMat (s v) = 1 := by
    delta uMat
    simp
  calc uMat (s⁻¹ v) *ᵥ x = uMat (s⁻¹ v) *ᵥ (uMat (s v) *ᵥ x) := by rw [hx]
    _ = x := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem ninf_conj (u : D.what₂.Word) (s : X.B.I.Ginf)
    (he : ∀ v a, uMat (s v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : ∀ v, uMat (s v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u))
    {r : X.B.I.Ginf} (hr : r ∈ X.NinfU u) : s⁻¹ * r * s ∈ X.NinfU u := by
  dsimp [HidaSetting.NinfU, Ninf] at hr ⊢
  intro v
  have h1 : uMat (s⁻¹ v) * uMat (s v) = 1 := by
    delta uMat
    simp
  have hmul : uMat ((s v)⁻¹ * r v * s v) = uMat (s⁻¹ v) * uMat (r v) * uMat (s v) := by
    delta uMat
    simp
  have hU : (uMat (s v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (s v) = Formalism.REAL.Jm (X.B.I.ε v) := by
    delta uMat
    first
    | exact (s v).2
    | exact (s v).1.2
    | simpa using (s v).2
  rw [hmul]
  exact inN_conj _ _ _ (uMat (s v)) (uMat (s⁻¹ v)) (uMat (r v)) h1 hU (he v) (hz v) (hr v)

theorem ninf_conj_iff (u : D.what₂.Word) (s : X.B.I.Ginf)
    (he : ∀ v a, uMat (s v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : ∀ v, uMat (s v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)) (r : X.B.I.Ginf) :
    r ∈ X.NinfU u ↔ s⁻¹ * r * s ∈ X.NinfU u := by
  constructor
  · exact ninf_conj X u s he hz
  · intro h
    have he' : ∀ v a, uMat (s⁻¹ v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
      fun v a => fix_inv X s (he v a)
    have hz' : ∀ v, uMat (s⁻¹ v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
      fun v => fix_inv X s (hz v)
    have h2 := ninf_conj X u s⁻¹ he' hz' h
    simpa [mul_assoc] using h2

end Grp


open Formalism.L2.SG.TermOp.Vanish in
theorem fixNormC : FixNormC := by
  intro D X Y u u' t h hh r
  have hfe : ∀ v a, uMat (h v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
    fun v a => fix_rv hh (basis_mem_fixedSubspace t.rep a) v
  have hfz : ∀ v, uMat (h v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
    fun v => fix_rv hh (zu_mem_fixedSubspaceOfRepresentative t.rep) v
  have hfe' : ∀ v a, uMat ((t.pt.1⁻¹ * h * t.pt.1) v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
    fun v a => fix'_rv hh (ge_mem_fixedSubspace t.rep a) v
  have hfz' : ∀ v, uMat ((t.pt.1⁻¹ * h * t.pt.1) v) *ᵥ rv X.B.I v (X.zR u') = rv X.B.I v (X.zR u') :=
    fun v => fix'_rv hh (gz_mem_fixedSubspace t.rep) v
  have e : t.pt.1⁻¹ * (h⁻¹ * r * h) * t.pt.1 =
      (t.pt.1⁻¹ * h * t.pt.1)⁻¹ * (t.pt.1⁻¹ * r * t.pt.1) * (t.pt.1⁻¹ * h * t.pt.1) := by group
  show (r ∈ X.NinfU u ∧ t.pt.1⁻¹ * r * t.pt.1 ∈ X.NinfU u') ↔
    (h⁻¹ * r * h ∈ X.NinfU u ∧ t.pt.1⁻¹ * (h⁻¹ * r * h) * t.pt.1 ∈ X.NinfU u')
  rw [e, ← ninf_conj_iff X u h hfe hfz r, ← ninf_conj_iff X u' _ hfe' hfz' (t.pt.1⁻¹ * r * t.pt.1)]

end Formalism.L2.SG.CovariantRepresentation
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelevantSetZeroGNotIdentity
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZsC1b

variable {D : D7} {X : HidaSetting D}

theorem fixedFlag_level_ne_zero (D : D7) (u : D.what₂.Word) : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero

theorem relevantSet_zeroG_not_identity {Y : Full X} {u : D.what₂.Word} {t : GTu Y u} (ht : t ∈ relSet Y u) :
    t.relevant ∧ t.G = 0 ∧ ¬ t.isId := by
  obtain ⟨⟨hG, hid⟩, hr⟩ := ht
  refine ⟨hr, ?_, hid⟩
  have h : Gt t = 0 := hG
  unfold Gt at h
  by_contra hne
  rw [if_neg hne] at h
  exact one_ne_zero h

theorem exists_nfFull_of_relevant_of_G_eq_zero (Y : Full X) {u : D.what₂.Word} (t : GTu Y u) (hr : t.relevant) (hG : t.G = 0) :
    ∃ (j : ℕ) (hj : j ≤ D.R.rS) (c : D.host.E),
      Formalism.HermitianLatticeCounting.S6.NFFull (nfF (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u)) (nfF (frq X t.rep).fl (nf_T_ne D u)) j hj c := by
  obtain ⟨hrel, hG0⟩ := relRepC D X Y u u t hr hG
  obtain ⟨σ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hpos : 0 < (σ ((Tu D u : ℕ) : D.host.E)).re := by
    rw [map_natCast, Complex.natCast_re]
    exact_mod_cast tie_Tu_pos D u
  refine Formalism.HermitianLatticeCounting.Final.S6.normalForm D.host.E (hS D).V σ (nfH (hS D)) D.R.rS _ _ (fun x => p_starConj D σ x)
    hpos hpos (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u) _) σ) (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u) _) σ)
    (nf_rel D.host.F (tie_trace D.sp.cm) _ _ _ _ hrel) ?_
  rw [nf_G (lf D (X.Fu u)).fl (frq X t.rep).fl (fixedFlag_level_ne_zero D u) (nf_T_ne D u)]
  exact hG0

theorem index_eq_normalForm {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) {j : ℕ} {hj : j ≤ D.R.rS} {c : D.host.E}
    (hN : Formalism.HermitianLatticeCounting.S6.NFFull (nfF (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u)) (nfF (frq X t.rep).fl (nf_T_ne D u)) j hj c) :
    jT t = j := by
  have hfin := hN.1.2.1
  rw [nf_II (lf D (X.Fu u)).fl (frq X t.rep).fl (fixedFlag_level_ne_zero D u) (nf_T_ne D u)] at hfin
  unfold jT
  rw [hfin]
  omega

theorem realAbs_zero_eq_one (rd : ℝ) (τ : D.host.E →+* ℂ) (x : D.host.E) (hx : x = 1) :
    absReal rd τ D.R.rS 0 x = 1 := by
  subst hx
  simp [absReal, frameExp]

theorem delta_pos_le_height_sq (hPF : PFHost D) (large₂ : SizeData₂ D) {CH C : ℝ} (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C)
    {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) (ht : t ∈ relSet Y u) :
    0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
  obtain ⟨hr, hG, -⟩ := relevantSet_zeroG_not_identity ht
  obtain ⟨j, hj, c, hN⟩ := exists_nfFull_of_relevant_of_G_eq_zero Y t hr hG
  have hjT := index_eq_normalForm t hN
  have hD : Dl (lf D (X.Fu u)).fl (frq X t.rep).fl j ≠ 0 := (nf_gen _ _ _ _ j hj c hN).2.2.2.1
  have hlab : labT t (jT t) = Dl (lf D (X.Fu u)).fl (frq X t.rep).fl j := by
    unfold labT
    rw [if_pos le_rfl, hjT]
  have hdel : k2Del D (jT t) (labT t) =
      ∏ τ : D.what₂.Tau, absReal D.host.rdE (embS D τ) D.R.rS (jT t) (labT t (jT t)) ^ 2 := by
    unfold k2Del
    exact hPF _ _
  have hrd := pf_rd_pos D
  have hpos : ∀ τ, 0 < absReal D.host.rdE (embS D τ) D.R.rS (jT t) (labT t (jT t)) := by
    intro τ
    unfold absReal
    rw [hlab]
    exact mul_pos (norm_pos_iff.2 ((map_ne_zero _).2 hD)) (Real.rpow_pos_of_pos hrd _)
  refine ⟨by rw [hdel]; exact Finset.prod_pos fun τ _ => pow_pos (hpos τ) 2, ?_⟩
  rw [hdel]
  have hb := two_le_scale_b D large₂
  have hH1 : 1 ≤ H1C large₂ CH := by
    unfold H1C
    exact Real.one_le_rpow (by linarith) (by positivity)
  unfold k2S
  rw [← Finset.prod_pow]
  refine Formalism.HermitianLatticeCounting.Final.S6.normSgBound D.what₂.Tau D.R.rS D.R.f _ _ (H1C large₂ CH) _ (szf_card_Tau D)
    (by linarith) (two_pow_le_height_bound _ CH C _ _ _ hb (two_rank_add_two_eq_m D) hCH hC) (fun τ => (hpos τ).le) (fun τ => ?_) (fun τ => ?_)
  · exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  · rcases Nat.eq_zero_or_pos (jT t) with h0 | h0
    · have hl0 : labT t (jT t) = 1 := by
        rw [hlab, ← hjT, h0]
        unfold Dl leadMinorE
        simp
      have h1 : absReal D.host.rdE (embS D τ) D.R.rS (jT t) (labT t (jT t)) = 1 := by
        rw [h0] at hl0 ⊢
        exact realAbs_zero_eq_one _ _ _ hl0
      rw [h1]
      have h2 : (1 : ℝ) ≤ (2 * H1C large₂ CH) ^ (2 * D.R.rS) := one_le_pow₀ (by linarith)
      have h3 : (1 : ℝ) / (2 * H1C large₂ CH) ^ (2 * D.R.rS) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact h2
      exact h3.trans ((Finset.le_fold_max _).2 (Or.inl le_rfl))
    · have hmem : jT t ∈ k2ends D (jT t) (labT t) := by
        unfold k2ends
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨h0, le_rfl⟩, by rw [hlab]; exact hD⟩
      exact (Finset.le_fold_max _).2 (Or.inr ⟨jT t, hmem, le_rfl⟩)

theorem localNorm_le_height_sq (hPF : PFHost D) (large₂ : SizeData₂ D) {CH C : ℝ} (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C)
    {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) (l : ℕ) (hl : l ∈ k2ends D (jT t) (labT t)) :
    ((Nloc (ddS D) D.R.rS l (labT t l) : ℚ) : ℝ) ≤
      Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
  have hb := two_le_scale_b D large₂
  have hH1 : 1 ≤ H1C large₂ CH := by
    unfold H1C
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hrd := pf_rd_pos D
  rw [hPF]
  unfold k2S
  rw [← Finset.prod_pow]
  refine Formalism.HermitianLatticeCounting.Final.S6.normSgBound D.what₂.Tau D.R.rS D.R.f _ _ (H1C large₂ CH) _ (szf_card_Tau D)
    (by linarith) (two_pow_le_height_bound _ CH C _ _ _ hb (two_rank_add_two_eq_m D) hCH hC) (fun τ => ?_) (fun τ => ?_) (fun τ => ?_)
  · unfold absReal
    positivity
  · exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  · exact (Finset.le_fold_max _).2 (Or.inr ⟨l, hl, le_rfl⟩)

end ZsC1b

theorem DelC_holds : DelC := by
  intro Cg cb Cw cT CT C0 CH hCH
  refine ⟨2 * (CH + 1), fun C hC => ⟨0, 0, fun C' Cl _ _ D large₂ X Y u hH _ t ht => ?_⟩⟩
  exact delta_pos_le_height_sq (PFHost_of_data D hH.1.2.1) large₂ hCH hC t ht

end Formalism.L2.SG.KappaOffDiagonal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SummableLogAlpD
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.AlTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.DataInst

variable {D : D7} (X : HidaSetting D)

theorem alX_eq (hEta : EtaTie X) (u u' : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    alX X u u' v = alpD u u' (plEquiv X v) := by
  have haP : ∀ T : ℕ, aP (E := X.B.I.E) v D.R.k X.B.I.n T = aPD (plEquiv X v) T := by
    intro T
    unfold aP aPD
    have hI : Finset.Icc (if ((T : 𝓞 X.B.I.F) ∈ v.asIdeal) then D.R.k else D.R.k + 1) X.B.I.n =
        Finset.Icc (if ((T : 𝓞 D.host.F) ∈ (plEquiv X v).asIdeal) then D.R.k else D.R.k + 1) D.R.r := by
      rw [X.n_eq]
      by_cases hm : ((T : 𝓞 X.B.I.F) ∈ v.asIdeal)
      · rw [if_pos hm, if_pos ((natCast_mem_plEquiv X v T).2 hm)]
      · rw [if_neg hm, if_neg (fun h => hm ((natCast_mem_plEquiv X v T).1 h))]
    rw [hI]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hEta v, absNorm_plEquiv]
  unfold alX alpD Tw
  rw [haP, haP]
  by_cases h : TypAt X v
  · rw [if_pos h, if_pos ((typAt_iff X v).1 h)]
  · rw [if_neg h, if_neg (fun h' => h ((typAt_iff X v).2 h'))]

theorem summable_log_alpD (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word) :
    (∀ p, 0 < alpD u u' p) ∧ Summable fun p => Real.log (alpD u u' p) := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  have hα := Formalism.L2.SG.IntegralApproximation.AlpBound_holds D
  set s := D.R.k - 2 * D.R.rS - 2 with hs
  have hs2 : 2 ≤ s := by omega
  set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hs2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum
  have hαb := hα hk u u'
  have hal0 : ∀ p, 0 < alpD u u' p := fun p => lt_of_lt_of_le (Real.exp_pos _) (hαb p).1
  refine ⟨hal0, ?_⟩
  refine Summable.of_norm_bounded (g := fun p => 2 * a p) (haS.mul_left 2) (fun p => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have h1 := Real.log_le_log (Real.exp_pos _) (hαb p).1
  have h2 := Real.log_le_log (hal0 p) (hαb p).2
  rw [Real.log_exp] at h1 h2
  have ha' : a p = (Formalism.L2.SG.DataCut.qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹ := rfl
  constructor <;> linarith

theorem prod_split {β : Type} (f : β → ℝ) (s : Finset β) (hpos : ∀ v, 0 < f v)
    (hlog : Summable fun v => Real.log (f v)) :
    (∏ p : ↥s, f p.1) * ∏' v : {v // v ∉ s}, f v.1 = ∏' v, f v := by
  have hls : Summable (fun v : {v // v ∉ s} => Real.log (f v.1)) :=
    hlog.comp_injective (i := fun v : {v // v ∉ s} => v.1) Subtype.val_injective
  have hO : ∏' v : {v // v ∉ s}, f v.1 = Real.exp (∑' v : {v // v ∉ s}, Real.log (f v.1)) :=
    (Real.rexp_tsum_eq_tprod (f := fun v : {v // v ∉ s} => f v.1) (fun v => hpos v.1) hls).symm
  have hT : ∏ p : ↥s, f p.1 = Real.exp (∑ p : ↥s, Real.log (f p.1)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun p _ => (Real.exp_log (hpos _)).symm
  have hsplit : ∑ p : ↥s, Real.log (f p.1) + ∑' v : {v // v ∉ s}, Real.log (f v.1) = ∑' v, Real.log (f v) := by
    rw [Finset.sum_coe_sort s (fun x => Real.log (f x))]
    exact hlog.sum_add_tsum_compl (s := s)
  rw [hO, hT, ← Real.exp_add, hsplit, Real.rexp_tsum_eq_tprod hpos hlog]

theorem locOf_al_eq (hEta : EtaTie X) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) :
    (locOf X u u' ψ).al = ∏' q, alpD u u' q := by
  obtain ⟨hpos, hlog⟩ := summable_log_alpD hk u u'
  have he : ∀ v, alX X u u' v = alpD u u' (plEquiv X v) := alX_eq X hEta u u'
  have hxpos : ∀ v, 0 < alX X u u' v := fun v => (he v).symm ▸ hpos _
  have hxlog : Summable fun v => Real.log (alX X u u' v) := by
    have h1 : Summable fun v => Real.log (alpD u u' (plEquiv X v)) := (plEquiv X).summable_iff.2 hlog
    exact h1.congr fun v => by rw [he v]
  have hS := prod_split (alX X u u') (Formalism.L2.SG.TypedSets.typSet X.B.I.F (D.host.g 0) (D.host.g 1)) hxpos hxlog
  have hR : ∏' v, alX X u u' v = ∏' q, alpD u u' q := by
    rw [tprod_congr he]
    exact (plEquiv X).tprod_eq (alpD u u')
  rw [← hR, ← hS]
  rfl

end Formalism.L2.SG.Pf.AlTie

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm Formalism.L2.SG.Pf.RowForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem AlTieC_of {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hEta : AlTie.EtaTie X) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) :
    AlTieC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq := by
  unfold AlTieC
  exact AlTie.locOf_al_eq X hEta hk u u' ψ

theorem AlTieC_of_loc {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) :
    AlTieC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq :=
  AlTieC_of X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq (AlTie.etaTie_of X hL) hk

end Formalism.L2.SG.Pf
end
end

