module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleSimpleCharZero
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.AlcZero

theorem eq_of_hcVal_eq_charZero (k : Type) [Field k] [CharZero k] (N : ℕ) (ν μ : Fin N → ℕ)
    (hν : Antitone ν) (hμ : Antitone μ) (hc : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩)
    (hv : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j) : μ = ν := by
  have hZ : ∀ j, hcVal ℤ (fun i => (μ i : ℤ)) j = hcVal ℤ (fun i => (ν i : ℤ)) j := by
    intro j
    apply Int.cast_injective (α := k)
    have h1 := hcVal_map (Int.castRingHom k) (fun i => (μ i : ℤ)) j
    have h2 := hcVal_map (Int.castRingHom k) (fun i => (ν i : ℤ)) j
    simp only [eq_intCast, Int.cast_natCast] at h1 h2
    rw [← h1, ← h2]
    exact hv j
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (∑ i, ν i + N)
  haveI := Fact.mk hp
  apply eq_of_hcVal_eq p hp (ZMod p) N ν μ hν hμ
  · intro h
    refine ⟨(hc h).1, (hc h).2, ?_⟩
    have : ν ⟨0, h⟩ ≤ ∑ i, ν i := Finset.single_le_sum (fun i _ => Nat.zero_le (ν i)) (Finset.mem_univ _)
    omega
  · intro j
    have h1 := hcVal_map (Int.castRingHom (ZMod p)) (fun i => (μ i : ℤ)) j
    have h2 := hcVal_map (Int.castRingHom (ZMod p)) (fun i => (ν i : ℤ)) j
    simp only [eq_intCast, Int.cast_natCast] at h1 h2
    rw [h1, h2, hZ j]

end GlobalTheory.AlcZero

namespace GlobalTheory.AlcZero

theorem map_rowAct_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {N : ℕ}
    (g : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) R) :
    MvPolynomial.map φ (rowAct R (n := N) g f) = rowAct S (n := N) (g.map φ) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [rowAct, map_sum, Matrix.map_apply]

theorem map_mem_span_map {S A : Type} [CommRing S] [CommRing A] (ψ : S →+* A) {σ : Type}
    (X : Set (MvPolynomial σ S)) (P : MvPolynomial σ S) (hP : P ∈ Submodule.span S X) :
    MvPolynomial.map ψ P ∈ Submodule.span A (MvPolynomial.map ψ '' X) := by
  induction hP using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [(MvPolynomial.map ψ).map_add]; exact add_mem hy hz
  | smul c y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

theorem isGLSubmodule_of_stable (k : Type) [Field k] [Infinite k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k))
    (hG : ∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) : GlobalTheory.Published.IsGLSubmodule k N lam M := by
  intro A _ _ g f hf
  let S := MvPolynomial (Fin N × Fin N) k
  let Y : Matrix (Fin N) (Fin N) S := Matrix.mvPolynomialX (Fin N) (Fin N) k
  let P : MvPolynomial (Fin N × Fin N) S :=
    rowAct S (n := N) Y.transpose (MvPolynomial.map (algebraMap k S) f)
  have hP : P ∈ Submodule.span S (MvPolynomial.map (algebraMap k S) '' (M : Set (MvPolynomial (Fin N × Fin N) k))) := by
    refine GlobalTheory.T.mem_span_map_of_eval_mem_of_ne_zero k _ _ M Y.det (Matrix.det_mvPolynomialX_ne_zero _ _) P ?_
    intro y hy
    let m0 : Matrix (Fin N) (Fin N) k := Matrix.of fun i j => y (i, j)
    have hm0 : Y.map (MvPolynomial.eval y) = m0 := by
      ext i j; simp [Y, m0, Matrix.mvPolynomialX]
    have hdet : m0.det ≠ 0 := by
      rw [← hm0]; rw [RingHom.map_det] at hy; exact hy
    let g0 : GL (Fin N) k := Matrix.nonsingInvUnit m0 (isUnit_iff_ne_zero.mpr hdet)
    have h1 := hG g0 f hf
    have hu : detPow k N g0 lam.detShift ≠ 0 := Units.ne_zero _
    rw [sqAct, Submodule.smul_mem_iff M hu] at h1
    have e1 : MvPolynomial.map (MvPolynomial.eval y) P = rowAct k (n := N) (m0.transpose) f := by
      simp only [P]
      rw [map_rowAct_eq, MvPolynomial.map_map]
      have : (MvPolynomial.eval y).comp (algebraMap k S) = RingHom.id k := by
        ext a; simp [S]
      rw [this, MvPolynomial.map_id, Matrix.transpose_map, hm0]
    rw [e1]
    exact h1
  let ψ : S →+* A := MvPolynomial.eval₂Hom (algebraMap k A) fun v => (g : Matrix (Fin N) (Fin N) A) v.1 v.2
  have e2 : MvPolynomial.map ψ P =
      rowAct A (n := N) (g : Matrix (Fin N) (Fin N) A).transpose (MvPolynomial.map (algebraMap k A) f) := by
    simp only [P]
    rw [map_rowAct_eq, MvPolynomial.map_map]
    have h3 : ψ.comp (algebraMap k S) = algebraMap k A := by
      ext a; simp [ψ, S]
    have h4 : (Y.transpose).map ψ = (g : Matrix (Fin N) (Fin N) A).transpose := by
      ext i j
      simp only [Y, ψ, Matrix.mvPolynomialX, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, MvPolynomial.coe_eval₂Hom]
      exact MvPolynomial.eval₂_X _ _ _
    rw [h3, h4]
  have h5 := map_mem_span_map ψ _ P hP
  rw [Set.image_image] at h5
  have h6 : (fun x : MvPolynomial (Fin N × Fin N) k => MvPolynomial.map ψ (MvPolynomial.map (algebraMap k S) x)) =
      ⇑(MvPolynomial.map (σ := Fin N × Fin N) (algebraMap k A)) := by
    have h3 : ψ.comp (algebraMap k S) = algebraMap k A := by
      ext a; simp [ψ, S]
    funext x
    rw [MvPolynomial.map_map, h3]
  rw [h6, e2] at h5
  rw [sqAct]
  exact Submodule.smul_mem _ _ h5

end GlobalTheory.AlcZero

namespace GlobalTheory.AlcZero

theorem hw_mem_of_lt_charZero (k : Type) [Field k] [CharZero k] (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν)
    (hlast : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0)
    (M M' : Submodule k (MvPolynomial (Fin N × Fin N) k)) (hM : Good M) (hM' : Good M') (hlt : M < M')
    (hle : M' ≤ dualWeyl k N N ν) : hw k le_rfl ν ∈ M' ∧ hw k le_rfl ν ∉ M := by
  have dom := _root_.GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl k N ν
  obtain ⟨μ, v, hμ, hvM', hvM, hvw, hraise⟩ := _root_.GlobalTheory.Alc.exists_dominant_highest_vector_of_lt k N M M' hM hM' hlt
    ⟨∑ a, ν a, fun f hf m hm => ((dom f (hle hf) m hm).2).le⟩
  have hv0 : v ≠ 0 := fun h => hvM (h ▸ zero_mem M)
  have hwt := _root_.GlobalTheory.Alc.rowE_rowWeight k N N μ v hvw
  have hrel := (_root_.GlobalTheory.Alc.rowOperators_main k N N).1
  have hhw := _root_.GlobalTheory.Alc.trace_pow_hw k _ N (rowE k N N) hrel M (fun a b f hf => hM.1 a b f hf)
    (fun a => (μ a : k)) v hraise (fun a => by rw [hwt.1 a, sub_self]; exact zero_mem M)
  have hval : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j := by
    intro j
    by_contra hne
    have h1 := hhw j
    have h2 : gel k N N j v = hcVal k (fun i => (ν i : k)) j • v := _root_.GlobalTheory.Alc.gel_dualWeyl_field k N ν hν j v (hle hvM')
    change gel k N N j v - _ ∈ M at h1
    rw [h2, ← sub_smul] at h1
    exact hvM ((Submodule.smul_mem_iff M (sub_ne_zero.mpr (Ne.symm hne))).mp h1)
  obtain ⟨m, hm⟩ : v.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
  have hmμ : ∀ a, μ a = rowDeg m a := fun a => by
    rw [← hvw (mem_support_iff.mp hm)]; exact (weight_rowW_apply m a)
  have hcond : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ := by
    intro h
    refine ⟨hlast h, ?_⟩
    have hd := (dom v (hle hvM') m hm).1 1
    have hs : (Finset.univ.filter fun a : Fin N => a.val < 1) = {⟨0, h⟩} := by
      ext a; simp [Fin.ext_iff]
    rw [hs, Finset.sum_singleton, Finset.sum_singleton] at hd
    rw [hmμ]; exact hd
  have hμν : μ = ν := eq_of_hcVal_eq_charZero k N ν μ hν hμ hcond hval
  subst hμν
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.Alc.hw_line_field k N μ hν v (hle hvM') hvw
  have hc0 : c ≠ 0 := by rintro rfl; exact hv0 (by rw [hc, zero_smul])
  refine ⟨?_, fun h => hvM (hc ▸ M.smul_mem c h)⟩
  have : hw k le_rfl μ = c⁻¹ • v := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]; exact M'.smul_mem _ hvM'

theorem nablaSq_simple_charZero : ∀ (k : Type) [Field k] [CharZero k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)),
    M ≤ nablaSq k N lam → (∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) →
      M = ⊥ ∨ M = nablaSq k N lam := by
  intro k _ _ N lam M hM hG
  haveI : Infinite k := Infinite.of_injective _ Nat.cast_injective
  have hN := factNatW N lam
  by_contra hc
  push_neg at hc
  have hMg : Good M := good_of_isGLSubmodule k N lam M (isGLSubmodule_of_stable k N lam M hG)
  have key := hw_mem_of_lt_charZero k N lam.natW hN.1 hN.2.2
  have h1 := (key ⊥ M (good_top_bot k N N).2 hMg (bot_lt_iff_ne_bot.2 hc.1) hM).1
  have h2 := (key M (nablaSq k N lam) hMg (good_nablaSq k N lam) (lt_of_le_of_ne hM hc.2) le_rfl).2
  exact h2 h1

end GlobalTheory.AlcZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EgEqStep
section
open Formalism.BasicNotions Formalism.L2.SG.RowDict Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting MeasureTheory
open scoped Classical

noncomputable section

namespace GlobalTheory.Mem.GoodExpand

theorem eg_eq_step {D : D7} (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red) :
    eg X = fun x => if x ∈ X.B.I.Kset then D.ntypes.e0.coeff (red x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0 := by
  funext x
  unfold eg
  by_cases hx : x ∈ X.B.I.Kset
  · have hex : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ := ⟨hx, red x, hr.1 x hx⟩
    rw [dite_eq_left hex, if_pos hx,
      Formalism.L2.SG.Pf.rowDictEgWellDef_holds X x _ _ (Classical.choose_spec hex.2) (hr.1 x hx)]
  · rw [dite_eq_right (fun h => hx h.1), if_neg hx]

theorem rg_expand : ∀ (D : D7) (X : HidaSetting D) (G : GoodOp X) [Fintype (G0g D.nd)] (red : X.B.I.Gf → G0g D.nd) (s : G0g D.nd → X.B.I.Gf), IsRedHom X red → (∀ γ, s γ ∈ X.B.I.Kset ∧ red (s γ) = γ) → ∀ φ : L2X X, (∀ k ∈ X.B.I.Kg X.B.g, X.B.R (1, k) φ = φ) → G.Rg φ = ∑ γ, D.ntypes.e0.coeff γ • X.B.R (1, s γ) φ := by
  intro D X G _ red s hr hs φ hφ
  have hT := G.Rg_spec
  rw [eg_eq_step X hr] at hT
  refine GlobalTheory.Mem.SRe.ConvStep.top_expand X hr s hs (fun γ => D.ntypes.e0.coeff γ) G.Rg hT φ ?_
  intro k hk
  have hsk := (hs (red k)).1
  have hk' : (s (red k))⁻¹ * k ∈ X.B.I.Kg X.B.g :=
    (GlobalTheory.Mem.SRe.ConvStep.fibre_iff X hr hsk k).1 ⟨hk, ((hs (red k)).2).symm⟩
  have hmul := (GlobalTheory.RightRegFund.rightReg_unitary_continuous X.B).2.1
  have e : ((1, k) : X.B.I.GA) = (1, s (red k)) * (1, (s (red k))⁻¹ * k) := by
    ext
    · simp
    · simp
  rw [e, hmul]
  show X.B.R (1, s (red k)) (X.B.R (1, (s (red k))⁻¹ * k) φ) = _
  rw [hφ _ hk']

end GlobalTheory.Mem.GoodExpand
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNodeGapGeRankPow
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top Filter

namespace GlobalTheory.Mem.Top.NodeGap

theorem rank_le {s : Scale} {R : Ranks} (h : RankVal s R) (hx : 4 ≤ s.x) : (R.r : ℝ) ≤ s.x ^ 6 := by
  have h1 : (R.k : ℝ) ≤ 2 * s.x ^ (9 / 2 + 10 * s.eps) := h.2.2.1.2
  have h2 : s.x ^ (9 / 2 + 10 * s.eps) ≤ s.x ^ 5 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by have := s.eps_lt; push_cast; linarith)
  have h3 : R.r ≤ 2 * R.k := by have := R.m_add_three_le_k; unfold Ranks.r; omega
  have h4 : (R.r : ℝ) ≤ 2 * R.k := by exact_mod_cast h3
  have h5 : (0 : ℝ) < s.x ^ 5 := by positivity
  calc (R.r : ℝ) ≤ 4 * s.x ^ 5 := by linarith
    _ ≤ s.x * s.x ^ 5 := by gcongr
    _ = s.x ^ 6 := by ring

theorem le_m {s : Scale} {R : Ranks} (h : RankVal s R) {M : ℕ} (hx : (M : ℝ) ^ 4 ≤ s.x) : M ≤ R.m := by
  have h1 : Real.sqrt (s.x * s.delta1) ≤ (R.m : ℝ) := h.2.1.1
  have hx0 : 0 < s.x := by linarith [s.one_lt_alt]
  have h2 : (M : ℝ) ^ 2 ≤ s.x * s.delta1 := by
    have e : s.x * s.delta1 = s.x ^ (1 - s.eps / 8) := by
      unfold Scale.delta1
      rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
    have h3 : s.x ^ ((1 : ℝ) / 2) ≤ s.x ^ (1 - s.eps / 8) :=
      Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by have := s.eps_lt; linarith)
    rw [e]
    refine le_trans ?_ h3
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by rw [← pow_mul]; exact hx)
  have h4 : (M : ℝ) ≤ R.m := (Real.le_sqrt_of_sq_le h2).trans h1
  exact_mod_cast h4

theorem b_eq (K : Ctx) (u : K.P.Word) (τ : Tau K.P.R) :
    ∃ b1 : ℤ, ∀ j : Fin K.P.R.m, (K.P.hcW u τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h0v K.s K.ch : ℚ) ∧
      (K.P.hcW u τ).e j = (K.P.hcW u τ).b j + (h0v K.s K.ch : ℚ) / 2 := by
  obtain ⟨b1, h, -⟩ := (K.ok.hc u).2.2.1
  exact ⟨b1 τ, h τ⟩

theorem eventually_nodeGap_ge_rank_pow (A : ℝ) (N M : ℕ) : Ev fun K => M ≤ K.P.R.m ∧ A * (K.P.R.r : ℝ) ^ N ≤ (h0v K.s K.ch : ℝ) := by
  refine ⟨1, one_pos, fun eps C8 _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨6 * N + 1, fun ch hch =>
    ⟨max (max 4 A) ((M : ℝ) ^ 4), fun K _ _ h3 _ hx => ?_⟩⟩⟩⟩⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx4, hxA⟩, hxM⟩ := hx
  refine ⟨le_m K.ok.rank hxM, ?_⟩
  have h1 := rank_le K.ok.rank hx4
  have h2 : K.s.x ^ (6 * N + 1) ≤ K.s.x ^ K.ch := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le K.s.one_lt_alt.le (by rw [h3]; push_cast; exact hch)
  have h5 : K.s.x ^ K.ch ≤ (⌈K.s.x ^ K.ch⌉₊ : ℝ) := Nat.le_ceil _
  have h6 : (0 : ℝ) ≤ (⌈K.s.x ^ K.ch⌉₊ : ℝ) := Nat.cast_nonneg _
  calc A * (K.P.R.r : ℝ) ^ N ≤ K.s.x * (K.s.x ^ 6) ^ N := by gcongr
    _ = K.s.x ^ (6 * N + 1) := by ring
    _ ≤ (h0v K.s K.ch : ℝ) := by unfold h0v; push_cast; linarith

theorem ev_nodes (A : ℝ) (N M : ℕ) : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → M ≤ X.toD7.R.m ∧
    ∃ h : ℕ, A * (X.toD7.R.r : ℝ) ^ N ≤ (h : ℝ) ∧ ∀ τ, ∃ b1 : ℤ, ∀ j : Fin X.toD7.R.m,
      (X.toD7.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ) ∧ (X.toD7.hc τ).e j = (X.toD7.hc τ).b j + (h : ℚ) / 2 := by
  obtain ⟨a, ha, hp⟩ := eventually_nodeGap_ge_rank_pow A N M
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K0, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K0, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  refine ⟨a3, fun K h1 h2 h3 h4 hx X hO => ?_⟩
  obtain ⟨g1, g2⟩ := ha3 K h1 h2 h3 h4 hx
  have key : ∀ B : Pre, K.Over B → M ≤ B.R.m ∧
      ∃ h : ℕ, A * (B.R.r : ℝ) ^ N ≤ (h : ℝ) ∧ ∀ τ, ∃ b1 : ℤ, ∀ j : Fin B.R.m,
        (B.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ) ∧ (B.hc τ).e j = (B.hc τ).b j + (h : ℚ) / 2 := by
    rintro B ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩
    exact ⟨g1, _, g2, fun τ => b_eq K K.P.u₀ τ⟩
  exact key _ hO

end GlobalTheory.Mem.Top.NodeGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjReferenceChartIndexStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_referenceChartIndex : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (a : I.ι) (i : ℕ), 1 ≤ i → i < B.R.m →
    ∀ b : Idx I.sel (I.tup a) (I.idx a) i, ∃ (b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i)
      (x : ∀ w : (B.primes X).vGs, GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ w.1.asIdeal)),
      (i + 1 = B.R.m → ∀ w, x w = 1) ∧
      (∀ g : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs), g ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp ↔
        (fun w => x w * g w * (x w)⁻¹) ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp) ∧
      ∀ (g : ↥(levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp) (g0 : ↥(levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp),
        (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) →
        (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).chr g = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).chr g0 := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch.idx_match | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch.idx_match | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch.idx_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRepIntertwinerImageModels
section
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct ContDiff

noncomputable section

namespace GlobalTheory.ConjRowRepModels


set_option maxHeartbeats 1000000 in
theorem exists_contRep_models : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → ∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hE _ _ hθ _ _ c hc Φ hΦ u
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h R.θ hθ hE
  obtain ⟨-, hcomm, g, hg, hfix⟩ := GlobalTheory.IdemProj.re_orth_proj X.B
  have := X.B.sf
  have := X.B.haar
  let T : GA D (D.sp.Y 0) ≃* X.B.I.GA := (iotaX X h).toMulEquiv
  have hT : Continuous T := (iotaX X h).continuous
  have hT' : Continuous T.symm := (iotaX X h).symm.continuous
  obtain ⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'
  obtain ⟨U, hU, hUg⟩ := h11 g hg
  have hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    obtain ⟨A, hA, rfl⟩ := hΦ
    intro g
    show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w := by
    obtain ⟨A, -, rfl⟩ := hΦ
    intro k hk w
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)
  obtain ⟨m, hm, -⟩ := GlobalTheory.exists_continuousMultilinearMap_of_inner_prod (H := X.B.H) X.B.tens
    X.B.tens_spec.1 X.B.tens_spec.2.2
  let C : (∀ τ, (MP R).H τ) → ∀ v, X.B.H v := fun y => Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (y τ))
  have hC : ∀ y τ, C y (X.pl.symm τ) = c τ (y τ) := fun y τ => Equiv.piCongrLeft_apply_apply _ _ _ _
  have hCd : ContDiff ℝ ∞ C := by
    refine contDiff_pi.2 fun v => ?_
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    simp only [hC]
    exact (GlobalTheory.ConjRowRep.contDiff_anti (c τ)).comp (contDiff_pi.1 contDiff_id τ)
  let F : (∀ τ, (MP R).H τ) → L2X X := fun y => Φ (X.B.tens (C y))
  have hF : ContDiff ℝ ∞ F := by
    have e : F = fun y => (Φ.compContinuousMultilinearMap m) (C y) := by
      funext y
      show Φ (X.B.tens (C y)) = Φ (m (C y))
      rw [hm]
    rw [e]
    exact (((Φ.compContinuousMultilinearMap m).contDiff (n := ∞)).restrict_scalars ℝ).comp hCd
  have hsm := GlobalTheory.ConjRowRep.smooth_of_contDiff R.θ (MP R) ρ F hF (fun τ a ha y => by
    obtain ⟨q1, q2, -⟩ := hat τ a ha
    rw [h3]
    refine GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_
    obtain ⟨τ', rfl⟩ := X.pl.symm.surjective v
    rw [hC, hC]
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact hc _ a ha _
    · rw [Function.update_of_ne e]
      have q : (iotaX X h (atTau R.θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1 := q2 _ (X.pl.symm.injective.ne e)
      rw [q]
      have : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds _).2.2.1.1.1
      show _ = X.B.σ (X.pl.symm τ') 1 _
      rw [this]
      rfl) u
  obtain ⟨R', L, -, hR, -⟩ := GlobalTheory.TensRep.exists_adelic_rep (ι := fun v x => X.B.I.ext v (T x)) hθ h1 h2 h5 h6 h7
    h8 h9 hU
  obtain ⟨p1, p2⟩ := hR _ hsm (fun k hk hk' => by
    rw [h3]
    have e : T k = (1, (T k).2) := Prod.ext ((hf k).1 hk') rfl
    rw [e]
    exact hlev _ (hUg k hk) _)
  refine ⟨fun x => R' (F fun τ => (u τ : (MP R).H τ)) (T.symm x),
    GlobalTheory.RepSmooth.isContRep_of_ae X.B (p1.comp hT') (fun γ hγ x => ?_) ?_⟩
  · have e : (fun x => R' (F fun τ => (u τ : (MP R).H τ)) (T.symm γ * x)) = R' (F fun τ => (u τ : (MP R).H τ)) :=
      ((p1.comp (continuous_const_mul _)).ae_eq_iff_eq μ p1).1
        (Filter.EventuallyEq.trans
          (((measurePreserving_mul_left μ _).quasiMeasurePreserving.ae p2).mono fun _ hy => hy.symm)
          ((h10 (T.symm γ) (by rw [T.apply_symm_apply]; exact hγ) _).trans p2))
    rw [map_mul]
    exact congrFun e _
  · filter_upwards [h4 _ p2] with x hx
    rw [← hx, T.apply_symm_apply]
    rfl

end GlobalTheory.ConjRowRepModels

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulMemOfSpan
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Full

theorem exists_nsmul_mem_of_span {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (x : V) (hx : x ∈ Submodule.span K (L : Set V)) :
    ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegerMultiple.main
  | exact _root_.GlobalTheory.NatMulIntegerMultiple.main
  | (apply _root_.GlobalTheory.NatMulIntegerMultiple.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegerMultiple.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegerMultiple.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegerMultiple.main ..)

theorem dgam_pos_and_full : ∀ D : D7, (∀ u, 0 < (D.mem u).C.DGam) ∧
    ∀ u (x : (D.div.Nu u).V), ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ DV.MramL D u := by
  intro D
  refine ⟨fun u => (D.mem u).C.DGam_pos, fun u x => ?_⟩
  obtain ⟨n, hn, h⟩ := exists_nsmul_mem_of_span ((D.fm u).lat 0).L (D.nuIn u x)
    (by rw [((D.fm u).lat_good 0).2.2]; trivial)
  refine ⟨n, hn, ?_⟩
  show D.nuIn u (n • x) ∈ ((D.fm u).lat 0).L
  rw [map_nsmul]
  exact h

end GlobalTheory.Mem.Full
end

