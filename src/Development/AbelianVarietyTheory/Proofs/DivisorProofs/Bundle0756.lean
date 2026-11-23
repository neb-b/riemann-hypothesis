module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0727
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePrimeSizesLeBudgetFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.TypeSize

variable {D : D7}

theorem card_TT_le (D : D7) : (D.host.TT.card : ℝ) ≤ D.R.f := by
  have h : Fintype.card D.host.TT ≤ Fintype.card D.what₂.Tau := by
    refine Fintype.card_le_of_injective
      (fun t => D.eTau.symm ⟨D.R.tau1 t, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩) ?_
    intro a b hab
    have h1 := congrArg Subtype.val (D.eTau.symm.injective hab)
    exact Subtype.ext (GlobalTheory.FockDegreeGap.tau1_injective h1)
  rw [Fintype.card_coe, D.what₂.card_Tau] at h
  exact_mod_cast h

theorem errG_abs_le {L : SizeData₂ D} (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (C : ℝ) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) : |WeightDegreeSizes.errG L C j| ≤ (6 + 4 * |C|) * D.R.f * L.sc.b := by
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨e1, e2, e3⟩ := GlobalTheory.FockDegreeGap.errors_le h P
  have hb := GlobalTheory.HCEntries.one_le_b L
  have hb' := GlobalTheory.HCEntries.b'_pos L
  have hbb : L.sc.b' ≤ L.sc.b := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩ := h
    linarith [GlobalTheory.HCEntries.b'_Sc_le hS, L.Sc_pos]
  have hx0 : 0 < L.sc.x := by linarith
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b := (div_le_self hb'.le (by linarith)).trans hbb
  have hTT := card_TT_le D
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hTT0 : (0 : ℝ) ≤ D.host.TT.card := Nat.cast_nonneg _
  have hw0 : 0 ≤ ∑ τ : D.what₂.Tau, wj D j τ :=
    Finset.sum_nonneg fun τ _ => (GlobalTheory.HCEntries.wj_bounds h hx j j1 j2 τ).1
  have hw1 : ∑ τ : D.what₂.Tau, wj D j τ ≤ D.R.f * (3 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset D.what₂.Tau) (fun τ => wj D j τ) (3 * L.sc.b)
      (fun τ _ => (GlobalTheory.HCEntries.wj_bounds h hx j j1 j2 τ).2)
    rwa [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at this
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hN0 : (0 : ℝ) ≤ Formalism.MainNotions.G.Nm D := by unfold Formalism.MainNotions.G.Nm; positivity
  have hmt : (D.R.m : ℝ) * D.R.t * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
    have : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    nlinarith
  have hkN : (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D ≤ L.sc.b := e3
  set Y : ℝ := (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D) +
    (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x with hY
  have hY0 : 0 ≤ Y := by
    rw [hY]
    have : 0 ≤ (D.R.m : ℝ) * D.R.t * L.etaSz := by positivity
    have : 0 ≤ (D.R.k : ℝ) * L.Sc := by positivity
    have : 0 ≤ (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D := by positivity
    have : 0 ≤ (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x := by positivity
    positivity
  have hY1 : Y ≤ 4 * D.R.f * L.sc.b := by
    rw [hY, mul_div_assoc]
    have a1 : (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D) ≤
        D.R.f * (3 * L.sc.b) := mul_le_mul_of_nonneg_left (by linarith) hf0
    have a2 : (D.host.TT.card : ℝ) * (L.sc.b' / L.sc.x) ≤ D.R.f * L.sc.b :=
      mul_le_mul hTT hbx (by positivity) hf0
    linarith
  have hCY : |C * Y| ≤ 4 * |C| * D.R.f * L.sc.b := by
    rw [abs_mul, abs_of_nonneg hY0]
    calc |C| * Y ≤ |C| * (4 * D.R.f * L.sc.b) := mul_le_mul_of_nonneg_left hY1 (abs_nonneg _)
      _ = _ := by ring
  have e : WeightDegreeSizes.errG L C j = 2 * (∑ τ : D.what₂.Tau, wj D j τ) + C * Y := by
    unfold WeightDegreeSizes.errG; rw [hY]
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (∑ τ : D.what₂.Tau, wj D j τ))]
  nlinarith

theorem typePrime_sizes_le_budget_single {L : SizeData₂ D} (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (c : ErrC) (Cd C₂ : ℝ)
    (h2 : FactDGam D C₂) :
    WeightDegreeSizes.TypePrimeSizeBound D L c Cd (|(6 + 4 * |Cd|)| * (P.CYL + 1) + 2 * |C₂| + 4 * |c.g| * (P.CYL + 1)) := by
  intro i u j hj
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hmn := D.R.two_le_m
  have hkn := D.R.m_add_three_le_k
  have hmfn : D.R.m ≤ D.R.f := D.R.m_le_f
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hmf : (D.R.m : ℝ) ≤ D.R.f := by exact_mod_cast hmfn
  have hf : (1 : ℝ) ≤ D.R.f := hm.trans hmf
  have ht : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have hN : (1 : ℝ) ≤ D.R.N D.R.m := by
    exact_mod_cast (by unfold Ranks.N; omega : 1 ≤ D.R.N D.R.m)
  have hη0 := L.etaSz_pos.le
  have hNη : (D.R.N D.R.m : ℝ) ^ 2 ≤ L.etaSz := by
    have a1 := P.h0_ge.2.2.2.2.1
    have a2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη0 hm
    have a3 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
    have a4 : 0 ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
    linarith
  have hfη : (D.R.f : ℝ) * L.etaSz ≤ L.sc.b := by
    have a1 := P.eta_le
    rw [le_div_iff₀ (by positivity)] at a1
    have a2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) (one_le_pow₀ hk)
    have a3 : (D.R.f : ℝ) * L.etaSz ≤ (D.R.f : ℝ) * L.etaSz * ((D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3) :=
      le_mul_of_one_le_right (by positivity) a2
    calc _ ≤ _ := a3
      _ = L.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := by ring
      _ ≤ _ := a1
  have hg0 : (0 : ℝ) < D.host.g i := by exact_mod_cast (D.host.g_prime i).pos
  have hlg0 : 0 ≤ Real.log (D.host.g i) := Real.log_natCast_nonneg _
  have hlg : Real.log (D.host.g i) ≤ (P.CYL + 1) * L.sc.L := by
    obtain ⟨Y, -, -, hY, hg⟩ := P.g_Y
    have hY0 : 0 < Y := by linarith [(hg i).2]
    have a1 : Real.log (D.host.g i) ≤ Real.log (2 * Y) := Real.log_le_log hg0 (hg i).2
    rw [Real.log_mul (by norm_num) hY0.ne'] at a1
    have a2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have key := GlobalTheory.TypeLoss.arith_bound (WeightDegreeSizes.errG L Cd j)
    ((padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) * Real.log (D.host.g i)) _ (Real.log (D.host.g i))
    D.R.f D.R.m L.sc.b L.sc.L (D.R.N D.R.m) L.etaSz (6 + 4 * |Cd|) C₂ c.g P.CYL L.B0 rfl hf hm hL hN P.CYL_pos.le
    (errG_abs_le h P hx Cd j hj)
    (mul_nonneg (Nat.cast_nonneg _) hlg0)
    ((GlobalTheory.TypeLoss.padic_log_le _ _ (D.host.g_prime i)).trans (h2 u)) rfl hlg0 hlg hη0 hNη hmf hfη
  have e : (WeightDegreeSizes.errG L Cd j + 2 * (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) +
      2 * (c.g * (D.R.f : ℝ) * (Formalism.MainNotions.G.Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz))) * Real.log (D.host.g i : ℝ) =
      WeightDegreeSizes.errG L Cd j * Real.log (D.host.g i) +
        2 * ((padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) * Real.log (D.host.g i)) +
        2 * (c.g * (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz)) * Real.log (D.host.g i) := by
    unfold Formalism.MainNotions.G.Nm; ring
  rw [e]
  exact (le_abs_self _).trans key

theorem typePrimeSizeBound_of_eps_lt_one_div_fiftyTwo : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → DGamSize Fm → ∀ Cd : ℝ, ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.TypePrimeSizeBound (Fm.D x i) (Fm.L x i) Fm.cX.err Cd C := by
  intro eps Fm _ _ ⟨C₂, x₂, h2⟩ Cd
  refine ⟨max (|(6 + 4 * |Cd|)| * (Fm.CYL + 1) + 2 * |C₂| + 4 * |Fm.cX.err.g| * (Fm.CYL + 1)) 0, max 2 x₂,
    le_max_right _ _, ?_⟩
  · intro x hx0 hx i
    have a := typePrime_sizes_le_budget_single (Fm.sizes x hx i) (Fm.params x hx i)
      (by rw [Fm.L_x x i hx]; exact (le_max_left _ _).trans hx0) Fm.cX.err Cd C₂
      (h2 x ((le_max_right _ _).trans hx0) i)
    rw [Fm.params_CYL x hx i] at a
    intro k u j hj
    exact (a k u j hj).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (WeightDegreeSizes.loss_bound_nonneg _))

end GlobalTheory.TypeSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitNormGramDetPlaneReduction
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PlaneNormReduce

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_inclR' (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem hE_sub_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a b y : Fin M → E) (c : E) :
    hE σ J (a - c • b) y = hE σ J a y - σ c * hE σ J b y := by
  simp only [hE, Formalism.UG.hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul,
    AlgHom.coe_toRingHom, RingHom.coe_coe, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_sub_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (y a b : Fin M → E) (c : E) :
    hE σ J y (a - c • b) = hE σ J y a - c * hE σ J y b := by
  simp only [hE, Formalism.UG.hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_swap' (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (x y : Fin M → E) : hE σ J y x = σ (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ.1 b a]
  ring

end Alg

theorem sigma_sigma' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem reduce : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x z : Fin M → E, hE σ J x x ≠ 0 → IsUnitNorm K σ (-(inclR K (gram2E σ J x z))) → hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x)) = 0 := by
  intro F E _ _ _ _ _ σ hCM K _ _ M J hJ x z hx hN
  have hσ := sigma_sigma' σ hCM
  set a := hE σ J x x with ha
  set c := hE σ J x z / a with hc
  set q := hE σ J (z - c • x) (z - c • x) with hq
  have hsa : σ a = a := (hE_swap' σ hσ J hJ x x).symm
  have hzx : hE σ J z x = σ (hE σ J x z) := hE_swap' σ hσ J hJ x z
  have hsc : σ c = hE σ J z x / a := by rw [hc, map_div₀, hsa, hzx]

  have hqa : q * a = gram2E σ J x z := by
    rw [hq, hE_sub_smul_left, hE_sub_smul_right, hE_sub_smul_right, hsc, hc, gram2E]
    field_simp
    ring

  obtain ⟨s, hs, hss⟩ := hN
  have hinj : Function.Injective (inclR (F := F) (E := E) K) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have hG : gram2E σ J x z ≠ 0 := by
    intro h0
    rw [h0, map_zero, neg_zero] at hss
    have hu : IsUnit (0 : K ⊗[F] E) := by
      rw [← hss]; exact hs.mul (hs.map (sigR K σ))
    have h01 : (0 : K ⊗[F] E) = 1 := isUnit_zero_iff.mp hu
    have : inclR (F := F) K (0 : E) = inclR (F := F) K 1 := by rw [map_zero, map_one, h01]
    exact zero_ne_one (hinj this)
  have hq0 : q ≠ 0 := by
    intro h0; apply hG; rw [← hqa, h0, zero_mul]
  refine ⟨hq0, ?_⟩

  set v : K ⊗[F] E := ↑(hs.unit⁻¹) with hv
  have h1 : v * s = 1 := by rw [hv]; exact hs.val_inv_mul
  have h2 : sigR K σ v * sigR K σ s = 1 := by rw [← map_mul, h1, map_one]
  refine ⟨inclR K a * v, ?_⟩
  have hw : IsUnit (s * sigR K σ s) := hs.mul (hs.map (sigR K σ))
  apply hw.mul_left_eq_zero.mp
  have e1 : inclR K a * v * sigR K σ (inclR K a * v) * (s * sigR K σ s) = inclR K (a * a) := by
    rw [map_mul, sigR_inclR', hsa]
    calc inclR K a * v * (inclR K a * sigR K σ v) * (s * sigR K σ s)
        = inclR K a * inclR K a * (v * s) * (sigR K σ v * sigR K σ s) := by ring
      _ = inclR K (a * a) := by rw [h1, h2, map_mul]; ring
  have e2 : inclR K (a / q) * (s * sigR K σ s) = - inclR K (a * a) := by
    rw [hss, mul_neg, ← map_mul, ← hqa]
    congr 2
    field_simp
  rw [add_mul, e1, e2, add_neg_cancel]

end GlobalTheory.PlaneNormReduce
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VAddNonnegOfIsIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.SeenHalf

variable {D : D7}

theorem vAdd_add_star (D : D7) (w : D.what₂.places.Pl) (y : D.what₂.LL)
    (hy : y * star y = ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)) :
    vAdd (D.plEq w) y + vAdd (D.plEq w) (star y) = (D.what₂.places.ramIdx w : ℤ) := by
  have hp0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  have hy0 : y ≠ 0 := fun h => hp0 (by rw [← hy, h, zero_mul])
  rw [← GlobalTheory.TypeLoss.additiveValuation_residueChar_eq_ramIndex, ← hy, GlobalTheory.TypeLoss.additiveValuation_mul_of_ne_zero _ hy0 (star_ne_zero.2 hy0)]

theorem vAdd_nonneg_of_isIntegral {K : Type} [Field K] [NumberField K]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {x : K}
    (hx : x ≠ 0) (hi : IsIntegral ℤ x) : 0 ≤ vAdd w x := by
  have h := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := K) w (⟨x, hi⟩ : 𝓞 K)
  have hx' : w.valuation K x ≠ 0 := (map_ne_zero _).2 hx
  unfold vAdd
  rw [neg_nonneg, ← WithZero.log_one, WithZero.log_le_log hx' one_ne_zero]
  exact h

theorem sigmaOf_fix {R : Ranks} (H : Host R) (g : R.Psi) {x : H.E} (hx : x ∈ H.K) : H.sigmaOf g x = x := by
  have h : H.sigmaOf g (H.sqd) = H.sqd := by
    refine (H.galE_mem_Psi_iff _).1 ?_
    have : H.galE (H.sigmaOf g) = g :=
      (H.gal).apply_symm_apply _
    rw [this]
    exact g.2
  have hle : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers (H.sigmaOf g)) := by
    refine IntermediateField.adjoin_simple_le_iff.2 ?_
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have : Subgroup.zpowers (H.sigmaOf g) ≤ MulAction.stabilizer _ (H.sqd) := by
      rw [Subgroup.zpowers_le]
      exact h
    exact this hf
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) _ (Subgroup.mem_zpowers _)

theorem ETpi_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ Formalism.MainNotions.product_first_zeroth_parts.ETpi D u := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.ETpi
  positivity

theorem sz_ET_nonneg (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    0 ≤ SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET D u w) := by
  have h0 := ETpi_nonneg D u
  have l0 : 0 ≤ SizeData₂.lwP w := by
    unfold SizeData₂.lwP lw
    exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have h1 : 0 ≤ Formalism.MainNotions.product_first_zeroth_parts.ET D u w := by
    rw [Formalism.MainNotions.product_first_zeroth_parts.ET_eq]
    split_ifs
    · exact h0
    · exact le_rfl
  unfold SizeData₂.sz
  positivity

theorem sum_over_eq {X : ErrX D} (hs : SeenDef D X) (u : D.what₂.Word) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w, w ∈ S ↔ D.what₂.places.resChar w = (D.mem u).A.T) :
    ∑ w ∈ S, SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET D u w) = Formalism.MainNotions.product_first_zeroth_parts.ETpi D u * Real.log ((D.mem u).A.T : ℝ) := by
  have hT : ((D.mem u).A.T).Prime := (D.mem u).A.T_prime
  set y : D.what₂.LL := D.embE (X.piT u : D.host.E) with hy
  have hn : y * star y = ((D.mem u).A.T : D.what₂.LL) := by
    rw [hy, ← D.embE_conj, ← map_mul, X.piT_norm]
    simp
  have hy0 : y ≠ 0 := fun h => (Nat.cast_ne_zero.2 hT.ne_zero : ((D.mem u).A.T : D.what₂.LL) ≠ 0)
    (by rw [← hn, h, zero_mul])
  have hi1 : IsIntegral ℤ y := IsIntegral.map (D.embE : D.host.E →+* D.what₂.LL).toIntAlgHom (X.piT u).isIntegral_coe
  have hi2 : IsIntegral ℤ (star y) := IsIntegral.map (starRingEnd D.what₂.LL).toIntAlgHom hi1
  rw [← GlobalTheory.TypeLoss.sum_half D _ hT S hS y hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw := (hS w).1 hw
  have a1 := vAdd_nonneg_of_isIntegral (D.plEq w) hy0 hi1
  have a2 := vAdd_nonneg_of_isIntegral (D.plEq w) (star_ne_zero.2 hy0) hi2
  have a3 := vAdd_add_star D w y (by rw [hw]; exact hn)
  have a4 := GlobalTheory.LevelCoprime.coprime_conj X u w hw
  rw [← hy] at a4
  have a5 : (D.fm u).seenP w = true ↔ 0 < vAdd (D.plEq w) y := by
    rw [hs u w hw]
    have e : ∀ τ, tauLL D τ (X.piT u : D.host.E) = y := fun τ => by
      unfold tauLL
      rw [sigmaOf_fix D.host (D.eTau τ) (X.piT_K u)]
    simp only [e, D.val_eq w y hy0]
    constructor
    · intro h
      exact_mod_cast h (D.eTau.symm 1)
    · intro h _
      exact_mod_cast h
  rw [Formalism.MainNotions.product_first_zeroth_parts.ET_eq]
  unfold SizeData₂.sz
  by_cases h : (D.fm u).seenP w = true
  · have b1 := a5.1 h
    have b2 : vAdd (D.plEq w) y = (D.what₂.places.ramIdx w : ℤ) := by
      by_contra hne
      exact a4 ⟨b1, by omega⟩
    rw [if_pos h, b2]
    push_cast
    ring
  · have b2 : vAdd (D.plEq w) y = 0 := by
      have := mt a5.2 h
      omega
    rw [if_neg h, b2]
    simp

theorem seen_half : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) (S : Finset (Fm.D x i).what₂.places.Pl), (∀ w ∈ S, Formalism.MainNotions.product_first_zeroth_parts.OverT (Fm.D x i) u w) → 0 ≤ ∑ w ∈ S, SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET (Fm.D x i) u w) ∧ ∑ w ∈ S, SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET (Fm.D x i) u w) ≤ Formalism.MainNotions.product_first_zeroth_parts.ETpi (Fm.D x i) u * Real.log (((Fm.D x i).mem u).A.T : ℝ) := by
  intro eps Fm x hx i u S hS
  refine ⟨Finset.sum_nonneg fun w _ => sz_ET_nonneg _ u w, ?_⟩
  obtain ⟨S', hS'⟩ := GlobalTheory.TypeLoss.exists_over (Fm.D x i) _ ((Fm.D x i).mem u).A.T_prime
  rw [← sum_over_eq (Fm.ex x hx i).err.seen u S' hS']
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => (hS' w).2 (hS w hw)) fun w _ _ => sz_ET_nonneg _ u w

end GlobalTheory.SeenHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeaklyRegularRelationsEqKoszulRelations
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open RingTheory.Sequence in
theorem weaklyRegular_relations_koszul :
    ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∀ a : Fin g → O, ∑ i, a i * f i = 0 → ∃ c : Matrix (Fin g) (Fin g) O, (∀ i, c i i = 0) ∧ (∀ i j, c i j = - c j i) ∧ a = c.mulVec f := by
  intro O _ g
  induction g with
  | zero =>
    intro f _ a _
    exact ⟨0, by simp, by simp, funext fun i => i.elim0⟩
  | succ g ih =>
    intro f hf a ha
    have hsplit : List.ofFn f =
        List.ofFn (fun i : Fin g => f i.castSucc) ++ [f (Fin.last g)] := by
      rw [List.ofFn_succ_last]
    rw [hsplit, isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at hf
    obtain ⟨hf1, hf2⟩ := hf
    rw [Fin.sum_univ_castSucc] at ha
    have hIt : (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O) =
        Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) := by
      rw [smul_eq_mul, Ideal.mul_top]
    have hmem : a (Fin.last g) ∈
        (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      apply hf2
      simp only [smul_zero]
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hIt, smul_eq_mul, mul_comm,
        eq_neg_of_add_eq_zero_right ha, neg_mem_iff]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    rw [hIt, Ideal.ofList, show {r | r ∈ List.ofFn fun i : Fin g => f i.castSucc}
        = Set.range (fun i : Fin g => f i.castSucc) by ext; simp [List.mem_ofFn],
      Ideal.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨b, hb⟩ := hmem
    obtain ⟨c', hc0, hcs, hca⟩ := ih (fun i => f i.castSucc) hf1
      (fun i => a i.castSucc + b i * f (Fin.last g)) (by
        simp only [add_mul, Finset.sum_add_distrib]
        rw [← ha, ← hb, Finset.sum_mul, add_right_inj]
        exact Finset.sum_congr rfl fun i _ => by ring)
    refine ⟨fun i j => Fin.lastCases (Fin.lastCases 0 (fun j => b j) j)
      (fun i => Fin.lastCases (-b i) (fun j => c' i j) j) i, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.lastCases with
      | last => simp
      | cast i => simp [hc0]
    · intro i j
      cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp <;> exact hcs _ _
    · funext i
      cases i using Fin.lastCases with
      | last => simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hb]
      | cast i =>
        have := congrFun hca i
        simp only [Matrix.mulVec, dotProduct] at this
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.lastCases_castSucc,
          Fin.lastCases_last]
        rw [← this]
        ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightTieRec
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnNormCompare

theorem mem_tops_rec (D : D7) (z : Bool × Formalism.MainNotions.G.HH D) :
    tauPl D z ∈ topsOf D.host D.eTau ↔ z.1 = false ∧ z.2 ∈ D.host.TT := by
  classical
  have hinj := D.R.toFrame.tau1_injective
  have hP := factPlaces D.R.toFrame
  have h0 : (D.eTau (tauPl D z) : D.R.GG) = Formalism.MainNotions.G.plGG D z := by simp [tauPl]
  unfold topsOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h0]
  unfold Host.topPlaces
  rw [Finset.mem_image]
  obtain ⟨b, t⟩ := z
  constructor
  · rintro ⟨t', ht, h⟩
    cases b <;> simp only [Formalism.MainNotions.G.plGG, if_true, if_false, Bool.false_eq_true] at h
    · exact ⟨rfl, (hinj h) ▸ ht⟩
    · exact absurd h (hP.2 _ _)
  · rintro ⟨h1, h2⟩
    refine ⟨t, h2, ?_⟩
    simp only at h1
    simp [Formalism.MainNotions.G.plGG, h1]

end GlobalTheory.ColumnNormCompare
end

