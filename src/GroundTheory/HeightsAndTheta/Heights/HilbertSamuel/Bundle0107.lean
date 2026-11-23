module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0106
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockStepBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Module

noncomputable section

namespace TwoBlockStepBound

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem relIndex_le_pow {H K : Submodule ℤ Ω} [Module.Finite ℤ K] {N : ℕ} (hN : 0 < N)
    (hNK : ∀ u ∈ K, (N : Ω) * u ∈ H) :
    H.toAddSubgroup.relIndex K.toAddSubgroup ≠ 0 ∧
      H.toAddSubgroup.relIndex K.toAddSubgroup ≤ N ^ finrank ℤ K := by
  have : Module.Finite ℤ (AddSubgroup.toIntSubmodule K.toAddSubgroup) := ‹Module.Finite ℤ K›
  have : Module.Free ℤ (AddSubgroup.toIntSubmodule K.toAddSubgroup) := Module.free_of_finite_type_torsion_free'
  have key := AddSubgroup.relIndex_map_nsmul N K.toAddSubgroup
  have hsub : K.toAddSubgroup.map (nsmulAddMonoidHom (α := Ω) N) ≤ H.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [nsmul_eq_mul] using hNK y hy
  have hne : (K.toAddSubgroup.map (nsmulAddMonoidHom (α := Ω) N)).relIndex K.toAddSubgroup ≠ 0 := by
    rw [key]
    exact pow_ne_zero _ hN.ne'
  refine ⟨fun h0 => hne (AddSubgroup.relIndex_eq_zero_of_le_left hsub h0), ?_⟩
  calc H.toAddSubgroup.relIndex K.toAddSubgroup ≤ _ := AddSubgroup.relIndex_le_of_le_left hsub hne
    _ = N ^ finrank ℤ K := key

theorem pow_mul_mem_sec {x x' : Ix κ → Ω} {M : ℕ} (hM : ∀ s ∈ sec ℤ x' 1, (M : Ω) * s ∈ sec ℤ x 1) :
    ∀ n : ℕ, ∀ s ∈ sec ℤ x' n, (M : Ω) ^ n * s ∈ sec ℤ x n
  | 0, s, hs => by
    rw [sec_zero'] at hs ⊢
    simpa using hs
  | n + 1, s, hs => by
    rw [← sec_mul_sec] at hs ⊢
    induction hs using Submodule.mul_induction_on' with
    | mem_mul_mem u hu v hv =>
      have := Submodule.mul_mem_mul (pow_mul_mem_sec hM n u hu) (hM v hv)
      convert this using 1
      ring
    | add u _ v _ hu hv =>
      rw [mul_add]
      exact add_mem hu hv

theorem exists_finrank_sec_le (hRank : RankOfSections.Statement) {x : Ix κ → Ω} {D : ℕ}
    (hX : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ m : ℕ, 1 ≤ m → (finrank ℤ (sec ℤ x m) : ℝ) ≤ R * (m : ℝ) ^ D := by
  obtain ⟨hqP, hqd⟩ := GenericFibre.proof Ω κ x D hX
  obtain ⟨C, hC⟩ := hRank κ _ D hqP hqd
  set δ : ℝ := (GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ
    ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ : Fin D => fun _ => (1 : ℤ)) : ℝ)
  refine ⟨|δ| + |C| * 2 ^ D, by positivity, fun m hm => ?_⟩
  have e : (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
      ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (m : ℤ)) : ℝ) =
      (finrank ℤ (sec ℤ x m) : ℝ) := by exact_mod_cast SectionsRank.proof Ω κ x m
  have h := (abs_le.mp (hC m)).2
  rw [e] at h
  have ht : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) ≤ (m : ℝ) ^ D := by positivity
  have h1 : ((m : ℝ) + 1) ^ ((D : ℝ) - 1) ≤ ((m : ℝ) + 1) ^ D := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : ((m : ℝ) + 1) ^ D ≤ 2 ^ D * (m : ℝ) ^ D := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) D
  have h3 : δ * (m : ℝ) ^ D / D.factorial ≤ |δ| * (m : ℝ) ^ D := by
    have hf : (1 : ℝ) ≤ D.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero D)
    rw [div_le_iff₀ (by linarith)]
    calc δ * (m : ℝ) ^ D ≤ |δ| * (m : ℝ) ^ D := mul_le_mul_of_nonneg_right (le_abs_self δ) hp
      _ ≤ |δ| * (m : ℝ) ^ D * D.factorial := le_mul_of_one_le_right (by positivity) hf
  have h4 : C * ((m : ℝ) + 1) ^ ((D : ℝ) - 1) ≤ |C| * (2 ^ D * (m : ℝ) ^ D) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg C))
  nlinarith

end TwoBlockStepBound


open TwoBlockStepBound in
theorem TwoBlockStepBound.proof (hRank : RankOfSections.Statement) : TwoBlockStepBound.Statement := by
  intro D Ω _ _ κ _ x B hX _ _ hsp
  set x' := matAct B x
  obtain ⟨M, hM0, hM⟩ := ChangeOfLatticeNested.exists_mul_mem_sec_one x B
  obtain ⟨R, hR0, hR⟩ := exists_finrank_sec_le hRank hX
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM0)
  refine ⟨R * Real.log M, fun a b => ?_⟩
  have hsp1 : sec ℤ x 1 ≤ sec ℤ x' 1 := by
    rw [sec_one', sec_one']
    exact hsp
  have eH : sec ℤ x (a + 1) * sec ℤ x' b = sec ℤ x a * sec ℤ x' b * sec ℤ x 1 := by
    rw [← sec_mul_sec x a 1, mul_right_comm]
  have eK : sec ℤ x a * sec ℤ x' (b + 1) = sec ℤ x a * sec ℤ x' b * sec ℤ x' 1 := by
    rw [← sec_mul_sec x' b 1, mul_assoc]
  have hKQ : sec ℤ x a * sec ℤ x' (b + 1) ≤ sec ℤ x' (a + b + 1) := by
    rw [add_assoc, ← sec_mul_sec x' a (b + 1)]
    exact mul_le_mul' (ChangeOfLattice.sec_mono hsp a) le_rfl
  have : Module.Finite ℤ (sec ℤ x a * sec ℤ x' (b + 1)) :=
    Module.Finite.iff_fg.mpr ((sec_fg x a).mul (sec_fg x' (b + 1)))
  obtain ⟨hne, hle⟩ := relIndex_le_pow (H := sec ℤ x (a + 1) * sec ℤ x' b)
    (K := sec ℤ x a * sec ℤ x' (b + 1)) hM0 (by rw [eH, eK]; exact mul_mem_of_forall hM _)
  have hMn : ((M : Ω) ^ (a + b + 1)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hM0.ne')
  let f := (LinearMap.mulLeft ℤ ((M : Ω) ^ (a + b + 1))).restrict (pow_mul_mem_sec hM (a + b + 1))
  have hf : Function.Injective f := fun s t hst =>
    Subtype.ext (mul_left_cancel₀ hMn (congrArg Subtype.val hst))
  have hrk : finrank ℤ (sec ℤ x a * sec ℤ x' (b + 1)) ≤ finrank ℤ (sec ℤ x (a + b + 1)) :=
    (Submodule.finrank_mono hKQ).trans (LinearMap.finrank_le_finrank_of_injective hf)
  have hpos : (0 : ℝ) ≤ twoBlockStep x x' a b :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne)
  have ht : ((a + b : ℝ) + 1) = ((a + b + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [abs_of_nonneg hpos, ht]
  unfold twoBlockStep
  calc Real.log ((sec ℤ x (a + 1) * sec ℤ x' b).toAddSubgroup.relIndex (sec ℤ x a * sec ℤ x' (b + 1)).toAddSubgroup)
      ≤ Real.log ((M ^ finrank ℤ (sec ℤ x a * sec ℤ x' (b + 1)) : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hne) (by exact_mod_cast hle)
    _ = finrank ℤ (sec ℤ x a * sec ℤ x' (b + 1)) * Real.log M := by
        push_cast
        rw [Real.log_pow]
    _ ≤ finrank ℤ (sec ℤ x (a + b + 1)) * Real.log M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hrk) hlogM
    _ ≤ R * ((a + b + 1 : ℕ) : ℝ) ^ D * Real.log M :=
        mul_le_mul_of_nonneg_right (hR _ (by omega)) hlogM
    _ = R * Real.log M * ((a + b + 1 : ℕ) : ℝ) ^ D := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResChiSandwichLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResChiSandwich

open MvPolynomial MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds
open scoped ComplexOrder Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem bNormSq_le_of_pts_of {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    [IsProbabilityMeasure μ] (hcar : μ (pts (coordIdeal ℤ x))ᶜ = 0) {n r : ℕ}
    (s : Fin r → (Ix κ → ℂ) → ℂ) (c : Fin r → ℂ) {B : ℝ}
    (h : ∀ z ∈ pts (coordIdeal ℤ x), ‖∑ j, c j * s j z‖ ^ 2 * wgt m n z ≤ B) :
    bNormSq μ s (wgt m n) c ≤ B := by
  have hae : ∀ᵐ z ∂μ, z ∈ pts (coordIdeal ℤ x) := ae_iff.mpr hcar
  unfold bNormSq
  calc ∫ z, ‖∑ j, c j * s j z‖ ^ 2 * wgt m n z ∂μ ≤ ∫ _z, B ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun z => ?_) (integrable_const B) ?_
        · exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (pow_nonneg (m.nonneg z) _))
        · filter_upwards [hae] with z hz using h z hz
    _ = B := by simp

theorem form_le_rho {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {e : Fin (D + 1) → Ix κ}
    (hfr : IsProjFrame x e) (hFS : IsPullFS x e m) (k : ℕ) (f : MvPolynomial (Ix κ) ℂ) (hf : f.IsHomogeneous k) :
    ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z f‖ ≤ S * m.ρ z ^ k := by
  obtain ⟨S, -, hS⟩ := form_le_pnorm hfr k f hf
  refine ⟨S, fun z hz => ?_⟩
  have hmz : m.ρ z = pnorm e z := hFS z hz
  rw [hmz]
  exact hS z hz

theorem lower {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hFS : IsPullFS x e m)
    [IsProbabilityMeasure μ] (hcar : μ (pts (coordIdeal ℤ x))ᶜ = 0)
    (hint : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b → ∀ i j,
      Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ)) μ)
    (hpd : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      (bGram μ (fun k => secFun (b k)) (wgt m n)).PosDef) :
    ∃ (k : ℕ) (C : ℝ), ∀ n : ℕ, k + 1 ≤ n → ∀ (r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      (projDeg x e : ℝ) * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤
        -(1 / 2) * Real.log (bGram μ (fun j => secFun (b j)) (wgt m n)).det.re := by
  classical
  obtain ⟨kε, ε, hε, hli⟩ := exists_indep_sections x e hfr.isRatProjFrame
  have hεH : ∀ l, ∃ Hl : MvPolynomial (Ix κ) ℤ, Hl.IsHomogeneous kε ∧ aeval x Hl = ε l := fun l => by
    obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.mp (hε l)
    exact ⟨p, (mem_homogeneousSubmodule _ _).mp hp, hpe⟩
  choose H hHh hHe using hεH
  have hliH : LinearIndependent (fnField (x ∘ e)) fun l => aeval x (H l) := by
    rw [show (fun l => aeval x (H l)) = ε from funext hHe]; exact hli
  have hCl : ∀ l, ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ S * m.ρ z ^ kε :=
    fun l => form_le_rho hfr hFS kε _ ((hHh l).map _)
  choose Cl hCl using hCl
  set Cε := ∑ l, |Cl l| with hCεdef
  have hCε0 : 0 ≤ Cε := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ kε := fun l z hz =>
    (hCl l z hz).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Cl i|) (fun i _ => abs_nonneg _) (Finset.mem_univ l)))
      (pow_nonneg (m.nonneg z) _))
  obtain ⟨k₀, hk₀⟩ := exists_sec_eq_mul x e hfr
  obtain ⟨tb, htb⟩ := exists_isSecBasis x k₀
  choose Tf hTfh hTfb using htb.1
  have hCt : ∀ i, ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (Tf i))‖ ≤ S * m.ρ z ^ k₀ :=
    fun i => form_le_rho hfr hFS k₀ _ ((hTfh i).map _)
  choose Cti hCti using hCt
  set Ct := ∑ i, |Cti i| with hCtdef
  have hCt : ∀ i, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (Tf i))‖ ≤ Ct * m.ρ z ^ k₀ := fun i z hz =>
    (hCti i z hz).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Cti i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
      (pow_nonneg (m.nonneg z) _))
  have hCt0 : 0 ≤ Ct := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨k', hk'⟩ := finrank_sec_le x e hfr
  set T : ℝ := max 1 (Cε ^ 2 * (projDeg x e : ℝ) * ((1 + 0 + D : ℕ) : ℝ) ^ D) with hTdef
  have hT1 : 1 ≤ T := le_max_left _ _
  set lam : ℝ := max 1 Ct with hlamdef
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hloglam : 0 ≤ Real.log lam := Real.log_nonneg hlam1
  refine ⟨max kε k₀, (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D *
    ((1 / 2) * (Real.log T / Real.log 2 + D) + Real.log lam / Real.log 2), fun n hn r b hb => ?_⟩
  obtain rfl := hb.card_eq
  have hn1 : 1 ≤ n := by omega
  have hnk : n - kε + kε = n := Nat.sub_add_cancel (by omega)
  have hnk₀ : n - k₀ + k₀ = n := Nat.sub_add_cancel (by omega)
  obtain ⟨crd, hcrd1, hcrd2⟩ := exists_crd hb

  have hQh : ∀ p : Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card),
      (prodForm e (adtEnum D (n - kε) (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1)).IsHomogeneous n :=
    fun p => by
      have := prodForm_isHomogeneous e (adtEnum_sum D (n - kε) (finProdFinEquiv.symm p).2)
        (hHh (finProdFinEquiv.symm p).1)
      rwa [hnk] at this
  have hQm : ∀ p, aeval x (prodForm e (adtEnum D (n - kε) (finProdFinEquiv.symm p).2)
      (H (finProdFinEquiv.symm p).1)) ∈ sec ℤ x n := fun p =>
    Submodule.mem_map.mpr ⟨_, (mem_homogeneousSubmodule _ _).mpr (hQh p), rfl⟩
  set M : Matrix (Fin (finrank ℤ (sec ℤ x n)))
      (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card)) ℤ :=
    Matrix.of fun j p => crd ⟨_, hQm p⟩ j with hMdef
  have hM : ∀ p, ∑ j, (M j p : Ω) * aeval x (b j) = aeval x (prodForm e
      (adtEnum D (n - kε) (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1)) :=
    fun p => hcrd1 ⟨_, hQm p⟩
  have hinj := injective_map_of_int_ker M (alphaMat_ker hfr H hliH M hM)
  have hr := le_of_injective_mulVec _ hinj
  have hG' := monoDiag_posDef D (n - kε) (projDeg x e)
  have hG := hpd n _ b hb
  set A := Real.sqrt (T * (n : ℝ) ^ D) with hAdef
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hTn : 1 ≤ T * (n : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hT1 (one_le_pow₀ hn1')
  have hA : 0 < A := Real.sqrt_pos.mpr (by linarith)
  have hA2 : A ^ 2 = T * (n : ℝ) ^ D := Real.sq_sqrt (by linarith)
  have hnorm : (((A : ℂ) ^ 2) • monoDiag D (n - kε) (projDeg x e) -
      (M.map (Int.cast : ℤ → ℂ))ᴴ * bGram μ (fun j => secFun (b j)) (wgt m n) *
        M.map (Int.cast : ℤ → ℂ)).PosSemidef := by
    refine psd_sub_of_quad_le (isHermitian_sq_smul hG'.isHermitian A)
      (Matrix.isHermitian_conjTranspose_mul_mul _ hG.isHermitian) fun c => ?_
    rw [quad_conj, ← bNormSq_eq_re μ _ _ (hint n _ b hb), Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul, quad_monoDiag]
    have hq0 : 0 ≤ ∑ l : Fin (projDeg x e), ∑ i, monoNormSq (adtEnum D (n - kε) i) *
        ‖c (finProdFinEquiv (l, i))‖ ^ 2 := Finset.sum_nonneg fun l _ =>
      Finset.sum_nonneg fun i _ => mul_nonneg (monoNormSq_pos _).le (sq_nonneg _)
    refine bNormSq_le_of_pts_of hcar _ _ fun z hz => ?_
    rw [sum_mulVec_secFun hb M _ hQh hM c z hz]
    have h1 := pt_lower hFS H hCε0 hCε c hz
    rw [hnk] at h1
    refine h1.trans ?_
    have hswap : ∑ l : Fin (projDeg x e), ∑ i, ‖c (finProdFinEquiv (l, i))‖ ^ 2 *
        monoNormSq (adtEnum D (n - kε) i) = ∑ l : Fin (projDeg x e), ∑ i,
        monoNormSq (adtEnum D (n - kε) i) * ‖c (finProdFinEquiv (l, i))‖ ^ 2 :=
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hswap, hA2]
    refine mul_le_mul_of_nonneg_right ?_ hq0
    have hB1 : (((n - kε + D).choose D : ℕ) : ℝ) ≤ (((n + 0 + D).choose D : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose D (by omega)
    have hB2 := choose_bound 0 D hn1
    calc Cε ^ 2 * (projDeg x e : ℝ) * (((n - kε + D).choose D : ℕ) : ℝ)
        ≤ Cε ^ 2 * (projDeg x e : ℝ) * (((1 + 0 + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D) :=
          mul_le_mul_of_nonneg_left (hB1.trans hB2) (by positivity)
      _ = (Cε ^ 2 * (projDeg x e : ℝ) * ((1 + 0 + D : ℕ) : ℝ) ^ D) * (n : ℝ) ^ D := by ring
      _ ≤ T * (n : ℝ) ^ D := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

  have hQ'h : ∀ s : Fin (Finset.Nat.antidiagonalTuple (D + 1) (n - k₀)).card × Fin (finrank ℤ (sec ℤ x k₀)),
      (prodForm e (adtEnum D (n - k₀) s.1) (Tf s.2)).IsHomogeneous n := fun s => by
    have := prodForm_isHomogeneous e (adtEnum_sum D (n - k₀) s.1) (hTfh s.2)
    rwa [hnk₀] at this
  have hwm : ∀ s : Fin (Finset.Nat.antidiagonalTuple (D + 1) (n - k₀)).card × Fin (finrank ℤ (sec ℤ x k₀)),
      aeval x (prodForm e (adtEnum D (n - k₀) s.1) (Tf s.2)) ∈ sec ℤ x n := fun s =>
    Submodule.mem_map.mpr ⟨_, (mem_homogeneousSubmodule _ _).mpr (hQ'h s), rfl⟩
  have hspan := crd_span hcrd2 hb _ hwm (sec_le_span_prod (hk₀ n (by omega)) htb Tf hTfb)
  obtain ⟨f, hfdet⟩ := exists_cols_det_ne_zero _ hspan
  set Nm : Matrix (Fin (finrank ℤ (sec ℤ x n))) (Fin (finrank ℤ (sec ℤ x n))) ℤ :=
    Matrix.of fun p q => crd ⟨_, hwm (f q)⟩ p with hNm
  have hsmall : ∀ i, (((Nm.map (Int.cast : ℤ → ℂ))ᴴ * bGram μ (fun j => secFun (b j)) (wgt m n) *
      Nm.map (Int.cast : ℤ → ℂ)) i i).re ≤ lam ^ 2 := by
    intro i
    rw [diag_conj_eq, ← bNormSq_eq_re μ _ _ (hint n _ b hb)]
    refine bNormSq_le_of_pts_of hcar _ _ fun z hz => ?_
    have hv : Nm.map (Int.cast : ℤ → ℂ) *ᵥ Pi.single i 1 =
        fun p => ((crd ⟨_, hwm (f i)⟩ p : ℤ) : ℂ) := by
      funext p
      simp [hNm, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, sum_secFun_eq' hb _ (hQ'h (f i)) _ (hcrd1 ⟨_, hwm (f i)⟩) z hz]
    have h1 := pt_small hFS (adtEnum_sum D (n - k₀) (f i).1) (Tf (f i).2) (hCt (f i).2) hz
    rw [hnk₀] at h1
    exact h1.trans (pow_le_pow_left₀ hCt0 (le_max_right _ _) 2)
  have key := neg_log_det_le hr hG' hG M hinj _ hfdet hA (by linarith) hnorm hsmall
  rw [neg_log_det_monoDiag] at key

  have hmono : Monotone (chiP D) := monotone_nat_of_le_succ fun n => by
    have := chiP_succ_sub_nonneg D n; linarith
  have hm := mul_le_mul_of_nonneg_left (hmono (show n - max kε k₀ ≤ n - kε by omega))
    (Nat.cast_nonneg (projDeg x e) : (0 : ℝ) ≤ projDeg x e)
  obtain ⟨hL0, hL⟩ := log_sqrt_bound D hT1 hn1
  have hll := log_le_div_mul hloglam hn1
  set R' := projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card
  set r := finrank ℤ (sec ℤ x n)
  have hrR : (R' : ℝ) ≤ r := by exact_mod_cast hr
  have hR0 : (0 : ℝ) ≤ R' := Nat.cast_nonneg _
  have hrb : (r : ℝ) ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by
    have h1 : (r : ℝ) ≤ (projDeg x e : ℝ) * (((n + k' + D).choose D : ℕ) : ℝ) := by
      exact_mod_cast hk' n
    rw [mul_assoc]
    exact h1.trans (mul_le_mul_of_nonneg_left (choose_bound k' D hn1) (Nat.cast_nonneg _))
  have hX : 0 ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by positivity
  have hlogn : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have h3 : (R' : ℝ) * Real.log A ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) :=
    (mul_le_mul_of_nonneg_right (hrR.trans hrb) hL0).trans (mul_le_mul_of_nonneg_left hL hX)
  have h4 : ((r : ℝ) - R') * Real.log lam ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D *
      (n : ℝ) ^ D * (Real.log lam / Real.log 2 * Real.log (n + 1)) :=
    (mul_le_mul_of_nonneg_right (by linarith) hloglam).trans (mul_le_mul_of_nonneg_left hll hX)
  have h5 : (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) + Real.log lam / Real.log 2) * (n : ℝ) ^ D *
        Real.log (n + 1) = (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) +
      (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      (Real.log lam / Real.log 2 * Real.log (n + 1)) := by ring
  linarith

end

end ResChiSandwich

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

