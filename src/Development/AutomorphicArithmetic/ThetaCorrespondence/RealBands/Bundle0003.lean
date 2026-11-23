module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.DecaysZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.RightDerivativeZeroOutsideSupport

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvCoef
section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.conv_coef :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → ∀ v a : H,
        Continuous (coefOn (ε := ε) σ a v) ∧
          ∀ x, conv (muG ε) (coefOn σ v v) (coefOn σ a v) x = ((‖v‖ ^ 2 / d : ℝ) : ℂ) * coefOn σ a v x := by
  intro n ε H _ _ σ d hrep hF v a
  obtain ⟨⟨_, hmul⟩, hiso, hcont⟩ := hrep
  have hinner : ∀ g ∈ UJset ε, ∀ x y : H, ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g hg x y =>
    LinearIsometry.inner_map_map ⟨(σ g).toLinearMap, hiso g hg⟩ x y
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hcoef : ∀ w z : H, Continuous (coefOn (ε := ε) σ w z) := by
    intro w z
    have hu : Continuous fun g : UJ ε => umat g :=
      Units.continuous_val.comp continuous_subtype_val
    have hs : Continuous fun g : UJ ε => σ (umat g) w :=
      (hcont w).comp_continuous hu hmem
    exact continuous_const.inner hs
  refine ⟨hcoef a v, fun x => ?_⟩
  have hback : ∀ (g : UJ ε) (y : H), σ (umat g) (σ (umat g⁻¹) y) = y := by
    intro g y
    have h := hmul _ (hmem g) _ (hmem g⁻¹)
    have hone : umat g * umat g⁻¹ = 1 := by
      show ((g * g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = 1
      rw [mul_inv_cancel]
      rfl
    rw [hone] at h
    have h1 : σ 1 = 1 := by assumption
    rw [h1] at h
    exact (congrArg (fun f : H →L[ℂ] H => f y) h).symm
  have key : ∀ g : UJ ε, coefOn σ v v g * coefOn σ a v (g⁻¹ * x) =
      coefOn σ v v g * star (coefOn σ v (σ (umat x) a) g) := by
    intro g
    congr 1
    simp only [coefOn]
    have hsplit : σ (umat (g⁻¹ * x)) a = σ (umat g⁻¹) (σ (umat x) a) := by
      rw [show umat (g⁻¹ * x) = umat g⁻¹ * umat x from rfl, hmul _ (hmem _) _ (hmem _)]
      rfl
    rw [hsplit]
    calc ⟪v, σ (umat g⁻¹) (σ (umat x) a)⟫_ℂ
        = ⟪σ (umat g) v, σ (umat g) (σ (umat g⁻¹) (σ (umat x) a))⟫_ℂ :=
          (hinner _ (hmem g) _ _).symm
      _ = ⟪σ (umat g) v, σ (umat x) a⟫_ℂ := by rw [hback]
      _ = star ⟪σ (umat x) a, σ (umat g) v⟫_ℂ := by
          rw [← inner_conj_symm]
          rfl
  show ∫ g, coefOn σ v v g * coefOn σ a v (g⁻¹ * x) ∂(muG ε) = _
  rw [show (fun g => coefOn σ v v g * coefOn σ a v (g⁻¹ * x)) =
      fun g => coefOn σ v v g * star (coefOn σ v (σ (umat x) a) g) from funext key,
    (hF.2 v v v (σ (umat x) a)).2, inner_self_eq_norm_sq_to_K]
  show _ = _ * ⟪v, σ (umat x) a⟫_ℂ
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, mul_comm]
  rw [mul_comm (_ * _) _, mul_comm ⟪v, σ (umat x) a⟫_ℂ, ← mul_assoc]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.FlagNW
section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

private theorem herm_eq_zero_iff {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) :
    Formalism.QuantumDeterminants.herm (Jm ε) x y = 0 ↔ star x ⬝ᵥ (Jm ε *ᵥ y) = 0 := by
  have e : Formalism.QuantumDeterminants.herm (Jm ε) x y = star (star x ⬝ᵥ (Jm ε *ᵥ y)) := by
    simp only [Formalism.QuantumDeterminants.herm, Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply, star_mul', star_star]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases ε i <;> simp <;> ring
  rw [e, star_eq_zero]

private theorem herm_keep {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H) (x y : Fin n → ℂ) :
    Formalism.QuantumDeterminants.herm H (g *ᵥ x) (g *ᵥ y) = Formalism.QuantumDeterminants.herm H x y := by
  simp only [Formalism.QuantumDeterminants.herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem UpperTheory.Lit.Cusp.flagN_eq_NW :
    ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), IsIsoC ε W →
      IsIsoFlag ε ![Module.finrank ℂ W] ![⊥, W] ∧ 1 ≤ Module.finrank ℂ W ∧ flagN ε ![⊥, W] = NW ε W ∧
        ∃ S : Subgroup (UJ ε), (S : Set (UJ ε)) = NW ε W := by
  intro n ε W hW
  have hl : (![⊥, W] : Fin (1 + 1) → Submodule ℂ (Fin n → ℂ)) (Fin.last 1) = W := rfl
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_, ?_, GlobalTheory.Dec.nwSub ε W, rfl⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    show Module.finrank ℂ W = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + Module.finrank ℂ W
    rw [finrank_bot, zero_add]
  · rw [hl]
    intro x hx y hy
    exact (herm_eq_zero_iff ε x y).1 (hW.2 x hx y hy)
  · exact Submodule.one_le_finrank_iff.2 hW.1
  · ext g
    have e : ∀ y, (umat g - 1) *ᵥ y = uMat g *ᵥ y - y := fun y => by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [flagN, NW, Set.mem_setOf_eq, hl, e]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : ∀ x ∈ W, uMat g *ᵥ x - x = 0 := fun x hx => (Submodule.mem_bot ℂ).1 (h1 0 x hx)
      refine ⟨h1', fun y hy => h2 y fun x hx => (herm_eq_zero_iff ε x y).1 (hy x hx), fun y x hx => ?_⟩
      have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
      have k := herm_keep hg x y
      rw [sub_eq_zero.1 (h1' x hx)] at k
      simp only [Formalism.QuantumDeterminants.herm, star_sub, sub_dotProduct] at k ⊢
      rw [k, sub_self]
    · rintro ⟨h1, h2, -⟩
      refine ⟨fun i y hy => ?_, fun y hy => h2 y fun x hx => (herm_eq_zero_iff ε x y).2 (hy x hx)⟩
      fin_cases i
      exact (Submodule.mem_bot ℂ).2 (h1 y hy)
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Imports
section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.exists_split :
    ∀ (n : ℕ) (ε : Fin n → Bool) (j : Fin 1 → ℕ) (W : Flag n 1), IsIsoFlag ε j W →
      ∃ a : ℝ → UJ ε, Continuous a ∧ (∀ s t, a (s + t) = a s * a t) ∧ ∀ t, IsSplit ε W (fun _ => t) (a t) := by
  intro n ε j W hW
  obtain ⟨P, h0, h1, h2⟩ := GlobalTheory.RealIwasawa.exists_proj (W (Fin.last 1))
  have hJ := Jm_mul_self ε
  have hPP : P * P = P := Matrix.ext_iff_mulVec.2 fun y => by rw [← mulVec_mulVec, h2 _ (h1 y)]
  have hi : P * Jm ε * P = 0 := GlobalTheory.RealIwasawa.proj_iso hW h0 fun y => h1 y
  have key : ∀ r : ℝ, ∃ t : UJ ε,
      uMat t = GlobalTheory.IsoTorus.tor P (Jm ε * P * Jm ε) (Real.exp r) (Real.exp (-r)) := by
    intro r
    set Q := Jm ε * P * Jm ε with hQ
    have hQQ : Q * Q = Q := by
      simp only [hQ, mul_assoc]; rw [← mul_assoc (Jm ε) (Jm ε), hJ, one_mul, ← mul_assoc P P, hPP]
    have hPQ : P * Q = 0 := by rw [hQ, ← mul_assoc, ← mul_assoc, hi, zero_mul]
    have hQP : Q * P = 0 := by rw [hQ, mul_assoc, mul_assoc, ← mul_assoc P, hi, mul_zero]
    set c : ℂ := (Real.exp r : ℂ) with hc
    set d : ℂ := (Real.exp (-r) : ℂ) with hd
    have hH : (GlobalTheory.IsoTorus.tor P Q c d)ᴴ = GlobalTheory.IsoTorus.tor P Q c d := by
      simp [GlobalTheory.IsoTorus.tor, hQ, h0, Jm_conjTranspose, hc, hd, mul_assoc, -Complex.ofReal_exp]
    have hm : (GlobalTheory.IsoTorus.tor P Q c d)ᴴ * Jm ε * GlobalTheory.IsoTorus.tor P Q c d = Jm ε := by
      have e : GlobalTheory.IsoTorus.tor P Q c d * Jm ε = Jm ε * GlobalTheory.IsoTorus.tor P Q d c := by
        simp only [GlobalTheory.IsoTorus.tor, hQ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
          mul_assoc, hJ, ← mul_assoc (Jm ε) (Jm ε)]
        abel
      rw [hH, e, mul_assoc, GlobalTheory.IsoTorus.tor_tor hPP hQQ hPQ hQP, hc, hd, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
      simp [GlobalTheory.IsoTorus.tor_one]
    obtain ⟨t, ht, -⟩ := GlobalTheory.RealIwasawa.exists_uMat _ hm
    exact ⟨t, ht⟩
  choose a ha using key
  have hs : ∀ t, IsSplit ε W (fun _ => t) (a t) := fun t => by
    convert isSplit_of_tor hW h0 h1 h2 (ha t) using 2 with i
    rw [if_pos (Fin.le_last _)]
  refine ⟨a, ?_, fun s t => ?_, hs⟩
  · refine (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff.2 ?_
    refine Continuous.congr (f := fun r : ℝ => GlobalTheory.IsoTorus.tor P (Jm ε * P * Jm ε) (Real.exp r) (Real.exp (-r)))
      ?_ fun r => (ha r).symm
    unfold GlobalTheory.IsoTorus.tor
    fun_prop
  · exact (existsUnique_isSplit hW (fun _ => s + t)).unique (hs _) ((hs s).mul (hs t))
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsCompactBall
section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.isCompact_ball :
    ∀ (n : ℕ) (ε : Fin n → Bool), (∀ R : ℝ, IsCompact {g : UJ ε | hs (umat g) ≤ R}) ∧
      (∀ x y : Matrix (Fin n) (Fin n) ℂ, Real.sqrt (hs (x * y)) ≤ Real.sqrt (hs x) * Real.sqrt (hs y)) ∧
      (∀ g : UJ ε, hs (umat g⁻¹) = hs (umat g)) ∧ Continuous (fun g : UJ ε => hs (umat g)) := by
  intro n ε
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R
    obtain ⟨hemb, -⟩ := isClosedEmbeddingMatrix n ε
    have hK := (hermitian_small_ball n ε).1 R
    have hpre := hemb.isCompact_preimage hK
    convert hpre using 1
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨g.2, h⟩
    · intro h
      exact h.2
  · intro x y
    rw [← Real.sqrt_mul (frobenius_nonneg x)]
    exact Real.sqrt_le_sqrt (frobenius_mul_le x y)
  · intro g
    have h1 : umat g⁻¹ = Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε := coeMatrix_inv_eq ε g
    have h2 : coeMatrixAlt ε g = umat g := rfl
    rw [h1, h2]
    have hd : ∀ i, ‖(if ε i = true then (1 : ℂ) else -1)‖ = 1 := by
      intro i
      split <;> simp
    simp only [hs, Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, norm_mul, hd,
      one_mul, mul_one, norm_star]
    exact Finset.sum_comm
  · exact continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)
end

