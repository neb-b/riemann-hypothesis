module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceSeesawWScalarFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1938
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxGe
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem eq_zero_of_skew_of_I_smul_skew {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    (M : Matrix (Fin r) (Fin r) ℂ)
    (h1 : ∀ u w, hermC τ G (M *ᵥ u) w + hermC τ G u (M *ᵥ w) = 0)
    (h2 : ∀ u w, hermC τ G ((Complex.I • M) *ᵥ u) w + hermC τ G u ((Complex.I • M) *ᵥ w) = 0) :
    M = 0 := by
  have hl : ∀ (c : ℂ) v w, hermC τ G (c • v) w = c * hermC τ G v w := by
    intro c v w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hr : ∀ (c : ℂ) v w, hermC τ G v (c • w) = starRingEnd ℂ c * hermC τ G v w := by
    intro c v w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hA : ∀ u w, hermC τ G (M *ᵥ u) w = 0 := by
    intro u w
    have e1 := h1 u w
    have e2 := h2 u w
    rw [smul_mulVec, smul_mulVec, hl, hr, Complex.conj_I] at e2
    have : Complex.I * (2 * hermC τ G (M *ᵥ u) w) = 0 := by linear_combination e2 + Complex.I * e1
    simpa [Complex.I_ne_zero] using this
  have hGt : (G.map τ).det ≠ 0 := by
    have e := RingHom.map_det τ G
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]; exact (map_ne_zero τ).2 hG
  have hv : ∀ u, M *ᵥ u = 0 := by
    intro u
    refine Matrix.eq_zero_of_vecMul_eq_zero hGt ?_
    funext b
    have := hA u (Pi.single b 1)
    simpa [hermC, Matrix.vecMul, dotProduct, Pi.single_apply] using this
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem finrank_comap_realLie_le (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hr : 1 ≤ r) (hG : G.det ≠ 0) (hx : ∀ τ, (mat x τ).det ≠ 0) :
    Module.finrank ℝ ((realLie Ψ G).comap (fromFrame x)) ≤ Ψ.card * (r ^ 2 - 1) := by
  set W := (realLie Ψ G).comap (fromFrame x) with hW
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have hsm : ∀ (c : ℂ) (V : EuclideanSpace ℂ (Ψ × Fin r × Fin r)),
      fromFrame x (c • V) = c • fromFrame x V := by
    intro c V
    funext τ
    have e : Matrix.of (fun a b => (c • V) (τ, a, b)) = c • Matrix.of (fun a b => V (τ, a, b)) := rfl
    show (mat x τ * Matrix.of (fun a b => (c • V) (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) =
      c • (mat x τ * Matrix.of (fun a b => V (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
    rw [e, Matrix.mul_smul, Matrix.smul_mul]
  have hIW : ∀ V, V ∈ W → Complex.I • V ∈ W → V = 0 := by
    intro V h1 h2
    have h1' : fromFrame x V ∈ realLie Ψ G := h1
    have h2' : fromFrame x (Complex.I • V) ∈ realLie Ψ G := h2
    rw [hsm] at h2'
    have hM : ∀ τ, Matrix.of (fromFrame x V τ) = 0 := fun τ =>
      eq_zero_of_skew_of_I_smul_skew hG _ (h1' τ).2 (h2' τ).2
    refine PiLp.ext fun p => ?_
    obtain ⟨τ, a, b⟩ := p
    have e : (mat x τ * Matrix.of (fun a b => V (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = 0 := hM τ
    have := key1 τ (Matrix.of (fun a b => V (τ, a, b)))
    rw [e, Matrix.mul_zero, Matrix.zero_mul] at this
    have := congrFun (congrFun this a) b
    simpa using this.symm
  let L : (W × W) →ₗ[ℝ] EuclideanSpace ℂ (Ψ × Fin r × Fin r) :=
    { toFun := fun p => (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) + Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r))
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
        rw [smul_comm] }
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    have hp' : (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) + Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = 0 := hp
    have e1 : (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = Complex.I • ((-p.2 : W) : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) := by
      rw [Submodule.coe_neg, smul_neg]; exact eq_neg_of_add_eq_zero_left hp'
    have h3 : Complex.I • ((-p.2 : W) : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) ∈ W := e1 ▸ p.1.2
    have h4 := hIW _ (-p.2).2 h3
    have h5 : p.2 = 0 := by
      have : -p.2 = 0 := Subtype.ext h4
      simpa using this
    have h6 : p.1 = 0 := by
      apply Subtype.ext
      rw [e1, h4, smul_zero]; rfl
    exact Prod.ext h6 h5
  let tr : EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] (Ψ → ℂ) :=
    { toFun := fun Y τ => ∑ a, Y (τ, a, a)
      map_add' := by
        intro Y Z; funext τ; simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c Y; funext τ; simp [Finset.smul_sum] }
  have htrW : ∀ Y ∈ W, tr Y = 0 := by
    intro Y hY
    have hY' : fromFrame x Y ∈ realLie Ψ G := hY
    funext τ
    have ht := (hY' τ).1
    have e : Matrix.of (fromFrame x Y τ) = mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹ := rfl
    rw [e, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ (hx τ).isUnit, Matrix.one_mul] at ht
    show ∑ a, Y (τ, a, a) = (0 : Ψ → ℂ) τ
    simpa [Matrix.trace] using ht
  have hrange : L.range ≤ LinearMap.ker tr := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.mem_ker]
    have e : L p = (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) + Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) := rfl
    rw [e, map_add (f := _)]
    have h2 : tr (Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r))) = Complex.I • tr p.2 := by
      funext τ; simp [tr, Finset.mul_sum]
    rw [h2, htrW _ p.1.2, htrW _ p.2.2, smul_zero, add_zero]
  have hsurj : LinearMap.range tr = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      if p.2.1 = ⟨0, hr⟩ ∧ p.2.2 = ⟨0, hr⟩ then c p.1 else 0), ?_⟩
    funext τ
    simp [tr]
  have hdimE : Module.finrank ℝ (EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = 2 * (Ψ.card * (r * r)) := by
    rw [(WithLp.linearEquiv 2 ℝ (Ψ × Fin r × Fin r → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Fintype.card_prod, Fintype.card_coe, mul_comm]
  have hdimP : Module.finrank ℝ (Ψ → ℂ) = 2 * Ψ.card := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Fintype.card_coe, mul_comm]
  have h1 := LinearMap.finrank_range_add_finrank_ker tr
  rw [hsurj, finrank_top, hdimE, hdimP] at h1
  have h2 := Submodule.finrank_mono hrange
  rw [LinearMap.finrank_range_of_inj hLinj, Module.finrank_prod] at h2
  have h3 : Ψ.card * (r ^ 2 - 1) = Ψ.card * (r * r) - Ψ.card := by
    rw [Nat.mul_sub_one, sq]
  rw [h3]
  omega

end GlobalTheory.CovTop.VolUp

namespace GlobalTheory.CovTop.VolUp

theorem riemLie_frameBox_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ((ε / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε} := by
  intro E _ _ _ r Ψ G x hr hG hx ε hε hε1
  set W := (realLie Ψ G).comap (fromFrame x) with hW
  unfold riemLie
  have hf : Measurable (fun Y : W => fromFrame x Y.1) :=
    ((fromFrame x).comp W.subtype).continuous_of_finiteDimensional.measurable
  refine le_trans ?_ (Measure.le_map_apply hf.aemeasurable _)
  rw [OrthonormalBasis.addHaar_eq_volume]
  have hdim := finrank_comap_realLie_le Ψ G x hr hG hx
  set N := Module.finrank ℝ W with hN
  obtain ⟨b⟩ : Nonempty (OrthonormalBasis (Fin N) ℝ W) := ⟨stdOrthonormalBasis ℝ W⟩
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  set η : ℝ := ε / ((Ψ.card : ℝ) * (r : ℝ) ^ 2) with hη
  have hη0 : 0 ≤ η := by positivity
  have hcr : (N : ℝ) ≤ (Ψ.card : ℝ) * (r : ℝ) ^ 2 := by
    have : N ≤ Ψ.card * r ^ 2 := hdim.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    exact_mod_cast this
  have hη1 : η ≤ 1 := by
    rcases Nat.eq_zero_or_pos Ψ.card with h0 | h0
    · simp [hη, h0]
    · have : (1 : ℝ) ≤ (Ψ.card : ℝ) * (r : ℝ) ^ 2 := by
        have : 1 ≤ Ψ.card * r ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
        exact_mod_cast this
      exact div_le_one_of_le₀ (hε1.trans this) (by positivity)
  have hNη : (N : ℝ) * η ≤ ε := by
    calc (N : ℝ) * η ≤ ((Ψ.card : ℝ) * (r : ℝ) ^ 2) * η := mul_le_mul_of_nonneg_right hcr hη0
      _ ≤ ε := by
        rcases eq_or_ne ((Ψ.card : ℝ) * (r : ℝ) ^ 2) 0 with h0 | h0
        · rw [h0, zero_mul]; exact hε.le
        · rw [hη, mul_div_cancel₀ _ h0]
  let C : Set (Fin N → ℝ) := Set.univ.pi fun _ => Set.Ioo (-(η / 2)) (η / 2)
  have hmp : MeasurePreserving (fun Y : W => (b.repr Y).ofLp) volume volume :=
    (PiLp.volume_preserving_ofLp _).comp b.measurePreserving_repr
  have hC : volume ((fun Y : W => (b.repr Y).ofLp) ⁻¹' C) = ENNReal.ofReal η ^ N := by
    rw [hmp.measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo]
    simp [Finset.prod_const]
  calc ENNReal.ofReal (η ^ (Ψ.card * (r ^ 2 - 1))) = ENNReal.ofReal η ^ (Ψ.card * (r ^ 2 - 1)) :=
        ENNReal.ofReal_pow hη0 _
    _ ≤ ENNReal.ofReal η ^ N := pow_le_pow_right_of_le_one' (ENNReal.ofReal_le_one.2 hη1) hdim
    _ = volume ((fun Y : W => (b.repr Y).ofLp) ⁻¹' C) := hC.symm
    _ ≤ _ := by
      refine measure_mono fun Y hY => ?_
      simp only [Set.mem_preimage, C, Set.mem_pi, Set.mem_univ, Set.mem_Ioo, true_implies] at hY
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      intro τ a c
      have e : Matrix.of (fromFrame x Y.1 τ) =
          mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ := rfl
      rw [e, key1]
      have h1 : ‖(Y.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (τ, a, c)‖ ≤ ‖Y‖ := PiLp.norm_apply_le _ _
      have h2 : ‖Y‖ ≤ ∑ i, |(b.repr Y).ofLp i| := by
        calc ‖Y‖ = ‖∑ i, (b.repr Y).ofLp i • b i‖ := by rw [b.sum_repr]
          _ ≤ ∑ i, ‖(b.repr Y).ofLp i • b i‖ := norm_sum_le _ _
          _ = ∑ i, |(b.repr Y).ofLp i| := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs]
      have h3 : ∑ i, |(b.repr Y).ofLp i| ≤ (N : ℝ) * (η / 2) := by
        calc ∑ i, |(b.repr Y).ofLp i| ≤ ∑ _i : Fin N, η / 2 :=
              Finset.sum_le_sum fun i _ => (abs_lt.2 (hY i)).le
          _ = (N : ℝ) * (η / 2) := by simp
      simp only [Matrix.of_apply]
      linarith

end GlobalTheory.CovTop.VolUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyTangentBoundNonconstant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegelTangentBound

def acts (W : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ
  | .inl uv => Matrix.single uv.1 uv.2 1
  | .inr true => (W + W.transpose).adjugate * W
  | .inr false => (W + W.transpose).adjugate * W.transpose

theorem main : ∀ (h n : ℕ), 1 ≤ h → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : cycAway n →+* K) (c : SiegPre h n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), c.Principal → (∀ (lam : (Fin r → K) →ₗ[K] K) (c' : SiegPre h n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), SiegPB c' c (spMap (dirMap lam)) → SiegPB c' c (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ h * (h + 1) / 2 := by
  intro h n _ h3 hodd K _ _ r β c hc hun
  have hn : n ≠ 0 := by omega
  obtain ⟨L1, L2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨W, hW, hbasAll⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hbas⟩ := hbasAll h
  have hζ : (cycBase hn).ζ ^ n = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, cycBase_ζ]
    exact Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one)
  have hdet : (W + W.transpose).det = 1 := hW.2
  have hw : (W + W.transpose) * acts W (.inr true) = W := by
    simp only [acts]; rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]
  have hw' : (W + W.transpose) * acts W (.inr false) = W.transpose := by
    simp only [acts]; rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]
  have he : ∀ u v : Fin 8, ∃ j, acts W j = Matrix.single u v 1 := fun u v => ⟨.inl (u, v), rfl⟩
  obtain ⟨t, ht⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h (8 * h) W _ (acts W) bas hW hbas n (cycAway n)
    (cycBase hn) _ _ c hodd h3 hζ hc
  refine GlobalTheory.PowerTangent.main L1 L2 GlobalTheory.Moduli.cube_of_isLB h (8 * h) W _ (acts W) bas hW hbas (.inr true) (.inr false)
    hw hw' n (cycAway n) (cycBase hn) K r β t c hc ht ?_
  intro lam t' m₁ m₂
  have hf : spMap (dirMap lam) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
      spMap ((algebraMap K (DualNumber K)).comp β) ≫ spMap (RingHom.id (cycAway n)) := by
    rw [← spMap_comp, ← spMap_comp]
    exact congrArg spMap (RingHom.ext fun z => by
      simp [dirMap, TrivSqZeroExt.algebraMap_eq_inl])
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n _ _ (zetaAway n) (zetaAway n) (RingHom.id _) _ _ _ _
    (spMap (dirMap lam)) rfl hf).1 c
  have hc'P := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n _ _ (zetaAway n) (zetaAway n) (RingHom.id _) _ _ _ _
    (spMap (dirMap lam)) rfl hf).2.1 c c' hc' hc
  obtain ⟨t'', ht''⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h (8 * h) W _ (acts W) bas hW hbas n (cycAway n)
    (cycBase hn) _ _ c' hodd h3 hζ hc'P
  have m₃ : TMap t'' t (spMap (dirMap lam)) :=
    (GlobalTheory.PowerPullback.main L1 L2 h (8 * h) W _ (acts W) bas hW hbas n _ (cycBase hn) _ _ _ _ c c' t t''
      (spMap (dirMap lam)) hc hc'P ht ht'').1 hc'
  have m₄ : TMap t'' t' (𝟙 _) :=
    ((GlobalTheory.ZM.tmap_id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ t t' t'').2 _ (𝟙 _) m₁).2 (by rwa [Category.id_comp])
  have m₅ : TMap t'' t (constPt (spMap (dirMap lam))) := by
    have := ((GlobalTheory.ZM.tmap_id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ t t' t'').2 _ (𝟙 _) m₂).1 m₄
    rwa [Category.id_comp] at this
  exact hun lam c' hc' ((GlobalTheory.PowerPullback.main L1 L2 h (8 * h) W _ (acts W) bas hW hbas n _ (cycBase hn) _ _ _ _ c c' t t''
    _ hc hc'P ht ht'').2 he m₅)

end GlobalTheory.SiegelTangentBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLevCalc

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''} {d d' d'' : ℕ}

theorem sRel_comp {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SRel c' c d' d f) (m' : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) := by
  obtain ⟨φ, hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨ψ, hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩ := m'
  refine ⟨ψ ≫ φ, hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem sRel_cancel {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SRel c' c d' d f) (m' : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' := by
  obtain ⟨φ, hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨χ, hχ, ⟨χ₂, hs', hw'⟩, hl'⟩ := m'
  have hp := hφ.1
  let F : c''.A.left ⟶ c'.A.left := hp.lift χ (c''.A.hom ≫ f') (by rw [hχ.1.w, Category.assoc])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ c'.A.hom = c''.A.hom ≫ f' := hp.lift_snd _ _ _
  let U : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A ⊗ c'.A :=
    lift (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A))
  let F₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left := U.left
  have h₁ : F₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₂ : F₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = _ ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd c.A c.A).left = _ ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨F₂, ⟨h₁, h₂⟩, ?_⟩, fun a => ?_⟩
  · rw [← h₃] at hw'
    exact (hw'.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (iso_pull_pull c.isLB φ₂ F₂).symm).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c'.isLB _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans ((hl' a).trans ((Category.assoc _ _ _).trans
        ((congrArg (f' ≫ ·) (hl a).symm).trans (Category.assoc _ _ _).symm))))
    · have a₁ : (c''.lev a ^ d'').left ≫ c''.A.hom = 𝟙 S'' := Over.w (c''.lev a ^ d'')
      have a₂ : (c'.lev a ^ d').left ≫ c'.A.hom = 𝟙 S' := Over.w (c'.lev a ^ d')
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

theorem sRel_principal {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {f : S' ⟶ S} (m : SRel c' c d' d f)
    (hc : c.Principal) : c'.Principal := by
  obtain ⟨φ, pb, ⟨φ₂, sq, iso⟩, -⟩ := m
  obtain ⟨h₁, h₂⟩ := hc
  exact ⟨(pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
    (diag_iso sq iso)).2.1 h₁, nondeg_pull pb sq c.isLB c'.isLB iso h₂⟩

theorem pow_section {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (hφ : IsGrpPullback A' A f φ) (x' : 𝟙_ (Over S') ⟶ A') (x : 𝟙_ (Over S) ⟶ A)
    (e : x'.left ≫ φ = f ≫ x.left) (k : ℕ) : (x' ^ k).left ≫ φ = f ≫ (x ^ k).left := by
  have e₁ : x' = SiegelPull.secPull hφ x := by
    refine push_injective hφ _ (Over.OverMorphism.ext ?_)
    exact e.trans (SiegelPull.secPull_left hφ x).symm
  have e₂ : x' ^ k = SiegelPull.secPull hφ (x ^ k) := push_injective hφ _ (by
    rw [map_pow, e₁, push_secPull', push_secPull', MonObj.comp_pow])
  rw [e₂, SiegelPull.secPull_left]

theorem sRel_mul {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {f : S' ⟶ S} (m : SRel c' c d' d f) (e : ℕ) :
    SRel c' c (d' * e) (d * e) f := by
  obtain ⟨φ, pb, sq, hl⟩ := m
  refine ⟨φ, pb, sq, fun a => ?_⟩
  rw [pow_mul, pow_mul]
  exact pow_section pb _ _ (hl a) e

theorem sRel_calculus : ∀ (h n n' n'' : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h n ζ s) (c' : SiegPre h n' ζ' s') (c'' : SiegPre h n'' ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S') (d d' d'' : ℕ), SRel c' c d' d f → (SRel c'' c' d'' d' f' ↔ SRel c'' c d'' d (f' ≫ f)) ∧ (c.Principal → c'.Principal) ∧ ∀ e, SRel c' c (d' * e) (d * e) f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m =>
    ⟨⟨sRel_comp m, sRel_cancel m⟩, sRel_principal m, sRel_mul m⟩

end GlobalTheory.SiegLevCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianLatticeSelfDualSmulTransposeInert
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SkewScaleInert

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem latLoc_le_of_unit {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n : ℕ}
    {L L' : Submodule (𝓞 E) (Fin n → E)} {s : E} (hs : w.valuation E s = 1) (hL : ∀ y ∈ L, s • y ∈ L') :
    latLoc F L v ≤ latLoc F L' v := by
  have hs0 : s ≠ 0 := fun h0 => by simp [h0] at hs
  have hu : (1 : Fv F v) ⊗ₜ[F] s⁻¹ ∈ intLoc F E v := by
    rw [InertChart.mem_intLoc_iff hw h, toCompl_tmul, map_one, one_mul]
    change Valued.v (algebraMap E (w.adicCompletion E) s⁻¹) ≤ 1
    rw [show Valued.v (algebraMap E (w.adicCompletion E) s⁻¹) = w.valuation E s⁻¹ from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _, map_inv₀, hs, inv_one]
  intro y hy
  refine latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  convert (latLoc F L' v).smul_mem ⟨_, hu⟩ (tmul_mem_latLoc ha (hL x hx)) using 1
  funext i
  change _ = ((1 : Fv F v) ⊗ₜ[F] s⁻¹) * (a ⊗ₜ[F] (s • x) i)
  rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel_left₀ hs0]

theorem isSelfDualAt_smul_transpose : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s →
    ∀ {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
    ∀ (t : F), t ≠ 0 → ∀ (s₁ s₂ : E), w.valuation E s₁ = 1 → w.valuation E s₂ = 1 →
    (∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) →
      s₁ * algebraMap F E t * e ∈ (algebraMap (𝓞 E) E).range) →
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (s₂ * (algebraMap F E t)⁻¹)))) →
    GlobalTheory.AdelicU.IsSelfDualAt σ (algebraMap F E t • W.Jᵀ) W.L v := by
  intro F E _ _ _ _ _ σ B d W r s hX v w hw t ht s₁ s₂ hs₁ hs₂ h₁ h₂
  have h : w.under (𝓞 F) = v := GlobalTheory.LFun.under_eq_of_isInertAt hw
  have ht0 : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
  have hdet : (algebraMap F E t • W.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ ht0) (GlobalTheory.SkewFrameInert.det_ne_zero hX)
  have hform : ∀ (c : E) (y x : Fin d → E), form σ W.J (c • y) x = c * form σ W.J y x := by
    intro c y x
    simp [form, smul_dotProduct]
  unfold IsSelfDualAt
  rw [← SelfDual.latLoc_dualGlob hdet hX.lat]
  refine le_antisymm (latLoc_le_of_unit hw h hs₁ fun y hy x hx => ?_) (latLoc_le_of_unit hw h hs₂ fun y hy => ?_)
  · rw [GlobalTheory.SkewFrameInert.hE_smul_transpose, hform,
      show algebraMap F E t * (s₁ * form σ W.J y x) = s₁ * algebraMap F E t * form σ W.J y x by ring]
    exact h₁ _ ((hX.dual y).1 hy x hx)
  · refine (hX.dual (s₂ • y)).2 fun x hx o => ?_
    obtain ⟨c, hc⟩ := hy x hx
    rw [GlobalTheory.SkewFrameInert.hE_smul_transpose] at hc
    have e : (o : E) * form σ W.J (s₂ • y) x = ((o * c : 𝓞 E) : E) * (s₂ * (algebraMap F E t)⁻¹) := by
      have hoc : ((o * c : 𝓞 E) : E) = (o : E) * (c : E) := map_mul (algebraMap (𝓞 E) E) o c
      have hc' : (c : E) = algebraMap F E t * form σ W.J y x := hc
      rw [hform, hoc, hc']
      field_simp
    rw [e]
    exact h₂ (o * c)

end GlobalTheory.SkewScaleInert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSymplecticLabelsOfLevelStructureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionSymplecticLabels_of_levelStructure : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (g k : ℕ), 1 ≤ k → ∀ (ζ : Cˣ) (pt : (Fin (2 * g) → ZMod k) → (TFK (R := V) C ⟶ A.A)), IsPrimitiveRoot ζ k → (∀ a b, pt (a + b) = pt a * pt b) → Function.Injective pt → (∀ z : TFK (R := V) C ⟶ A.A, z ^ k = 1 → ∃ a, pt a = z) → (∀ i j, WeilIs A.A A.L k (pt (Pi.single i 1)) (pt (Pi.single j 1)) (unitOn (ζ ^ stdSymp g i j))) → ∃ (p : (Fin (2 * g) → ZMod k) → QkPt D.toPre C k) (q : (Fin (2 * g) → ZMod k) → N.QT k), QLevel N g k ζ q ∧ ∀ a, ν.QPt (p a) (q a) ∧ QkToAkU U.toUnifPre C k (p a) (pt a) := by
  first | exact @GlobalTheory.MBLow.qLevel_of_torsion_labels | exact GlobalTheory.MBLow.qLevel_of_torsion_labels | (intros; apply GlobalTheory.MBLow.qLevel_of_torsion_labels <;> assumption)
end

