module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramified
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0335
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormProdSignMulDetSubmatrixSubOneLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LeviFinsetSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def hat {κ : Type} (w : (κ → F) × (κ → F)) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (w.1 i), fun i => algebraMap F (AF F) (w.2 i))

theorem hat_add {κ : Type} (a b : (κ → F) × (κ → F)) : hat (a + b) = hat a + hat b := by
  simp only [hat, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add (f := _)]; rfl

theorem hat_smul {κ : Type} (c : F) (a : (κ → F) × (κ → F)) : hat (c • a) = algebraMap F (AF F) c • hat a := by
  simp only [hat, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul]; rfl

theorem hat_zero {κ : Type} : hat (0 : (κ → F) × (κ → F)) = 0 := by
  simp only [hat, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, map_zero]; rfl

theorem schr_comp {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add,
    add_assoc, add_dotProduct, dotProduct_add]
  congr 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : R)

variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

def IsMixed (M₁ : Model σ X W₁) (H' : Plane E d d₁) (m : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Prop :=
  ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))), ∃ z : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    (M₁.co.e z).1 = 0 ∧ m = u + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ

theorem isMixed_zero (M₁ : Model σ X W₁) (H' : Plane E d d₁) : IsMixed M₁ H' 0 :=
  ⟨0, ⟨0, by ext i j; simp [Matrix.vecMulVec_apply]⟩, 0, by simp, by simp⟩

theorem IsMixed.add {M₁ : Model σ X W₁} {H' : Plane E d d₁} {m m' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (h : IsMixed M₁ H' m) (h' : IsMixed M₁ H' m') : IsMixed M₁ H' (m + m') := by
  obtain ⟨u, ⟨y, rfl⟩, z, hz, rfl⟩ := h
  obtain ⟨u', ⟨y', rfl⟩, z', hz', rfl⟩ := h'
  refine ⟨Matrix.vecMulVec (y + y') (incV F H'.x), ⟨y + y', rfl⟩, z + z', by simp [hz, hz'], ?_⟩
  rw [Matrix.add_vecMulVec, Matrix.mul_add, Matrix.add_mul]
  abel

theorem IsMixed.smul {M₁ : Model σ X W₁} {H' : Plane E d d₁} {m : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (h : IsMixed M₁ H' m) (t : AF F) : IsMixed M₁ H' (t • m) := by
  obtain ⟨u, ⟨y, rfl⟩, z, hz, rfl⟩ := h
  refine ⟨Matrix.vecMulVec (t • y) (incV F H'.x), ⟨t • y, rfl⟩, t • z, by simp [hz], ?_⟩
  rw [smul_add, Matrix.smul_vecMulVec, Matrix.mul_smul, Matrix.smul_mul]

def lagr (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) :
    Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) where
  carrier := {w | IsMixed M₁ H' (M.co.e.symm (hat w))}
  zero_mem' := by simpa [hat_zero] using isMixed_zero M₁ H'
  add_mem' := fun ha hb => by simpa [Set.mem_setOf_eq, hat_add, map_add (f := _)] using ha.add hb
  smul_mem' := fun c a ha => by
    show IsMixed M₁ H' (M.co.e.symm (hat (c • a)))
    rw [hat_smul, LinearEquiv.map_smul]
    exact ha.smul _

theorem mem_lagr {M : Model σ X W} {M₁ : Model σ X W₁} {H' : Plane E d d₁} {w} :
    w ∈ lagr M M₁ H' ↔ IsMixed M₁ H' (M.co.e.symm (hat w)) := Iff.rfl

theorem mul_transpose_injective : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n d d₁ : ℕ)
    (JW : Matrix (Fin d) (Fin d) E) (JW₁ : Matrix (Fin d₁) (Fin d₁) E) (ι : Matrix (Fin d) (Fin d₁) E),
    ιᵀ * JW * ι.map σ = JW₁ → JW₁.det ≠ 0 → Function.Injective fun z : Matrix (Fin n) (Fin d₁) E => z * ιᵀ := by
  intro F E _ _ _ σ n d d₁ JW JW₁ ι hg hdet z z' h
  simp only at h
  have h0 : (z - z') * JW₁ = 0 := by
    rw [← hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.sub_mul, h, sub_self, Matrix.zero_mul, Matrix.zero_mul]
  have h1 : z - z' = 0 := by
    have := congrArg (· * JW₁⁻¹) h0
    simp only [Matrix.zero_mul] at this
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one] at this
  exact sub_eq_zero.mp h1

end GlobalTheory.MixedLagr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiformHeightLowerBound
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HtLowProof

theorem eval_blockScale_multi {B N : ℕ} {a : Fin B → ℕ} {h : MvPolynomial (Fin B × Fin N) ℂ}
    (hh : IsMultiHomogeneous a h) (r : Fin B → ℂ) (v : Fin B × Fin N → ℂ) :
    eval (fun q => r q.1 * v q) h = (∏ i, r i ^ a i) * eval v h := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hr : ∏ q : Fin B × Fin N, r q.1 ^ s q = ∏ i, r i ^ a i := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    show ∏ y, r i ^ s (i, y) = _
    rw [Finset.prod_pow_eq_pow_sum, hh s hs i]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hr]
  ring

theorem frameNorm_sum_le {N n : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : Fin n → ℂ) (u : Fin n → Fin N → ℂ)
    (Λ : ℝ) (hc : ∀ k, ‖c k‖ ≤ 1) (hu : ∀ k, frameNorm A (u k) ≤ Λ) :
    frameNorm A (∑ k, c k • u k) ≤ n * Λ := by
  let T : (Fin N → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).symm.toLinearMap ∘ₗ A⁻¹.mulVecLin
  have hT : ∀ z, frameNorm A z = ‖T z‖ := fun z => by
    rw [frameNorm, EuclideanSpace.norm_eq]; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hT, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _k : Fin n, Λ := Finset.sum_le_sum fun k _ => by
        rw [map_smul, norm_smul, ← hT]
        exact (mul_le_of_le_one_left (GlobalTheory.MaxPoint.frameNorm_nonneg' _ _) (hc k)).trans (hu k)
    _ = n * Λ := by simp

theorem norm_eval_le {B N : ℕ} {a : Fin B → ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) (hN : 0 < N)
    {h : MvPolynomial (Fin B × Fin N) ℂ} (hh : IsMultiHomogeneous a h) (R : ℝ) (hR : 0 ≤ R)
    (u : Fin B × Fin N → ℂ) (hu : ∀ i, frameNorm A (fun j => u (i, j)) ≤ R) :
    ‖eval u h‖ ≤ Real.exp (blockSphereMean B N (linSubst A h) + (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2) *
      R ^ (∑ i, a i) := by
  set r : Fin B → ℝ := fun i => frameNorm A (fun j => u (i, j)) with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => GlobalTheory.MaxPoint.frameNorm_nonneg' _ _
  set e : Fin N → ℂ := A.mulVec (Pi.single ⟨0, hN⟩ 1) with he'
  have he : frameNorm A e = 1 := by
    rw [he', GlobalTheory.MaxPoint.frameNorm_mulVec hA]
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N) (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
    simp
  let p : Fin B × Fin N → ℂ := fun q => if r q.1 = 0 then e q.2 else ((r q.1)⁻¹ : ℂ) * u q
  have hp : ∀ i, frameNorm A (fun j => p (i, j)) = 1 := fun i => by
    by_cases h0 : r i = 0
    · have : (fun j => p (i, j)) = e := by funext j; simp [p, h0]
      rw [this, he]
    · have : (fun j => p (i, j)) = ((r i)⁻¹ : ℂ) • (fun j => u (i, j)) := by
        funext j; simp [p, h0]
      rw [this, GlobalTheory.MaxPoint.frameNorm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hr0 i)]
      exact inv_mul_cancel₀ h0
  have hup : u = fun q => ((r q.1 : ℝ) : ℂ) * p q := by
    funext q
    by_cases h0 : r q.1 = 0
    · have hz : (fun j => u (q.1, j)) = 0 := GlobalTheory.MaxPoint.eq_zero_of_frameNorm_eq_zero hA h0
      have := congrFun hz q.2
      simp only [Pi.zero_apply] at this
      simp [h0, this]
    · simp only [p, if_neg h0]
      rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ h0, Complex.ofReal_one, one_mul]
  have hval : ‖eval u h‖ = (∏ i, r i ^ a i) * ‖eval p h‖ := by
    rw [hup, eval_blockScale_multi hh (fun i => ((r i : ℝ) : ℂ)) p, norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (hr0 i)]
  have hprod : ∏ i, r i ^ a i ≤ R ^ (∑ i, a i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun i _ => pow_nonneg (hr0 i) _) fun i _ => pow_le_pow_left₀ (hr0 i) (hu i) _
  rw [hval]
  by_cases hz : eval p h = 0
  · rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hR _)
  · have harch := _root_.GlobalTheory.LelongBlocksMulti.log_eval_sub_le_blockSphereMean B N a A h hA hh p hp hz
    have hle : ‖eval p h‖ ≤ Real.exp (blockSphereMean B N (linSubst A h) +
        (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 hz)]
      exact Real.exp_le_exp.2 (by linarith)
    rw [mul_comm]
    exact mul_le_mul hle hprod (Finset.prod_nonneg fun i _ => pow_nonneg (hr0 i) _) (Real.exp_pos _).le

theorem eval₂_linSubst {F : Type} [Field F] {B N n : ℕ} (s : F →+* ℂ) (w : Matrix (Fin N) (Fin n) F)
    (G : MvPolynomial (Fin B × Fin N) F) (z : Fin B × Fin n → ℂ) :
    eval₂ s z (linSubst w G) = eval (fun q => ∑ k, z (q.1, k) * s (w q.2 k)) (MvPolynomial.map s G) := by
  have e : ((eval₂Hom s z).comp (aeval (fun p : Fin B × Fin N => ∑ k, C (w p.2 k) * X (p.1, k)) :
      MvPolynomial (Fin B × Fin N) F →ₐ[F] MvPolynomial (Fin B × Fin n) F).toRingHom) =
      (eval (fun q => ∑ k, z (q.1, k) * s (w q.2 k))).comp (MvPolynomial.map s) := by
    refine MvPolynomial.ringHom_ext (fun c => by simp) (fun q => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, map_sum, map_mul,
      coe_eval₂Hom, eval₂_C, eval₂_X, map_X, eval_X]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  exact RingHom.congr_fun e G

theorem htLow : HtLow := by
  intro F _ _ B N n w A Λ hL a G hG ha
  obtain ⟨P, hP⟩ := GlobalTheory.HeightUnique.exists_right_inv hL.spans
  have hk : linSubst w G ≠ 0 := GlobalTheory.HeightUnique.linSubst_ne_zero hP hG
  have hNn : N ≤ n := by
    have h1 := finrank_range_le_card (R := F) w.col
    unfold Set.finrank at h1
    rw [hL.spans, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
    exact h1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (hL.pos.trans_le hNn)
  have hnΛ : (0 : ℝ) < n * Λ := mul_pos (by linarith) (by linarith [hL.one_le])
  set deg : ℝ := ∑ b, (a b : ℝ) with hdeg
  set H : ℝ := (harmonic (N - 1) : ℝ) with hH
  set m : (F →+* ℂ) → ℝ := fun σ => blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ G)) with hm
  have key := GlobalTheory.HSFloor.floor F (Fin B × Fin n) (linSubst w G)
    (fun s => Real.exp (m s + deg * H / 2) * ((n : ℝ) * Λ) ^ (∑ b, a b)) hk (fun s z hz => by
      rw [eval₂_linSubst]
      refine norm_eval_le (hL.det s) hL.pos (isMultiHomogeneous_map_ring a G ha s) _ hnΛ.le _ fun i => ?_
      have e : (fun j => ∑ k, z (i, k) * s (w j k)) = ∑ k, z (i, k) • (fun j => s (w j k)) := by
        funext j; simp [Finset.sum_apply]
      rw [e]
      exact frameNorm_sum_le _ _ _ Λ (fun k => hz _) fun k => hL.le k s)
  have hd : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.2 Module.finrank_pos
  have hcard : (Fintype.card (F →+* ℂ) : ℝ) = Module.finrank ℚ F := by
    rw [NumberField.Embeddings.card]
  have hlog : ∀ s, Real.log (Real.exp (m s + deg * H / 2) * ((n : ℝ) * Λ) ^ (∑ b, a b)) =
      m s + (deg * H / 2 + deg * Real.log (n * Λ)) := fun s => by
    rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hnΛ _).ne', Real.log_exp, Real.log_pow, hdeg]
    push_cast
    ring
  have hmean : mean F (fun s => Real.log (Real.exp (m s + deg * H / 2) * ((n : ℝ) * Λ) ^ (∑ b, a b))) =
      mean F m + (deg * H / 2 + deg * Real.log (n * Λ)) := by
    simp only [hlog, mean, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    field_simp
  have hht : ht w A G = finPart (linSubst w G) + mean F m := by
    simp only [ht, formHeight, finPart, mean, hm]
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
    rw [add_div]
  have hHle : H ≤ Real.log n + 1 := by
    have h1 : H ≤ 1 + Real.log ((N - 1 : ℕ) : ℝ) := by
      rw [hH]; exact_mod_cast harmonic_le_one_add_log (N - 1)
    have h2 : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log n := by
      rcases Nat.eq_zero_or_pos (N - 1) with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg hn1
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (by omega : N - 1 ≤ n))
    linarith
  have hdeg0 : 0 ≤ deg := Finset.sum_nonneg fun b _ => Nat.cast_nonneg _
  rw [hmean] at key
  rw [hht, cst]
  nlinarith [mul_le_mul_of_nonneg_left hHle hdeg0]

end GlobalTheory.HtLowProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonSplitPlaceStabilizerFixesLatticeVacuum
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem nonSplit_fixes_latVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (H : Geo.Tor.Host D.host.E) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ f, IsThetaFunO ψ V W f → IsLatVac (heisO ψ V W) (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) f → ∀ v ε (k : GA D W), GlobalTheory.WeilParts.NonSplitAt D v ε → GlobalTheory.WeilParts.SuppPl ε W k → (∀ u, u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ actO V W 1 k u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True)) → om (1, k) f = f ∧ (V.rank ≠ 0 → mu k = 1) := by
  intro D ψ θ V W χV χW om hP mu hmu _ ΛV ΛW hV hW f hf hvac v ε k hv hk hst
  obtain ⟨uV, uW⟩ := hP.unr v ε hv
  refine ⟨?_, fun _ => ?_⟩
  · have h1 : GlobalTheory.WeilParts.SuppPl ε V 1 := fun i j => by
      rw [GlobalTheory.FinWeilO.mt_one, sub_self, Matrix.zero_apply, mul_zero]
    refine _root_.GlobalTheory.VacInert.fixesVacAt_of_unram D ψ hP.weil.std V W ΛV ΛW hV hW χV χW om hP.eta hP.weil v ε hv uV uW 1 k h1 hk
      (fun u => ?_) f hf fun u hu => ?_
    · rw [GlobalTheory.InertVac.mem_latO_place_iff hv.1, GlobalTheory.InertVac.mem_latO_place_iff hv.1, ← hst,
        ← GlobalTheory.FinWeilO.actO_smul, (GlobalTheory.InertVac.actO_injective 1 k).eq_iff]
    · obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hv
      have h1 : 2 • (a • u) = u := by
        rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.InertVac.placeIdem_smul_eq hv.1 hu]
      have h2 := hvac.1 (a • u)
        (GlobalTheory.LatticeStable.smul_mem_latO D V W _ _ _ a ha u (GlobalTheory.PlaceModel.latO_le_top _ hu))
      rwa [h1] at h2
  · obtain ⟨x, hx, -, xs, x1, x2⟩ := GlobalTheory.VacInert.exists_unit_root hv W k hk
    rw [hmu.2 k x hx, uV x xs x1 x2, Circle.coe_one]

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.ChartNearOne

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sum_succ_sub_castSucc {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  rw [Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ f
  have h2 := Fin.sum_univ_castSucc f
  linarith

theorem nmat_entry_le (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    ‖nmat X z τ a b - (if a = b then 1 else 0)‖ ≤ ‖z‖ := by
  unfold nmat
  by_cases h : b < a
  · have hab : a ≠ b := fun e => lt_irrefl b (e ▸ h)
    rw [dite_eq_left h, if_neg hab, sub_zero]
    exact PiLp.norm_apply_le z _
  · rw [dite_eq_right h]
    split_ifs <;> simp

theorem det_nmat (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : (mat (nmat X z) τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [mat, nmat]
  · intro a b hab
    have h1 : ¬ b < a := fun h => lt_asymm h hab
    have h2 : a ≠ b := ne_of_lt hab
    simp [mat, nmat, h1, h2]

theorem norm_dmin_zero (X : Data E r) (y : Frame X.Ψ r) (τ : X.Ψ) : ‖dmin X.Gm y τ 0‖ = 1 := by
  haveI : IsEmpty (Fin ((0 : Fin (r + 1)) : ℕ)) := ⟨fun i => absurd i.2 (by simp)⟩
  rw [dmin, lminor, Matrix.det_isEmpty, norm_one]

theorem norm_dmin_last (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) :
    ‖dmin X.Gm (cpt X x z) τ (Fin.last r)‖ = 1 := by
  rw [PoinPf.dmin_cpt_orth X hx]
  have e : lminor (PoinPf.Gw X z τ) (Fin.last r) = (PoinPf.Gw X z τ).det := rfl
  rw [e, PoinPf.Gw, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_nmat,
    show (mat (nmat X z) τ).map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (mat (nmat X z) τ) from rfl,
    ← RingHom.map_det, det_nmat, PoinPf.Jd, Matrix.det_diagonal]
  simp only [one_mul, map_one, mul_one, norm_prod, Complex.norm_real, Real.norm_eq_abs, PoinPf.abs_sgn]
  simp

theorem abs_sub_mid_le (X : Data E r) (la : Wt X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    |(la τ i : ℝ) - ((⨆ k, (la τ k : ℝ)) + ⨅ k, (la τ k : ℝ)) / 2| ≤ X.spread la τ / 2 := by
  have h1 := le_ciSup (Finite.bddAbove_range fun k => (la τ k : ℝ)) i
  have h2 := ciInf_le (Finite.bddBelow_range fun k => (la τ k : ℝ)) i
  unfold Data.spread
  rw [abs_le]
  constructor <;> linarith

theorem weighted_diff_le (X : Data E r) (la : Wt X.Ψ r) (τ : X.Ψ) (L : Fin (r + 1) → ℝ) {t : ℝ}
    (hL : ∀ i, |L i| ≤ t) (h0 : L 0 = 0) (hr : L (Fin.last r) = 0) :
    ∑ i : Fin r, (la τ i : ℝ) * (L i.succ - L i.castSucc) ≤ r * t * X.spread la τ := by
  set c := ((⨆ k, (la τ k : ℝ)) + ⨅ k, (la τ k : ℝ)) / 2
  have hs : 0 ≤ X.spread la τ := by
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp [Data.spread]
    · have := abs_sub_mid_le X la τ ⟨0, hr0⟩
      linarith [abs_nonneg ((la τ ⟨0, hr0⟩ : ℝ) - c)]
  have e : ∑ i : Fin r, (la τ i : ℝ) * (L i.succ - L i.castSucc) =
      ∑ i : Fin r, ((la τ i : ℝ) - c) * (L i.succ - L i.castSucc) +
        c * ∑ i : Fin r, (L i.succ - L i.castSucc) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, sum_succ_sub_castSucc, h0, hr, sub_zero, mul_zero, add_zero]
  calc ∑ i : Fin r, ((la τ i : ℝ) - c) * (L i.succ - L i.castSucc)
      ≤ ∑ i : Fin r, X.spread la τ / 2 * (2 * t) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        have h1 := abs_sub (L i.succ) (L i.castSucc)
        have h2 : |L i.succ - L i.castSucc| ≤ 2 * t := by linarith [hL i.succ, hL i.castSucc]
        exact mul_le_mul (abs_sub_mid_le X la τ i) h2 (abs_nonneg _) (by linarith)
    _ = r * t * X.spread la τ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end

theorem chart_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w →
    ∀ z : V (nd X), ‖z‖ ≤ chartRad E r w → cpt X x z ∈ X.dom ∧
      Real.exp (-(1/20)) ≤ X.nfac la (cpt X x z) ^ 2 ∧ Real.exp (-(1/10)) ≤ densF X x z := by
  intro E _ _ _ r X la w x hr hx hw z hz
  have hf : (1 : ℝ) ≤ fdeg E := one_le_field_half_degree
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsp : ∀ τ, 0 ≤ X.spread la τ := fun τ => by
    have := abs_sub_mid_le X la τ ⟨0, hr⟩
    linarith [abs_nonneg ((la τ ⟨0, hr⟩ : ℝ) - ((⨆ k, (la τ k : ℝ)) + ⨅ k, (la τ k : ℝ)) / 2)]
  have hw0 : 0 ≤ w := le_trans (Finset.sum_nonneg fun τ _ => hsp τ) hw
  set δ := chartRad E r w with hδdef
  have hwf : 0 < w + fdeg E := by linarith
  have hδ0 : 0 < δ := by rw [hδdef, chartRad]; positivity
  have key : (r : ℝ) ^ 3 * δ * (w + fdeg E) * 200 = 1 := by
    rw [hδdef, chartRad]
    have : (r : ℝ) ≠ 0 := by positivity
    field_simp
  have hA0 : 0 ≤ (r : ℝ) ^ 3 * δ := by positivity
  have hA : (r : ℝ) ^ 3 * δ ≤ 1 / 200 := by
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ w + fdeg E by linarith) hA0]
  have hr2 : (r : ℝ) ^ 2 * δ ≤ (r : ℝ) ^ 3 * δ := by
    have : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this hδ0.le
  obtain ⟨hdom, hd⟩ := GlobalTheory.dmin_rmul_near_one X x hx (nmat X z) hδ0.le (by linarith)
    (fun τ a b => (nmat_entry_le X z τ a b).trans hz)
  change cpt X x z ∈ X.dom at hdom
  change ∀ τ i, dmin X.Gm (cpt X x z) τ i ≠ 0 ∧ |Real.log ‖dmin X.Gm (cpt X x z) τ i‖| ≤ 9 * ((r : ℝ) ^ 2 * δ) at hd
  set t := 9 * ((r : ℝ) ^ 2 * δ) with ht
  have ht0 : 0 ≤ t := by positivity
  refine ⟨hdom, ?_, ?_⟩
  ·
    have hne : ∀ τ i, dmin X.Gm (cpt X x z) τ i ≠ 0 := fun τ i => (hd τ i).1
    have hN := CurvPf.neg2log_nfac X la (cpt X x z) hne
    have hbound : -2 * Real.log (X.nfac la (cpt X x z)) ≤ r * t * w := by
      rw [hN]
      calc ∑ τ, ∑ i : Fin r, (la τ i : ℝ) * (Real.log ‖dmin X.Gm (cpt X x z) τ i.succ‖ -
            Real.log ‖dmin X.Gm (cpt X x z) τ i.castSucc‖)
          ≤ ∑ τ, (r : ℝ) * t * X.spread la τ :=
            Finset.sum_le_sum fun τ _ => weighted_diff_le X la τ
              (fun i => Real.log ‖dmin X.Gm (cpt X x z) τ i‖) (fun i => (hd τ i).2)
              (by simp only [norm_dmin_zero, Real.log_one])
              (by simp only [norm_dmin_last X hx, Real.log_one])
        _ = (r : ℝ) * t * ∑ τ, X.spread la τ := (Finset.mul_sum _ _ _).symm
        _ ≤ (r : ℝ) * t * w := mul_le_mul_of_nonneg_left hw (by positivity)
    have hsmall : (r : ℝ) * t * w ≤ 1 / 20 := by
      have e1 : (r : ℝ) * t * w = 9 * ((r : ℝ) ^ 3 * δ * w) := by rw [ht]; ring
      have e2 : 0 ≤ (r : ℝ) ^ 3 * δ * fdeg E := by positivity
      rw [e1]
      nlinarith
    have hpos : 0 < X.nfac la (cpt X x z) := by
      unfold Data.nfac
      exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
        Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hne _ _) (hne _ _))) _
    have e : X.nfac la (cpt X x z) ^ 2 = Real.exp (-(-2 * Real.log (X.nfac la (cpt X x z)))) := by
      rw [show -(-2 * Real.log (X.nfac la (cpt X x z))) =
        Real.log (X.nfac la (cpt X x z)) + Real.log (X.nfac la (cpt X x z)) by ring,
        Real.exp_add, Real.exp_log hpos, sq]
    rw [e]
    exact Real.exp_le_exp.2 (by linarith)
  ·
    have hfac : ∀ τ (i : Fin r), Real.exp (-(2 * t)) ≤ ‖dmin X.Gm (cpt X x z) τ i.castSucc‖ ^ (-2 : ℤ) := by
      intro τ i
      obtain ⟨h0, h1⟩ := hd τ i.castSucc
      have hu : 0 < ‖dmin X.Gm (cpt X x z) τ i.castSucc‖ := norm_pos_iff.2 h0
      have hu' : ‖dmin X.Gm (cpt X x z) τ i.castSucc‖ ≤ Real.exp t := by
        calc ‖dmin X.Gm (cpt X x z) τ i.castSucc‖
            = Real.exp (Real.log ‖dmin X.Gm (cpt X x z) τ i.castSucc‖) := (Real.exp_log hu).symm
          _ ≤ Real.exp t := Real.exp_le_exp.2 (abs_le.1 h1).2
      rw [zpow_neg, zpow_two, Real.exp_neg, two_mul, Real.exp_add]
      exact inv_anti₀ (by positivity) (mul_le_mul hu' hu' hu.le (Real.exp_pos _).le)
    have hprod : Real.exp (-(2 * t)) ^ (Fintype.card X.Ψ * r) ≤ densF X x z := by
      unfold densF
      calc Real.exp (-(2 * t)) ^ (Fintype.card X.Ψ * r)
          = ∏ τ : X.Ψ, ∏ i : Fin r, Real.exp (-(2 * t)) := by
            rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ,
              Fintype.card_fin, ← pow_mul, Nat.mul_comm (Fintype.card X.Ψ)]
        _ ≤ _ := Finset.prod_le_prod₀ (fun τ _ => by positivity) (fun τ _ =>
            Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hfac τ i))
    refine le_trans ?_ hprod
    rw [← Real.exp_nat_mul, QuadraticCoefficientForms.card_Psi X]
    refine Real.exp_le_exp.2 ?_
    push_cast
    have e1 : (fdeg E : ℝ) * r * -(2 * t) = -(18 * ((r : ℝ) ^ 3 * δ * fdeg E)) := by rw [ht]; ring
    have e2 : 0 ≤ (r : ℝ) ^ 3 * δ * w := by positivity
    rw [e1]
    nlinarith

end GlobalTheory.ChartNearOne
end

