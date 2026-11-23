module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0231
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionMatrixGramOperatorNormLe
section
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.ConnPointwise

variable {g : ℕ}

theorem gnorm_one_eq (v : Fin g → ℂ) : gnorm 1 v = √(∑ a, ‖v a‖ ^ 2) := by
  rw [gnorm, form_eq_sum]
  congr 1
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ofReal_re]

theorem opNorm_one_le_of_entry (M : Matrix (Fin g) (Fin g) ℂ) {E : ℝ} (hE : 0 ≤ E)
    (h : ∀ j k, ‖M j k‖ ≤ E) : opNorm 1 1 M ≤ g * E := by
  refine opNorm_le_of_bound (by positivity) fun v => ?_
  rw [gnorm_one_eq, gnorm_one_eq]
  set S := ∑ a, ‖v a‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrw : (g : ℝ) * E * √S = √(((g : ℝ) * E) ^ 2 * S) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hrw]
  apply Real.sqrt_le_sqrt
  have hrow : ∀ j, ‖(M *ᵥ v) j‖ ^ 2 ≤ E ^ 2 * (g * S) := fun j => by
    have h1 : ‖(M *ᵥ v) j‖ ≤ E * ∑ k, ‖v k‖ := by
      rw [Finset.mul_sum]
      simp only [mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h j k) (norm_nonneg _)
    have h2 : (∑ k, ‖v k‖) ^ 2 ≤ g * S := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖v k‖)
      simpa [hS] using this
    calc ‖(M *ᵥ v) j‖ ^ 2 ≤ (E * ∑ k, ‖v k‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = E ^ 2 * (∑ k, ‖v k‖) ^ 2 := by ring
      _ ≤ E ^ 2 * (g * S) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  calc ∑ j, ‖(M *ᵥ v) j‖ ^ 2 ≤ ∑ _j : Fin g, E ^ 2 * (g * S) := Finset.sum_le_sum fun j _ => hrow j
    _ = ((g : ℝ) * E) ^ 2 * S := by simp; ring

theorem inv_entry_le (Y : Matrix (Fin g) (Fin g) ℝ) {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) : IsUnit Y.det ∧ ∀ j k, |Y⁻¹ j k| ≤ 1 / c := by
  have hdet : IsUnit Y.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨x, hx, hx0⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have h1 := hY x
    rw [hx0, dotProduct_zero] at h1
    have h2 : x ⬝ᵥ x ≤ 0 := by nlinarith [show 0 ≤ x ⬝ᵥ x from Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)]
    apply hx
    funext i
    have h3 : ∀ i ∈ Finset.univ, 0 ≤ x i * x i := fun i _ => mul_self_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg h3).1 (le_antisymm h2 (Finset.sum_nonneg h3)) i (Finset.mem_univ _)
    simpa using mul_self_eq_zero.1 this
  refine ⟨hdet, fun j k => ?_⟩
  set u := Y⁻¹ *ᵥ Pi.single k 1 with hu
  have hYu : Y *ᵥ u = Pi.single k 1 := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hentry : Y⁻¹ j k = u j := by
    rw [hu, mulVec_single_one]; rfl
  set N := u ⬝ᵥ u with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  have hcomp : ∀ i, u i ^ 2 ≤ N := fun i => by
    rw [hN, dotProduct, sq]
    exact Finset.single_le_sum (f := fun i => u i * u i) (fun i _ => mul_self_nonneg (u i)) (Finset.mem_univ i)
  have h1 : c * N ≤ u k := by
    have := hY u
    rwa [hYu, dotProduct_single, mul_one] at this
  have huk : 0 ≤ u k := le_trans (mul_nonneg hc.le hN0) h1
  have h2 : c ^ 2 * N ^ 2 ≤ N := by
    calc c ^ 2 * N ^ 2 = (c * N) ^ 2 := by ring
      _ ≤ u k ^ 2 := pow_le_pow_left₀ (mul_nonneg hc.le hN0) h1 2
      _ ≤ N := hcomp k
  have h3 : c ^ 2 * N ≤ 1 := by
    rcases hN0.eq_or_lt with h | h
    · rw [← h]; simp
    · nlinarith
  have h4 : (c * u j) ^ 2 ≤ 1 := by
    calc (c * u j) ^ 2 = c ^ 2 * u j ^ 2 := by ring
      _ ≤ c ^ 2 * N := mul_le_mul_of_nonneg_left (hcomp j) (sq_nonneg c)
      _ ≤ 1 := h3
  rw [hentry, le_div_iff₀ hc, mul_comm]
  have := (sq_le_one_iff_abs_le_one _).1 h4
  rwa [abs_mul, abs_of_pos hc] at this

end GlobalTheory.ConnPointwise

namespace GlobalTheory.ConnPointwise

variable {g : ℕ}

theorem entry_le_of_mulVec (P : Matrix (Fin g) (Fin g) ℝ) {W : ℝ} (hW : 0 ≤ W)
    (h : ∀ x, ‖P *ᵥ x‖ ≤ W * ‖x‖) (j k : Fin g) : |P j k| ≤ W := by
  have h1 := h (Pi.single k 1)
  have hs : ‖(Pi.single k (1 : ℝ) : Fin g → ℝ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      by_cases hi : i = k
      · subst hi; simp
      · simp [Pi.single_apply, hi]
  rw [mulVec_single_one] at h1
  calc |P j k| = ‖Pᵀ k j‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖Pᵀ k‖ := norm_le_pi_norm _ j
    _ ≤ W * ‖(Pi.single k (1 : ℝ) : Fin g → ℝ)‖ := h1
    _ ≤ W := mul_le_of_le_one_right hW hs

end GlobalTheory.ConnPointwise

namespace GlobalTheory

open GlobalTheory.ConnPointwise

theorem connMatrix_opNorm_le : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ) (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K W : ℝ), 0 < c → 0 ≤ K → 0 ≤ W → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, 0 < t i) → (∀ i x, ‖(t i • (Y⁻¹ * Bs i)) *ᵥ x‖ ≤ W * ‖x‖) → (∀ j k, ‖Dm j k‖ ≤ K) → opNorm 1 1 ((Y.map Complex.ofReal)⁻¹ * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) ≤ g * (g * K / c + W * ∑ i, ‖s i‖ / t i) := by
  intro g a Y Bs Dm s t c K W hc hK hW hY ht hB hD
  obtain ⟨hdet, hinv⟩ := inv_entry_le Y hc hY
  have hmapinv : (Y.map Complex.ofReal)⁻¹ = (Y⁻¹).map Complex.ofReal := by
    apply inv_eq_left_inv
    show (Y⁻¹).map Complex.ofRealHom * Y.map Complex.ofRealHom = 1
    rw [← Matrix.map_mul, nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBe : ∀ i j k, |(Y⁻¹ * Bs i) j k| ≤ W / t i := fun i j k => by
    have := entry_le_of_mulVec _ hW (hB i) j k
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (ht i)] at this
    rw [le_div_iff₀ (ht i), mul_comm]; exact this
  have hE0 : 0 ≤ (g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i := by
    have : 0 ≤ ∑ i, ‖s i‖ / t i := Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (ht i).le
    positivity
  refine opNorm_one_le_of_entry _ hE0 fun j k => ?_
  rw [hmapinv]
  have hexp : ((Y⁻¹).map Complex.ofReal * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) j k
      = (1 / (2 * Complex.I)) * (∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k + ∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)) := by
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, map_apply, smul_eq_mul, ofReal_sum,
      ofReal_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hexp, norm_mul]
  have hhalf : ‖(1 / (2 * Complex.I) : ℂ)‖ ≤ 1 := by simp; norm_num
  have hA : ‖∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k‖ ≤ g * K / c := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ l, ‖((Y⁻¹ j l : ℝ) : ℂ) * Dm l k‖ ≤ ∑ _l : Fin g, 1 / c * K :=
          Finset.sum_le_sum fun l _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul (hinv j l) (hD l k) (norm_nonneg _) (by positivity)
      _ = g * K / c := by simp; ring
  have hBs : ‖∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)‖ ≤ W * ∑ i, ‖s i‖ / t i := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖s i‖ * |(Y⁻¹ * Bs i) j k| ≤ ‖s i‖ * (W / t i) :=
          mul_le_mul_of_nonneg_left (hBe i j k) (norm_nonneg _)
      _ = W * (‖s i‖ / t i) := by ring
  calc ‖(1 / (2 * Complex.I) : ℂ)‖ * ‖∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k + ∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)‖
      ≤ 1 * ((g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i) :=
        mul_le_mul hhalf ((norm_add_le _ _).trans (add_le_add hA hBs)) (norm_nonneg _) zero_le_one
    _ = (g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i := one_mul _

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeUnitEtaleExtension
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coprime_unit_etale_extension : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f g : B, g ≠ 0 → ∀ (u : (Localization.Away (f * g))ˣ) (t n' d' : B), IsCoprime g n' → IsCoprime g d' → (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' → ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  first | (exact @GlobalTheory.EtC.unit_isPow_on_excisionNbhd) | (exact GlobalTheory.EtC.unit_isPow_on_excisionNbhd) | (intros; apply GlobalTheory.EtC.unit_isPow_on_excisionNbhd  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosimplicialSesExactAtSucc
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem cosimplicial_ses_exactAt_succ :
    ∀ (Z M Q : CosimplicialObject AddCommGrpCat.{1}) (i : Z ⟶ M) (p : M ⟶ Q), (∀ k, Function.Injective (i.app k)) → (∀ k (y : M.obj k), p.app k y = 0 ↔ ∃ w, i.app k w = y) → (∀ k, Function.Surjective (p.app k)) → (∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj Z).ExactAt (n + 1)) → (∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj M).ExactAt (n + 1)) → ∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj Q).ExactAt (n + 1) := by
  intro Z M Q i p hinj hex hsurj h₁ h₂
  let F := AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}
  have hw : F.map i ≫ F.map p = 0 := by
    ext k y
    exact (hex _ (i.app _ y)).2 ⟨y, rfl⟩
  let T : ShortComplex (CochainComplex AddCommGrpCat.{1} ℕ) := ShortComplex.mk (F.map i) (F.map p) hw
  have hT : T.ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun k => ?_
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.ab_exact_iff]; intro x hx; exact (hex _ x).1 hx
    · rw [AddCommGrpCat.mono_iff_injective]; exact hinj _
    · rw [AddCommGrpCat.epi_iff_surjective]; exact hsurj _
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have e := hT.homology_exact₃ (n + 1) (n + 2) rfl
  have z2 : IsZero (T.X₂.homology (n + 1)) := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₂ n)
  have z1 : IsZero (T.X₁.homology (n + 2)) := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₁ (n + 1))
  exact e.isZero_X₂ (z2.eq_of_src _ _) (z1.eq_of_tgt _ _)

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringsRefineOfCechConerveProperty
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem refines_of_coAug : ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Cov : MorphismProperty T) (Q : ∀ (U : T) (X : CosimplicialObject T), ((CosimplicialObject.const T).obj U ⟶ X) → Prop), (∀ (U V : T) (g : U ⟶ V), Cov g → Q U _ (coAug g)) → Refines Cov Q := by
  intro T _ _ Cov Q hQ U V g hg
  refine ⟨_, coAug g, WidePushout.ι (fun _ : Fin 1 => g) 0, ?_, hQ U V g hg⟩
  exact WidePushout.arrow_ι (fun _ : Fin 1 => g) 0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclicTorsorEtale
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclic_torsor_etale : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act → Algebra.Etale B D := by
  first | (exact @GlobalTheory.KeyOriginCut.etale_of_isZTorsor) | (exact GlobalTheory.KeyOriginCut.etale_of_isZTorsor) | (intros; apply GlobalTheory.KeyOriginCut.etale_of_isZTorsor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegISupMapRankOneLatticeOfGram
section
open NumberField ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory

open scoped ComplexOrder

theorem deg_iSup_map_of_gram : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (hW : HermFam K W) (hV : HermFam K V) (p : ℕ) (M : Fin p → (W →ₗ[K] V)) (ℓ : Submodule (𝓞 K) W)
  (y : Matrix (Fin p) (Fin p) K), ℓ.FG → latRank K ℓ = 1 → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (∀ (s : K →+* ℂ) a b, ∀ c ∈ ℓ, hV.form s (M b c) (M a c) = s (y a b) * hW.form s c c) →
  y.det ≠ 0 ∧ deg hV (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) =
    p * deg hW ℓ - (∑ s : K →+* ℂ, Real.log ‖s y.det‖) / (2 * Module.finrank ℚ K) := by
  intro K _ _ W V _ _ _ _ _ _ _ _ hW hV p M ℓ y hfg hrk hinj hind hgram
  have hr : Module.finrank K (Submodule.span K (ℓ : Set W)) = 1 := hrk
  haveI : FiniteDimensional K (Submodule.span K (ℓ : Set W)) :=
    Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  obtain ⟨c, hcℓ, hc0⟩ : ∃ c ∈ ℓ, c ≠ 0 := by
    by_contra hne
    push_neg at hne
    have h0 : Submodule.span K (ℓ : Set W) = ⊥ := by
      rw [Submodule.span_eq_bot]; intro x hx; exact hne x hx
    rw [h0, finrank_bot] at hr; exact zero_ne_one hr
  have hspan : (ℓ : Set W) ⊆ Submodule.span K {c} := by
    have hle : Submodule.span K {c} ≤ Submodule.span K (ℓ : Set W) :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr hcℓ)
    have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hr, finrank_span_singleton hc0])
    rw [heq]; exact Submodule.subset_span
  have hfℓ : IsFrame K ℓ ![c] := by
    refine ⟨fun i => by fin_cases i; simpa using hcℓ, ?_, ?_⟩
    · exact linearIndependent_unique_iff.mpr (by simpa using hc0)
    · intro x hx
      refine Submodule.span_mono ?_ (hspan hx)
      rintro _ rfl; exact ⟨0, rfl⟩
  set v : Fin p → V := fun a => M a c with hvdef
  have hvS : ∀ a, v a ∈ ℓ.map ((M a).restrictScalars (𝓞 K)) := fun a => ⟨c, hcℓ, rfl⟩
  have hfS : IsFrame K (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) v := by
    refine ⟨fun a => (le_iSup (fun a => ℓ.map ((M a).restrictScalars (𝓞 K))) a) (hvS a), ?_, ?_⟩
    · exact iSupIndep.linearIndependent _ hind (fun a => Submodule.subset_span (hvS a))
        (fun a h => hc0 (hinj a (h.trans (map_zero (M a)).symm)))
    · intro x hx
      have hle : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) ≤
          (Submodule.span K (Set.range v)).restrictScalars (𝓞 K) := by
        refine iSup_le fun a => ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp (hspan hz)
        rw [Submodule.restrictScalars_mem, LinearMap.restrictScalars_apply, LinearMap.map_smul]
        exact Submodule.smul_mem _ k (Submodule.subset_span ⟨a, rfl⟩)
      exact hle hx
  have hSfg : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).FG :=
    Submodule.fg_iSup _ (fun a => hfg.map _)
  have hidx : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex
      (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
      ((Submodule.span (𝓞 K) {c}).toAddSubgroup.relIndex ℓ.toAddSubgroup) ^ p := by
    have h1 : Submodule.span (𝓞 K) (Set.range v) =
        ⨆ a, (Submodule.span (𝓞 K) {c}).map ((M a).restrictScalars (𝓞 K)) := by
      rw [Submodule.span_range_eq_iSup]
      congr 1; funext a
      rw [Submodule.map_span, Set.image_singleton]; rfl
    rw [h1]
    exact _root_.GlobalTheory.SumIndex.relIndex_iSup_map_eq_pow K W V p M ℓ _ ((Submodule.span_singleton_le_iff_mem _ _).mpr hcℓ) hinj hind
  have hgr : ∀ s : K →+* ℂ, hV.gram s v = hW.form s c c • (s.mapMatrix y).transpose := by
    intro s; ext i j
    simp [HermFam.gram, v, hgram s j i c hcℓ, mul_comm]
  have hdet : ∀ s : K →+* ℂ, (hV.gram s v).det = (hW.form s c c) ^ p * s y.det := by
    intro s; rw [hgr, Matrix.det_smul, Matrix.det_transpose, RingHom.map_det, Fintype.card_fin]
  have hpos : ∀ s : K →+* ℂ, 0 < (hV.gram s v).det := fun s => (hV.posDef s p v hfS.2.1).det_pos
  have hA1 : ∀ s : K →+* ℂ, 0 < hW.form s c c := fun s => by
    have := (hW.posDef s 1 ![c] hfℓ.2.1).det_pos
    simpa [Matrix.det_fin_one] using this
  have hAeq : ∀ s : K →+* ℂ, hW.form s c c = (((hW.form s c c).re : ℝ) : ℂ) := fun s =>
    Complex.ext (by simp) (by simp [← (Complex.pos_iff.mp (hA1 s)).2])
  have hkey : ∀ s : K →+* ℂ, 0 < (s y.det).re ∧ (s y.det).im = 0 ∧
      (hV.gram s v).det.re = (hW.form s c c).re ^ p * (s y.det).re := by
    intro s
    have h1 := Complex.pos_iff.mp (hpos s)
    have hA := (Complex.pos_iff.mp (hA1 s)).1
    rw [hdet s, hAeq s, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.im_ofReal_mul] at h1
    have hApow : 0 < (hW.form s c c).re ^ p := pow_pos hA p
    refine ⟨pos_of_mul_pos_right h1.1 hApow.le, ?_, ?_⟩
    · exact (mul_eq_zero.mp h1.2.symm).resolve_left hApow.ne'
    · rw [hdet s, hAeq s, ← Complex.ofReal_pow, Complex.re_ofReal_mul]; simp
  have hlogV : ∀ s : K →+* ℂ, Real.log (hV.gram s v).det.re =
      p * Real.log (hW.form s c c).re + Real.log ‖s y.det‖ := by
    intro s
    obtain ⟨hre, him, heq⟩ := hkey s
    have hn : ‖s y.det‖ = (s y.det).re := by
      rw [← Complex.abs_re_eq_norm.mpr him, abs_of_pos hre]
    rw [heq, hn, Real.log_mul (pow_pos (Complex.pos_iff.mp (hA1 s)).1 p).ne' hre.ne', Real.log_pow]
  have hlogW : ∀ s : K →+* ℂ, Real.log (hW.gram s ![c]).det.re = Real.log (hW.form s c c).re := by
    intro s; simp [HermFam.gram, Matrix.det_fin_one]
  refine ⟨?_, ?_⟩
  · obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
    intro h; have := (hkey s).1; rw [h, map_zero] at this; simp at this
  · rw [arakelovDegree_eq_degreeOfFamily hV hSfg hfS, arakelovDegree_eq_degreeOfFamily hW hfg hfℓ]
    unfold degreeOfFamily
    have hrg : Set.range ![c] = {c} := by ext x; simp [eq_comm]
    rw [hrg, hidx, Nat.cast_pow, Real.log_pow, Finset.sum_congr rfl (fun s _ => hlogV s),
      Finset.sum_congr rfl (fun s _ => hlogW s), Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlocksTwistedConjBlockUpperTriangularStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalBlocks_twistedConj_blockUpperTriangular : ∀ (F : Type) [Field F] (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (p x : GL (Fin n) F), InPar a p → InPar a x → tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧ brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) := by
  first | (exact @GlobalTheory.Shin.BlocksTwist.blocks_twist) | (exact GlobalTheory.Shin.BlocksTwist.blocks_twist) | (intros; apply GlobalTheory.Shin.BlocksTwist.blocks_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorDescentFlatNormalDomainsStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_descent_flat_normal_domains : ∀ (A' B' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [IsIntegrallyClosed A']
    [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B'] [Algebra A' B']
    [Module.Flat A' B'] (s : A'), s ≠ 0 →
    (∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → s ∈ 𝔭 → (𝔭.map (algebraMap A' B')).IsPrime) →
    ∀ b c : B', b * c = algebraMap A' B' s →
    b ∈ ((Ideal.span {b}).comap (algebraMap A' B')).map (algebraMap A' B') := by
  first | (exact @GlobalTheory.DivDescent.divisor_descent) | (exact GlobalTheory.DivDescent.divisor_descent) | (intros; apply GlobalTheory.DivDescent.divisor_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsClosedPointsOfOriginStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin : GlobalTheory.VertUnits.DivConstOrigin → GlobalTheory.VertUnits.DivConstClosedPts := by
  first | (exact @GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin) | (exact GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin) | (intros; apply GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etFF_eq_toMorphismProperty :
    EtFF = RingHom.toMorphismProperty (fun f => RingHom.Etale f ∧ RingHom.FaithfullyFlat f) := by
  ext A B g; rfl

theorem etFF_iff_spec {A B : CommRingCat.{0}} (g : A ⟶ B) :
    EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g) := by
  have he : Etale (Spec.map g) ↔ g.hom.Etale := HasRingHomProperty.Spec_iff
  have hs : Surjective (Spec.map g) ↔ Function.Surjective (PrimeSpectrum.comap g.hom) := by
    rw [surjective_iff]; rfl
  rw [he, hs]
  change g.hom.Etale ∧ g.hom.FaithfullyFlat ↔ _
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  constructor
  · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (RingHom.Etale.iff_flat_and_formallyUnramified.1 h1).1, h2⟩

theorem etFF_isMultiplicative : EtFF.IsMultiplicative := by
  refine { id_mem := ?_, comp_mem := ?_ }
  · intro A
    change (RingHom.id A).Etale ∧ (RingHom.id A).FaithfullyFlat
    exact ⟨RingHom.Etale.of_bijective Function.bijective_id,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id⟩
  · intro A B C f g hf hg
    change (f ≫ g).hom.Etale ∧ (f ≫ g).hom.FaithfullyFlat
    rw [CommRingCat.hom_comp]
    exact ⟨RingHom.Etale.stableUnderComposition _ _ hf.1 hg.1,
      RingHom.FaithfullyFlat.stableUnderComposition _ _ hf.2 hg.2⟩

theorem etFF_isStableUnderCobaseChange : EtFF.IsStableUnderCobaseChange := by
  rw [etFF_eq_toMorphismProperty]
  exact RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
    (RingHom.Etale.isStableUnderBaseChange.and RingHom.FaithfullyFlat.isStableUnderBaseChange)

theorem etFF_respectsIso : EtFF.RespectsIso := by
  rw [etFF_eq_toMorphismProperty]
  exact RingHom.toMorphismProperty_respectsIso_iff.1
    (RingHom.Etale.respectsIso.and RingHom.FaithfullyFlat.respectsIso)

theorem finiteType_of_etFF {A B : CommRingCat.{0}} (g : A ⟶ B) (hg : EtFF g)
    (hA : Algebra.FiniteType ℤ A) : Algebra.FiniteType ℤ B := by
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale A B := RingHom.Etale.toAlgebra hg.1
  exact Algebra.FiniteType.trans hA inferInstance

theorem etFF_basic :
    (EtFF.IsMultiplicative ∧ EtFF.IsStableUnderCobaseChange ∧ EtFF.RespectsIso) ∧
    (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g)) ∧
    ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Algebra.FiniteType ℤ A → Algebra.FiniteType ℤ B :=
  ⟨⟨etFF_isMultiplicative, etFF_isStableUnderCobaseChange, etFF_respectsIso⟩,
    fun _ _ g => etFF_iff_spec g, fun _ _ g hg hA => finiteType_of_etFF g hg hA⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalNormApproxOfLocalPadicNormStatement
section
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_norm_approx_of_local_padic_norm : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E →ₐ[ℚ] E) (ℓ : ℕ) [Fact ℓ.Prime]
    (a : E) (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ), IsUnit a →
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] E) (u : ℚ_[ℓ]) *
      ((z : ℚ_[ℓ] ⊗[ℚ] E) * Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ (z : ℚ_[ℓ] ⊗[ℚ] E)) →
    ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y) := by
  first | (exact @GlobalTheory.LocalApprox.main) | (exact GlobalTheory.LocalApprox.main) | (intros; apply GlobalTheory.LocalApprox.main  <;> assumption)
end

