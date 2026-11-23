module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0065
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueMulMemBoxTriangularLayers
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov

theorem existsUnique_mul_mem_box_of_layers : ∀ (M I A B D : Type) [Monoid M] [Fintype I] [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] (ht : I → ℕ) (C : (I → A) × B × D → M) (Γ : Set M) (Λ₁ F₁ : I → Set A) (Λ₂ F₂ : Set B) (Λ₃ F₃ : Set D), Function.Injective C → C 0 = 1 → (∀ p q, ∃ w, C p * C q = C w ∧ (∀ i, (∀ l, ht l < ht i → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2)) → Γ ⊆ Set.range C → (1 : M) ∈ Γ → (∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ) → (∀ a ∈ Γ, ∃ b ∈ Γ, b * a = 1) → (∀ p, C p ∈ Γ → ∀ i, p.1 i ∈ Λ₁ i) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 ∈ Λ₂) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 = 0 → p.2.2 ∈ Λ₃) → (∀ i, ∀ a ∈ Λ₁ i, ∃ p, C p ∈ Γ ∧ p.1 = Pi.single i a) → (∀ b ∈ Λ₂, ∃ p, C p ∈ Γ ∧ p.1 = 0 ∧ p.2.1 = b) → (∀ d ∈ Λ₃, C (0, 0, d) ∈ Γ) → (∀ i a, ∃! b, b ∈ Λ₁ i ∧ b + a ∈ F₁ i) → (∀ a, ∃! b, b ∈ Λ₂ ∧ b + a ∈ F₂) → (∀ a, ∃! b, b ∈ Λ₃ ∧ b + a ∈ F₃) → ∀ q, ∃! m, m ∈ Γ ∧ m * C q ∈ C '' (Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃) := by
  intro M I A B D _ _ _ _ _ ht C Γ Λ₁ F₁ Λ₂ F₂ Λ₃ F₃ hC hC0 hmul hΓC h1 hmulΓ hinv h1Λ h2Λ h3Λ
    h1s h2s h3s hF₁ hF₂ hF₃ q
  classical

  have h0Γ : C 0 ∈ Γ := hC0 ▸ h1
  have z1 : ∀ i, (0 : A) ∈ Λ₁ i := fun i => h1Λ 0 h0Γ i
  have z2 : (0 : B) ∈ Λ₂ := h2Λ 0 h0Γ rfl
  have z3 : (0 : D) ∈ Λ₃ := h3Λ 0 h0Γ rfl rfl

  have layer1 : ∀ s : Finset I, ∀ q, ∃ m ∈ Γ, ∃ w, m * C q = C w ∧ ∀ i ∈ s, w.1 i ∈ F₁ i := by
    intro s
    induction s using Finset.induction_on_max_value ht with
    | empty => exact fun q => ⟨1, h1, q, one_mul _, by simp⟩
    | insert a s has hmax ih =>
      intro q
      obtain ⟨m, hm, w, hmw, hw⟩ := ih q
      obtain ⟨b, ⟨hbΛ, hbF⟩, -⟩ := hF₁ a (w.1 a)
      obtain ⟨p, hpΓ, hp1⟩ := h1s a b hbΛ
      obtain ⟨w', hw'eq, hw'1, -, -⟩ := hmul p w
      refine ⟨C p * m, hmulΓ _ hpΓ _ hm, w', by rw [mul_assoc, hmw, hw'eq], ?_⟩
      have key : ∀ i, ht i ≤ ht a → w'.1 i = p.1 i + w.1 i := fun i hi =>
        hw'1 i (fun l hl => by
          rw [hp1]; exact Pi.single_eq_of_ne (ne_of_apply_ne ht (by omega)) _)
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [key i le_rfl, hp1, Pi.single_eq_same]; exact hbF
      · have hia : i ≠ a := fun h => has (h ▸ hi)
        rw [key i (hmax i hi), hp1, Pi.single_eq_of_ne hia, zero_add]; exact hw i hi

  have hex : ∃ m ∈ Γ, ∃ u, m * C q = C u ∧ u ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ := by
    obtain ⟨m, hm, w, hmw, hw⟩ := layer1 Finset.univ q
    obtain ⟨b, ⟨hbΛ, hbF⟩, -⟩ := hF₂ w.2.1
    obtain ⟨p, hpΓ, hp1, hp2⟩ := h2s b hbΛ
    obtain ⟨w', hw'eq, hw'1, hw'2, -⟩ := hmul p w
    obtain ⟨d, ⟨hdΛ, hdF⟩, -⟩ := hF₃ w'.2.2
    obtain ⟨w'', hw''eq, hw''1, hw''2, hw''3⟩ := hmul (0, 0, d) w'
    refine ⟨C (0, 0, d) * (C p * m), hmulΓ _ (h3s d hdΛ) _ (hmulΓ _ hpΓ _ hm), w'',
      by rw [mul_assoc, mul_assoc, hmw, hw'eq, hw''eq], ?_⟩
    have e1 : ∀ i, w'.1 i = w.1 i := fun i => by
      rw [hw'1 i (fun l _ => by rw [hp1]; rfl), hp1]; exact zero_add _
    have e1' : ∀ i, w''.1 i = w'.1 i := fun i => by
      rw [hw''1 i (fun l _ => rfl)]; exact zero_add _
    have e2 : w''.2.1 = w'.2.1 := by rw [hw''2 rfl]; exact zero_add _
    refine Set.mk_mem_prod ?_ (Set.mk_mem_prod ?_ ?_)
    · exact Set.mem_univ_pi.2 fun i => by
        rw [e1', e1]; exact hw i (Finset.mem_univ i)
    · rw [e2, hw'2 hp1, hp2]; exact hbF
    · rw [hw''3 rfl rfl]; exact hdF

  have rigid : ∀ g ∈ Γ, ∀ u u', u ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ →
      u' ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ → g * C u = C u' → g = 1 := by
    intro g hg u u' hu hu' hgu
    obtain ⟨p, rfl⟩ := hΓC hg
    obtain ⟨w, hweq, hw1, hw2, hw3⟩ := hmul p u
    have hwu : w = u' := hC (hweq.symm.trans hgu)
    rw [hwu] at hw1 hw2 hw3
    simp only [Set.mem_prod, Set.mem_univ_pi] at hu hu'

    have key : ∀ n, ∀ i, ht i = n → p.1 i = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro i hi
        have e := hw1 i (fun l hl => ih (ht l) (hi ▸ hl) l rfl)
        exact (hF₁ i (u.1 i)).unique ⟨h1Λ p hg i, e ▸ hu'.1 i⟩ ⟨z1 i, (zero_add (u.1 i)).symm ▸ hu.1 i⟩
    have hp1 : p.1 = 0 := funext fun i => key _ i rfl
    have hp2 : p.2.1 = 0 :=
      (hF₂ u.2.1).unique ⟨h2Λ p hg hp1, hw2 hp1 ▸ hu'.2.1⟩ ⟨z2, (zero_add u.2.1).symm ▸ hu.2.1⟩
    have hp3 : p.2.2 = 0 :=
      (hF₃ u.2.2).unique ⟨h3Λ p hg hp1 hp2, hw3 hp1 hp2 ▸ hu'.2.2⟩
        ⟨z3, (zero_add u.2.2).symm ▸ hu.2.2⟩
    have hp : p = 0 := Prod.ext hp1 (Prod.ext hp2 hp3)
    rw [hp, hC0]

  obtain ⟨m, hmΓ, u, hmu, hu⟩ := hex
  refine ⟨m, ⟨hmΓ, u, hu, hmu.symm⟩, ?_⟩
  rintro m' ⟨hm'Γ, u', hu', hm'u⟩
  obtain ⟨n, hnΓ, hnm⟩ := hinv m hmΓ
  have hg : m' * n = 1 := by
    refine rigid (m' * n) (hmulΓ _ hm'Γ _ hnΓ) u u' hu hu' ?_
    rw [← hmu, hm'u, ← mul_assoc, mul_assoc m', hnm, mul_one]
  calc m' = m' * (n * m) := by rw [hnm, mul_one]
    _ = m' * n * m := (mul_assoc _ _ _).symm
    _ = m := by rw [hg, one_mul]

end GlobalTheory.DegVol.RefCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealPlaces

variable (D : D7)

theorem embS_injective : Function.Injective (embS D) := by
  intro τ τ' h
  exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem mem_cm_iff (φ : D.host.E →+* ℂ) :
    φ ∈ D.host.cmType ↔ ∃ τ, embS D τ = φ := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 φ
    have hg := ((factEmb D.R D.host).2 g).1 h
    refine ⟨D.eTau.symm ⟨g, hg⟩, ?_⟩
    unfold embS
    rw [Equiv.apply_symm_apply]
  · rintro ⟨τ, rfl⟩
    exact ((factEmb D.R D.host).2 _).2 (D.eTau τ).2

theorem range_iff (φ : D.host.E →+* ℂ) :
    (∃ τ, embS D τ = φ) ↔ ¬ ∃ τ, embS D τ = ComplexEmbedding.conjugate φ := by
  rw [← mem_cm_iff, ← mem_cm_iff]
  exact D.host.der.cmType.1 φ

theorem ne_conj (τ τ' : D.what₂.Tau) : embS D τ' ≠ ComplexEmbedding.conjugate (embS D τ) :=
  fun h => (range_iff D _).1 ⟨τ, rfl⟩ ⟨τ', h⟩

theorem sum_bijective : Function.Bijective
    (Sum.elim (embS D) (fun τ => ComplexEmbedding.conjugate (embS D τ))) := by
  constructor
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg _ (embS_injective D h)
    · exact absurd h (ne_conj D _ _)
    · exact absurd h.symm (ne_conj D _ _)
    · exact congrArg _ (embS_injective D (star_injective h))
  · intro φ
    by_cases h : ∃ τ, embS D τ = φ
    · obtain ⟨τ, hτ⟩ := h
      exact ⟨Sum.inl τ, hτ⟩
    · obtain ⟨τ, hτ⟩ := not_not.1 (fun h' => h ((range_iff D φ).2 h'))
      refine ⟨Sum.inr τ, ?_⟩
      show star (embS D τ) = φ
      rw [hτ]
      exact star_star φ

theorem existsUnique_place (w : InfinitePlace D.host.E) :
    ∃! τ, InfinitePlace.mk (embS D τ) = w := by
  have hex : ∃ τ, InfinitePlace.mk (embS D τ) = w := by
    obtain ⟨τ | τ, h⟩ := (sum_bijective D).2 w.embedding
    · exact ⟨τ, by rw [show embS D τ = w.embedding from h, InfinitePlace.mk_embedding]⟩
    · refine ⟨τ, ?_⟩
      rw [← InfinitePlace.mk_conjugate_eq,
        show ComplexEmbedding.conjugate (embS D τ) = w.embedding from h, InfinitePlace.mk_embedding]
  obtain ⟨τ, hτ⟩ := hex
  refine ⟨τ, hτ, fun τ' h' => ?_⟩
  rcases InfinitePlace.mk_eq_iff.1 (h'.trans hτ.symm) with h | h
  · exact embS_injective D h
  · exact absurd h.symm (ne_conj D _ _)

theorem prod_norm (a : D.host.E) :
    ∏ τ, ‖embS D τ a‖ ^ 2 = |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  have hb : Function.Bijective (fun τ => InfinitePlace.mk (embS D τ)) :=
    (Function.bijective_iff_existsUnique _).2 (existsUnique_place D)
  have h := InfinitePlace.prod_eq_abs_norm a
  rw [Rat.cast_abs] at h
  rw [← h, ← hb.prod_comp]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hc : (InfinitePlace.mk (embS D τ)).IsComplex := by
    rw [InfinitePlace.isComplex_mk_iff]
    exact fun hr => ne_conj D τ τ (ComplexEmbedding.isReal_iff.1 hr).symm
  rw [hc.mult_eq_two, InfinitePlace.apply]

theorem placeProd_eq (X : (D.host.E →+* ℂ) → ℝ) (h0 : ∀ φ, 0 ≤ X φ)
    (hc : ∀ φ, X (ComplexEmbedding.conjugate φ) = X φ) : placeProd X = ∏ τ, X (embS D τ) := by
  unfold placeProd
  rw [← (sum_bijective D).prod_comp, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, hc]
  exact Real.sqrt_mul_self (Finset.prod_nonneg fun τ _ => h0 _)

theorem finrank_E : finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField, Ranks.f, Ranks.n]
  ring

theorem finrank_F : finrank ℚ D.host.F = D.R.f := by
  have h := finrank_mul_finrank ℚ D.host.F D.host.E
  rw [finrank_E, D.sp.cm.deg2] at h
  omega

theorem one_le_rdE : 1 ≤ D.host.rdE := by
  unfold Host.rdE
  refine Real.one_le_rpow ?_ (by positivity)
  have := Int.one_le_abs (discr_ne_zero D.host.E)
  exact_mod_cast this

theorem absNorm_ddS :
    ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = D.host.rdE ^ (2 * D.R.f) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hpos : finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  unfold ddS Host.rdE
  rw [FractionalIdeal.coeIdeal_absNorm, h2, ← finrank_E, one_div,
    Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
  have h3 : |(discr D.host.E : ℝ)| = (discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
  rw [h3]
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

end GlobalTheory.RealPlaces

theorem GlobalTheory.real_places_facts : ∀ D : D7, Fintype.card D.what₂.Tau = D.R.f ∧ finrank ℚ D.host.E = 2 * D.R.f ∧ finrank ℚ D.host.F = D.R.f ∧ D.R.m = 2 * D.R.rS + 2 ∧ 1 ≤ D.host.rdE ∧ (∀ τ (a : D.host.E), embS D τ (star a) = starRingEnd ℂ (embS D τ a)) ∧ (∀ a : D.host.E, ∏ τ, ‖embS D τ a‖ ^ 2 = |((Algebra.norm ℚ a : ℚ) : ℝ)|) ∧ (∀ X : (D.host.E →+* ℂ) → ℝ, (∀ φ, 0 ≤ X φ) → (∀ φ, X (NumberField.ComplexEmbedding.conjugate φ) = X φ) → placeProd X = ∏ τ, X (embS D τ)) ∧ ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = D.host.rdE ^ (2 * D.R.f) ∧ (∀ w : InfinitePlace D.host.E, ∃! τ, InfinitePlace.mk (embS D τ) = w) := by
  intro D
  refine ⟨D.what₂.card_Tau, GlobalTheory.RealPlaces.finrank_E D, GlobalTheory.RealPlaces.finrank_F D, D.R.rS_two.symm,
    GlobalTheory.RealPlaces.one_le_rdE D, fun τ a => D.sp.cm.cmUnram.2.1 _ a, GlobalTheory.RealPlaces.prod_norm D,
    GlobalTheory.RealPlaces.placeProd_eq D, GlobalTheory.RealPlaces.absNorm_ddS D,
    GlobalTheory.RealPlaces.existsUnique_place D⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLayerCoordsToBlocks
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.LayerIso

variable {n m d : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
  {U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {B : Fin d → Matrix (Fin n) (Fin n) ℂ} {deg : Fin d → ℕ}

theorem block_eq_zero (hU : Biorth r m U (fun b => (U b)ᴴ)) {t : ℕ} (ht : m ≤ t) : U t = 0 := by
  obtain ⟨-, h2, h3⟩ := hU
  have : U t = (∑ b ∈ range m, U b * (U b)ᴴ) * U t := by rw [h3, Matrix.one_mul]
  rw [this, Matrix.sum_mul]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hb' : b ≠ t := by have := Finset.mem_range.1 hb; omega
  rw [Matrix.mul_assoc, h2 b t hb', Matrix.mul_zero]

theorem mem_lowers_iff (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) (c : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y ∈ lowers W c ↔ ∀ s t, t ≤ s + c → (U s)ᴴ * Y * U t = 0 := by
  obtain ⟨-, h2, h3⟩ := hU
  rw [mem_lowers]
  constructor
  · intro h s t hst
    rw [Matrix.ext_iff_mulVec]
    intro x
    have hx : U t *ᵥ x ∈ W (s + c + 1) := by
      rw [hW]
      intro b hb
      rw [Matrix.mulVec_mulVec, h2 b t (by omega), Matrix.zero_mulVec]
    have := (hW _ _).1 (h s _ hx) s le_rfl
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rw [this, Matrix.zero_mulVec]
  · intro h b y hy
    rw [hW] at hy ⊢
    intro s hs
    have : y = (∑ t ∈ range m, U t * (U t)ᴴ) *ᵥ y := by rw [h3, Matrix.one_mulVec]
    rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_sum, Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [← Matrix.mul_assoc]
    by_cases ht : t ≤ s + c
    · rw [h s t ht, Matrix.zero_mul, Matrix.zero_mulVec]
    · rw [← Matrix.mulVec_mulVec, hy t (by omega), Matrix.mulVec_zero]

theorem expand (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) (S : Set (Fin d))
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ Submodule.span ℂ (B '' S)) :
    Y = ∑ i, (Y * (B i)ᴴ).trace • B i ∧ ∀ i, i ∉ S → (Y * (B i)ᴴ).trace = 0 := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨by simp [hB], fun i hi => ?_⟩
    rw [hB, if_neg]
    rintro rfl
    exact hi hj
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [Matrix.add_mul, trace_add, add_smul, Finset.sum_add_distrib]
      rw [← hx.1, ← hy.1]
    · rw [Matrix.add_mul, trace_add, hx.2 i hi, hy.2 i hi, add_zero]
  | smul a x _ hx =>
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [Matrix.smul_mul, trace_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
      rw [← hx.1]
    · rw [Matrix.smul_mul, trace_smul, hx.2 i hi, smul_zero]

theorem trace_self {p q : Type} [Fintype p] [Fintype q] (A : Matrix p q ℂ) :
    (A * Aᴴ).trace = ((∑ s, ∑ t, ‖A s t‖ ^ 2 : ℝ) : ℂ) := by
  simp [Matrix.trace, Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem trace_blocks (hU : Biorth r m U (fun b => (U b)ᴴ)) (Y : Matrix (Fin n) (Fin n) ℂ) :
    (Y * Yᴴ).trace = ∑ s ∈ range m, ∑ t ∈ range m,
      (((U s)ᴴ * Y * U t) * ((U s)ᴴ * Y * U t)ᴴ).trace := by
  obtain ⟨-, -, h3⟩ := hU
  have : Y * Yᴴ = (∑ b ∈ range m, U b * (U b)ᴴ) * (Y * (∑ b ∈ range m, U b * (U b)ᴴ) * Yᴴ) := by
    rw [h3, Matrix.one_mul, Matrix.mul_one]
  rw [this, Matrix.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.mul_assoc (U s), Matrix.trace_mul_comm]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem placed_block (hU : Biorth r m U (fun b => (U b)ᴴ)) {s t s' t' : ℕ}
    (Z : Matrix (Fin (r s)) (Fin (r t)) ℂ) (h : s' ≠ s ∨ t ≠ t') :
    (U s')ᴴ * (U s * Z * (U t)ᴴ) * U t' = 0 := by
  obtain ⟨-, h2, -⟩ := hU
  have : (U s')ᴴ * (U s * Z * (U t)ᴴ) * U t' = ((U s')ᴴ * U s) * Z * ((U t)ᴴ * U t') := by
    simp only [Matrix.mul_assoc]
  rw [this]
  rcases h with h | h
  · rw [h2 _ _ h]; simp
  · rw [h2 _ _ h]; simp

theorem placed_block_self (hU : Biorth r m U (fun b => (U b)ᴴ)) {s t : ℕ}
    (Z : Matrix (Fin (r s)) (Fin (r t)) ℂ) :
    (U s)ᴴ * (U s * Z * (U t)ᴴ) * U t = Z := by
  obtain ⟨h1, -, -⟩ := hU
  have : (U s)ᴴ * (U s * Z * (U t)ᴴ) * U t = ((U s)ᴴ * U s) * Z * ((U t)ᴴ * U t) := by
    simp only [Matrix.mul_assoc]
  rw [this, h1, h1]; simp

noncomputable def toBlocks (m : ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ)
    (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ) (c : ℕ) :
    ({i : Fin d // deg i = c} → ℂ) →ₗ[ℂ] (∀ b : Fin m, Fin (r b) → Fin (r (b + c + 1)) → ℂ) where
  toFun z b s t := ((U b)ᴴ * (∑ i, z i • B i.1) * U (b + c + 1)) s t
  map_add' z w := by
    funext b s t
    simp [add_smul, Finset.sum_add_distrib, Matrix.mul_add, Matrix.add_mul]
  map_smul' a z := by
    funext b s t
    simp [mul_smul, ← Finset.smul_sum]

theorem of_toBlocks (c : ℕ) (z : {i : Fin d // deg i = c} → ℂ) (b : Fin m) :
    Matrix.of (toBlocks m U B deg c z b) = (U b)ᴴ * (∑ i, z i • B i.1) * U (b + c + 1) := rfl

theorem toBlocks_coords (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0)
    (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hL : ∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) (c : ℕ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y ∈ lowers W c) (b : Fin m) :
    Matrix.of (toBlocks m U B deg c (fun i => (Y * (B i.1)ᴴ).trace) b)
      = (U b)ᴴ * Y * U (b + c + 1) := by
  rw [of_toBlocks]
  rw [hL] at hY
  obtain ⟨h1, h2⟩ := expand hB _ hY
  conv_rhs => rw [h1]
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => deg i = c) (by simp)
    (fun i => (Y * (B i)ᴴ).trace • B i)]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  have hi' : deg i ≠ c := by simpa using hi
  by_cases hc : c ≤ deg i
  · have : B i ∈ lowers W (c + 1) := by
      rw [hL]
      exact Submodule.subset_span ⟨i, by show c + 1 ≤ deg i; omega, rfl⟩
    rw [Matrix.mul_smul, Matrix.smul_mul,
      (mem_lowers_iff hU hW _ _).1 this b (b + c + 1) (by omega), smul_zero]
  · rw [h2 i hc]; simp

theorem toBlocks_surjective (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0)
    (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hL : ∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) (c : ℕ) :
    Function.Surjective (toBlocks m U B deg c) := by
  intro Z
  set Y : Matrix (Fin n) (Fin n) ℂ :=
    ∑ b : Fin m, U b * Matrix.of (Z b) * (U (b + c + 1))ᴴ with hYdef
  have hY : Y ∈ lowers W c := by
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [mem_lowers_iff hU hW]
    intro s t hst
    exact placed_block hU _ (by omega)
  refine ⟨fun i => (Y * (B i.1)ᴴ).trace, funext fun b => ?_⟩
  apply Matrix.of.injective
  rw [toBlocks_coords hU hW hB hL c Y hY b, hYdef, Matrix.mul_sum, Matrix.sum_mul,
    Finset.sum_eq_single b]
  · exact placed_block_self hU _
  · intro b' _ hb
    exact placed_block hU _ (Or.inl fun h => hb (Fin.ext h.symm))
  · simp

theorem toBlocks_norm (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0)
    (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hL : ∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) (c : ℕ)
    (z : {i : Fin d // deg i = c} → ℂ) :
    ∑ b, ∑ s, ∑ t, ‖toBlocks m U B deg c z b s t‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  set Y : Matrix (Fin n) (Fin n) ℂ := ∑ i, z i • B i.1 with hYdef
  have hY : Y ∈ lowers W c := by
    rw [hL]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i.1, i.2.ge, rfl⟩)
  have h1 : (Y * Yᴴ).trace = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
    simp [hYdef, conjTranspose_sum, Matrix.mul_sum, Matrix.sum_mul, trace_sum, hB,
      Subtype.val_inj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.conj_mul']
  have horth : ∀ X ∈ lowers W (c + 1), (X * Yᴴ).trace = 0 := by
    intro X hX
    rw [hL] at hX
    have h2 := (expand hB _ hX).2
    rw [hYdef, conjTranspose_sum, Matrix.mul_sum, trace_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [conjTranspose_smul, Matrix.mul_smul, trace_smul, h2 i.1, smul_zero]
    have := i.2
    show ¬ (c + 1 ≤ deg i.1)
    omega
  have h2 : (Y * Yᴴ).trace = ∑ s ∈ range m,
      (((U s)ᴴ * Y * U (s + c + 1)) * ((U s)ᴴ * Y * U (s + c + 1))ᴴ).trace := by
    rw [trace_blocks hU]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_eq_single _ (fun t _ ht => ?_) (fun h => ?_)
    · by_cases hst : t ≤ s + c
      · rw [(mem_lowers_iff hU hW _ _).1 hY s t hst]; simp
      · have hX : U s * ((U s)ᴴ * Y * U t) * (U t)ᴴ ∈ lowers W (c + 1) := by
          rw [mem_lowers_iff hU hW]
          intro s' t' h'
          exact placed_block hU _ (by omega)
        rw [← horth _ hX, Matrix.mul_assoc (U s), Matrix.mul_assoc (U s), Matrix.trace_mul_comm (U s)]
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    · rw [block_eq_zero hU (t := s + c + 1) (by simpa using h)]; simp
  rw [h2, ← Fin.sum_univ_eq_sum_range
    (fun s => (((U s)ᴴ * Y * U (s + c + 1)) * ((U s)ᴴ * Y * U (s + c + 1))ᴴ).trace)] at h1
  simp only [trace_self] at h1
  rw [← Complex.ofReal_sum] at h1
  exact Complex.ofReal_injective h1

theorem exists_layerIso : ∀ (n m d : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ), Biorth r m U (fun b => (U b)ᴴ) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) → (∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) → (∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) → ∀ c : ℕ, ∃ Φ : ({i : Fin d // deg i = c} → ℂ) ≃ₗ[ℂ] (∀ b : Fin m, Fin (r b) → Fin (r (b + c + 1)) → ℂ), (∀ z, ∑ b, ∑ s, ∑ t, ‖Φ z b s t‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) ∧ ∀ Y ∈ lowers W c, ∀ b : Fin m, Matrix.of (Φ (fun i => (Y * (B i.1)ᴴ).trace) b) = (U b)ᴴ * Y * U (b + c + 1) := by
  intro n m d W r U B deg hU hW hB hL c
  have hinj : Function.Injective (toBlocks m U B deg c) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    have h := toBlocks_norm hU hW hB hL c z
    rw [hz] at h
    have h0 : ∑ i, ‖z i‖ ^ 2 = 0 := by rw [← h]; simp
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)] at h0
    funext i
    simpa using h0 i (Finset.mem_univ i)
  exact ⟨LinearEquiv.ofBijective _ ⟨hinj, toBlocks_surjective hU hW hB hL c⟩,
    toBlocks_norm hU hW hB hL c, toBlocks_coords hU hW hB hL c⟩

end GlobalTheory.LayerIso
end

