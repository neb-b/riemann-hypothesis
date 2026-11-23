module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeLocalization
section
open NumberField Matrix IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

section SlopeTestRemainingChoices

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

theorem locAt_locAt {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L)
    (A : Submodule (𝓞 L) W) : locAt v (locAt v A) = locAt v A := by
  refine le_antisymm (fun x hx => ?_) (le_locAt v _)
  obtain ⟨s, hs, h⟩ := mem_locAt.1 hx
  obtain ⟨t, ht, h'⟩ := mem_locAt.1 h
  refine mem_locAt.2 ⟨t * s, fun hm => (v.maximalIdeal.isPrime.mem_or_mem hm).elim ht hs, ?_⟩
  rwa [mul_smul]

theorem locAt_mono {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L)
    {A B : Submodule (𝓞 L) W} (h : A ≤ B) : locAt v A ≤ locAt v B := fun x hx => by
  obtain ⟨t, ht, hx⟩ := mem_locAt.1 hx
  exact mem_locAt.2 ⟨t, ht, h hx⟩

theorem finite_not_le_one (a : L) : {w : FinitePlace L | ¬ w a ≤ 1}.Finite := by
  by_cases ha : a = 0
  · subst ha
    refine Set.finite_empty.subset fun w hw => hw ?_
    rw [map_zero]
    exact zero_le_one
  · refine (FinitePlace.hasFiniteMulSupport ha).subset fun w hw => ?_
    change w a ≠ 1
    intro h
    exact hw (h ▸ le_rfl)

theorem exists_mul_le_one {v w : FinitePlace L} (hvw : w ≠ v) (a : L) :
    ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ w ((t : L) * a) ≤ 1 := by
  have hne : w.maximalIdeal.asIdeal ≠ v.maximalIdeal.asIdeal := fun h =>
    hvw (FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h))
  have hnle : ¬ w.maximalIdeal.asIdeal ≤ v.maximalIdeal.asIdeal := fun h =>
    hne (w.maximalIdeal.isMaximal.eq_of_le v.maximalIdeal.isPrime.ne_top h)
  obtain ⟨p, hpw, hpv⟩ := SetLike.not_le_iff_exists.1 hnle
  have hp0 : (p : L) ≠ 0 := by
    intro h
    have : p = 0 := by exact_mod_cast h
    exact hpv (this ▸ Ideal.zero_mem _)
  have hlt : w (p : L) < 1 := by
    have h1 : w (p : L) ≤ 1 := place_int_le_one w p
    refine lt_of_le_of_ne h1 fun h => ?_
    have h2 := (place_le_one_iff w ((p : L)⁻¹)).1 (by rw [map_inv₀, h, inv_one])
    have h3 : w.maximalIdeal.valuation L (p : L) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hpw
    have h4 : 0 < w.maximalIdeal.valuation L (p : L) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hp0)
    rw [map_inv₀, inv_le_one₀ h4] at h2
    exact absurd h3 (not_lt.2 h2)
  by_cases ha : w a = 0
  · exact ⟨1, fun h => v.maximalIdeal.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
      simp [ha]⟩
  · have hapos : 0 < w a := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm ha)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hapos) hlt
    refine ⟨p ^ k, fun h => hpv (v.maximalIdeal.isPrime.mem_of_pow_mem _ h), ?_⟩
    push_cast
    rw [map_mul, map_pow]
    calc w (p : L) ^ k * w a ≤ (w a)⁻¹ * w a := by gcongr
      _ = 1 := inv_mul_cancel₀ ha

theorem exists_smul_mem_locAt_frame {v w : FinitePlace L} (hvw : w ≠ v)
    {T : Matrix (Fin n) (Fin n) L} (hT : T.det ≠ 0) (x : Fin n → L) :
    ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ t • x ∈ locAt w (frame T) := by
  classical
  choose s hs hs' using fun i => exists_mul_le_one hvw ((T⁻¹ *ᵥ x) i)
  refine ⟨∏ i, s i, fun h => ?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.maximalIdeal.isPrime)).1 h
    exact hs i hi
  · refine mem_locAt_frame.2 ⟨((∏ i, s i : 𝓞 L) : L) • (T⁻¹ *ᵥ x), fun i => ?_, ?_⟩
    · have e : (((∏ i, s i : 𝓞 L) : L) • (T⁻¹ *ᵥ x)) i =
          ((∏ j ∈ Finset.univ.erase i, s j : 𝓞 L) : L) * ((s i : L) * (T⁻¹ *ᵥ x) i) := by
        rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i), Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [e]
      exact place_mul_le_one w (place_int_le_one w _) (hs' i)
    · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hT),
        Matrix.one_mulVec]
      funext i
      simp [Algebra.smul_def]

theorem finite_notMem_locAt_frame {T : FinitePlace L → Matrix (Fin n) (Fin n) L}
    (hfin : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite) (x : Fin n → L) :
    {w : FinitePlace L | x ∉ locAt w (frame (T w))}.Finite := by
  refine (hfin.union (Set.finite_iUnion fun i => finite_not_le_one (x i))).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hc
  apply hw
  rw [hc.1.locAt_frame]
  exact mem_locAt_frame_one.2 hc.2

end SlopeTestRemainingChoices

theorem locAt_glued (L : Type) [Field L] [NumberField L] (n : ℕ)
    (T : FinitePlace L → Matrix (Fin n) (Fin n) L) (hdet : ∀ v, (T v).det ≠ 0)
    (hfin : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite) (v : FinitePlace L) :
    locAt v (glued T) = locAt v (frame (T v)) := by
  classical
  refine le_antisymm ?_ fun x hx => ?_
  · have h : glued T ≤ locAt v (frame (T v)) := iInf_le _ v
    exact (locAt_mono v h).trans (locAt_locAt v _).le
  · have hone : (1 : 𝓞 L) ∉ v.maximalIdeal.asIdeal := fun h =>
      v.maximalIdeal.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    have hex : ∀ w : FinitePlace L, ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧
        (w ≠ v → t • x ∈ locAt w (frame (T w))) := fun w => by
      by_cases hw : w = v
      · exact ⟨1, hone, fun h => absurd hw h⟩
      · obtain ⟨t, ht, h⟩ := exists_smul_mem_locAt_frame hw (hdet w) x
        exact ⟨t, ht, fun _ => h⟩
    choose τ hτ hτ' using hex
    let S : Finset (FinitePlace L) := (finite_notMem_locAt_frame hfin x).toFinset.erase v
    refine mem_locAt.2 ⟨∏ w ∈ S, τ w, fun h => ?_, ?_⟩
    · obtain ⟨w, -, hw⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.maximalIdeal.isPrime)).1 h
      exact hτ w hw
    · refine Submodule.mem_iInf _ |>.2 fun w => ?_
      by_cases hw : w ∈ S
      · rw [← Finset.mul_prod_erase S τ hw, mul_comm, mul_smul]
        exact Submodule.smul_mem _ _ (hτ' w (Finset.ne_of_mem_erase hw))
      · refine Submodule.smul_mem _ _ ?_
        by_cases hv : w = v
        · rw [hv]; exact hx
        · by_contra hc
          exact hw (Finset.mem_erase.2 ⟨hv, (Set.Finite.mem_toFinset _).2 hc⟩)

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flag

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

private theorem div_mem_of_mem_span_singleton {R : Subring Ω} {x y : Ω} (hy : y ≠ 0)
    (h : x ∈ Submodule.span R {y}) : x / y ∈ R := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h
  have e : r • y = (r : Ω) * y := rfl
  rw [← hr, e, mul_div_assoc, div_self hy, mul_one]
  exact r.2

private theorem zpow_mem_lemma_2 {R : Subring Ω} {x : Ω} (hx : x ∈ R) (hxi : x⁻¹ ∈ R) (n : ℤ) :
    x ^ n ∈ R := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact pow_mem hx n
  | negSucc n => rw [zpow_negSucc, ← inv_pow]; exact pow_mem hxi _

theorem tens_gen {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  have hs0 : ∀ i, s i ≠ 0 := fun i => (hs i).1
  refine ⟨Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs0 i), ?_⟩
  show Submodule.span (regAt ξ p) {t | ∃ s' : I → Ω, (∀ i, (Λ i).IsGenAt p (s' i)) ∧ t = ∏ i, s' i ^ a i} = _
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨s', hs', rfl⟩
    have hs'0 : ∀ i, s' i ≠ 0 := fun i => (hs' i).1
    have hw : ∀ i, s' i / s i ∈ regAt ξ p := fun i => by
      refine div_mem_of_mem_span_singleton (hs0 i) ?_
      rw [← (hs i).2, (hs' i).2]
      exact Submodule.mem_span_singleton_self _
    have hwi : ∀ i, (s' i / s i)⁻¹ ∈ regAt ξ p := fun i => by
      rw [inv_div]
      refine div_mem_of_mem_span_singleton (hs'0 i) ?_
      rw [← (hs' i).2, (hs i).2]
      exact Submodule.mem_span_singleton_self _
    have hc : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_mem_lemma_2 (hw i) (hwi i) (a i)
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨_, hc⟩, ?_⟩
    show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (hs0 i)]
  · apply Submodule.span_mono
    rw [Set.singleton_subset_iff]
    exact ⟨s, hs, rfl⟩

variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem step_succ {r : ℕ} (b : Fin r → E) (i : Fin r) : flagStep Ω b (i+1) = flagStep Ω b i ⊔ Submodule.span Ω {b i} := by
  unfold flagStep
  have hset : {k : Fin r | (k : ℕ) < (i : ℕ) + 1} = {k : Fin r | (k : ℕ) < i} ∪ {i} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      by_cases h' : (k : ℕ) = i
      · exact Or.inr (Fin.ext h')
      · exact Or.inl (by omega)
    · rintro (h | h)
      · omega
      · subst h
        omega
  rw [hset, Set.image_union, Set.image_singleton, Submodule.span_union]

private theorem eq_zero_of_sum_smul_mem_span_lt {r : ℕ} {b : Fin r → E} (hli : LinearIndependent Ω b) (g : Fin r → Ω)
    (n : ℕ) (hg : ∑ k, g k • b k ∈ Submodule.span Ω (b '' {k | (k : ℕ) < n})) (k : Fin r)
    (hk : n ≤ (k : ℕ)) : g k = 0 := by
  classical
  have hhi : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j ∈
      Submodule.span Ω (b '' {k | (k : ℕ) < n}ᶜ) := by
    apply Submodule.sum_mem
    intro j _
    by_cases hj : (j : ℕ) < n
    · simp [hj]
    · rw [if_neg hj]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  have hlo : ∑ j : Fin r, (if (j : ℕ) < n then g j else 0) • b j ∈
      Submodule.span Ω (b '' {k | (k : ℕ) < n}) := by
    apply Submodule.sum_mem
    intro j _
    by_cases hj : (j : ℕ) < n
    · rw [if_pos hj]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · simp [hj]
  have hsplit : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j =
      ∑ j : Fin r, g j • b j - ∑ j : Fin r, (if (j : ℕ) < n then g j else 0) • b j := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : (j : ℕ) < n <;> simp [hj]
  have hzero : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j = 0 := by
    have hmem : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j ∈
        Submodule.span Ω (b '' {k | (k : ℕ) < n}) := by
      rw [hsplit]
      exact Submodule.sub_mem _ hg hlo
    exact (Submodule.disjoint_def.mp (hli.disjoint_span_image disjoint_compl_right)) _ hmem hhi
  have := Fintype.linearIndependent_iff.mp hli _ hzero k
  simpa [show ¬ (k : ℕ) < n by omega] using this

theorem gr_gen (L : Lat ξ E) {r : ℕ} (b b₀ : Fin r → E) (p : Cpt ξ) (h : ∀ i, flagStep Ω b i = flagStep Ω b₀ i)
    (hb : L.IsFrameAt b p) (i : Fin r) : ∃ t, (L.gr b₀ i).IsGenAt p t := by
  obtain ⟨hli, hLp⟩ := hb
  have hbi : b i ∈ flagStep Ω b₀ i ⊔ Submodule.span Ω {b₀ i} := by
    rw [← step_succ, ← h]
    unfold flagStep
    exact Submodule.subset_span ⟨i, show (i : ℕ) < (i : ℕ) + 1 by omega, rfl⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hbi
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hyz
    rw [← h, hyz] at hy
    unfold flagStep at hy
    exact hli.notMem_span_image (by simp) hy
  refine ⟨c, hc, ?_⟩
  show Submodule.span (regAt ξ p) {t | ∃ e ∈ L p, e - t • b₀ i ∈ flagStep Ω b₀ i} =
    Submodule.span (regAt ξ p) {c}
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨e, he, hte⟩
    rw [hLp] at he
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp he
    have hsm : ∀ k, g k • b k = (g k : Ω) • b k := fun k => rfl
    have hsum : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k =
        c • ∑ k, g k • b k - t • b i := by
      simp only [hsm, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, mul_smul, Finset.smul_sum]
    have hx : c • (∑ k, g k • b k - t • b₀ i) - t • y ∈ flagStep Ω b₀ i :=
      Submodule.sub_mem _ (Submodule.smul_mem _ c hte) (Submodule.smul_mem _ t hy)
    have heq : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k =
        c • (∑ k, g k • b k - t • b₀ i) - t • y := by
      rw [hsum, ← hyz, smul_add, smul_sub, smul_smul, smul_smul, mul_comm t c]
      abel
    have key : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k ∈ flagStep Ω b i := by
      rw [h, heq]
      exact hx
    unfold flagStep at key
    have hci := eq_zero_of_sum_smul_mem_span_lt hli _ i key i le_rfl
    rw [if_pos rfl, sub_eq_zero] at hci
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨g i, ?_⟩
    show (g i : Ω) * c = t
    rw [mul_comm]
    exact hci
  · apply Submodule.span_mono
    rw [Set.singleton_subset_iff]
    refine ⟨b i, ?_, ?_⟩
    · rw [hLp]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [← hyz, add_sub_cancel_right]
      exact hy

theorem gr_gen_of_isFlagVBOn {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ} {b₀ : Fin r → E} (h : L.IsFlagVBOn T b₀)
    {p : Cpt ξ} (hp : p ∈ T) (i : Fin r) : ∃ t, (L.gr b₀ i).IsGenAt p t := by
  obtain ⟨U, hU, b, hflag, hframe⟩ := h p hp
  exact gr_gen L b b₀ p hflag (hframe p hp hU) i

end GlobalTheory.CompanionTheory.Ar.Flag
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrIsGenAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagGrGen

theorem exists_coord {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b : Fin r → E}
    (hb : LinearIndependent Ω b) (i : Fin r) :
    ∃ φ : E →ₗ[Ω] Ω, φ (b i) = 1 ∧ ∀ k, k ≠ i → φ (b k) = 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hb).coord i)
  have key : ∀ k, g (b k) = Finsupp.single k (1 : Ω) i := by
    intro k
    have hk : (Module.Basis.span hb k : E) = b k := by rw [Module.Basis.span_apply]
    have := LinearMap.congr_fun hg (Module.Basis.span hb k)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply, Module.Basis.repr_self] at this
    rw [hk] at this
    exact this
  refine ⟨g, ?_, ?_⟩
  · rw [key]
    simp
  · intro k hk
    rw [key]
    simp [Ne.symm hk]

theorem gr_isGenAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (b₀ b : Fin r → E) (p : Cpt ξ) (i : Fin r) (t : Ω), LinearIndependent Ω b₀ → (∀ s, flagStep Ω b s = flagStep Ω b₀ s) → L.IsFrameAt b p → b i - t • b₀ i ∈ flagStep Ω b₀ i → (L.gr b₀ i).IsGenAt p t := by
  intro X Ω _ ξ E _ _ L r b₀ b p i t hb₀ hflag hframe hti
  obtain ⟨hb, hLp⟩ := hframe
  obtain ⟨f0, hf0⟩ := exists_coord hb₀ i
  obtain ⟨g, hg⟩ := exists_coord hb i
  have hflag_i : flagStep Ω b₀ (i : ℕ) = flagStep Ω b (i : ℕ) := (hflag (i : ℕ)).symm
  have hf0ker : ∀ v ∈ flagStep Ω b₀ (i : ℕ), f0 v = 0 := by
    intro v hv
    have hle : flagStep Ω b₀ (i : ℕ) ≤ LinearMap.ker f0 := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      have hki : k ≠ i := by
        rintro rfl
        simp at hk
      exact LinearMap.mem_ker.mpr (hf0.2 k hki)
    exact LinearMap.mem_ker.mp (hle hv)
  have hgker : ∀ v ∈ flagStep Ω b (i : ℕ), g v = 0 := by
    intro v hv
    have hle : flagStep Ω b (i : ℕ) ≤ LinearMap.ker g := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      have hki : k ≠ i := by
        rintro rfl
        simp at hk
      exact LinearMap.mem_ker.mpr (hg.2 k hki)
    exact LinearMap.mem_ker.mp (hle hv)
  have hf0bi : f0 (b i) = t := by
    have := hf0ker _ hti
    rw [map_sub, map_smul, hf0.1, smul_eq_mul, _root_.mul_one, sub_eq_zero] at this
    exact this
  have ht0 : t ≠ 0 := by
    rintro rfl
    have hbi : b i ∈ flagStep Ω b (i : ℕ) := by
      rw [← hflag_i]
      simpa using hti
    have := hgker _ hbi
    rw [hg.1] at this
    exact one_ne_zero this
  have hmono : flagStep Ω b (i : ℕ) ≤ flagStep Ω b ((i : ℕ) + 1) :=
    Submodule.span_mono (Set.image_mono (fun k hk => by
      simp only [Set.mem_setOf_eq] at hk ⊢
      omega))
  have hb0i : b₀ i ∈ flagStep Ω b ((i : ℕ) + 1) := by
    rw [hflag]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  have hagree : ∀ v ∈ flagStep Ω b ((i : ℕ) + 1), f0 v = t * g v := by
    intro v hv
    have hle : flagStep Ω b ((i : ℕ) + 1) ≤ LinearMap.eqLocus f0 (t • g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      have hk' : (k : ℕ) < (i : ℕ) + 1 := hk
      rw [SetLike.mem_coe, LinearMap.mem_eqLocus, LinearMap.smul_apply, smul_eq_mul]
      rcases lt_or_eq_of_le (by omega : (k : ℕ) ≤ (i : ℕ)) with hlt | heq
      · have hki : k ≠ i := by
          rintro rfl
          exact lt_irrefl _ hlt
        rw [hg.2 k hki, mul_zero]
        apply hf0ker
        rw [hflag_i]
        exact Submodule.subset_span ⟨k, hlt, rfl⟩
      · have hki : k = i := Fin.ext heq
        rw [hki, hg.1, _root_.mul_one, hf0bi]
    have := hle hv
    rw [LinearMap.mem_eqLocus, LinearMap.smul_apply, smul_eq_mul] at this
    exact this
  have hgO : ∀ v ∈ Submodule.span (regAt ξ p) (Set.range b), g v ∈ regAt ξ p := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      by_cases hki : k = i
      · rw [hki, hg.1]
        exact one_mem _
      · rw [hg.2 k hki]
        exact zero_mem _
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul a x _ hx =>
      show g ((a : Ω) • x) ∈ regAt ξ p
      rw [map_smul, smul_eq_mul]
      exact mul_mem a.2 hx
  have hbiL : b i ∈ L p := by
    rw [hLp]
    exact Submodule.subset_span ⟨i, rfl⟩
  show t ≠ 0 ∧ Submodule.span (regAt ξ p) {s | ∃ e ∈ L p, e - s • b₀ i ∈ flagStep Ω b₀ i} = Submodule.span (regAt ξ p) {t}
  refine ⟨ht0, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro s ⟨e, he, hes⟩
    rw [hLp] at he
    have he_flag : e ∈ flagStep Ω b ((i : ℕ) + 1) := by
      have h1 : e - s • b₀ i ∈ flagStep Ω b ((i : ℕ) + 1) := hmono (by rw [← hflag_i]; exact hes)
      have h2 : s • b₀ i ∈ flagStep Ω b ((i : ℕ) + 1) := Submodule.smul_mem _ s hb0i
      simpa using add_mem h1 h2
    have hs : s = f0 e := by
      have := hf0ker _ hes
      rw [map_sub, map_smul, hf0.1, smul_eq_mul, _root_.mul_one, sub_eq_zero] at this
      exact this.symm
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨g e, hgO e he⟩, ?_⟩
    show g e * t = s
    rw [hs, hagree e he_flag, _root_.mul_comm]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨b i, hbiL, hti⟩

end GlobalTheory.CompanionTheory.Ar.FlagGrGen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtBaseChange
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.regular_at_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ.RegularAt f (F g') → Γ'.RegularAt (fun t => κ (f t)) g' := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF κ hκ f g' ⟨U, hU, s, hs⟩
  refine ⟨F ⁻¹ᵁ U, hU, (F.app U).hom s, fun t h => ?_⟩
  have e := GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange R T Γ R' Γ' F hF κ hκ t
  have h1 : ⊤ ≤ ((Γ'.pt t).left ≫ F) ⁻¹ᵁ U := h
  have h2 : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left) ⁻¹ᵁ U := e ▸ h1
  have h3 : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := fun z _ => by
    have hz : z = Spec.map (CommRingCat.ofHom κ) (IsLocalRing.closedPoint (FractionRing R')) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [hz]
    exact h2 (by trivial)
  refine (PositivityTheory.HtPt.Htat.Pull.valAt_comp _ F U h1 s).symm.trans
    ((PositivityTheory.HtPt.Htat.Pull.valAt_congr e U h1 h2 s).trans ?_)
  rw [PositivityTheory.HtPt.Htat.Pull.valAt_spec κ _ U h3, hs t h3]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReversedDualTriangular
section
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.DualPair

theorem dualRevTri : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w w' v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
    (∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) → (∀ i j, w' i ⬝ᵥ v' j = if i = j.rev then 1 else 0) →
    (∀ i j, i < j → w.repr (w' i) j = 0) →
    (∀ i j, i < j → v.repr (v' i) j = 0) ∧ ∀ i, v.repr (v' i) i * w.repr (w' i.rev) i.rev = 1 := by
  intro Ω _ r w w' v v' h1 h2 h3
  exact PositivityTheory.Xgn.dual_basis_reverse_triangular Ω r w w' v v' h1 h2 h3

end GlobalTheory.CompanionTheory.Ar.DualPair
end

