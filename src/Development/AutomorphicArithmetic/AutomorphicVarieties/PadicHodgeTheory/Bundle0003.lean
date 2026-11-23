module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0045
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0049

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.HeightKerSectionLeOfCotangentGenerators
section
open IsLocalRing UpperTheory.V.Alg

theorem UpperTheory.height_ker_section_le_of_cotangent_generators :
    ∀ (O S : Type) [CommRing O] [IsDomain O] [CommRing S] [Algebra O S] [IsNoetherianRing S] (x : S →ₐ[O] O) (n : ℕ) (t : Fin n → S), (∀ i, x (t i) = 0) → (∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2) → (RingHom.ker x).height ≤ (n : ℕ∞) := by
  classical
  intro O S _ _ _ _ _ x n t ht hx
  set P := RingHom.ker x with hPdef
  haveI hP : P.IsPrime := RingHom.ker_isPrime x
  set L := Localization.AtPrime P
  set T : Ideal L := Ideal.span ((Finset.univ.image (fun i => algebraMap S L (t i)) : Finset L) : Set L) with hT
  have hTm : T ≤ maximalIdeal L := by
    rw [hT, Ideal.span_le]
    intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (ht i)
  have key : Ideal.map (algebraMap S L) P ≤ T ⊔ maximalIdeal L • maximalIdeal L := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨e, o, he, hmem⟩ := hx a ha
    have hunit : IsUnit (algebraMap S L (algebraMap O S e)) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff L P]
      intro hin
      apply he
      have : x (algebraMap O S e) = 0 := hin
      simpa using this
    rw [Ideal.mem_comap]
    have h2 : algebraMap S L (e • a - ∑ i, o i • t i) ∈ maximalIdeal L • maximalIdeal L := by
      rw [smul_eq_mul, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_mul, ← pow_two]
      exact Ideal.mem_map_of_mem _ hmem
    have h3 : algebraMap S L (∑ i, o i • t i) ∈ T := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Ideal.sum_mem _ (fun i _ => ?_)
      rw [Algebra.smul_def, map_mul]
      refine Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
      simp
    have h4 : algebraMap S L (algebraMap O S e) * algebraMap S L a ∈ T ⊔ maximalIdeal L • maximalIdeal L := by
      have : algebraMap S L (algebraMap O S e) * algebraMap S L a = algebraMap S L (∑ i, o i • t i) + algebraMap S L (e • a - ∑ i, o i • t i) := by
        rw [← map_mul, ← Algebra.smul_def, ← map_add (f := _)]
        congr 1
        abel
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left h3) (Ideal.mem_sup_right h2)
    obtain ⟨u, hu⟩ := hunit
    have : algebraMap S L a = ((u⁻¹ : Lˣ) : L) * (algebraMap S L (algebraMap O S e) * algebraMap S L a) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ h4
  have hmT : maximalIdeal L ≤ T ⊔ maximalIdeal L • maximalIdeal L := by
    rwa [Localization.AtPrime.map_eq_maximalIdeal] at key
  have hmle : maximalIdeal L ≤ T :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hmT
  have heq : T = maximalIdeal L := le_antisymm hTm hmle
  have hmin : maximalIdeal L ∈ T.minimalPrimes := by
    rw [heq]
    exact ⟨⟨inferInstance, le_rfl⟩, fun q hq _ => hq.2⟩
  have hh := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have hPL : P.height = (maximalIdeal L).height := by
    rw [← IsLocalization.height_under P.primeCompl (maximalIdeal L), Localization.AtPrime.under_maximalIdeal]
  rw [hPL]
  refine hh.trans ?_
  have hc : (Finset.univ.image (fun i => algebraMap S L (t i))).card ≤ n := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun i => algebraMap S L (t i)))
  exact_mod_cast hc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LiftSymplecticSimilitudeNilpotent
section
open UpperTheory.V.GradeZeroInterpolatingElement

section SlopeTestRemainingChoices

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem adj_mul' (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem adj_adj' (X : M4 R) : adj (adj X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

private theorem adj_one' : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.one_apply]

private theorem adj_add' (X Y : M4 R) : adj (X + Y) = adj X + adj Y := by
  ext i j
  simp only [adj_apply, Matrix.add_apply, smul_add]

private theorem adj_sub' (X Y : M4 R) : adj (X - Y) = adj X - adj Y := by
  ext i j
  simp only [adj_apply, Matrix.sub_apply, smul_sub]

private theorem adj_smul' (c : R) (X : M4 R) : adj (c • X) = c • adj X := by
  ext i j
  simp only [adj_apply, Matrix.smul_apply]
  rw [smul_comm]

private theorem adj_map' (f : R →+* R') (X : M4 R) : f.mapMatrix (adj X) = adj (f.mapMatrix X) := by
  ext i j
  simp only [adj_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_zsmul]

private theorem isUnit_of_res {E B : Type} [Field E] [CommRing B] [Algebra E B] (π : B →ₐ[E] E)
    (hπ : ∀ a, π a = 0 → IsNilpotent a) (M : M4 B) (h : IsUnit ((π : B →+* E).mapMatrix M)) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det] at h ⊢
  rw [← RingHom.map_det] at h
  have h1 : IsUnit (algebraMap E B (π M.det)) := IsUnit.map (algebraMap E B) h
  have h2 : IsNilpotent (M.det - algebraMap E B (π M.det)) := hπ _ (by simp)
  have := h2.isUnit_add_left_of_commute h1 (Commute.all _ _)
  simpa using this

end SlopeTestRemainingChoices

theorem UpperTheory.lift_symplectic_similitude_nilpotent :
    ∀ {E B B' : Type} [Field E] [CharZero E] [CommRing B] [CommRing B'] [Algebra E B] [Algebra E B'] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ h' : (M4 B')ˣ, IsGSp 1 (h' : M4 B') → (h' : M4 B').map π' = 1 → ∃ h : (M4 B)ˣ, IsGSp 1 (h : M4 B) ∧ (h : M4 B).map π = 1 ∧ (h : M4 B).map p = (h' : M4 B') := by
  intro E B B' _ _ _ _ _ _ π hπ π' hπ' p hp hc h' hG hr
  generalize (h' : M4 B') = g at hG hr ⊢
  have hG' : adj g * g = 1 := by simpa [IsGSp] using hG
  have hr' : (π' : B' →+* E).mapMatrix g = 1 := hr
  have hcomp : ∀ X : M4 B, (π : B →+* E).mapMatrix X =
      (π' : B' →+* E).mapMatrix ((p : B →+* B').mapMatrix X) := by
    intro X
    ext i j
    subst hc
    rfl
  have hu0 : IsUnit ((π' : B' →+* E).mapMatrix (1 + g)) := by
    rw [map_add (f := _), map_one, hr']
    have := (IsUnit.mk0 (2 : E) two_ne_zero).map (algebraMap E (M4 E))
    rwa [map_ofNat, ← one_add_one_eq_two] at this
  obtain ⟨U, hU⟩ := isUnit_of_res π' hπ' _ hu0
  have hcm : Commute (U : M4 B') (g - 1) := by
    rw [hU]
    exact ((Commute.one_left _).add_left ((Commute.refl g).sub_right (Commute.one_right g)))
  have e1 : (U : M4 B') * ((↑U⁻¹ : M4 B') * (g - 1)) = g - 1 := Units.mul_inv_cancel_left _ _
  have e2 : ((↑U⁻¹ : M4 B') * (g - 1)) * U = g - 1 := by
    rw [mul_assoc, ← hcm.eq, Units.inv_mul_cancel_left]
  generalize (↑U⁻¹ : M4 B') * (g - 1) = Y' at e1 e2
  have hk : g * (1 - Y') = 1 + Y' := by
    have : g * (1 - Y') - (1 + Y') = -((1 + g) * Y' - (g - 1)) := by noncomm_ring
    rw [← sub_eq_zero, this, ← hU, e1, sub_self, neg_zero]
  have hY'0 : (π' : B' →+* E).mapMatrix Y' = 0 := by
    have := congrArg (π' : B' →+* E).mapMatrix e1
    rw [map_mul, map_sub, map_one, hr', sub_self, hU, hu0.mul_right_eq_zero] at this
    exact this
  have hadj : adj Y' = -Y' := by
    have hT : IsUnit (adj (U : M4 B')) :=
      ⟨⟨adj (U : M4 B'), adj (↑U⁻¹ : M4 B'), by rw [← adj_mul', Units.inv_mul, adj_one'],
        by rw [← adj_mul', Units.mul_inv, adj_one']⟩, rfl⟩
    rw [← add_eq_zero_iff_eq_neg, ← hT.mul_right_eq_zero, ← U.isUnit.mul_left_eq_zero]
    have : adj (U : M4 B') * (adj Y' + Y') * (U : M4 B') =
        adj (Y' * (U : M4 B')) * (U : M4 B') + adj (U : M4 B') * (Y' * (U : M4 B')) := by
      rw [adj_mul']; noncomm_ring
    rw [this, e2, hU, adj_sub', adj_add', adj_one']
    have e3 : (adj g - 1) * (1 + g) + (1 + adj g) * (g - 1) =
        (adj g * g - 1) + (adj g * g - 1) := by noncomm_ring
    rw [e3, hG', sub_self, add_zero]
  obtain ⟨Z, hZ⟩ : ∃ Z : M4 B, (p : B →+* B').mapMatrix Z = Y' :=
    ⟨Matrix.of fun i j => (hp (Y' i j)).choose, by
      ext i j
      exact (hp (Y' i j)).choose_spec⟩
  obtain ⟨Y, hY, hYa⟩ : ∃ Y : M4 B, (p : B →+* B').mapMatrix Y = Y' ∧ adj Y = -Y := by
    refine ⟨algebraMap E B 2⁻¹ • (Z - adj Z), ?_, ?_⟩
    · have h1 : (p : B →+* B').mapMatrix (Z - adj Z) = Y' + Y' := by
        rw [map_sub, adj_map', hZ, hadj, sub_neg_eq_add]
      ext i j
      have h2 : p ((Z - adj Z) i j) = Y' i j + Y' i j := congrFun (congrFun h1 i) j
      have h3 : algebraMap E B' 2⁻¹ * 2 = 1 := by
        rw [← map_ofNat (algebraMap E B') 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
      show p (algebraMap E B 2⁻¹ * (Z - adj Z) i j) = Y' i j
      rw [map_mul, h2, AlgHom.commutes, ← two_mul, ← mul_assoc, h3, one_mul]
    · rw [adj_smul', adj_sub', adj_adj', ← smul_neg, neg_sub]
  have hY0 : (π : B →+* E).mapMatrix Y = 0 := by rw [hcomp, hY, hY'0]
  obtain ⟨V, hV⟩ := isUnit_of_res π hπ (1 - Y) (by rw [map_sub, map_one, hY0, sub_zero]; exact isUnit_one)
  obtain ⟨V', hV'⟩ := isUnit_of_res π hπ (1 + Y) (by rw [map_add (f := _), map_one, hY0, add_zero]; exact isUnit_one)
  have e4 : ((V' * V⁻¹ : (M4 B)ˣ) : M4 B) * (1 - Y) = 1 + Y := by
    rw [← hV, ← hV', Units.val_mul, Units.inv_mul_cancel_right]
  refine ⟨V' * V⁻¹, ?_⟩
  generalize ((V' * V⁻¹ : (M4 B)ˣ) : M4 B) = h at e4 ⊢
  have hph : (p : B →+* B').mapMatrix h = g := by
    have h1 := congrArg (p : B →+* B').mapMatrix e4
    rw [map_mul, map_sub, map_add (f := _), map_one, hY, ← hk] at h1
    have h2 : IsUnit (1 - Y') := by
      have := V.isUnit.map (p : B →+* B').mapMatrix
      rwa [hV, map_sub, map_one, hY] at this
    exact h2.mul_left_inj.1 h1
  refine ⟨?_, ?_, hph⟩
  · have hT : IsUnit (1 + Y) := hV' ▸ V'.isUnit
    have hT' : IsUnit (1 - Y) := hV ▸ V.isUnit
    have a1 : adj (1 - Y) = 1 + Y := by rw [adj_sub', adj_one', hYa, sub_neg_eq_add]
    have a2 : adj (1 + Y) = 1 - Y := by rw [adj_add', adj_one', hYa, sub_eq_add_neg]
    unfold IsGSp
    rw [one_smul, ← sub_eq_zero, ← hT.mul_right_eq_zero, ← hT'.mul_left_eq_zero]
    have : (1 + Y) * (adj h * h - 1) * (1 - Y) =
        adj (h * (1 - Y)) * (h * (1 - Y)) - (1 + Y) * (1 - Y) := by
      rw [adj_mul', a1]
      simp only [mul_sub (1 + Y) (adj h * h), sub_mul _ _ (1 - Y), mul_one, mul_assoc]
    rw [this, e4, a2]
    noncomm_ring
  · show (π : B →+* E).mapMatrix h = 1
    rw [hcomp, hph, hr']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PowerSeriesApproximationModMaximal
section
open IsLocalRing UpperTheory.V.Alg

open MvPowerSeries in
private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

section Abstract

variable {O R A : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [CommRing A] [Algebra O A]

private def Appr (φ : R →ₐ[O] A) (J : Ideal A) (f : A) : Prop :=
  ∃ (a : R) (e : O), e ≠ 0 ∧ e • f - φ a ∈ J

private theorem appr_zero (φ : R →ₐ[O] A) (J : Ideal A) : Appr φ J 0 :=
  ⟨0, 1, one_ne_zero, by simp⟩

private theorem appr_add {φ : R →ₐ[O] A} {J : Ideal A} {f g : A} (hf : Appr φ J f) (hg : Appr φ J g) :
    Appr φ J (f + g) := by
  obtain ⟨a, e, he, h⟩ := hf
  obtain ⟨b, d, hd, h'⟩ := hg
  refine ⟨d • a + e • b, e * d, mul_ne_zero he hd, ?_⟩
  have : (e * d) • (f + g) - φ (d • a + e • b) =
      algebraMap O A d * (e • f - φ a) + algebraMap O A e * (d • g - φ b) := by
    rw [map_add (f := _), map_smul, map_smul]
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [this]
  exact J.add_mem (J.mul_mem_left _ h) (J.mul_mem_left _ h')

private theorem appr_mul {φ : R →ₐ[O] A} {m : Ideal A} {i j : ℕ} {f g : A} (hfm : f ∈ m ^ i) (hgm : g ∈ m ^ j)
    (hf : Appr φ (m ^ (i + 1)) f) (hg : Appr φ (m ^ (j + 1)) g) : Appr φ (m ^ (i + j + 1)) (f * g) := by
  obtain ⟨a, e, he, h⟩ := hf
  obtain ⟨b, d, hd, h'⟩ := hg
  refine ⟨a * b, e * d, mul_ne_zero he hd, ?_⟩
  have hb : φ b ∈ m ^ j := by
    have h1 : φ b = algebraMap O A d * g - (d • g - φ b) := by
      rw [Algebra.smul_def]; ring
    rw [h1]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hgm) (Ideal.pow_le_pow_right (Nat.le_succ j) h')
  have : (e * d) • (f * g) - φ (a * b) =
      algebraMap O A e * (f * (d • g - φ b)) + (e • f - φ a) * φ b := by
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [this]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) ?_
  · rw [add_assoc, pow_add]
    exact Ideal.mul_mem_mul hfm h'
  · rw [add_right_comm, pow_add]
    exact Ideal.mul_mem_mul h hb

private theorem appr_step {φ : R →ₐ[O] A} {m : Ideal A} (h0 : ∀ f, Appr φ (m ^ (0 + 1)) f)
    (h1 : ∀ f ∈ m, Appr φ (m ^ (1 + 1)) f) (N : ℕ) : ∀ f ∈ m ^ N, Appr φ (m ^ (N + 1)) f := by
  induction N with
  | zero => exact fun f _ => h0 f
  | succ N ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => appr_add ha hb)
    exact appr_mul (j := 1) ha (by rwa [pow_one]) (ih a ha) (h1 b hb)

private theorem appr_all {φ : R →ₐ[O] A} {m : Ideal A} (h : ∀ N, ∀ f ∈ m ^ N, Appr φ (m ^ (N + 1)) f)
    (N : ℕ) (f : A) : Appr φ (m ^ N) f := by
  induction N with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | succ N ih =>
    obtain ⟨a, e, he, ha⟩ := ih
    obtain ⟨b, d, hd, hb⟩ := h N _ ha
    refine ⟨d • a + b, d * e, mul_ne_zero hd he, ?_⟩
    have : (d * e) • f - φ (d • a + b) = d • (e • f - φ a) - φ b := by
      rw [map_add (f := _), map_smul]
      simp only [Algebra.smul_def, map_mul]
      ring
    rw [this]
    exact hb

end Abstract

theorem UpperTheory.power_series_approximation_mod_maximal :
    ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (t : Fin n → R) (c : O), c ≠ 0 → (∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2) → ∀ (N : ℕ) (f : MvPowerSeries (Fin n) E), ∃ (a : R) (e : O), e ≠ 0 ∧ e • f - φ a ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ N := by
  intro O E _ _ _ _ _ R _ _ n φ t c hc ht N f
  have hmem : ∀ g : MvPowerSeries (Fin n) E,
      g ∈ maximalIdeal (MvPowerSeries (Fin n) E) ↔ MvPowerSeries.constantCoeff g = 0 := fun g => by
    simp only [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
      not_not]
  have h0 : ∀ g, Appr φ (maximalIdeal (MvPowerSeries (Fin n) E) ^ (0 + 1)) g := by
    intro g
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := O) (MvPowerSeries.constantCoeff g)
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hy1 : algebraMap O E y ≠ 0 := fun h => hy0 (IsFractionRing.injective O E (by rw [h, map_zero]))
    refine ⟨algebraMap O R x, y, hy0, ?_⟩
    rw [zero_add, pow_one, hmem, AlgHom.commutes, Algebra.smul_def, map_sub, map_mul, ← hxy,
      MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, MvPowerSeries.constantCoeff_C,
      MvPowerSeries.constantCoeff_C]
    rw [mul_div_cancel₀ _ hy1, sub_self]
  have h1 : ∀ g ∈ maximalIdeal (MvPowerSeries (Fin n) E),
      Appr φ (maximalIdeal (MvPowerSeries (Fin n) E) ^ (1 + 1)) g := by
    intro g hg
    have hs := mem_span_X g ((hmem g).1 hg)
    obtain ⟨r, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
    refine Finset.sum_induction _ _ (fun a b ha hb => appr_add ha hb) (appr_zero _ _) fun i _ => ?_
    refine appr_mul (i := 0) (j := 1) (by simp) (by rw [pow_one, hmem]; simp) (h0 _) ⟨t i, c, hc, ?_⟩
    have h2 := neg_mem (ht i)
    rwa [neg_sub] at h2
  exact appr_all (appr_step h0 h1) N f
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RingKrullDimMvPowerSeriesFinField
section
open IsLocalRing UpperTheory.V.Alg

private theorem dim_ge (E : Type) [Field E] (n : ℕ) :
    ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin n) E) := by
  induction n with
  | zero => simpa using (ringKrullDim_nonneg_of_nontrivial (R := MvPowerSeries (Fin 0) E))
  | succ n ih =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPowerSeries.finSuccEquiv E n).toRingEquiv]
    refine le_trans ?_ ringKrullDim_succ_le_ringKrullDim_powerseries
    push_cast at ih ⊢
    gcongr

private theorem mem_max_iff (E : Type) [Field E] (σ : Type) (g : MvPowerSeries σ E) :
    g ∈ maximalIdeal (MvPowerSeries σ E) ↔ MvPowerSeries.constantCoeff g = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
  simp

open MvPowerSeries in
private theorem pi_span_X {O σ : Type} [CommRing O] (s : Finset σ) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → coeff n f = 0) →
      f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X s

private theorem max_eq_span (E : Type) [Field E] (σ : Type) [Finite σ] :
    maximalIdeal (MvPowerSeries σ E) ≤
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ E)) := by
  intro g hg
  rw [mem_max_iff] at hg
  cases nonempty_fintype σ
  refine pi_span_X Finset.univ g fun n hn => ?_
  have : n = 0 := by ext i; exact hn i (Finset.mem_univ i)
  subst this
  simpa using hg

theorem UpperTheory.ringKrullDim_mvPowerSeries_fin_field :
    ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (S : Type) [CommRing S] [Algebra O S] [IsNoetherianRing S] (x : S →ₐ[O] O) (n : ℕ) (φ : S →ₐ[O] MvPowerSeries (Fin n) E) (t : Fin n → S) (c : O), c ≠ 0 → (∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) → (∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2) → (n : ℕ∞) ≤ (RingHom.ker x).height := by
  intro O E _ _ _ _ _ S _ _ _ x n φ t c hc hx ht
  have hinj := IsFractionRing.injective O E
  letI : Algebra S (MvPowerSeries (Fin n) E) := φ.toRingHom.toAlgebra
  have halg : ∀ a, algebraMap S (MvPowerSeries (Fin n) E) a = φ a := fun _ => rfl
  set m := maximalIdeal (MvPowerSeries (Fin n) E) with hm
  have hker : ∀ a, a ∈ RingHom.ker x ↔ φ a ∈ m := fun a => by
    rw [hm, mem_max_iff, hx, RingHom.mem_ker, map_eq_zero_iff _ hinj]
  haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  haveI : m.LiesOver (RingHom.ker x) := ⟨by
    ext a
    rw [hker, Ideal.under_def, Ideal.mem_comap, halg]⟩
  have hX : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ∈ m := fun i => by
    rw [hm, mem_max_iff]; simp
  have hsm : ∀ g : MvPowerSeries (Fin n) E, c • g = MvPowerSeries.C (algebraMap O E c) * g := by
    intro g
    rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply]
  have hc' : algebraMap O E c ≠ 0 := (map_ne_zero_iff _ hinj).2 hc
  have htm : ∀ i, t i ∈ RingHom.ker x := fun i => by
    rw [hker]
    have h1 : φ (t i) - c • MvPowerSeries.X i ∈ m := Ideal.pow_le_self two_ne_zero (ht i)
    have h2 : c • (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ∈ m := by
      rw [hsm]; exact m.mul_mem_left _ (hX i)
    simpa using m.add_mem h1 h2
  set J := (RingHom.ker x).map (algebraMap S (MvPowerSeries (Fin n) E)) with hJ
  have hle : m ≤ J := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := m) (IsNoetherian.noetherian _) ?_ ?_
    · rw [hm, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    · refine (max_eq_span E (Fin n)).trans ?_
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : φ (t i) ∈ J ⊔ m • m := Submodule.mem_sup_left (Ideal.mem_map_of_mem _ (htm i))
      have h2 : φ (t i) - c • MvPowerSeries.X i ∈ J ⊔ m • m := by
        refine Submodule.mem_sup_right ?_
        rw [smul_eq_mul, ← pow_two]; exact ht i
      have h3 := Ideal.mul_mem_left _ (MvPowerSeries.C (algebraMap O E c)⁻¹) (Submodule.sub_mem _ h1 h2)
      rw [sub_sub_cancel, hsm, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc', map_one, one_mul] at h3
      exact h3
  have h := Ideal.height_le_height_add_of_liesOver (RingHom.ker x) m
  have h0 : m.map (Ideal.Quotient.mk J) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]; exact hle
  have hJm : J ≤ m := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    intro a ha
    exact (hker a).1 ha
  haveI : Nontrivial (MvPowerSeries (Fin n) E ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hJm)
  rw [← hJ, h0, Ideal.height_bot, add_zero] at h
  refine le_trans ?_ h
  have hd := dim_ge E n
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at hd
  exact WithBot.coe_le_coe.1 hd
end

