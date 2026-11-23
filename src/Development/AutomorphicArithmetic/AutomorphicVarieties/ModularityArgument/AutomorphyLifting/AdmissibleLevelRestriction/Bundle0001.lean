module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SplitIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SplitCM
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.PotQOf
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN.V UpperTheory.V.Z.Win

namespace UpperTheory.V.Z.Win.A4

section
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ}

private theorem place_under {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A w) :
    IsPlaceOver A (w.under (𝓞 ℚ)) := fun x => by
  rw [IsScalarTower.algebraMap_apply ℚ K Ω]
  exact h (algebraMap (𝓞 ℚ) (𝓞 K) x)

private theorem exists_over (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 ℚ) = v := by
  haveI := v.isMaximal
  have hker : RingHom.ker (algebraMap (𝓞 ℚ) (𝓞 K)) ≤ v.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 K))]
    exact bot_le
  obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) v.asIdeal hker
  refine ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, ?_⟩
  exact HeightOneSpectrum.ext hc

private def resD (A : ValuationSubring Ω) : ↥(Dec (F := K) A) →* ↥(Dec (F := ℚ) A) where
  toFun u := ⟨(AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω) u, u.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

private theorem resD_surj {A : ValuationSubring Ω}
    (h : ∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x) (s : ↥(Dec (F := ℚ) A)) :
    ∃ u : ↥(Dec (F := K) A), resD A u = s := by
  let t : G K Ω := { (s : G ℚ Ω).toRingEquiv with commutes' := h s s.2 }
  have ht : (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω) t = s := by
    ext x
    rfl
  have hm : t ∈ Dec (F := K) A := by
    have := s.2
    rw [← ht] at this
    exact this
  exact ⟨⟨t, hm⟩, Subtype.ext ht⟩

private theorem unl_res (r : G ℚ Ω →* GL (Fin n) (Qbar l))
    (hK : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Dec (F := ℚ) A, ∀ x : K,
      g (algebraMap K Ω x) = algebraMap K Ω x)
    (hU : UnlAll r) (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    Unl1 (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) w := by
  intro A hA
  have hl : A.valuation (l : Ω) < 1 := by
    simpa using (hA ((l : ℕ) : 𝓞 K)).2 hw
  have hv : ((l : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := Ideal.mem_comap.2 (by simpa using hw)
  obtain ⟨κ, ⟨g, hg⟩, hne⟩ := hU (w.under (𝓞 ℚ)) hv A (place_under hA)
  refine ⟨fun i => (κ i).comp (resD A), ⟨g, fun u => hg (resD A u)⟩, fun i j e => hne i j ?_⟩
  refine MonoidHom.ext fun s => ?_
  obtain ⟨u, rfl⟩ := resD_surj (hK A hl) s
  exact DFunLike.congr_fun e u

end

theorem potQ :
    FlagLaws → SplitIrr → PotQ := by
  intro hF hS Ω _ _ _ l _ ι n r hc hirr haut hU v hv
  obtain ⟨K, _, _, _, _, _, hrank, hK, hdec⟩ := hS Ω l n r hirr
  have hflag : Flagged r := fun u hu A hA => (hU u hu A hA).imp fun κ h => h.1
  obtain ⟨w, rfl⟩ := exists_over K v
  have hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := by simpa using Ideal.mem_comap.1 hv
  have hpot := (haut hc K hrank hK).2.1 w hw (unl_res r hdec hU w hw)
  obtain ⟨-, -, -, hlast⟩ := hF ℚ Ω l n r
  exact (((hlast K).2.2 w hw).2 hflag).1 hpot

end UpperTheory.V.Z.Win.A4
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.SplitIrr
section
open NumberField IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Br UpperTheory.V.Z.Win

namespace UpperTheory.V.Z.Win.A4.SplitIrreducibility

private theorem fix_of_dec {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {l p c : ℕ} (hc : p + 1 = 4 * l * c)
    {δ : Ω} (hδ : δ ^ 2 = -(p : Ω)) (hl : A.valuation (l : Ω) < 1) (g : Ω ≃ₐ[ℚ] Ω)
    (hg : ∀ x, g x ∈ A ↔ x ∈ A) : g δ = δ := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hg2 : g δ = δ ∨ g δ = -δ := by
    refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    rw [← map_pow, hδ, map_neg, map_natCast]
  refine hg2.resolve_right fun hneg => ?_
  have hl0 : l ≠ 0 := by rintro rfl; simp at hc
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have hcast : (p : Ω) + 1 = 4 * l * c := by exact_mod_cast hc
  obtain ⟨w, hw⟩ : ∃ w : Ω, w = (1 + δ) / 2 := ⟨_, rfl⟩
  have h2 : (2 : Ω) ≠ 0 := two_ne_zero
  have hprod : w * (1 - w) = l * c := by
    rw [hw]
    field_simp
    linear_combination (-1 : Ω) * hδ + hcast
  have hgw : g w = 1 - w := by
    rw [hw, map_div₀, map_add (f := _), map_one, hneg, map_ofNat]
    field_simp
    ring
  have hgw' : g (1 - w) = w := by rw [map_sub, map_one, hgw]; ring
  have hlc : (l : Ω) * c ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hl0) (Nat.cast_ne_zero.2 hc0)
  have hw0 : w ≠ 0 := fun h => hlc (by rw [← hprod, h, zero_mul])
  have hw1 : 1 - w ≠ 0 := fun h => hlc (by rw [← hprod, h, mul_zero])
  have small : ∀ x : Ω, x⁻¹ ∉ A → A.valuation x < 1 := fun x hx => by
    by_contra hge
    refine hx ((A.valuation_le_one_iff _).1 ?_)
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (not_lt.1 hge)
  by_cases hin : w⁻¹ ∈ A
  · have hin' : (1 - w)⁻¹ ∈ A := by
      have := (hg _).2 hin
      rwa [map_inv₀, hgw] at this
    have hli : (l : Ω)⁻¹ ∈ A := by
      have e : (l : Ω)⁻¹ = (c : Ω) * (w⁻¹ * (1 - w)⁻¹) := by
        have hl' : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl0
        have hc' : (c : Ω) ≠ 0 := Nat.cast_ne_zero.2 hc0
        rw [← mul_inv, hprod]
        field_simp
      rw [e]
      exact mul_mem (natCast_mem A c) (mul_mem hin hin')
    have h1 : (1 : _) ≤ A.valuation (l : Ω) := by
      have h3 := (A.valuation_le_one_iff _).2 hli
      rw [map_inv₀] at h3
      exact (inv_le_one₀ (zero_lt_iff.2 (by simpa using hl0))).1 h3
    exact absurd hl (not_lt.2 h1)
  · have hout : (1 - w)⁻¹ ∉ A := fun h => hin (by
      have := (hg _).2 h
      rwa [map_inv₀, hgw'] at this)
    have := Valuation.map_add_lt _ (small w hin) (small _ hout)
    simp at this

private theorem no_sq_pos {t : ℚ} {q : ℕ} (hq : q.Prime) (h : t * t = -(q : ℚ)) : False := by
  have h1 : (0 : ℚ) < q := by exact_mod_cast hq.pos
  nlinarith [mul_self_nonneg t]

private theorem no_sq_mul {t : ℚ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : t * t = (p : ℚ) * q) : False := by
  have h1 : IsSquare (((p * q : ℕ)) : ℚ) := ⟨t, by push_cast; exact h.symm⟩
  rw [Rat.isSquare_natCast_iff] at h1
  obtain ⟨m, hm⟩ := h1
  have h2 : p ∣ m := by
    have : p ∣ m * m := hm ▸ Dvd.intro _ rfl
    exact (hp.dvd_mul.1 this).elim id id
  obtain ⟨k, rfl⟩ := h2
  have h3 : q = p * (k * k) := by
    have : p * q = p * (p * (k * k)) := by rw [hm]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos this
  have h4 : p ∣ q := ⟨_, h3⟩
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 h4)

private theorem no_two {K : Type} [Field K] [Algebra ℚ K] (h2 : Module.finrank ℚ K = 2) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {x y : K} (hx : x * x = -(p : K)) (hy : y * y = -(q : K)) : False := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  haveI : FiniteDimensional ℚ K := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  have hdep : ¬ LinearIndependent ℚ ![(1 : K), x, y] := fun h => by
    have := h.fintype_card_le_finrank
    rw [h2] at this
    simp at this
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Algebra.smul_def, mul_one] at hg
  obtain ⟨a, b, c, ha, hb, hc⟩ : ∃ a b c : ℚ, a = g 0 ∧ b = g 1 ∧ c = g 2 := ⟨_, _, _, rfl, rfl, rfl⟩
  rw [← ha, ← hb, ← hc] at hg
  let φ := algebraMap ℚ K
  have inj : ∀ s t : ℚ, φ s = φ t → s = t := fun s t h => φ.injective h
  have hcast : ∀ m : ℕ, φ (m : ℚ) = (m : K) := fun m => map_natCast φ m
  have one_var : ∀ {u : K} {m : ℕ} {d e : ℚ}, m.Prime → u * u = -(m : K) → d ≠ 0 → φ e + φ d * u = 0 → False := by
    intro u m d e hm hu hd h
    have hd' : φ d ≠ 0 := fun h0 => hd (inj _ _ (by rw [h0, map_zero]))
    have e1 : u = φ (-e / d) := by
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
    refine no_sq_pos (t := -e / d) hm (inj _ _ ?_)
    rw [map_mul, ← e1, hu, map_neg, hcast]
  by_cases hb0 : b = 0
  · by_cases hc0 : c = 0
    · have ha0 : a = 0 := inj _ _ (by simpa [hb0, hc0, φ] using hg)
      fin_cases i
      · exact hi (ha ▸ ha0)
      · exact hi (hb ▸ hb0)
      · exact hi (hc ▸ hc0)
    · exact one_var hq hy hc0 (by simpa [hb0, φ] using hg)
  · by_cases hc0 : c = 0
    · exact one_var hp hx hb0 (by simpa [hc0, φ] using hg)
    · have hb' : φ b ≠ 0 := fun h0 => hb0 (inj _ _ (by rw [h0, map_zero]))
      have hc' : φ c ≠ 0 := fun h0 => hc0 (inj _ _ (by rw [h0, map_zero]))
      have h2' : (2 : K) ≠ 0 := two_ne_zero
      have hxy : x * y = φ ((a * a + b * b * p + c * c * q) / (2 * b * c)) := by
        have e2 : φ b * x + φ c * y = -φ a := by linear_combination hg
        have e3 : 2 * (φ b * φ c) * (x * y) = φ a * φ a + φ b * φ b * p + φ c * φ c * q := by
          linear_combination (φ b * x + φ c * y - φ a) * e2 - φ b * φ b * hx - φ c * φ c * hy
        rw [map_div₀]
        simp only [map_add (f := _), map_mul, hcast, map_ofNat]
        field_simp
        linear_combination e3
      refine no_sq_mul (t := (a * a + b * b * p + c * c * q) / (2 * b * c)) hp hq hpq (inj _ _ ?_)
      rw [map_mul, ← hxy, map_mul, hcast, hcast]
      linear_combination (x * x) * hy + (-(q : K)) * hx

private theorem good_inf (l : ℕ) (hl : l ≠ 0) : {p : ℕ | p.Prime ∧ 4 * l ∣ p + 1}.Infinite := by
  obtain ⟨k, hk⟩ : ∃ k, 4 * l = k + 1 := ⟨4 * l - 1, by omega⟩
  refine Set.infinite_of_forall_exists_gt fun n => ?_
  obtain ⟨q, hn, hq, hm⟩ := Nat.forall_exists_prime_gt_and_modEq n (q := k + 1) (a := k) (by omega) (by simp)
  refine ⟨q, ⟨hq, ?_⟩, hn⟩
  rw [hk]
  exact (Nat.modEq_zero_iff_dvd).1 ((hm.add_right 1).trans (by simp [Nat.ModEq]))

private theorem mem_of_range {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] (K K' : Type) [Field K] [Field K'] [NumberField K] [NumberField K'] [Algebra K Ω]
    [Algebra K' Ω] [IsScalarTower ℚ K Ω] [IsScalarTower ℚ K' Ω] (h : (res ℚ Ω K).range = (res ℚ Ω K').range) (y : K') :
    ∃ x : K, algebraMap K Ω x = algebraMap K' Ω y := by
  have hy : algebraMap K' Ω y ∈ IntermediateField.fixedField
      (IsScalarTower.toAlgHom ℚ K Ω).fieldRange.fixingSubgroup := by
    rintro ⟨s, hs⟩
    have hs' : s ∈ (res ℚ Ω K).range := by
      rw [IntermediateField.mem_fixingSubgroup_iff] at hs
      refine ⟨{ s.toRingEquiv with commutes' := fun z => hs _ ⟨z, rfl⟩ }, ?_⟩
      ext x
      rfl
    rw [h] at hs'
    obtain ⟨t, rfl⟩ := hs'
    exact t.commutes y
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hy
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx⟩

private theorem finrank_any {M : Type} [AddCommGroup M] (m₁ m₂ : Module ℚ M) :
    @Module.finrank ℚ M _ _ m₁ = @Module.finrank ℚ M _ _ m₂ := by
  rw [Subsingleton.elim m₁ m₂]

private theorem fix_gen {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (L : IntermediateField F Ω) {δ : Ω} (h : L = F⟮δ⟯)
    (g : Ω ≃ₐ[F] Ω) (hg : g δ = δ) (x : L) : g (x : Ω) = x := by
  have hext : (g : Ω →ₐ[F] Ω).comp L.val = L.val := by
    refine IntermediateField.algHom_ext_of_eq_adjoin F h ?_
    rintro y rfl
    exact hg
  exact DFunLike.congr_fun hext x

private theorem exK (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {p : ℕ} (hp : p.Prime) (δ : Ω) (hδ : δ ^ 2 = -(p : Ω)) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K) (_ : Algebra K Ω) (_ : IsScalarTower ℚ K Ω),
      Module.finrank ℚ K = 2 ∧ (∃ x : K, algebraMap K Ω x = δ) ∧
      ∀ g : Ω ≃ₐ[ℚ] Ω, g δ = δ → ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x := by
  obtain ⟨Q, hQ⟩ := GlobalTheory.ExSplitCM.exists_qcm (F := ℚ) (-(p : ℚ)) δ (by simp [hδ]) fun φ => by
    simp only [map_neg, map_natCast, neg_lt_zero]
    exact_mod_cast hp.pos
  have hmem : δ ∈ Q.K := hQ ▸ IntermediateField.mem_adjoin_simple_self ℚ δ
  have t : IsScalarTower ℚ ↥Q.K Ω := IsScalarTower.of_algebraMap_eq fun x => by simp
  refine ⟨↥Q.K, inferInstance, inferInstance, inferInstance, inferInstance, t, ?_, ⟨⟨δ, hmem⟩, rfl⟩, ?_⟩
  · exact (finrank_any _ _).trans Q.two
  · exact fun g hg x => fix_gen Q.K hQ g hg x

end UpperTheory.V.Z.Win.A4.SplitIrreducibility

open UpperTheory.V.Z.Win.A4.SplitIrreducibility in
theorem UpperTheory.V.Z.Win.A4.splitIrr :
    SplitIrr := by
  intro Ω _ _ _ l _ n r hr
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hsq : ∀ p : ℕ, ∃ δ : Ω, δ ^ 2 = -(p : Ω) := fun p => IsAlgClosed.exists_pow_nat_eq _ two_pos
  choose δ hδ using hsq
  have hS := good_inf l hl0
  let P : Fin (n ^ 2 + 1) → ℕ := fun i => (hS.natEmbedding _ (i : ℕ)).1
  have hPi : Function.Injective P := fun i j h =>
    Fin.ext (hS.natEmbedding _ |>.injective (Subtype.ext h))
  have hPp : ∀ i, (P i).Prime ∧ 4 * l ∣ P i + 1 := fun i => (hS.natEmbedding _ (i : ℕ)).2
  choose K i1 i2 i3 i4 i5 h2 hx hfix using fun i => exK Ω (hPp i).1 (δ (P i)) (hδ _)
  haveI clo : ∀ i, IsAlgClosure (K i) Ω := fun i => ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  choose χ _ _ hχ _ using fun i => UpperTheory.exists_quadratic_sign_character ℚ (K i) Ω l (h2 i)
  have hsqK : ∀ i (x : K i) j, algebraMap (K i) Ω x = δ (P j) → x * x = -(P j : K i) := fun i x j h => by
    apply (algebraMap (K i) Ω).injective
    rw [map_mul, h, ← sq, hδ, map_neg, map_natCast]
  have hχi : Function.Injective χ := fun i j hij => by
    by_contra hne
    have hrange : (res ℚ Ω (K i)).range = (res ℚ Ω (K j)).range := Subgroup.ext fun s => by
      rw [← (hχ i).1, ← (hχ j).1, hij]
    obtain ⟨x, hx'⟩ := hx i
    obtain ⟨y₀, hy₀⟩ := hx j
    obtain ⟨y, hy⟩ := mem_of_range (K i) (K j) hrange y₀
    exact no_two (h2 i) (hPp i).1 (hPp j).1 (fun h => hne (hPi h)) (hsqK i x i hx') (hsqK i y j (hy.trans hy₀))
  obtain ⟨i, hi⟩ : ∃ i, ¬ RepIso r (tw r (χ i)) := by
    by_contra hall
    have h1 := twCard _ _ n r hr (Finset.univ.image χ) fun d hd => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hd
      by_contra h
      exact hall ⟨i, h⟩
    rw [Finset.card_image_of_injective _ hχi, Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hirr := (resTwo _ _ _ n (res ℚ Ω (K i)) (χ i) (hχ i).1 (hχ i).2 r).1 hr hi
  refine ⟨K i, i1 i, i2 i, i3 i, i4 i, i5 i, h2 i, hirr, fun A hA g hg x => hfix i g ?_ x⟩
  obtain ⟨c, hc⟩ := (hPp i).2
  exact fix_of_dec A hc (hδ _) hA g ((GlobalTheory.QuadSplit.mem_decompositionSubgroup_iff' A g).1 hg)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.UnlOfOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.GalN.V
open UpperTheory.V UpperTheory.V.Z.Win
open scoped Pointwise

namespace UpperTheory.V.Z.Win.A4

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

private def conjDec (A B : ValuationSubring Ω) (γ : G F Ω) (h : γ • A = B) :
    ↥(Dec (F := F) B) →* ↥(Dec (F := F) A) where
  toFun u := ⟨γ⁻¹ * u * γ, by
    have hu := mem_Dec.1 u.2
    rw [mem_Dec, mul_smul, mul_smul, h, hu, ← h, inv_smul_smul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem conjDec_coe (A B : ValuationSubring Ω) (γ : G F Ω) (h : γ • A = B) (u : ↥(Dec (F := F) B)) :
    ((conjDec A B γ h u : ↥(Dec (F := F) A)) : G F Ω) = γ⁻¹ * u * γ := rfl

private theorem conjDec_surj (A B : ValuationSubring Ω) (γ : G F Ω) (h : γ • A = B) (s : ↥(Dec (F := F) A)) :
    ∃ u, conjDec A B γ h u = s := by
  refine ⟨⟨γ * s * γ⁻¹, ?_⟩, ?_⟩
  · rw [mem_Dec, ← h, mul_smul, mul_smul, inv_smul_smul, mem_Dec.1 s.2]
  · apply Subtype.ext
    rw [conjDec_coe]
    simp [mul_assoc]

private theorem char_conj {Γ C : Type} [Group Γ] [CommGroup C] (f : Γ →* C) (γ s : Γ) :
    f (γ⁻¹ * s * γ) = f s := by
  rw [map_mul, map_mul, map_inv, mul_comm (f γ)⁻¹ (f s), inv_mul_cancel_right]

private theorem flag_conj {r : G F Ω →* GL (Fin n) (Qbar l)} {A B : ValuationSubring Ω} {γ : G F Ω} (h : γ • A = B)
    {κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ} (hκ : IsFlagOn r (Dec (F := F) A) κ) :
    IsFlagOn r (Dec (F := F) B) fun i => (κ i).comp (conjDec A B γ h) := by
  obtain ⟨g, hg⟩ := hκ
  refine ⟨g * r γ⁻¹, fun u => ?_⟩
  have key : g * r γ⁻¹ * r ↑u * (g * r γ⁻¹)⁻¹ = g * r ↑(conjDec A B γ h u) * g⁻¹ := by
    rw [conjDec_coe, map_mul, map_mul, map_inv]
    group
  rw [key]
  exact hg (conjDec A B γ h u)

end UpperTheory.V.Z.Win.A4

open UpperTheory.V.Z.Win.A4 in
theorem UpperTheory.V.Z.Win.A4.unlOfOne :
    UnlOfOne := by
  intro F Ω _ _ _ _ _ l _ n r v A hA κ hκ hne B hB
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hA hB
  refine ⟨fun i => (κ i).comp (conjDec A B γ hγ), flag_conj hγ hκ, fun i j e => hne i j ?_⟩
  refine MonoidHom.ext fun s => ?_
  obtain ⟨u, rfl⟩ := conjDec_surj A B γ hγ s
  have e1 := DFunLike.congr_fun e u
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at e1 ⊢
  rw [e1, conjDec_coe, char_conj]
end
end

