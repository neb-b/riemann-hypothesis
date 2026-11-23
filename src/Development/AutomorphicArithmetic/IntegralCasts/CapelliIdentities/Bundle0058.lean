module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SplittingFieldConstruction
section
open Polynomial

noncomputable def UpperTheory.Reformulated.B.SplittingFieldConstruction.SplitField :
    Prop :=
    ∀ (A B : Type) [inst : CommRing A] [inst_1 : IsDomain A] [inst_2 : CommRing B] [inst_3 : Algebra A B]
      [Module.Finite A B],
      ∃ (L : Type) (x : Field L) (x_1 : Algebra A L) (x_2 : Algebra (FractionRing A) L) (_ :
        IsScalarTower A (FractionRing A) L),
        FiniteDimensional (FractionRing A) L ∧
          Normal (FractionRing A) L ∧
            Finite (B →ₐ[A] ↥(integralClosure A L)) ∧
              ∀ (Ω : Type) [inst_5 : Field Ω] (φ : ↥(integralClosure A L) →+* Ω) (z : B →+* Ω),
                Function.Injective (⇑(φ.comp (Algebra.algebraMap A ↥(integralClosure A L))) : A → Ω) →
                  z.comp (Algebra.algebraMap A B) = φ.comp (Algebra.algebraMap A ↥(integralClosure A L)) →
                    ∃! σ : B →ₐ[A] ↥(integralClosure A L), φ.comp (↑σ : B →+* ↥(integralClosure A L)) = z

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.exists_monic {A B : Type} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (s : Finset B) :
    ∃ p : A[X], p.Monic ∧ ∀ b ∈ s, aeval b p = 0 := by
  have h : ∀ b : B, ∃ q : A[X], q.Monic ∧ aeval b q = 0 := fun b =>
    (Algebra.IsIntegral.isIntegral (R := A) b)
  choose q hq hq0 using h
  refine ⟨∏ b ∈ s, q b, monic_prod_of_monic _ _ fun b _ => hq b, fun b hb => ?_⟩
  rw [map_prod]
  exact Finset.prod_eq_zero hb (hq0 b)

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.finite_algHom {A B C : Type} [CommRing A] [CommRing B]
    [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] (s : Finset B)
    (hs : Submodule.span A (s : Set B) = ⊤) (p : A[X]) (hp : p.Monic)
    (h0 : ∀ b ∈ s, aeval b p = 0) : Finite (B →ₐ[A] C) := by
  let f : (B →ₐ[A] C) → (s → p.rootSet C) := fun σ b =>
    ⟨σ b, by
      rw [hp.mem_rootSet, aeval_algHom_apply, h0 b b.2, map_zero]⟩
  refine Finite.of_injective f fun σ τ h => ?_
  apply AlgHom.toLinearMap_injective
  refine LinearMap.ext_on hs fun b hb => ?_
  exact congrArg Subtype.val (congrFun h ⟨b, hb⟩)

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.factor {A B C Ω : Type} [CommRing A] [Nontrivial A] [CommRing B]
    [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] [Algebra.IsIntegral A C] [Field Ω]
    (s : Finset B) (hs : Submodule.span A (s : Set B) = ⊤) (p : A[X]) (hp : p.Monic)
    (h0 : ∀ b ∈ s, aeval b p = 0) (hsp : (p.map (algebraMap A C)).Splits)
    (φ : C →+* Ω) (z : B →+* Ω) (hinj : Function.Injective (φ.comp (algebraMap A C)))
    (hz : z.comp (algebraMap A B) = φ.comp (algebraMap A C)) :
    ∃! σ : B →ₐ[A] C, φ.comp (σ : B →+* C) = z := by
  have hφ : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    rw [Ideal.under_def, RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 hinj
  have hzA : ∀ a : A, z (algebraMap A B a) = φ (algebraMap A C a) := fun a =>
    DFunLike.congr_fun hz a
  have hgen : ∀ b ∈ s, z b ∈ φ.range := by
    intro b hb
    have h1 : eval (z b) ((p.map (algebraMap A C)).map φ) = 0 := by
      rw [Polynomial.map_map, ← hz, eval_map, ← hom_eval₂, ← aeval_def, h0 b hb, map_zero]
    rw [hsp.eq_prod_roots_of_monic (hp.map _), Polynomial.map_multiset_prod,
      eval_multiset_prod, Multiset.prod_eq_zero_iff] at h1
    simp only [Multiset.map_map, Multiset.mem_map, Function.comp_apply, Polynomial.map_sub,
      map_X, map_C, eval_sub, eval_X, eval_C] at h1
    obtain ⟨c, -, hc⟩ := h1
    exact ⟨c, (sub_eq_zero.1 hc).symm⟩
  have hall : ∀ b : B, z b ∈ φ.range := by
    intro b
    have hb : b ∈ Submodule.span A (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, hzA]
      exact mul_mem ⟨_, rfl⟩ hx
  choose g hg using hall
  let σ : B →ₐ[A] C :=
    { toFun := g
      map_one' := hφ (by rw [hg, map_one, map_one])
      map_mul' := fun x y => hφ (by rw [map_mul φ, hg, hg, hg, map_mul])
      map_zero' := hφ (by rw [hg, map_zero, map_zero])
      map_add' := fun x y => hφ (by rw [map_add φ, hg, hg, hg, map_add (f := _)])
      commutes' := fun a => hφ (by rw [hg, hzA]) }
  refine ⟨σ, RingHom.ext fun b => hg b, fun τ hτ => AlgHom.ext fun b => hφ ?_⟩
  exact (DFunLike.congr_fun hτ b).trans (hg b).symm

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.splits_closure {A L : Type} [CommRing A] [Field L]
    [Algebra A L] (p : A[X]) (hp : p.Monic) (hsp : (p.map (algebraMap A L)).Splits) :
    (p.map (algebraMap A (integralClosure A L))).Splits := by
  have hm : (p.map (algebraMap A (integralClosure A L))).map
      (algebraMap (integralClosure A L) L) = p.map (algebraMap A L) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  refine Splits.of_splits_map_of_injective (i := algebraMap (integralClosure A L) L)
    Subtype.val_injective (hm ▸ hsp) fun a ha => ?_
  rw [hm] at ha
  have h1 := isRoot_of_mem_roots ha
  rw [IsRoot.def, eval_map] at h1
  exact ⟨⟨a, p, hp, h1⟩, rfl⟩

theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.splitField_of :
    UpperTheory.Reformulated.B.SplittingFieldConstruction.SplitField := by
  intro A B _ _ _ _ _
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  obtain ⟨p, hp, h0⟩ := UpperTheory.Reformulated.B.SplittingFieldConstruction.exists_monic (A := A) s
  let q : (FractionRing A)[X] := p.map (algebraMap A (FractionRing A))
  let L : Type := q.SplittingField
  letI iK : Algebra (FractionRing A) L := inferInstance
  letI iA : Algebra A L :=
    ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))).toAlgebra
  haveI iT : @IsScalarTower A (FractionRing A) L Algebra.toSMul iK.toSMul iA.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hsp : (p.map (algebraMap A L)).Splits := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) L, ← Polynomial.map_map]
    exact SplittingField.splits q
  refine ⟨L, inferInstance, iA, iK, iT, inferInstance, inferInstance,
    UpperTheory.Reformulated.B.SplittingFieldConstruction.finite_algHom s hs p hp h0, ?_⟩
  intro Ω _ φ z hinj hz
  exact UpperTheory.Reformulated.B.SplittingFieldConstruction.factor s hs p hp h0
    (UpperTheory.Reformulated.B.SplittingFieldConstruction.splits_closure p hp hsp) φ z hinj hz
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SquareOfApproximation
section
namespace UpperTheory.Reformulated.B.SquareOfApproximation

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Filter Topology

private lemma small_power_bound {A : Type*} [Ring A] [_i : Valued A (WithZero (Multiplicative ℤ))]
    (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ) :
    ∃ N : ℕ, ∀ x : A, Valued.v x ≤ exp (-(N : ℤ)) → _i.v.restrict x < γ.1 := by
  have hg : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = exp k :=
    ⟨log _, (exp_log hg).symm⟩
  refine ⟨(-k + 1).toNat, fun x hx => ?_⟩
  apply _i.v.restrict_lt_iff_lt_embedding.mpr
  change _i.v x < MonoidWithZeroHom.ValueGroup₀.embedding γ.1
  rw [hk]
  refine lt_of_le_of_lt hx ?_
  rw [exp_lt_exp]
  have := Int.self_le_toNat (-k + 1)
  omega

private lemma square_of_approx {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (b : ℕ → R) (d : R)
    (hb : ∀ m k, m ≤ k → b k - b m ∈ v.asIdeal ^ m)
    (hd : ∀ m, b m * b m - d ∈ v.asIdeal ^ m) :
    IsSquare (algebraMap K (v.adicCompletion K) (algebraMap R K d)) := by
  set f : ℕ → v.adicCompletion K :=
    fun m => algebraMap K (v.adicCompletion K) (algebraMap R K (b m)) with hf
  set D := algebraMap K (v.adicCompletion K) (algebraMap R K d) with hD
  have hval : ∀ (r : R) (m : ℕ), r ∈ v.asIdeal ^ m →
      Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ exp (-(m : ℤ)) := by
    intro r m hr
    have h1 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) =
        v.valuation K (algebraMap R K r) := valuedAdicCompletion_eq_valuation' v _
    rw [h1, valuation_of_algebraMap]
    exact (intValuation_le_pow_iff_mem v r m).2 hr
  have hcau : CauchySeq f := by
    rw [CauchySeq, Valued.cauchy_iff]
    refine ⟨inferInstance, fun γ => ?_⟩
    obtain ⟨N, hN⟩ := small_power_bound γ
    refine ⟨f '' Set.Ici N, Filter.image_mem_map (Filter.mem_atTop N), ?_⟩
    rintro _ ⟨m, hm, rfl⟩ _ ⟨k, hk, rfl⟩
    apply hN
    have hm' : N ≤ m := hm
    have hk' : N ≤ k := hk
    have : b k - b m ∈ v.asIdeal ^ N := by
      rcases le_total m k with h | h
      · exact Ideal.pow_le_pow_right hm' (hb m k h)
      · have := Ideal.pow_le_pow_right hk' (hb k m h)
        rw [← neg_sub]; exact neg_mem this
    have h2 := hval _ _ this
    simpa [hf, map_sub] using h2
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  have h0 : Tendsto (fun m => f m * f m - D) atTop (𝓝 0) := by
    rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
    intro γ _
    obtain ⟨N, hN⟩ := small_power_bound γ
    filter_upwards [Filter.eventually_ge_atTop N] with m hm
    apply hN
    have := hval _ _ (Ideal.pow_le_pow_right hm (hd m))
    simpa [hf, hD, map_sub, map_mul] using this
  have h1 : Tendsto (fun m => f m * f m - D) atTop (𝓝 (L * L - D)) :=
    (hL.mul hL).sub_const D
  have h2 : L * L - D = 0 := tendsto_nhds_unique h1 h0
  exact ⟨L, (sub_eq_zero.1 h2).symm⟩

private lemma approx {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →+* S)
    (hσ : ∀ x, σ (σ x) = x)
    (htr : ∀ y, ∃ r : R, algebraMap R S r = y + σ y)
    (hnm : ∀ y, ∃ r : R, algebraMap R S r = y * σ y)
    (P Q : Ideal S) [hP : P.IsMaximal] [hQ : Q.IsMaximal] (hne : P ≠ Q)
    (hc : P.comap (algebraMap R S) = Q.comap (algebraMap R S)) (t : S) (n : ℕ) :
    ∃ a : R, t - algebraMap R S a ∈ P ^ n := by
  have hsurj : Function.Surjective σ := fun x => ⟨σ x, hσ x⟩
  have hP'max : (P.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
  have hne' : P ≠ P.comap σ := by
    intro h
    obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q, x ∉ P := by
      by_contra hcon
      push Not at hcon
      exact hne ((hQ.eq_of_le hP.ne_top hcon).symm)
    obtain ⟨r, hr⟩ := hnm x
    have h1 : r ∈ Q.comap (algebraMap R S) := by
      rw [Ideal.mem_comap, hr]; exact Q.mul_mem_right _ hxQ
    rw [← hc, Ideal.mem_comap, hr] at h1
    rcases hP.isPrime.mem_or_mem h1 with h2 | h2
    · exact hxP h2
    · apply hxP; rw [h]; exact h2
  have hcop : IsCoprime (P ^ n) ((P.comap σ) ^ n) :=
    IsCoprime.pow ((Ideal.isCoprime_iff_sup_eq).2 (Ideal.IsMaximal.coprime_of_ne hP hP'max hne'))
  obtain ⟨p, hp, q, hq, hpq⟩ := Ideal.isCoprime_iff_exists.1 hcop
  obtain ⟨a, ha⟩ := htr (t * q)
  refine ⟨a, ?_⟩
  have hsq : σ q ∈ P ^ n := by
    have h1 : σ q ∈ ((P.comap σ) ^ n).map σ := Ideal.mem_map_of_mem σ hq
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono (Ideal.map_comap_le) n h1
  rw [ha, map_mul]
  have h3 : t - (t * q + σ t * σ q) = t * p - σ t * σ q := by
    have : q = 1 - p := by rw [← hpq]; ring
    rw [this]; simp only [map_sub, map_one]; ring
  rw [h3]
  exact sub_mem (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hsq)

private theorem core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {θ : E} {d : 𝓞 F} (hd : (d : F) ≠ 0) (hσ : σ θ = -θ)
    (hθ : θ * θ = algebraMap F E d)
    (hsp : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {v : HeightOneSpectrum (𝓞 F)} (P Q : HeightOneSpectrum (𝓞 E)) (hne : P ≠ Q)
    (hP : P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal)
    (hQ : Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal) :
    IsSquare (algebraMap F (v.adicCompletion F) (d : F)) := by
  have hsp' : ∀ x : E, ∃ u w : F, x = algebraMap F E u + algebraMap F E w * θ := by
    intro x
    obtain ⟨u, w, h⟩ := hsp x
    exact ⟨u, w, by rw [h, Algebra.smul_def, Algebra.smul_def, mul_one]⟩
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    apply hd
    have h0 : algebraMap F E d = 0 := by rw [← hθ]; simp
    exact (map_eq_zero (algebraMap F E)).1 h0
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨u, w, rfl⟩ := hsp' x
    simp only [map_add (f := _), map_mul, AlgHom.commutes, hσ, map_neg, mul_neg, neg_neg]
  have hfix : ∀ x, σ x = x → ∃ u : F, x = algebraMap F E u := by
    intro x hx
    obtain ⟨u, w, rfl⟩ := hsp' x
    simp only [map_add (f := _), map_mul, AlgHom.commutes, hσ, mul_neg] at hx
    have h2 : (2 : E) * (algebraMap F E w * θ) = 0 := by
      have h3 := add_left_cancel hx
      linear_combination -h3
    have hw : w = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h two_ne_zero
      · rcases mul_eq_zero.1 h with h | h
        · exact (map_eq_zero (algebraMap F E)).1 h
        · exact absurd h hθ0
    exact ⟨u, by simp [hw]⟩
  let s : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)
  have hs : ∀ y : 𝓞 E, ((s y : 𝓞 E) : E) = σ y := fun _ => rfl
  have hss : ∀ y, s (s y) = y := by
    intro y
    apply RingOfIntegers.ext
    rw [hs, hs, hσσ]
  have hfixO : ∀ y : 𝓞 E, s y = y → ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y := by
    intro y hy
    obtain ⟨u, hu⟩ := hfix (y : E) (by rw [← hs, hy])
    have hint : IsIntegral ℤ u := by
      have h1 : IsIntegral ℤ (algebraMap F E u) := hu ▸ RingOfIntegers.isIntegral_coe y
      exact (isIntegral_algebraMap_iff ).1 h1
    refine ⟨⟨u, hint⟩, ?_⟩
    apply RingOfIntegers.ext
    exact hu.symm
  have htr : ∀ y, ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y + s y := fun y =>
    hfixO _ (by rw [map_add (f := _), hss, add_comm])
  have hnm : ∀ y, ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y * s y := fun y =>
    hfixO _ (by rw [map_mul, hss, mul_comm])
  have hint : IsIntegral ℤ θ := by
    have h1 : IsIntegral ℤ (θ ^ 2) := by
      rw [pow_two, hθ]
      exact (RingOfIntegers.isIntegral_coe d).algebraMap
    exact h1.of_pow (by norm_num)
  let t : 𝓞 E := ⟨θ, hint⟩
  have ht : t * t = algebraMap (𝓞 F) (𝓞 E) d := by
    apply RingOfIntegers.ext
    exact hθ
  have := P.isMaximal
  have := Q.isMaximal
  have hne' : P.asIdeal ≠ Q.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  choose a ha using
    approx (R := 𝓞 F) s hss htr hnm P.asIdeal Q.asIdeal hne' (hP.trans hQ.symm) t
  have : P.asIdeal.LiesOver v.asIdeal := ⟨hP.symm⟩
  have he : v.asIdeal.ramificationIdx' P.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P.asIdeal v.ne_bot
  set e := v.asIdeal.ramificationIdx' P.asIdeal with he'
  have hdown : ∀ (x : 𝓞 F) (m : ℕ), algebraMap (𝓞 F) (𝓞 E) x ∈ P.asIdeal ^ (e * m) →
      x ∈ v.asIdeal ^ m := by
    intro x m hx
    rw [← intValuation_le_pow_iff_mem] at hx ⊢
    rw [← intValuation_liesOver v P x] at hx
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal P.asIdeal v.ne_bot, ← he'] at hx
    have h1 : exp (-((e * m : ℕ) : ℤ)) = (exp (-(m : ℤ))) ^ e := by
      rw [← exp_nsmul]
      congr 1
      simp
    rw [h1] at hx
    exact (pow_le_pow_iff_left₀ zero_le zero_le he).1 hx
  have hb : ∀ m k, m ≤ k → a (e * k) - a (e * m) ∈ v.asIdeal ^ m := by
    intro m k hmk
    apply hdown
    have h1 := ha (e * m)
    have h2 := Ideal.pow_le_pow_right (Nat.mul_le_mul_left e hmk) (ha (e * k))
    have h3 := sub_mem h1 h2
    have h4 : t - algebraMap (𝓞 F) (𝓞 E) (a (e * m)) - (t - algebraMap (𝓞 F) (𝓞 E) (a (e * k))) =
        algebraMap (𝓞 F) (𝓞 E) (a (e * k) - a (e * m)) := by
      rw [map_sub]; ring
    rwa [h4] at h3
  have hdd : ∀ m, a (e * m) * a (e * m) - d ∈ v.asIdeal ^ m := by
    intro m
    apply hdown
    have h1 := Ideal.mul_mem_left _ (-(t + algebraMap (𝓞 F) (𝓞 E) (a (e * m)))) (ha (e * m))
    have h2 : -(t + algebraMap (𝓞 F) (𝓞 E) (a (e * m))) * (t - algebraMap (𝓞 F) (𝓞 E) (a (e * m))) =
        algebraMap (𝓞 F) (𝓞 E) (a (e * m) * a (e * m) - d) := by
      rw [map_sub, map_mul, ← ht]; ring
    rwa [h2] at h1
  exact square_of_approx v (fun m => a (e * m)) d hb hdd

noncomputable def IsCMExt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  IsTotallyReal F ∧ IsTotallyComplex E ∧ Module.finrank F E = 2 ∧
    ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)

theorem aux2 {F E : Type} [Field F] [Field E] :
    RingHomClass (𝓞 F →+* 𝓞 E) (𝓞 F) (𝓞 E) :=
  inferInstance

noncomputable def IsSplit {F E : Type} [Field F] [Field E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ P Q : HeightOneSpectrum (𝓞 E),
    P ≠ Q ∧
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal ∧
      Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal

@[reducible] noncomputable def Fv (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : Type :=
  v.adicCompletion F

theorem main {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (_ : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd : (d : F) ≠ 0) (hσ : σ θ = -θ)
    (hθ : θ * θ = algebraMap F E d) (hsp : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsSplit (E := E) v) :
    IsSquare (algebraMap F (Fv F v) d) := by
  obtain ⟨P, Q, hne, hP, hQ⟩ := hv
  exact core σ hd hσ hθ hsp P Q hne hP hQ

end UpperTheory.Reformulated.B.SquareOfApproximation
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StabilizerIsOpen
section
theorem UpperTheory.Reformulated.B.StabilizerIsOpen.stab_open.{u_1, u_2} :
    ∀ {G : Type u_1} {V : Type u_2} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
    [inst_3 : AddCommGroup V] [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
    {k : G | ((ρ : G → V →ₗ[ℂ] V) k : V → V) v = v} ∈ nhds (1 : G) →
      IsOpen {k : G | ((ρ : G → V →ₗ[ℂ] V) k : V → V) v = v} := by
  intro G V _ _ _ _ _ ρ v h
  let H : Subgroup G :=
    { carrier := {k : G | ρ k v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ρ a⁻¹ (ρ a v) = v := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at h1 }
  exact H.isOpen_of_mem_nhds h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StabilizerOf
section
noncomputable def UpperTheory.Reformulated.B.StabilizerOf.stabilizerOf.{u_1, u_2} :
    {G : Type u_1} →
      [inst : Group G] →
        {V : Type u_2} → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → V → Subgroup G :=
  fun {G} _ {_V} _ _ ρ v =>
    { carrier := {g : G | ρ g v = v}
      one_mem' := by
        show ρ 1 v = v
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        show ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a v = v := ha
        show ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = ρ (a⁻¹ * a) v := by rw [map_mul, Module.End.mul_apply]
          _ = v := by rw [inv_mul_cancel, map_one]; rfl }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StabilizerSubgroup
section
noncomputable def UpperTheory.Reformulated.B.StabilizerSubgroup.stabG :
    {G V : Type} →
      [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → V → Subgroup G :=
  fun {G _V} _ _ _ ρ v =>
    { carrier := {g : G | ρ g v = v}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        show ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := by
        show ρ 1 v = v
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {a} ha => by
        have ha' : ρ a v = v := ha
        show ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = v := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply] }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StarEqOfSq
section
theorem UpperTheory.Reformulated.B.Ra8.star_eq_of_sq :
    ∀ {z : ℂ} {r : ℝ},
    (0 : ℝ) ≤ r → z * z = (↑r : ℂ) → Star.star z = z := by
  intro z r hr h
  have hre : z.re * z.re - z.im * z.im = r := by
    simpa using congrArg Complex.re h
  have him : z.re * z.im + z.im * z.re = 0 := by
    simpa using congrArg Complex.im h
  have h0 : z.im = 0 := by
    by_contra hne
    have h1 : z.re * z.im = 0 := by linarith [mul_comm z.re z.im]
    have h2 : z.re = 0 := (mul_eq_zero.mp h1).resolve_right hne
    have h3 : 0 < z.im * z.im := mul_self_pos.mpr hne
    rw [h2] at hre
    linarith
  exact Complex.conj_eq_iff_im.mpr h0
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumCompSurj
section
theorem UpperTheory.Reformulated.B.Rd1.sum_comp_surj :
    ∀ {A B : Type} [inst : AddCommGroup A] [inst_1 : AddCommGroup B]
    [inst_2 : Fintype A] [inst_3 : Fintype B] (π : A →+ B),
    Function.Surjective (⇑π : A → B) →
      ∀ (G : B → ℂ), (↑(Fintype.card B) : ℂ) * ∑ a : A, G ((π : A → B) a) = (↑(Fintype.card A) : ℂ) * ∑ b : B, G b := by
  intro A B _ _ _ _ π hπ G
  classical
  have hfib : ∀ b : B, (Finset.univ.filter (fun a : A => π a = b)).card
      = (Finset.univ.filter (fun a : A => π a = 0)).card := fun b =>
    AddMonoidHom.card_fiber_eq_of_mem_range π (hπ b) (hπ 0)
  set k : ℕ := (Finset.univ.filter (fun a : A => π a = 0)).card with hk
  have key : ∀ H : B → ℂ, ∑ a : A, H (π a) = (k : ℂ) * ∑ b : B, H b := by
    intro H
    rw [← Finset.sum_fiberwise' Finset.univ (fun a : A => π a) H, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_const, hfib b, nsmul_eq_mul]
  have h1 : (Fintype.card A : ℂ) = (k : ℂ) * (Fintype.card B : ℂ) := by
    simpa using key (fun _ => 1)
  rw [key G, h1]
  ring
end

