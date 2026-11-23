module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationIdxDvdOfGaloisDegreeDvdUnitDvr
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.RamGalDVR

theorem isSeparable_of_natCast_finrank_ne_zero' {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : (Module.finrank F E : F) ≠ 0) : Algebra.IsSeparable F E := by
  refine ⟨fun x => ?_⟩
  have hint : IsIntegral F x := IsIntegral.of_finite F x
  have hdvd := minpoly.degree_dvd hint
  show (minpoly F x).Separable
  rw [Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hint)]
  intro hd
  set n := (minpoly F x).natDegree with hn
  have hpos : 0 < n := minpoly.natDegree_pos hint
  have hc := congrArg (fun p : Polynomial F => p.coeff (n - 1)) hd
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hc
  rw [Nat.sub_add_cancel hpos] at hc
  have hlead : (minpoly F x).coeff n = 1 := minpoly.monic hint
  rw [hlead, one_mul] at hc
  have hn0 : (n : F) = 0 := by
    have : ((n - 1 : ℕ) : F) + 1 = ((n - 1 + 1 : ℕ) : F) := by push_cast; ring
    rw [this, Nat.sub_add_cancel hpos] at hc
    exact hc
  obtain ⟨c, hc'⟩ := hdvd
  exact h (by rw [hc', Nat.cast_mul, hn0, zero_mul])

theorem isSeparable_of_isField {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]
    [Module.Finite F E] (hF : IsField F) (hE : IsField E)
    (h : (Module.finrank F E : F) ≠ 0) : Algebra.IsSeparable F E := by
  letI := hF.toField
  letI := hE.toField
  exact @isSeparable_of_natCast_finrank_ne_zero' F E _ _ ‹Algebra F E› ‹Module.Finite F E› h

theorem ramGal : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field K] [Algebra S K]
    [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [IsGalois K L] (q : ℕ), 0 < q → IsUnit (q : S) →
    Module.finrank K L ∣ q →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) ∧
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ q _ hq hdeg
  set B := integralClosure S L
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have : Module.Finite S B := IsIntegralClosure.finite S K L B
  have : IsGaloisGroup (L ≃ₐ[K] L) S B := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have hinj : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
  have : FaithfulSMul S B :=
    (faithfulSMul_iff_algebraMap_injective S _).2 (fun a b h => hinj (congrArg Subtype.val h))
  have : Module.Flat S B :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (maximalIdeal S) B (L ≃ₐ[K] L)
  rw [IsGalois.card_aut_eq_finrank] at hfund
  have hef : Ideal.ramificationIdxIn (maximalIdeal S) B * Ideal.inertiaDegIn (maximalIdeal S) B ∣ q :=
    (Dvd.intro_left _ hfund).trans hdeg
  have hlies : ∀ P : Ideal B, P.IsMaximal → P.LiesOver (maximalIdeal S) := by
    intro P hP
    refine ⟨?_⟩
    have : (P.under S).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
    exact (IsLocalRing.eq_maximalIdeal this).symm
  refine ⟨fun P hP => ?_, fun P hP _ => ?_⟩
  · have := hlies P hP
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal S) P (L ≃ₐ[K] L)]
    exact (Dvd.intro _ rfl).trans hef
  · have := hP
    have : (maximalIdeal S).IsMaximal := IsLocalRing.maximalIdeal.isMaximal S
    have hf : Module.finrank (S ⧸ maximalIdeal S) (B ⧸ P) ∣ q := by
      rw [← Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal S) P,
        ← Ideal.inertiaDegIn_eq_inertiaDeg (maximalIdeal S) P (L ≃ₐ[K] L)]
      exact (Dvd.intro_left _ rfl).trans hef
    have : Module.Finite S (B ⧸ P) := inferInstance
    have : Module.Finite (S ⧸ maximalIdeal S) (B ⧸ P) :=
      Module.Finite.of_restrictScalars_finite S _ _
    refine isSeparable_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance)
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hP) ?_
    obtain ⟨c, hc⟩ := hf
    intro h0
    have hu : IsUnit ((q : S) : S ⧸ maximalIdeal S) := hq.map (Ideal.Quotient.mk _)
    rw [map_natCast, hc, Nat.cast_mul, h0, zero_mul] at hu
    exact not_isUnit_zero hu

end GlobalTheory.RamGalDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationLeCardOfSpan
section
namespace GlobalTheory

theorem eq_zero_of_sum_eq_zero_of_unit_mul_pow {R : Type*} [CommRing R] [IsDomain R] {ϖ : R}
    (hϖ : Irreducible ϖ) {e : ℕ} (c : Fin e → R)
    (hc : ∀ i, c i ≠ 0 → ∃ (n : ℕ) (w : R), IsUnit w ∧ c i = w * ϖ ^ (i.val + e * n))
    (hsum : ∑ i, c i = 0) : ∀ i, c i = 0 := by
  classical
  by_contra hne
  push_neg at hne
  choose! n w hw hcw using hc
  set S := Finset.univ.filter (fun i => c i ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [hS, hi]⟩
  obtain ⟨i0, hi0S, hmin⟩ := S.exists_min_image (fun i => i.val + e * n i) hSne
  have hi0 : c i0 ≠ 0 := (Finset.mem_filter.1 hi0S).2
  have hdvd : ∀ i ∈ Finset.univ.erase i0, ϖ ^ (i0.val + e * n i0 + 1) ∣ c i := by
    intro i hi
    have hii0 : i ≠ i0 := Finset.ne_of_mem_erase hi
    by_cases hci : c i = 0
    · rw [hci]; exact dvd_zero _
    · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hci⟩
      have hle : i0.val + e * n i0 ≤ i.val + e * n i := hmin i hiS
      have hne' : i.val + e * n i ≠ i0.val + e * n i0 := by
        intro heq
        apply hii0
        apply Fin.ext
        have h1 : (i.val + e * n i) % e = i.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
        have h2 : (i0.val + e * n i0) % e = i0.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i0.isLt]
        rw [← h1, ← h2, heq]
      rw [hcw i hci]
      exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
  obtain ⟨X, hX⟩ := Finset.dvd_sum hdvd
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hX, hcw i0 hi0] at hsum
  have h0 : ϖ ^ (i0.val + e * n i0) * (w i0 + ϖ * X) = 0 := by rw [← hsum]; ring
  have h1 : w i0 + ϖ * X = 0 :=
    (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hϖ.ne_zero)
  have h2 : ϖ ∣ w i0 := ⟨-X, by linear_combination h1⟩
  exact hϖ.not_isUnit (isUnit_of_dvd_unit h2 (hw i0 hi0))

theorem ramification_le_card_of_span :
    ∀ (F : Type) [Field F] (T' T'' : Subring F), IsDiscreteValuationRing T' →
      IsDiscreteValuationRing T'' → ∀ (h : T' ≤ T''),
      (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) → ∀ (s : Finset F),
      (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) →
      ∀ π : T', Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ ∃ e : ℕ, 1 ≤ e ∧ e ≤ s.card ∧
        Associated (Subring.inclusion h π) (ϖ ^ e) := by
  intro F _ T' T'' h1 h2 h hdom s hspan π hπ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T''
  have hπ0 : Subring.inclusion h π ≠ 0 := by
    intro h0
    apply hπ.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h0
    simpa using this
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hπ0 hϖ
  refine ⟨ϖ, hϖ, e, ?_, ?_, he⟩
  · rcases Nat.eq_zero_or_pos e with rfl | hpos
    · exfalso
      rw [pow_zero] at he
      have hu : IsUnit (Subring.inclusion h π) := he.isUnit_iff.2 isUnit_one
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      obtain ⟨z, hzT', hz⟩ := hdom (π : F) π.2
        ⟨(y : F), y.2, by simpa using congrArg Subtype.val hy⟩
      exact hπ.not_isUnit (isUnit_iff_exists_inv.2 ⟨⟨z, hzT'⟩, Subtype.ext hz⟩)
    · exact hpos
  ·
    choose d hdT hd0 hdspan using
      fun i : Fin e => hspan ((ϖ ^ (i : ℕ) : T'') : F) (ϖ ^ (i : ℕ)).2
    set D : F := ∏ i, d i with hDdef
    have hDT : D ∈ T' := Subring.prod_mem _ (fun i _ => hdT i)
    have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hd0 i)
    let f : Fin e → F := fun i => D * ((ϖ ^ (i : ℕ) : T'') : F)
    have hfspan : ∀ i, f i ∈ Submodule.span T' (s : Set F) := by
      intro i
      have hmem : (∏ j ∈ Finset.univ.erase i, d j) ∈ T' :=
        Subring.prod_mem _ (fun j _ => hdT j)
      have := Submodule.smul_mem (Submodule.span T' (s : Set F))
        (⟨∏ j ∈ Finset.univ.erase i, d j, hmem⟩ : T') (hdspan i)
      rw [Subring.smul_def] at this
      have heq : f i = (∏ j ∈ Finset.univ.erase i, d j) * (d i * ((ϖ ^ (i : ℕ) : T'') : F)) := by
        simp only [f, hDdef]
        rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]
        ring
      rw [heq]
      exact this
    have hli : LinearIndependent T' f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      obtain ⟨v, hv⟩ := he.symm
      let c : Fin e → T'' := fun i =>
        Subring.inclusion h (g i * ⟨D, hDT⟩) * ϖ ^ (i : ℕ)
      have hcsum : ∑ i, c i = 0 := by
        apply Subtype.ext
        have hcs : ((∑ i, c i : T'') : F) = ∑ i, g i • f i := by
          simp [c, f, Subring.smul_def, mul_assoc]
        rw [hcs, hg]
        rfl
      have hc : ∀ i, c i ≠ 0 → ∃ (n : ℕ) (w : T''), IsUnit w ∧ c i = w * ϖ ^ (i.val + e * n) := by
        intro i hci
        have ha : g i * ⟨D, hDT⟩ ≠ 0 := by
          intro h0; apply hci; simp only [c, h0, map_zero, zero_mul]
        obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
        refine ⟨m, Subring.inclusion h (u : T') * (v : T'') ^ m,
          (u.isUnit.map (Subring.inclusion h)).mul (v.isUnit.pow m), ?_⟩
        simp only [c]
        rw [hu, map_mul, map_pow, ← hv]
        ring
      have hc0 := eq_zero_of_sum_eq_zero_of_unit_mul_pow hϖ c hc hcsum
      intro i
      have := hc0 i
      simp only [c, mul_eq_zero, pow_eq_zero_iff', hϖ.ne_zero, false_and, or_false] at this
      have h3 : g i * ⟨D, hDT⟩ = 0 := by
        apply Subtype.ext
        have := congrArg Subtype.val this
        simpa using this
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h4
      · exact absurd (congrArg Subtype.val h4) hD0
    let f' : Fin e → Submodule.span T' (s : Set F) := fun i => ⟨f i, hfspan i⟩
    have hli' : LinearIndependent T' f' :=
      LinearIndependent.of_comp (Submodule.span T' (s : Set F)).subtype hli
    have hcard := hli'.cardinal_le_rank.trans (rank_span_finset_le s)
    simpa using hcard

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComapIncludeRightField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem range_comap_includeRight_field :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : Type) [Field k] [Algebra A k],
    Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom) = {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A k)} := by
  intro A B _ _ _ k _ _
  ext r
  constructor
  · rintro ⟨q, rfl⟩
    show Ideal.comap (algebraMap A B) (Ideal.comap _ q.asIdeal) = _
    rw [Ideal.comap_comap, ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap,
      ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ q.asIdeal),
      ← RingHom.ker_eq_comap_bot]
  · intro hr
    change Ideal.comap (algebraMap A B) r.asIdeal = RingHom.ker (algebraMap A k) at hr
    set f := algebraMap A k with hf
    let I := RingHom.ker f
    let K := r.asIdeal.ResidueField
    let g : A →+* K := (algebraMap B K).comp (algebraMap A B)
    have hg : RingHom.ker g = I := by
      change RingHom.ker ((algebraMap B K).comp (algebraMap A B)) = RingHom.ker f
      rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField, hr]
    have hIg : ∀ a ∈ I, g a = 0 := fun a ha => by rw [← RingHom.mem_ker, hg]; exact ha
    let ι₁ : A ⧸ I →+* k := RingHom.kerLift f
    let ι₂ : A ⧸ I →+* K := Ideal.Quotient.lift I g hIg
    have inj₁ : Function.Injective ι₁ := RingHom.kerLift_injective f
    have inj₂ : Function.Injective ι₂ := RingHom.lift_injective_of_ker_le_ideal I hIg hg.le
    letI : Algebra (A ⧸ I) k := ι₁.toAlgebra
    letI : Algebra (A ⧸ I) K := ι₂.toAlgebra
    haveI : Nontrivial (k ⊗[A ⧸ I] K) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain (A ⧸ I) k K inj₁ inj₂
    haveI : SMulCommClass (A ⧸ I) A k := ⟨fun x a y => by
      simp only [Algebra.smul_def]; ring⟩
    let α : k →ₐ[A] k ⊗[A ⧸ I] K := Algebra.TensorProduct.includeLeft
    let β : B →ₐ[A] k ⊗[A ⧸ I] K :=
      { ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp
          (algebraMap B K)) with
        commutes' := fun a => by
          change (1 : k) ⊗ₜ[A ⧸ I] (algebraMap (A ⧸ I) K (Ideal.Quotient.mk I a)) = _
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := K),
            ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]
          rfl }
    let φ : k ⊗[A] B →ₐ[A] k ⊗[A ⧸ I] K := Algebra.TensorProduct.lift α β (fun _ _ => Commute.all _ _)
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[A ⧸ I] K)
    refine ⟨PrimeSpectrum.comap φ.toRingHom ⟨m, hm.isPrime⟩, ?_⟩
    ext1
    show Ideal.comap _ (Ideal.comap φ.toRingHom m) = r.asIdeal
    have hcomp : φ.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom =
        ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp
          (algebraMap B K)) := by
      ext b
      simp [φ, α, β, Algebra.TensorProduct.lift_tmul]
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ m),
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeOfGrowthInRadius
section
open Filter Topology

namespace GlobalTheory

theorem rank_le_of_growth_in_radius : ∀ (D : ℕ) (f : ℝ → ℕ → ℝ) (α γ ρ t₀ t₁ : ℝ), 0 ≤ ρ →
    (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => f t m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α + γ * t))) →
    (∀ (t : ℝ) (m Q : ℕ), 0 < m → 0 < Q → ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) →
      ρ * (m : ℝ) ^ D * Real.log Q ≤ f t m) → ρ ≤ γ := by
  intro D f α γ ρ t₀ t₁ hρ hlim hbd
  have hev : ∀ᶠ m : ℕ in atTop, ρ * (m : ℝ) ^ D * Real.exp (-(m : ℝ)) ≤ 1 := by
    have h1 : Tendsto (fun x : ℝ => x ^ D * Real.exp (-x)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero D
    have h2 : Tendsto (fun m : ℕ => ρ * ((m : ℝ) ^ D * Real.exp (-(m : ℝ)))) atTop (𝓝 (ρ * 0)) :=
      (h1.comp tendsto_natCast_atTop_atTop).const_mul ρ
    rw [mul_zero] at h2
    filter_upwards [h2.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with m hm
    rw [mul_assoc]; exact hm.le
  have key : ∀ t, max t₀ (t₁ + 2) ≤ t → ρ * (t - t₁ - 2) ≤ α + γ * t := by
    intro t ht
    have ht0 : t₀ ≤ t := le_trans (le_max_left _ _) ht
    have ht1 : t₁ + 2 ≤ t := le_trans (le_max_right _ _) ht
    refine ge_of_tendsto (hlim t ht0) ?_
    filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
    have hm1' : (1:ℝ) ≤ m := by exact_mod_cast hm1
    set x := Real.exp ((t - t₁ - 1) * m) with hx
    have hx2 : 2 ≤ x := by
      have : 1 ≤ (t - t₁ - 1) * m := by nlinarith
      have h := Real.add_one_le_exp ((t - t₁ - 1) * m)
      linarith
    set Q := ⌊x⌋₊ with hQ
    have hQle : (Q : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hQgt : x < Q + 1 := Nat.lt_floor_add_one x
    have hQpos : 0 < Q := by
      rw [hQ]; exact Nat.floor_pos.mpr (by linarith)
    have e2 : Real.exp (-(m:ℝ)) ≤ 1 / 2 := by
      have h := Real.add_one_le_exp (m:ℝ)
      have hp : Real.exp (-(m:ℝ)) * Real.exp m = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-(m:ℝ))]
    have hQge : Real.exp ((t - t₁ - 2) * m) ≤ Q := by
      have e1 : Real.exp ((t - t₁ - 2) * m) = x * Real.exp (-(m:ℝ)) := by
        rw [hx, ← Real.exp_add]; congr 1; ring
      rw [e1]
      have : x * Real.exp (-(m:ℝ)) ≤ x * (1 / 2) := mul_le_mul_of_nonneg_left e2 (by linarith)
      linarith
    have e3 : x * Real.exp (t₁ * m) = Real.exp (-(m:ℝ)) * Real.exp (t * m) := by
      rw [hx, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hρm : 0 ≤ ρ * (m : ℝ) ^ D := mul_nonneg hρ (pow_nonneg hmpos.le _)
    have hcond : ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) := by
      calc ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m)
          ≤ ρ * (m : ℝ) ^ D * x * Real.exp (t₁ * m) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQle hρm) (Real.exp_pos _).le
        _ = (ρ * (m : ℝ) ^ D * Real.exp (-(m:ℝ))) * Real.exp (t * m) := by
            rw [mul_assoc (ρ * (m : ℝ) ^ D) x, e3]; ring
        _ ≤ 1 * Real.exp (t * m) := mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
        _ = Real.exp (t * m) := one_mul _
    have hb := hbd t m Q (by omega) hQpos hcond
    have hlog : (t - t₁ - 2) * (m : ℝ) ≤ Real.log Q :=
      calc (t - t₁ - 2) * (m : ℝ) = Real.log (Real.exp ((t - t₁ - 2) * m)) := (Real.log_exp _).symm
        _ ≤ Real.log Q := Real.log_le_log (Real.exp_pos _) hQge
    rw [le_div_iff₀ (by positivity)]
    calc ρ * (t - t₁ - 2) * (m : ℝ) ^ (D + 1) = ρ * (m : ℝ) ^ D * ((t - t₁ - 2) * m) := by ring
      _ ≤ ρ * (m : ℝ) ^ D * Real.log Q := mul_le_mul_of_nonneg_left hlog hρm
      _ ≤ f t m := hb
  by_contra h
  push_neg at h
  have hd : 0 < ρ - γ := sub_pos.mpr h
  set T := max (max t₀ (t₁ + 2)) ((α + ρ * (t₁ + 2)) / (ρ - γ) + 1) with hTdef
  have hk := key T (le_max_left _ _)
  have hT : (α + ρ * (t₁ + 2)) / (ρ - γ) + 1 ≤ T := le_max_right _ _
  have hlt : (α + ρ * (t₁ + 2)) / (ρ - γ) < T := by linarith
  have h3 : α + ρ * (t₁ + 2) < T * (ρ - γ) := (div_lt_iff₀ hd).mp hlt
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixIdentityTransferToComplexMap
section
open Matrix

namespace GlobalTheory

noncomputable def endRealMatrixRingHom {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) :
    Module.End ℂ (Fin g → ℂ) →+* Matrix (Fin n) (Fin n) ℝ where
  toFun f := LinearMap.toMatrix e e (f.restrictScalars ℝ)
  map_one' := by
    have : ((1 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 1 := rfl
    rw [this]; exact LinearMap.toMatrix_one e
  map_mul' f h := by
    have : ((f * h).restrictScalars ℝ) = f.restrictScalars ℝ * h.restrictScalars ℝ := rfl
    rw [this]; exact LinearMap.toMatrix_mul e _ _
  map_zero' := by
    have : ((0 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 0 := rfl
    rw [this]; exact map_zero _
  map_add' f h := by
    have : ((f + h).restrictScalars ℝ) = f.restrictScalars ℝ + h.restrictScalars ℝ := rfl
    rw [this]; exact map_add _ _ _

theorem endRealMatrixRingHom_injective {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) :
    Function.Injective (endRealMatrixRingHom e) := by
  intro f h hfh
  have h1 : f.restrictScalars ℝ = h.restrictScalars ℝ := (LinearMap.toMatrix e e).injective hfh
  exact LinearMap.restrictScalars_injective ℝ h1

theorem matrix_identity_transfer (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ)
    (hT : Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ))
    (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ)
    (hid : (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tq + ∑ i, c i • ((Polynomial.aeval Tq (p i)) ^ 2 * Tq)) :
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) := by
  let F := (endRealMatrixRingHom e).toRatAlgHom
  let ψ : Matrix (Fin n) (Fin n) ℚ →ₐ[ℚ] Matrix (Fin n) (Fin n) ℝ := (Algebra.ofId ℚ ℝ).mapMatrix
  have hψ : ∀ M, ψ M = M.map (Rat.cast : ℚ → ℝ) := by
    intro M; ext i j; simp [ψ]
  have hFγ : F γ = ψ Tq := by rw [hψ, hT]; rfl
  apply endRealMatrixRingHom_injective e
  change F 1 = F _
  have key := congrArg ψ hid
  rw [map_one] at key
  rw [map_one, key]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_smul, map_mul, map_pow, ← Polynomial.aeval_algHom_apply, hFγ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReGt
section
namespace GlobalTheory.UnitNormRealPartBound

lemma norm_eq_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) : ‖z‖ = 1 := by
  have hup : ∀ n : ℕ, ‖z‖ ^ n < 3 / 2 := fun n => by
    have := h n
    calc ‖z‖ ^ n = ‖(z ^ n - 1) + 1‖ := by rw [sub_add_cancel, norm_pow]
      _ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ < 3 / 2 := by rw [norm_one]; linarith
  have hlo : ∀ n : ℕ, 1 / 2 < ‖z‖ ^ n := fun n => by
    have := h n
    have h2 : ‖(1 : ℂ)‖ ≤ ‖z ^ n - 1‖ + ‖z ^ n‖ := by
      calc ‖(1 : ℂ)‖ = ‖-(z ^ n - 1) + z ^ n‖ := by ring_nf
        _ ≤ ‖-(z ^ n - 1)‖ + ‖z ^ n‖ := norm_add_le _ _
        _ = ‖z ^ n - 1‖ + ‖z ^ n‖ := by rw [norm_neg]
    rw [norm_one, norm_pow] at h2
    linarith
  rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) h1
    linarith [hlo n]
  · exact h1
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 / 2 : ℝ) h1
    linarith [hup n]

lemma re_gt {w : ℂ} (hw : ‖w‖ = 1) (h : ‖w - 1‖ < 1 / 2) : 7 / 8 < w.re := by
  have h1 : ‖w - 1‖ ^ 2 < 1 / 4 := by nlinarith [norm_nonneg (w - 1)]
  have h2 : ‖w‖ ^ 2 = 1 := by rw [hw]; norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h1 h2
  simp at h1
  nlinarith

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have hz := norm_eq_one h
  have hnp : ∀ n : ℕ, ‖z ^ n‖ = 1 := fun n => by rw [norm_pow, hz, one_pow]
  have hre : ∀ n : ℕ, 7 / 8 < (z ^ n).re := fun n => re_gt (hnp n) (h n)
  have key : ∀ k : ℕ, (7 / 4 : ℝ) ^ k * |z.im| ≤ |(z ^ (2 ^ k)).im| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z ^ (2 ^ (k + 1)) = z ^ (2 ^ k) * z ^ (2 ^ k) := by
        rw [pow_succ, pow_mul, sq]
      have hr := hre (2 ^ k)
      have e2 : (z ^ (2 ^ (k + 1))).im = 2 * (z ^ (2 ^ k)).re * (z ^ (2 ^ k)).im := by
        rw [e, Complex.mul_im]; ring
      rw [e2, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * (z ^ 2 ^ k).re), pow_succ]
      have : (7 / 4 : ℝ) ≤ 2 * (z ^ 2 ^ k).re := by linarith
      have hn : 0 ≤ (7 / 4 : ℝ) ^ k * |z.im| := by positivity
      nlinarith [abs_nonneg (z ^ 2 ^ k).im]
  have him : z.im = 0 := by
    by_contra hne
    have hpos : 0 < |z.im| := abs_pos.mpr hne
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / |z.im|) (by norm_num : (1 : ℝ) < 7 / 4)
    have hb : |(z ^ (2 ^ k)).im| ≤ 1 := (Complex.abs_im_le_norm _).trans (hnp _).le
    have : 1 < (7 / 4 : ℝ) ^ k * |z.im| := by rwa [div_lt_iff₀ hpos] at hk
    linarith [key k]
  have h1 := hre 1
  rw [pow_one] at h1
  have h2 : ‖z‖ ^ 2 = 1 := by rw [hz]; norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him] at h2
  apply Complex.ext
  · simp; nlinarith
  · simp [him]

end GlobalTheory.UnitNormRealPartBound
end

