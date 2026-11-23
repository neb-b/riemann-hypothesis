module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsIntegerNearConjVector
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

theorem exists_integer_near_conj_vector : ∀ (E : Type) [Field E] [NumberField E], ∃ B : ℝ, ∀ c : (E →+* ℂ) → ℂ, (∀ τ, c (ComplexEmbedding.conjugate τ) = starRingEnd ℂ (c τ)) → ∃ a : 𝓞 E, ∀ τ : E →+* ℂ, ‖τ (a : E) - c τ‖ ≤ B := by
  intro E _ _
  classical
  obtain ⟨bC, hv⟩ : ∃ bC : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℂ ((E →+* ℂ) → ℂ),
      ∀ i (τ : E →+* ℂ), bC i τ = τ (RingOfIntegers.basis E i : E) :=
    ⟨canonicalEmbedding.latticeBasis E, fun i τ => by
      rw [canonicalEmbedding.latticeBasis_apply, canonicalEmbedding.apply_at, integralBasis_apply]⟩
  refine ⟨∑ τ : E →+* ℂ, ∑ i, ‖τ (RingOfIntegers.basis E i : E)‖, fun c hc => ?_⟩
  have hsum : c = ∑ i, bC.repr c i • bC i := (bC.sum_repr c).symm
  have hcτ : ∀ τ : E →+* ℂ, c τ = ∑ i, bC.repr c i * τ (RingOfIntegers.basis E i : E) := by
    intro τ
    conv_lhs => rw [hsum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv]
  have hconj : ∀ τ : E →+* ℂ,
      ∑ i, starRingEnd ℂ (bC.repr c i) * τ (RingOfIntegers.basis E i : E) = c τ := by
    intro τ
    have h1 := hc τ
    rw [hcτ (ComplexEmbedding.conjugate τ)] at h1
    have h2 := congrArg (starRingEnd ℂ) h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Complex.conj_conj, map_sum] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  have hli := Fintype.linearIndependent_iff.mp bC.linearIndependent
    (fun i => bC.repr c i - starRingEnd ℂ (bC.repr c i)) (by
      funext τ
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hv, sub_mul,
        Finset.sum_sub_distrib]
      rw [hconj τ, ← hcτ τ, sub_self])
  have hreal : ∀ i, (bC.repr c i).im = 0 := by
    intro i
    have h3 := congrArg Complex.im (hli i)
    rw [Complex.sub_im, Complex.conj_im, sub_neg_eq_add, Complex.zero_im] at h3
    linarith
  obtain ⟨x, hx⟩ : ∃ x : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ i, bC.repr c i = (x i : ℂ) :=
    ⟨fun i => (bC.repr c i).re, fun i => Complex.ext (by simp) (by simp [hreal i])⟩
  refine ⟨∑ i, round (x i) • RingOfIntegers.basis E i, fun τ => ?_⟩
  have hτa : τ ((∑ i, round (x i) • RingOfIntegers.basis E i : 𝓞 E) : E) =
      ∑ i, (round (x i) : ℂ) * τ (RingOfIntegers.basis E i : E) := by
    change (τ.comp (algebraMap (𝓞 E) E)) (∑ i, round (x i) • RingOfIntegers.basis E i) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
    rfl
  have hcx : c τ = ∑ i, (x i : ℂ) * τ (RingOfIntegers.basis E i : E) := by
    rw [hcτ τ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx i]
  rw [hτa, hcx, ← Finset.sum_sub_distrib]
  calc ‖∑ i, ((round (x i) : ℂ) * τ (RingOfIntegers.basis E i : E) -
          (x i : ℂ) * τ (RingOfIntegers.basis E i : E))‖
      ≤ ∑ i, ‖(round (x i) : ℂ) * τ (RingOfIntegers.basis E i : E) -
          (x i : ℂ) * τ (RingOfIntegers.basis E i : E)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖τ (RingOfIntegers.basis E i : E)‖ := Finset.sum_le_sum fun i _ => by
        rw [← sub_mul, norm_mul]
        have hr : ‖(round (x i) : ℂ) - (x i : ℂ)‖ ≤ 1 := by
          have h := abs_sub_round (x i)
          rw [show ((round (x i) : ℤ) : ℂ) - ((x i : ℝ) : ℂ) = (((round (x i) : ℝ) - x i : ℝ) : ℂ) by
            push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
          linarith
        calc ‖(round (x i) : ℂ) - (x i : ℂ)‖ * ‖τ (RingOfIntegers.basis E i : E)‖
            ≤ 1 * ‖τ (RingOfIntegers.basis E i : E)‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
          _ = ‖τ (RingOfIntegers.basis E i : E)‖ := one_mul _
    _ ≤ ∑ τ' : E →+* ℂ, ∑ i, ‖τ' (RingOfIntegers.basis E i : E)‖ :=
        Finset.single_le_sum (f := fun τ' : E →+* ℂ => ∑ i, ‖τ' (RingOfIntegers.basis E i : E)‖)
          (fun τ' _ => Finset.sum_nonneg fun i _ => norm_nonneg _) (Finset.mem_univ τ)

end PositivityTheory.Xgf

end
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.NBasic
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

theorem isScalarTower_rat_of_ringHom {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') :
    letI : Algebra k k' := f.toAlgebra;
    IsScalarTower ℚ k k' := by
  letI : Algebra k k' := f.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem exists_extension_embedding_alg_closed : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (j : k →+* A), ∃ j' : k' →+* A, j'.comp f = j := by
  intro k k' A _ _ _ _ _ _ _ f j
  letI : Algebra k k' := f.toAlgebra
  letI : Algebra k A := j.toAlgebra
  haveI : IsScalarTower ℚ k k' := isScalarTower_rat_of_ringHom f
  haveI : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  haveI : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  refine ⟨(IsAlgClosed.lift : k' →ₐ[k] A).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : k' →ₐ[k] A).commutes x

open Classical in
theorem card_embeddings_extending {k k' A : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A]
    [IsAlgClosed A] (f : k →+* k') (j : k →+* A) :
    letI : Algebra k k' := f.toAlgebra;
    (Finset.univ.filter fun j' : k' →+* A => j'.comp f = j).card = Module.finrank k k' := by
  letI : Algebra k k' := f.toAlgebra
  letI : Algebra k A := j.toAlgebra
  haveI : IsScalarTower ℚ k k' := isScalarTower_rat_of_ringHom f
  haveI : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  rw [← Fintype.card_subtype, Fintype.card_eq_nat_card,
    ← AlgHom.natCard_of_splits k k' A (fun _ => IsAlgClosed.splits _)]
  refine Nat.card_congr
    { toFun := fun ψ => { ψ.1 with commutes' := fun r => RingHom.congr_fun ψ.2 r }
      invFun := fun φ => ⟨φ.toRingHom, RingHom.ext φ.commutes⟩
      left_inv := fun ψ => rfl
      right_inv := fun φ => rfl }

theorem sum_embeddings_base_change : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (F : (k →+* A) → ℝ), (Module.finrank ℚ k : ℝ) * ∑ j : k' →+* A, F (j.comp f) = (Module.finrank ℚ k' : ℝ) * ∑ j : k →+* A, F j := by
  intro k k' A _ _ _ _ _ _ _ f F
  classical
  letI : Algebra k k' := f.toAlgebra
  haveI : IsScalarTower ℚ k k' := isScalarTower_rat_of_ringHom f
  have hsum : ∑ j' : k' →+* A, F (j'.comp f) = (Module.finrank k k' : ℝ) * ∑ j : k →+* A, F j := by
    rw [← Finset.sum_fiberwise Finset.univ (fun j' : k' →+* A => j'.comp f), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => F j) (fun j' hj' => by rw [(Finset.mem_filter.1 hj').2]),
      Finset.sum_const, nsmul_eq_mul]
    congr 2
    convert card_embeddings_extending f j
  rw [hsum, ← Module.finrank_mul_finrank ℚ k k']
  push_cast
  ring

theorem finsum_const_mul {α : Type} (c : ℝ) (_hc : c ≠ 0) (g : α → ℝ) : ∑ᶠ p, c * g p = c * ∑ᶠ p, g p :=
  (mul_finsum g c).symm

theorem logNorms_ext_degree_adelic : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') (N : LogNorms k), (N.ext f).deg = N.deg ∧ ((N.ext f).IsAdelic ↔ N.IsAdelic) := by
  intro k k' _ _ _ _ f N
  have hd : (0:ℝ) < Module.finrank ℚ k := by exact_mod_cast Module.finrank_pos
  have hd' : (0:ℝ) < Module.finrank ℚ k' := by exact_mod_cast Module.finrank_pos
  set c : ℝ := (Module.finrank ℚ k' : ℝ) / Module.finrank ℚ k with hc_def
  have hc : c ≠ 0 := (div_pos hd' hd).ne'
  have hinf : ∑ s : k' →+* ℂ, N.inf (s.comp f) = c * ∑ s : k →+* ℂ, N.inf s := by
    rw [hc_def, div_mul_eq_mul_div, eq_div_iff hd.ne', ← sum_embeddings_base_change k k' ℂ f N.inf]
    ring
  have hfin : ∀ p : Nat.Primes, (N.ext f).finSum p = c * N.finSum p := by
    intro p
    show ∑ ι : k' →+* ℂ_[(p:ℕ)], N.fin p (ι.comp f) = c * ∑ ι : k →+* ℂ_[(p:ℕ)], N.fin p ι
    rw [hc_def, div_mul_eq_mul_div, eq_div_iff hd.ne', ← sum_embeddings_base_change k k' ℂ_[(p:ℕ)] f (N.fin p)]
    ring
  refine ⟨?_, ?_⟩
  · show -(∑ s : k' →+* ℂ, N.inf (s.comp f) + ∑ᶠ p, (N.ext f).finSum p) / (Module.finrank ℚ k' : ℝ) = N.deg
    rw [hinf, finsum_congr hfin, finsum_const_mul c hc, ← mul_add, LogNorms.deg, hc_def]
    field_simp
  · have hset : {p : Nat.Primes | ∃ ι : k' →+* ℂ_[(p:ℕ)], (N.ext f).fin p ι ≠ 0} =
        {p : Nat.Primes | ∃ ι : k →+* ℂ_[(p:ℕ)], N.fin p ι ≠ 0} := by
      ext p
      constructor
      · rintro ⟨ι, h⟩
        exact ⟨ι.comp f, h⟩
      · rintro ⟨ι, h⟩
        obtain ⟨ι', hι'⟩ := exists_extension_embedding_alg_closed k k' ℂ_[(p:ℕ)] f ι
        refine ⟨ι', ?_⟩
        show N.fin p (ι'.comp f) ≠ 0
        rw [hι']
        exact h
    unfold LogNorms.IsAdelic
    rw [hset]

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.NIdeal
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

namespace NI

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_int_le {E : Type} [Field E] [NumberField E] {p : Nat.Primes} (j : 𝓞 E →+* ℂ_[p]) (r : 𝓞 E) :
    ‖j r‖ ≤ 1 :=
  norm_le_one_of_isIntegral (map_isIntegral_int j (Algebra.IsIntegral.isIntegral r))

theorem logIdeal_eq {E : Type} [Field E] [NumberField E] {p : Nat.Primes} (j : 𝓞 E →+* ℂ_[p]) (I : Ideal (𝓞 E))
    {a : 𝓞 E} (ha : a ∈ I) (h : ∀ b ∈ I, ‖j b‖ ≤ ‖j a‖) : logIdeal j I = Real.log ‖j a‖ := by
  unfold logIdeal
  congr 1
  exact le_antisymm (ciSup_le fun x => h x.1 x.2)
    (le_ciSup (f := fun x : I => ‖j (x : 𝓞 E)‖) ⟨‖j a‖, by rintro _ ⟨x, rfl⟩; exact h x.1 x.2⟩ ⟨a, ha⟩)

end NI

theorem padic_logIdeal_max_element : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]) (I : Ideal (𝓞 E)), Function.Injective j → I ≠ ⊥ → ∃ a ∈ I, a ≠ 0 ∧ (∀ b ∈ I, ‖j b‖ ≤ ‖j a‖) ∧ logIdeal j I = Real.log ‖j a‖ := by
  intro E _ _ p j I hj hI
  classical
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · exact absurd (by rw [← hS, h, Finset.coe_empty, Submodule.span_empty]) hI
    · exact h
  obtain ⟨a, haS, hmax⟩ := S.exists_max_image (fun s => ‖j s‖) hSne
  have haI : a ∈ I := hS ▸ Submodule.subset_span haS
  have hle : ∀ b ∈ I, ‖j b‖ ≤ ‖j a‖ := by
    intro b hb
    rw [← hS] at hb
    induction hb using Submodule.span_induction with
    | mem x hx => exact hmax x hx
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    | smul r x _ hx =>
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (NI.norm_int_le j r)).trans hx
  have ha0 : a ≠ 0 := by
    intro h0
    apply hI
    rw [Submodule.eq_bot_iff]
    intro b hb
    have := hle b hb
    rw [h0, map_zero, norm_zero] at this
    exact hj (by rw [map_zero]; exact norm_le_zero_iff.1 this)
  exact ⟨a, haI, ha0, hle, NI.logIdeal_eq j I haI hle⟩

theorem log_ideal_mul_span_map : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]), Function.Injective j → (∀ I J : Ideal (𝓞 E), I ≠ ⊥ → J ≠ ⊥ → logIdeal j (I * J) = logIdeal j I + logIdeal j J) ∧ (∀ a : 𝓞 E, logIdeal j (Ideal.span {a}) = Real.log ‖j a‖) ∧ ∀ e : 𝓞 E ≃+* 𝓞 E, ∀ I : Ideal (𝓞 E), logIdeal j (I.map (e : 𝓞 E →+* 𝓞 E)) = logIdeal (j.comp (e : 𝓞 E →+* 𝓞 E)) I := by
  intro E _ _ p j hj
  refine ⟨fun I J hI hJ => ?_, fun a => ?_, fun e I => ?_⟩
  · obtain ⟨a, haI, ha0, hla, ea⟩ := padic_logIdeal_max_element E p j I hj hI
    obtain ⟨b, hbJ, hb0, hlb, eb⟩ := padic_logIdeal_max_element E p j J hj hJ
    have hle : ∀ c ∈ I * J, ‖j c‖ ≤ ‖j (a * b)‖ := by
      intro c hc
      rw [map_mul, norm_mul]
      refine Submodule.mul_induction_on (C := fun c => ‖j c‖ ≤ ‖j a‖ * ‖j b‖) hc (fun m hm n hn => ?_) (fun x y hx hy => ?_)
      · rw [map_mul, norm_mul]
        exact mul_le_mul (hla m hm) (hlb n hn) (norm_nonneg _) (norm_nonneg _)
      · rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    rw [NI.logIdeal_eq j (I * J) (Ideal.mul_mem_mul haI hbJ) hle, ea, eb, map_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 fun h => ha0 (hj (by rw [h, map_zero])))
        (norm_ne_zero_iff.2 fun h => hb0 (hj (by rw [h, map_zero])))]
  · refine NI.logIdeal_eq j _ (Ideal.mem_span_singleton_self a) fun b hb => ?_
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    rw [map_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (NI.norm_int_le j r)
  · unfold logIdeal
    congr 1
    let eq : I ≃ I.map (e : 𝓞 E →+* 𝓞 E) :=
      { toFun := fun x => ⟨e x, Ideal.mem_map_of_mem _ x.2⟩
        invFun := fun y => ⟨e.symm y, by
          obtain ⟨x, hx, hxy⟩ := (Ideal.mem_map_iff_of_surjective (e : 𝓞 E →+* 𝓞 E) e.surjective).1 y.2
          have : e.symm (y : 𝓞 E) = x := by rw [← hxy]; exact e.symm_apply_apply x
          rw [this]; exact hx⟩
        left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
        right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }
    exact (eq.iSup_congr fun x => rfl).symm

theorem logIdeal_support_finite : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ → {p : Nat.Primes | ∃ j : 𝓞 E →+* ℂ_[p], logIdeal j I ≠ 0}.Finite := by
  intro E _ _ I hI
  set n := Ideal.absNorm I with hn
  have hn0 : n ≠ 0 := by rw [hn]; exact fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  have hnI : (n : 𝓞 E) ∈ I := Ideal.absNorm_mem I
  refine ((Nat.primeFactors n).finite_toSet.preimage (Set.injOn_of_injective Subtype.val_injective)).subset ?_
  intro p hp
  obtain ⟨j, hj⟩ := hp
  simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_primeFactors]
  refine ⟨p.2, ?_, hn0⟩
  by_contra hdvd
  apply hj
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  have h1 : ‖j (n : 𝓞 E)‖ = 1 := by
    rw [map_natCast]
    have : ((n : ℚ_[p]) : ℂ_[p]) = (n : ℂ_[p]) := by simp
    rw [← this, PadicComplex.norm_extends', Padic.norm_natCast_eq_one_iff]
    first
    | exact hdvd
    | exact (Nat.Prime.coprime_iff_not_dvd p.2).2 hdvd
    | exact ((Nat.Prime.coprime_iff_not_dvd p.2).2 hdvd).symm
    | simpa using hdvd
  rw [NI.logIdeal_eq j I hnI (fun b _ => h1 ▸ NI.norm_int_le j b), h1, Real.log_one]

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.RatProductFormula
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

namespace NR

def Good (r : ℚ) : Prop :=
  {p : Nat.Primes | Real.log ‖(r : ℂ_[p])‖ ≠ 0}.Finite ∧ Real.log ‖(r : ℂ)‖ + ∑ᶠ p : Nat.Primes, Real.log ‖(r : ℂ_[p])‖ = 0

theorem norm_padicNat (p : Nat.Primes) (n : ℕ) : ‖(n : ℂ_[p])‖ = padicNorm p n := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  have : ((n : ℚ_[p]) : ℂ_[p]) = (n : ℂ_[p]) := by first | simp | norm_cast | exact map_natCast _ n
  rw [← this, PadicComplex.norm_extends', ← Rat.cast_natCast, Padic.eq_padicNorm]

theorem good_mul {x y : ℚ} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : Good x) (hy : Good y) : Good (x * y) := by
  have hxp : ∀ p : Nat.Primes, ‖(x : ℂ_[p])‖ ≠ 0 := fun p => by simpa using hx0
  have hyp : ∀ p : Nat.Primes, ‖(y : ℂ_[p])‖ ≠ 0 := fun p => by simpa using hy0
  have e : ∀ p : Nat.Primes, Real.log ‖((x * y : ℚ) : ℂ_[p])‖ = Real.log ‖(x : ℂ_[p])‖ + Real.log ‖(y : ℂ_[p])‖ :=
    fun p => by rw [Rat.cast_mul, norm_mul, Real.log_mul (hxp p) (hyp p)]
  have ea : Real.log ‖((x * y : ℚ) : ℂ)‖ = Real.log ‖(x : ℂ)‖ + Real.log ‖(y : ℂ)‖ := by
    rw [Rat.cast_mul, norm_mul, Real.log_mul (by simpa using hx0) (by simpa using hy0)]
  refine ⟨(hx.1.union hy.1).subset fun p hp => ?_, ?_⟩
  · by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hp (by rw [e, h.1, h.2, add_zero])
  · rw [ea, finsum_congr e, finsum_add_distrib hx.1 hy.1]
    linarith [hx.2, hy.2]

theorem good_inv {x : ℚ} (hx : Good x) : Good x⁻¹ := by
  have e : ∀ p : Nat.Primes, Real.log ‖((x⁻¹ : ℚ) : ℂ_[p])‖ = -Real.log ‖(x : ℂ_[p])‖ :=
    fun p => by rw [Rat.cast_inv, norm_inv, Real.log_inv]
  refine ⟨hx.1.subset fun p hp => ?_, ?_⟩
  · intro h; exact hp (by rw [e, h, neg_zero])
  · rw [Rat.cast_inv, norm_inv, Real.log_inv, finsum_congr e, finsum_neg_distrib]
    linarith [hx.2]

theorem good_neg {x : ℚ} (hx : Good x) : Good (-x) := by
  simpa [Good] using hx

theorem good_one : Good 1 := by
  simp [Good]

theorem good_prime (q : ℕ) (hq : q.Prime) : Good q := by
  unfold Good
  simp only [Rat.cast_natCast]
  have e : ∀ p : Nat.Primes, Real.log ‖(q : ℂ_[p])‖ = if (p : ℕ) = q then -Real.log q else 0 := by
    intro p
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    rw [norm_padicNat]
    split_ifs with h
    · subst h
      rw [padicNorm.padicNorm_p_of_prime, Rat.cast_inv, Rat.cast_natCast, Real.log_inv]
    · haveI : Fact q.Prime := ⟨hq⟩
      rw [padicNorm.padicNorm_of_prime_of_ne h, Rat.cast_one, Real.log_one]
  refine ⟨(Set.finite_singleton (⟨q, hq⟩ : Nat.Primes)).subset ?_, ?_⟩
  · intro (p : Nat.Primes) hp
    have hp' := hp
    simp only [Set.mem_setOf_eq, e] at hp'
    have h2 : (if (p : ℕ) = q then -Real.log q else 0) ≠ 0 := hp'
    by_cases h : (p : ℕ) = q
    · exact Set.mem_singleton_iff.2 (Subtype.ext h)
    · exact absurd (if_neg h) h2
  · rw [finsum_congr e, finsum_eq_single (fun x : Nat.Primes => if (x : ℕ) = q then -Real.log q else 0) ⟨q, hq⟩
      (fun p hp => if_neg fun h => hp (Subtype.ext h))]
    simp

theorem good_nat (n : ℕ) (hn : n ≠ 0) : Good n := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simpa using good_one
  | prime p hp => exact good_prime p hp
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := fun h => hn (by rw [h, zero_mul])
    have hb0 : b ≠ 0 := fun h => hn (by rw [h, mul_zero])
    rw [Nat.cast_mul]
    exact good_mul (by exact_mod_cast ha0) (by exact_mod_cast hb0) (ha ha0) (hb hb0)

theorem good_int (z : ℤ) (hz : z ≠ 0) : Good z := by
  rcases Int.natAbs_eq z with h | h
  · rw [h, Int.cast_natCast]; exact good_nat _ (Int.natAbs_ne_zero.2 hz)
  · rw [h, Int.cast_neg, Int.cast_natCast]; exact good_neg (good_nat _ (Int.natAbs_ne_zero.2 hz))

end NR

theorem rat_product_formula : ∀ r : ℚ, r ≠ 0 → {p : Nat.Primes | Real.log ‖(r : ℂ_[p])‖ ≠ 0}.Finite ∧ Real.log ‖(r : ℂ)‖ + ∑ᶠ p : Nat.Primes, Real.log ‖(r : ℂ_[p])‖ = 0 := by
  intro r hr
  have hnum : r.num ≠ 0 := Rat.num_ne_zero.2 hr
  have h := NR.good_mul (by exact_mod_cast hnum) (inv_ne_zero (by exact_mod_cast r.den_nz))
    (NR.good_int r.num hnum) (NR.good_inv (NR.good_nat r.den r.den_nz))
  rw [← div_eq_mul_inv, Rat.num_div_den] at h
  exact h

end PositivityTheory.Xgf
end

