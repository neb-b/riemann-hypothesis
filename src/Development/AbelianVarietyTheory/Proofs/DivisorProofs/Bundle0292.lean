module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMulPowLeFinrankOfPowerSeries
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import ReciprocityTheory.DualLattices.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyOriginRetractionLocalises
section
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlargeLoc

theorem retract_localises : ∀ (T O A₁ EA₁ : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra (Polynomial T) O]
    [CommRing A₁] [IsLocalRing A₁] (i₁ : A₁ →+* T), IsLocalHom i₁ → IsLocalHom (algebraMap T O) →
    ∀ [CommRing EA₁] [Algebra (Polynomial A₁) EA₁] [Algebra A₁ EA₁]
      (QA₁ : Ideal EA₁) [QA₁.IsPrime] (jA₁ : Localization.AtPrime QA₁ →+* O) (ρ' : EA₁ →+* A₁),
    algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ →
    ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 →
    (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
      Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) →
    (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) →
    ∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ρ₁.comp (algebraMap EA₁ (Localization.AtPrime QA₁)) = ρ' := by
  intro T O A₁ EA₁ _ _ _ _ _ _ _ i₁ hi₁ hTO _ _ _ QA₁ _ jA₁ ρ' hX hret hρX hcong hker
  set L := Localization.AtPrime QA₁
  set I : Ideal O := Ideal.span {algebraMap (Polynomial T) O Polynomial.X}
  have hI : I ≤ maximalIdeal O := by
    rw [Ideal.span_le]; simpa using hX
  have hunit : ∀ y : QA₁.primeCompl, IsUnit (ρ' y) := by
    intro y
    by_contra hy
    have h1 : ρ' y ∈ maximalIdeal A₁ := (mem_maximalIdeal _).2 hy
    have h2 : algebraMap T O (i₁ (ρ' y)) ∈ maximalIdeal O := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hy ((isUnit_map_iff i₁ _).1 ((isUnit_map_iff (algebraMap T O) _).1 hu))
    have h3 : jA₁ (algebraMap EA₁ L y) ∈ maximalIdeal O := by
      have := hI (hcong y)
      have := (maximalIdeal O).sub_mem h2 this
      simpa using this
    have h4 : IsUnit (jA₁ (algebraMap EA₁ L y)) :=
      (IsLocalization.map_units L y).map jA₁
    exact (mem_maximalIdeal _ |>.1 h3) h4
  let ρ₁ : L →+* A₁ := IsLocalization.lift (M := QA₁.primeCompl) hunit
  have hcomp : ρ₁.comp (algebraMap EA₁ L) = ρ' := by
    ext x; exact IsLocalization.lift_eq _ _
  refine ⟨ρ₁, ⟨?_, ?_, ?_⟩, hcomp⟩
  · rw [IsScalarTower.algebraMap_eq A₁ EA₁ L, ← RingHom.comp_assoc, hcomp, hret]
  · apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker] at hz
      obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective QA₁.primeCompl z
      dsimp only at hz ⊢
      have hx : ρ' x = 0 := by
        have := IsLocalization.lift_mk' (M := QA₁.primeCompl) (S := L) hunit x y
        change ρ₁ _ = _ at this
        rw [hz] at this
        exact (Units.mul_left_eq_zero _).1 this.symm
      obtain ⟨s, hs, hsx⟩ := hker x hx
      have hsy : s * (y : EA₁) ∈ QA₁.primeCompl := QA₁.primeCompl.mul_mem hs y.2
      have heq : IsLocalization.mk' L x y = IsLocalization.mk' L (s * x) (⟨s * y, hsy⟩ : QA₁.primeCompl) := by
        rw [IsLocalization.mk'_eq_iff_eq]
        simp only
        ring_nf
      rw [heq, IsLocalization.mk'_eq_mul_mk'_one]
      apply Ideal.mul_mem_right
      have : algebraMap EA₁ L (s * x) ∈ (Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}).map (algebraMap EA₁ L) :=
        Ideal.mem_map_of_mem _ hsx
      rwa [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply] at this
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
        IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ L]
      change (ρ₁.comp (algebraMap EA₁ L)) _ = 0
      rw [hcomp, hρX]
  · have key : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp ρ₁)) = (Ideal.Quotient.mk I).comp jA₁ := by
      apply IsLocalization.ringHom_ext QA₁.primeCompl
      ext x
      simp only [RingHom.comp_apply]
      rw [Ideal.Quotient.eq]
      have := hcong x
      rw [← hcomp] at this
      simpa using this
    intro x
    have := congrArg (fun f => f x) key
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.1 this

end GlobalTheory.KeyOriginEnlargeLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerOneHolds
section
noncomputable section

open Complex DirichletCharacter

namespace GlobalTheory.LogDerOneProof

theorem logDerOne_holds : GlobalTheory.Mem.An.LogDerOne := by
  classical
  obtain ⟨C, hC, H⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  refine ⟨2 * C, fun q _ χ hq hp => ?_⟩
  have hne : χ ≠ 1 := by
    intro h
    have h1 : χ.conductor = q := hp
    rw [h, DirichletCharacter.conductor_one] at h1
    omega
  have hL : LFunction χ 1 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simp)
  obtain ⟨hfin, hcount, hmain⟩ := H q χ hne 1 (by norm_num) (by norm_num) hL
  simp only [Complex.one_im, abs_zero, zero_add, Complex.ofReal_zero, zero_mul, add_zero] at hfin hcount hmain
  set D : Set ℂ := {w : ℂ | ‖w - 2‖ ≤ 7 / 2 ∧ LFunction χ w = 0} with hD
  set Z : Set ℂ := GlobalTheory.Mem.An.zerosIn χ 0 1 with hZ
  have hsub : Z ⊆ D := by
    rintro w ⟨h0, h1, h2, h3⟩
    refine ⟨?_, h3⟩
    have h4 := Complex.norm_le_abs_re_add_abs_im (w - 2)
    simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero] at h4 h2
    have h5 : |w.re - 2| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hZfin : Z.Finite := hfin.subset hsub
  have hsub' : hZfin.toFinset ⊆ hfin.toFinset := by
    intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    exact hsub hw
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hcount hmain
  have hz : GlobalTheory.Mem.An.zsum χ 0 1 (fun ρ => 1 / (1 - ρ)) =
      ∑ w ∈ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w) := by
    unfold GlobalTheory.Mem.An.zsum
    rw [← hZ, finsum_mem_eq_finite_toFinset_sum _ hZfin]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [GlobalTheory.Mem.An.zmult]
    ring
  rw [hz]
  rw [← Finset.sum_sdiff hsub'] at hmain
  have hrest : ‖∑ w ∈ hfin.toFinset \ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)‖ ≤
      ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun w hw => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => Nat.cast_nonneg _))
    simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset] at hw
    obtain ⟨⟨_, hw0⟩, hwn⟩ := hw
    have hre : w.re < 1 := by
      by_contra h
      exact LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (not_lt.1 h) hw0
    have h1 : 1 ≤ ‖1 - w‖ := by
      by_cases h0 : 0 < w.re
      · have him : 1 < |w.im| := by
          by_contra h
          exact hwn ⟨h0, hre, by simpa using not_lt.1 h, hw0⟩
        have h4 := Complex.abs_im_le_norm (1 - w)
        simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h4
        linarith
      · have h4 := Complex.re_le_norm (1 - w)
        simp only [Complex.sub_re, Complex.one_re] at h4
        linarith [not_lt.1 h0]
    rw [norm_div, Complex.norm_natCast]
    exact div_le_self (Nat.cast_nonneg _) h1
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log (q * 2) ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
  have hl2 : C * Real.log (q * 2) ≤ C * Real.log (3 * q) := mul_le_mul_of_nonneg_left hlog hC.le
  set A := deriv (LFunction χ) 1 / LFunction χ 1
  set R := ∑ w ∈ hfin.toFinset \ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)
  set S := ∑ w ∈ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)
  have e : A - S = (A - (R + S)) + R := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith

end GlobalTheory.LogDerOneProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ManyIndependentProductsInFunctionField
section
open Filter Topology

namespace GlobalTheory

theorem prod_mem_span_range_prod_mul {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type*} [Fintype J] (g : J → A) (m : ℕ) (f : Fin m → A)
    (hf : ∀ l, f l ∈ Submodule.span R (Set.range g)) (y : A) :
    (∏ l, f l) * y ∈
      Submodule.span R (Set.range fun u : Fin m → J => (∏ l, g (u l)) * y) := by
  choose c hc using fun l => (Submodule.mem_span_range_iff_exists_fun R).1 (hf l)
  have h : (∏ l, f l) * y = ∑ u : Fin m → J, (∏ l, c l (u l)) • ((∏ l, g (u l)) * y) := by
    simp_rw [← hc, Fintype.prod_sum, Finset.sum_mul, Algebra.smul_def, Finset.prod_mul_distrib,
      map_prod, mul_assoc]
  rw [h]
  exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩)

theorem many_independent_products_in_function_field : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ)
    (x : Fin D → K), IsTranscendenceBasis ℤ x → ∀ (J : Type) [Fintype J] (e : J → K),
    LinearIndependent ℤ e → ∀ m : ℕ, 0 < m → ∃ v : Fin (Fintype.card J * m ^ D) → K,
    LinearIndependent ℤ v ∧ ∀ s, ∃ (u : Fin m → J) (a : Fin D → ℕ), (∀ i, a i < m) ∧
      v s = (∏ l, e (u l)) * ∏ i, x i ^ a i := by
  intro K _ _ D x hx J _ e he m hm
  haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hxQ : IsTranscendenceBasis ℚ x := (Algebra.IsAlgebraic.isTranscendenceBasis_iff ℤ ℚ).1 hx
  have heQ : LinearIndependent ℚ e := (LinearIndependent.iff_fractionRing ℤ ℚ).1 he
  obtain ⟨P, ψ, g, c, hPm, hψ, hψx, hg, hge, hsep⟩ := _root_.GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization K D x hxQ J e
  choose e' he' using fun j => (AlgHom.mem_range ψ).1 (hge j)
  have he'Q : LinearIndependent ℚ e' := by
    have h1 : LinearIndependent ℚ (fun j => g * e j) := by
      refine heQ.map' (LinearMap.mulLeft ℚ g) (LinearMap.ker_eq_bot.2 ?_)
      exact mul_right_injective₀ hg
    have h2 : (ψ.toLinearMap ∘ e') = fun j => g * e j := funext he'
    exact LinearIndependent.of_comp ψ.toLinearMap (h2 ▸ h1)
  obtain ⟨τ, hτX, hτq, hτind⟩ := _root_.GlobalTheory.adjoinRoot_map_complex_linearIndependent D P hPm
  have hPCm : (P.map (MvPolynomial.map (algebraMap ℚ ℂ))).Monic := hPm.map _
  have hsepC : ((P.map (MvPolynomial.map (algebraMap ℚ ℂ))).map
      (MvPolynomial.eval (fun i => (c i : ℂ)))).Separable := by
    have h : (P.map (MvPolynomial.map (algebraMap ℚ ℂ))).map (MvPolynomial.eval (fun i => (c i : ℂ))) =
        (P.map (MvPolynomial.eval c)).map (algebraMap ℚ ℂ) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      ext <;> simp
    rw [h]; exact hsep.map
  let PC := P.map (MvPolynomial.map (algebraMap ℚ ℂ))
  obtain ⟨n, φ, hφinj, hφX⟩ := _root_.GlobalTheory.branches_of_unramified_point D PC (fun i => (c i : ℂ)) hPCm hsepC
  let w : (Fin m → J) × (Fin D → Fin m) → AdjoinRoot P := fun ub =>
    (∏ l, e' (ub.1 l)) * ∏ i, AdjoinRoot.of P (MvPolynomial.X i) ^ (ub.2 i : ℕ)
  obtain ⟨κ, a, ha, hspan, hind⟩ := exists_linearIndependent' ℚ w
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  let xC : Fin D → AdjoinRoot PC := fun i => AdjoinRoot.of PC (MvPolynomial.X i)
  let F : Submodule ℂ (AdjoinRoot PC) := Submodule.span ℂ (Set.range fun j => τ (e' j))
  let G : Submodule ℂ (AdjoinRoot PC) := Submodule.span ℂ (Set.range fun k => τ (w (a k)))
  haveI : Module.Finite ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : Module.Finite ℂ G := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hτspan : ∀ u ∈ Submodule.span ℚ (Set.range (w ∘ a)), τ u ∈ G := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact G.add_mem hy hz
    | smul q y _ hy => rw [hτq]; exact G.smul_mem _ hy
  have key := _root_.GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries D n (AdjoinRoot PC) φ xC (fun i => (c i : ℂ)) hφinj hφX F G m hm (by
    intro f b hf hb
    have h1 := prod_mem_span_range_prod_mul (R := ℂ) (fun j => τ (e' j)) m f hf (∏ i, xC i ^ b i)
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨u, rfl⟩
    have hw : w (u, fun i => ⟨b i, hb i⟩) ∈ Submodule.span ℚ (Set.range (w ∘ a)) := by
      rw [hspan]; exact Submodule.subset_span ⟨_, rfl⟩
    have h2 := hτspan _ hw
    simpa [w, map_prod, map_mul, map_pow, hτX, xC] using h2)
  have hFr : Module.finrank ℂ F = Fintype.card J := finrank_span_eq_card (hτind J e' he'Q)
  have hGr : Module.finrank ℂ G ≤ Fintype.card κ := finrank_range_le_card _
  let L : AdjoinRoot P →ₗ[ℚ] K := (LinearMap.mulLeft ℚ ((g ^ m)⁻¹)).comp ψ.toLinearMap
  have hL : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot.2 ?_
    show Function.Injective (fun u => (g ^ m)⁻¹ * ψ u)
    exact (mul_right_injective₀ (inv_ne_zero (pow_ne_zero _ hg))).comp hψ
  have hindK : LinearIndependent ℚ (L ∘ (w ∘ a)) := hind.map' L hL
  have hcard : Fintype.card J * m ^ D ≤ Fintype.card κ := hFr ▸ (key.trans hGr)
  let emb : Fin (Fintype.card J * m ^ D) ↪ κ :=
    (Fin.castLEEmb hcard).trans (Fintype.equivFin κ).symm.toEmbedding
  refine ⟨L ∘ (w ∘ a) ∘ emb, ?_, ?_⟩
  · exact (hindK.comp emb emb.injective).restrict_scalars' ℤ
  · intro s
    refine ⟨(a (emb s)).1, fun i => ((a (emb s)).2 i : ℕ), fun i => ((a (emb s)).2 i).isLt, ?_⟩
    simp only [Function.comp_apply, L, w, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.mulLeft_apply, map_mul, map_prod, map_pow, hψx, he', Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapEisensteinDivPeriod
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem E₄_div_period_eq {Λ : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf Λ c τ) (Ω : ℂ) :
    E₄ τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 4 = 12 * (Λ.g₂ / Ω ^ 4) := by
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ^ 4 = 16 * (Real.pi : ℂ) ^ 4 := by
    rw [mul_pow, Complex.I_pow_four]; ring
  rw [ReciprocityTheory.ChartRestriction.L1.g₂_eq h, div_pow, hI, div_div_eq_mul_div, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem E₆_div_period_eq {Λ : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf Λ c τ) (Ω : ℂ) :
    E₆ τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 6 = -(216 * (Λ.g₃ / Ω ^ 6)) := by
  have h6 : Complex.I ^ 6 = -1 := by
    rw [show 6 = 4 + 2 from rfl, pow_add, Complex.I_pow_four, Complex.I_sq, one_mul]
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ^ 6 = -(64 * (Real.pi : ℂ) ^ 6) := by
    rw [mul_pow, h6]; ring
  rw [ReciprocityTheory.ChartRestriction.L1.g₃_eq h, div_pow, hI, div_div_eq_mul_div, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem map_E₄_div_period (g : ℂ ≃+* ℂ) {Λ₀ Λ₁ : PeriodPair} {c₀ c₁ Ω₀ Ω₁ : ℂ} {τ₀ τ₁ : ℍ}
    (h₀ : IsTauOf Λ₀ c₀ τ₀) (h₁ : IsTauOf Λ₁ c₁ τ₁)
    (h : g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4) :
    g (E₄ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 4)
      = E₄ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 4 := by
  rw [E₄_div_period_eq h₀, E₄_div_period_eq h₁, map_mul, h, map_ofNat]

theorem map_E₆_div_period (g : ℂ ≃+* ℂ) {Λ₀ Λ₁ : PeriodPair} {c₀ c₁ Ω₀ Ω₁ : ℂ} {τ₀ τ₁ : ℍ}
    (h₀ : IsTauOf Λ₀ c₀ τ₀) (h₁ : IsTauOf Λ₁ c₁ τ₁)
    (h : g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6) :
    g (E₆ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 6)
      = E₆ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 6 := by
  rw [E₆_div_period_eq h₀, E₆_div_period_eq h₁, map_neg, map_mul, h, map_ofNat]

theorem map_eisenstein_div_period :
    ∀ (g : ℂ ≃+* ℂ) (Λ₀ Λ₁ : PeriodPair) (c₀ c₁ Ω₀ Ω₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4 → g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6 → g (E₄ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 4) = E₄ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 4 ∧ g (E₆ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 6) = E₆ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 6 :=
  fun g _ _ _ _ _ _ _ _ h₀ h₁ h₂ h₃ =>
    ⟨map_E₄_div_period g h₀ h₁ h₂, map_E₆_div_period g h₀ h₁ h₃⟩

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLinearEquivAddHaarLocalField
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped NNReal ENNReal

namespace GlobalTheory.KSp

theorem map_linearEquiv_haar : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (T : V ≃ₗ[F] V), μ.map T = (distribHaarChar F (LinearEquiv.det T))⁻¹ • μ := by
  intro F _ _ _ _ _ V _ _ _ _ _ _ _ μ _ T
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable F
  haveI := GlobalTheory.SplitWeil.t2Space F
  set n := Module.finrank F V
  set b := Module.finBasis F V
  set e : V ≃ₗ[F] (Fin n → F) := b.equivFun
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup F V
  have hec : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hes : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

  let E : V ≃L[F] (Fin n → F) := { e with continuous_toFun := hec, continuous_invFun := hes }
  let Em : V ≃ᵐ (Fin n → F) := E.toHomeomorph.toMeasurableEquiv
  have hEm : (Em : V → Fin n → F) = e := rfl
  have hEms : (Em.symm : (Fin n → F) → V) = e.symm := rfl
  let P : Measure (Fin n → F) := Measure.pi fun _ => (Measure.addHaar : Measure F)
  set X := μ.map Em with hX
  haveI : X.IsAddHaarMeasure := E.isAddHaarMeasure_map μ
  set M := LinearMap.toMatrix b b T.toLinearMap
  have hM : ∀ y, M.mulVec (e y) = e (T y) := fun y => by
    simp [M, e, LinearMap.toMatrix_mulVec_repr]
  have hdet : ((LinearEquiv.det T : Fˣ) : F) = M.det := by
    simp [M, LinearMap.det_toMatrix]
  set d := distribHaarChar F (LinearEquiv.det T)
  have key : (d : ℝ≥0∞) • P.map M.mulVec = P :=
    GlobalTheory.WeilM.smul_map_mulVec_pi (Measure.addHaar : Measure F) M (LinearEquiv.det T) hdet
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by simpa using (distribHaarChar_pos (A := F) (g := LinearEquiv.det T)).ne'
  have hPM : P.map M.mulVec = ((d⁻¹ : ℝ≥0) : ℝ≥0∞) • P := by
    conv_rhs => rw [← key]
    rw [smul_smul, ENNReal.coe_inv (by simpa using hd0), ENNReal.inv_mul_cancel hd0 ENNReal.coe_ne_top,
      one_smul]
  have hXP : X = (Measure.addHaarScalarFactor X P : ℝ≥0∞) • P := Measure.isAddLeftInvariant_eq_smul X P
  have hmv : Measurable M.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  have hXM : X.map M.mulVec = ((d⁻¹ : ℝ≥0) : ℝ≥0∞) • X := by
    rw [hXP, Measure.map_smul _ hmv.aemeasurable, hPM, smul_comm]
  have hμ : μ = X.map Em.symm := by rw [hX, Measure.map_map Em.symm.measurable Em.measurable]; simp
  have hcomp : (T : V → V) ∘ Em.symm = Em.symm ∘ M.mulVec := by
    funext x
    show T (e.symm x) = e.symm (M.mulVec x)
    apply e.injective
    rw [← hM, e.apply_symm_apply, e.apply_symm_apply]
  have hTm : Measurable (T : V → V) := by
    have : Continuous (T : V → V) := IsModuleTopology.continuous_of_linearMap T.toLinearMap
    exact this.measurable
  calc μ.map T = (X.map Em.symm).map T := by rw [← hμ]
    _ = X.map ((T : V → V) ∘ Em.symm) := Measure.map_map hTm Em.symm.measurable
    _ = X.map (Em.symm ∘ M.mulVec) := by rw [hcomp]
    _ = (X.map M.mulVec).map Em.symm := (Measure.map_map Em.symm.measurable hmv).symm
    _ = (d⁻¹ : ℝ≥0) • μ := by rw [hXM, Measure.map_smul _ Em.symm.measurable.aemeasurable, ← hμ]; rfl

end GlobalTheory.KSp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularFormPolynomialE4E6
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam


open ReciprocityTheory.PGsh in
theorem isMF_eq_sum_monomials :
    ∀ (w : ℕ) (F : ℍ → ℂ), IsMF w F → ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ),
      (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
        ∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  intro w F hF
  obtain ⟨g, hg⟩ := hF
  have hm := coe_mem_monoSpanF w g
  rw [monoSpanF, Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨(monoIdx w).image fun a => (a, monoB w a),
    fun p => if h : p.1 ∈ monoIdx w then c ⟨p.1, h⟩ else 0, ?_, fun τ => ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact monoIdx_wt ha
  · rw [Finset.sum_image (fun a _ b _ h => congrArg Prod.fst h), ← hg τ, ← hc,
      Finset.sum_apply, ← Finset.sum_coe_sort (monoIdx w)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coe_monoW a.2]
    simp [a.2]

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgCStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed : ∀ (D : Type) [CommRing D] [IsDomain D], AIC D ↔ (IsIntegrallyClosed D ∧ IsAlgClosed (FractionRing D)) := by
  first | (exact @GlobalTheory.AICIff.aic_iff) | (exact GlobalTheory.AICIff.aic_iff) | (intros; apply GlobalTheory.AICIff.aic_iff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLinearEquivOfPiFinPowFiniteStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_linearEquiv_of_pi_fin_pow_finite : ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M] [AddCommGroup N] [Module R N] [Finite N] (l : ℕ), 0 < l → Nonempty ((Fin l → M) ≃ₗ[R] (Fin l → N)) → Nonempty (M ≃ₗ[R] N) := by
  first | (exact @GlobalTheory.PowCancel.cancel_pow) | (exact GlobalTheory.PowCancel.cancel_pow) | (intros; apply GlobalTheory.PowCancel.cancel_pow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdL
section
namespace GlobalTheory.DiagVol

def ordL {n : Type*} (c : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => c + 1) (fun i => 2 * (i.val + 1))

end GlobalTheory.DiagVol
end

