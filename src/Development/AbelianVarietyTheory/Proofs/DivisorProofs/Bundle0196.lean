module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.WeightedHomogeneousComponentMemElimIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosedStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ b c : B, b * c - 1 ∈ Ideal.span {f} → ∃ r : B, b - r ^ q ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.exists_pow_sub_mem_span_of_isUnit_mod_of_isAlgClosed) | (exact GlobalTheory.exists_pow_sub_mem_span_of_isUnit_mod_of_isAlgClosed) | (intros; apply GlobalTheory.exists_pow_sub_mem_span_of_isUnit_mod_of_isAlgClosed  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotMemForallGtEqMaximalIdealStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_not_mem_forall_gt_eq_maximalIdeal' : ∀ (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C] (x : C), x ≠ 0 → x ∈ maximalIdeal C → ∃ q : Ideal C, q.IsPrime ∧ x ∉ q ∧ ∀ P : Ideal C, P.IsPrime → q < P → P = maximalIdeal C := by
  first | exact @GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal | exact GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal | (intros; apply GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeSaturationGenericHyperplaneSection
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.Chow

theorem exists_mul_pow_mem_incidenceIdeal_of_generic {σ β K F : Type*} [Fintype σ] [CommRing K]
    [Field F] [Algebra K F]
    {p : Ideal (MvPolynomial σ K)} {ξ : σ → F} (hξ : ∀ g, aeval ξ g = 0 ↔ g ∈ p)
    {h : MvPolynomial (β × σ) (MvPolynomial σ K)}
    (hf : map (aeval ξ : MvPolynomial σ K →ₐ[K] F).toRingHom h ∈
      Ideal.span (Set.range (linForm ξ : β → _))) (j : σ) :
    ∃ m : ℕ, h * C (X j ^ m) ∈ incidenceIdeal (β := β) p := by
  let φ : MvPolynomial σ K →+* F := (aeval ξ : MvPolynomial σ K →ₐ[K] F).toRingHom
  have hφ : (fun j => φ (X j)) = ξ := by ext j; simp [φ]
  by_cases hj : ξ j = 0
  · exact ⟨1, Ideal.mul_mem_left _ _ (C_mem_incidenceIdeal (by
      rw [pow_one, ← hξ, aeval_X, hj]))⟩
  obtain ⟨m, g, hg⟩ := exists_pow_mul_sub_rename_mem (X : σ → MvPolynomial σ K) j h
  refine ⟨m, ?_⟩
  have h1 := map_mem_span_linForm φ hg
  rw [hφ, map_sub, map_mul, map_rename] at h1
  have h2 : rename Subtype.val (map φ g) ∈ Ideal.span (Set.range (linForm ξ : β → _)) := by
    have := Ideal.sub_mem _ (Ideal.mul_mem_right (map φ (C (X j ^ m))) _ hf) h1
    rwa [sub_sub_cancel] at this
  rw [← Set.image_univ, ← ker_linFormElim ξ (Ne.isUnit hj), RingHom.mem_ker,
    linFormElim_rename, ← RingHom.mem_ker, MvPolynomial.ker_map] at h2
  have hker : RingHom.ker φ = p := Ideal.ext fun g => hξ g
  rw [hker] at h2
  have h3 : rename Subtype.val g ∈ p.map (C : _ →+* MvPolynomial (β × σ) (MvPolynomial σ K)) := by
    rw [← Ideal.mem_comap (f := (rename Subtype.val : _ →ₐ[MvPolynomial σ K] _))]
    refine Ideal.map_le_iff_le_comap.2 (fun a ha => ?_) h2
    simpa [Ideal.mem_comap] using Ideal.mem_map_of_mem _ ha
  have := Ideal.add_mem _ (Ideal.mem_sup_right (S := p.map C) hg) (Ideal.mem_sup_left h3)
  rwa [sub_add_cancel] at this

theorem exists_field_generic_point {σ K : Type} [CommRing K] {p : Ideal (MvPolynomial σ K)}
    [p.IsPrime] (hp : ∃ j, X j ∉ p) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (ξ : σ → F),
      (∀ g, aeval ξ g = 0 ↔ g ∈ p) ∧ ξ ≠ 0 :=
  ⟨FractionRing (MvPolynomial σ K ⧸ p), inferInstance, inferInstance, genericPoint p,
    aeval_genericPoint_eq_zero_iff p, genericPoint_ne_zero hp⟩

theorem eq_zero_of_mem_elimIdeal_of_forall_meets {K : Type} [Field K] {N : ℕ}
    {P : Ideal (MvPolynomial (Fin N) K)}
    (hP : ∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K,
      y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0)
    {f : MvPolynomial (Unit × Fin N) K} (hf : f ∈ elimIdeal (β := Unit) P) : f = 0 := by
  apply map_injective (algebraMap K (AlgebraicClosure K)) (algebraMap K _).injective
  rw [map_zero]
  apply MvPolynomial.funext
  intro t
  obtain ⟨y, hy, hyP, hs⟩ := hP (fun j => t ((), j))
  have := aeval_eq_zero_of_mem_elimIdeal (β := Unit) hyP hy (t := t) (fun _ => hs) hf
  rw [map_zero, eval_map, ← aeval_def, this]

theorem exists_prime_saturation_generic_section (K L : Type) [Field K] [Field L] (N : ℕ)
    [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L]
    [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L]
    (P : Ideal (MvPolynomial (Fin N) K)) (hprime : P.IsPrime)
    (hP : ∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K,
      y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0) :
    ∃ Q : Ideal (MvPolynomial (Fin N) L), Q.IsPrime ∧
      P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)} ≤ Q ∧
      ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈
        P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)} := by
  classical
  have hex : ∃ j, X j ∉ P := by
    obtain ⟨y, hy, hyP, -⟩ := hP 0
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
    exact ⟨j, fun h => hj (by simpa using hyP _ h)⟩
  obtain ⟨F, _, _, ξ, hξ, hne⟩ : ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (ξ : Fin N → F),
      (∀ g, aeval ξ g = 0 ↔ g ∈ P) ∧ ξ ≠ 0 :=
    exists_field_generic_point hex
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hne
  have hq := isPrime_span_linForm (ι := Unit) ξ (Ne.isUnit hj₀) Set.univ
  rw [Set.image_univ] at hq
  set q : Ideal (MvPolynomial (Unit × Fin N) F) :=
    Ideal.span (Set.range (linForm ξ : Unit → _)) with hqdef
  obtain ⟨Ω, _, π, hπ⟩ : ∃ (Ω : Type) (_ : Field Ω) (π : MvPolynomial (Unit × Fin N) F →+* Ω),
      ∀ a, π a = 0 ↔ a ∈ q := by
    refine ⟨FractionRing (MvPolynomial (Unit × Fin N) F ⧸ q), inferInstance,
      (algebraMap (MvPolynomial (Unit × Fin N) F ⧸ q) _).comp (Ideal.Quotient.mk q), fun a => ?_⟩
    rw [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let ρ : MvPolynomial (Fin N) K →+* MvPolynomial (Unit × Fin N) K :=
    (rename (fun j => ((), j)) : _ →ₐ[K] _).toRingHom
  let θ : MvPolynomial (Fin N) K →+* Ω := π.comp ((map (algebraMap K F)).comp ρ)
  have hθ : Function.Injective θ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : ρ a ∈ elimIdeal (β := Unit) P :=
      (mem_elimIdeal_iff_of_generic hξ hne).2 ((hπ _).1 ha)
    have h2 := eq_zero_of_mem_elimIdeal_of_forall_meets hP h1
    apply rename_injective (fun j : Fin N => ((), j)) (fun _ _ h => (Prod.ext_iff.1 h).2)
    rw [map_zero]
    exact h2
  let θL : L →+* Ω := IsFractionRing.lift hθ
  have hθL (a) : θL (algebraMap _ L a) = θ a := IsFractionRing.lift_algebraMap hθ a
  have hθK (a : K) : θL (algebraMap K L a) = π (C (algebraMap K F a)) := by
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L, hθL]
    simp [θ, ρ]
  let ev : MvPolynomial (Fin N) L →+* Ω := eval₂Hom θL (fun j => π (C (ξ j)))
  let Ψ : MvPolynomial (Unit × Fin N) (MvPolynomial (Fin N) K) →+* MvPolynomial (Fin N) L :=
    eval₂Hom (map (algebraMap K L))
      (fun v => C (algebraMap (MvPolynomial (Fin N) K) L (X v.2)))
  let φ : MvPolynomial (Fin N) K →+* F := (aeval ξ : MvPolynomial (Fin N) K →ₐ[K] F).toRingHom
  have hcomp : ev.comp Ψ = π.comp (map φ) := by
    ext a
    · simp [ev, Ψ, φ, hθK]
    · simp [ev, Ψ, φ]
    · simp [ev, Ψ, φ, hθL, θ, ρ]
  have hcomp' (h) : ev (Ψ h) = π (map φ h) := DFunLike.congr_fun hcomp h
  have hΨC (a) : Ψ (C a) = map (algebraMap K L) a := by simp [Ψ]
  have hΨL : Ψ (genericForm (K := K) (σ := Fin N) ()) =
      ∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [genericForm_eq, map_sum]
    exact Finset.sum_congr rfl fun j _ => by simp [Ψ, mul_comm]
  have hΨc (c : MvPolynomial (Fin N) K) : Ψ (map C (ρ c)) = C (algebraMap _ L c) := by
    have : Ψ.comp ((map C).comp ρ) = C.comp (algebraMap _ L) := by
      ext a
      · simp [Ψ, ρ, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L]
      · simp [Ψ, ρ]
    exact DFunLike.congr_fun this c
  have hden (g : MvPolynomial (Fin N) L) : ∃ c : MvPolynomial (Fin N) K, c ≠ 0 ∧
      ∃ h, Ψ h = C (algebraMap _ L c) * g := by
    induction g using MvPolynomial.induction_on with
    | C a =>
      obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin N) K) a
      have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
      refine ⟨y, hy0, map C (ρ x), ?_⟩
      have : algebraMap _ L y ≠ 0 := by
        simpa using hy0
      rw [hΨc, ← C_mul, mul_div_cancel₀ _ this]
    | add f g hf hg =>
      obtain ⟨c, hc, h, hh⟩ := hf
      obtain ⟨d, hd, k, hk⟩ := hg
      refine ⟨c * d, mul_ne_zero hc hd, map C (ρ d) * h + map C (ρ c) * k, ?_⟩
      rw [map_add (f := _), map_mul, map_mul, hΨc, hΨc, hh, hk, map_mul, map_mul]
      ring
    | mul_X f v hf =>
      obtain ⟨c, hc, h, hh⟩ := hf
      refine ⟨c, hc, h * C (X v), ?_⟩
      rw [map_mul, hh, hΨC, map_X, mul_assoc]
  refine ⟨RingHom.ker ev, RingHom.ker_isPrime ev, ?_, ?_⟩
  · refine sup_le (Ideal.map_le_iff_le_comap.2 fun g hg => ?_) ?_
    · rw [Ideal.mem_comap, RingHom.mem_ker, ← hΨC, hcomp', map_C]
      have : φ g = 0 := (hξ g).2 hg
      rw [this, map_zero, map_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, ← hΨL,
        hcomp', hπ, genericForm, map_linForm]
      have hφ : (fun j => φ (X j)) = ξ := by ext j; simp [φ]
      rw [hφ]
      exact Ideal.subset_span ⟨(), rfl⟩
  · intro g hg j
    obtain ⟨c, hc, h, hh⟩ := hden g
    have h1 : map φ h ∈ q := by
      rw [← hπ, ← hcomp', hh, map_mul, (RingHom.mem_ker.1 hg), mul_zero]
    obtain ⟨m, hm⟩ := exists_mul_pow_mem_incidenceIdeal_of_generic hξ h1 j
    refine ⟨m, ?_⟩
    have hle : incidenceIdeal (β := Unit) P ≤ Ideal.comap Ψ
        (P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)}) := by
      refine incidenceIdeal_le.2 ⟨fun a ha => ?_, fun i => ?_⟩
      · rw [Ideal.mem_comap, hΨC]
        exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)
      · rw [Ideal.mem_comap, hΨL]
        exact Ideal.mem_sup_right (Ideal.subset_span rfl)
    have h2 := hle hm
    rw [Ideal.mem_comap, map_mul, hh, hΨC, map_pow, map_X] at h2
    have hcL : algebraMap _ L c ≠ 0 := by simpa using hc
    have h3 := Ideal.mul_mem_left _ (C (algebraMap _ L c)⁻¹) h2
    convert h3 using 1
    rw [mul_assoc, ← mul_assoc (C _) (C _), ← C_mul, inv_mul_cancel₀ hcL, C_1, one_mul, mul_comm]

end GlobalTheory.Chow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveElementSeparabilityCertificateStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_element_separability_certificate : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F), IsTranscendenceBasis k ((↑) : s → F) → Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F → ∀ T : Finset F, ∃ θ : F, IsIntegral (Algebra.adjoin k (s : Set F)) θ ∧ ∃ H : Algebra.adjoin k (s : Set F), H ≠ 0 ∧ ∃ U V : Polynomial (Algebra.adjoin k (s : Set F)), U * minpoly (Algebra.adjoin k (s : Set F)) θ + V * Polynomial.derivative (minpoly (Algebra.adjoin k (s : Set F)) θ) = Polynomial.C H ∧ ∀ x ∈ T, (H : F) * x ∈ Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)) := by
  first | exact @GlobalTheory.SepPoint.exists_primitive_sep_certificate | exact GlobalTheory.SepPoint.exists_primitive_sep_certificate | (intros; apply GlobalTheory.SepPoint.exists_primitive_sep_certificate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularNearOfRegularQuotientPrime
section
open IsLocalRing TensorProduct

namespace GlobalTheory.RegularAscent

open IsLocalRing TensorProduct in
private lemma spanFinrank_maximalIdeal_le_add (A : Type) [CommRing A] [IsLocalRing A]
    (J : Ideal A) [IsLocalRing (A ⧸ J)] (hJ : J.FG) (hm : (maximalIdeal (A ⧸ J)).FG) :
    (maximalIdeal A).spanFinrank ≤ J.spanFinrank + (maximalIdeal (A ⧸ J)).spanFinrank := by
  classical
  obtain ⟨T, hTc, hT⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hJ
  obtain ⟨U, hUc, hU⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hm
  let L : Finset A := U.image Quotient.out
  have hJm : J ≤ maximalIdeal A := by
    refine le_maximalIdeal fun h => ?_
    have : Subsingleton (A ⧸ J) := Ideal.Quotient.subsingleton_iff.mpr h
    exact not_subsingleton (A ⧸ J) this
  have hL : ∀ l ∈ L, l ∈ maximalIdeal A := by
    intro l hl
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
    have hu' : u ∈ maximalIdeal (A ⧸ J) := hU ▸ Ideal.subset_span hu
    intro hunit
    apply hu'
    have := hunit.map (Ideal.Quotient.mk J)
    rwa [Ideal.Quotient.mk_out] at this
  have hspan : maximalIdeal A = Ideal.span (↑(T ∪ L) : Set A) := by
    apply le_antisymm
    · intro x hx
      have hx' : Ideal.Quotient.mk J x ∈ Ideal.span (Ideal.Quotient.mk J '' (L : Set A)) := by
        have e : Ideal.Quotient.mk J '' (L : Set A) = (U : Set (A ⧸ J)) := by
          ext u; simp [L, Ideal.Quotient.mk_out]
        rw [e]
        change _ ∈ Submodule.span (A ⧸ J) _
        rw [hU]
        intro hunit
        obtain ⟨y, hy⟩ := hunit.exists_right_inv
        obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
        have h1 : x * y' - 1 ∈ J := Ideal.Quotient.eq.mp (by simpa using hy)
        apply (maximalIdeal.isMaximal A).ne_top
        rw [Ideal.eq_top_iff_one]
        simpa using Ideal.sub_mem _ (Ideal.mul_mem_right y' _ hx) (hJm h1)
      rw [← Ideal.map_span] at hx'
      obtain ⟨y, hy, hyx⟩ := Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective |>.mp hx'
      have hxy : x - y ∈ J := by
        rw [← Ideal.Quotient.eq]; exact hyx.symm
      rw [← hT] at hxy
      rw [Finset.coe_union, Ideal.span_union]
      have := Submodule.add_mem_sup hxy hy
      simpa using this
    · rw [Ideal.span_le]
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hJm (hT ▸ Ideal.subset_span hx)
      · exact hL x hx
  calc (maximalIdeal A).spanFinrank ≤ (T ∪ L).card := hspan ▸ _root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le _
    _ ≤ T.card + L.card := Finset.card_union_le _ _
    _ ≤ J.spanFinrank + (maximalIdeal (A ⧸ J)).spanFinrank := by
        rw [hTc, ← hUc]; gcongr; exact Finset.card_image_le

open IsLocalRing TensorProduct in
private lemma height_add_ringKrullDim_quotient_le' (A : Type) [CommRing A] (I : Ideal A)
    [I.IsPrime] : (I.height : WithBot ℕ∞) + ringKrullDim (A ⧸ I) ≤ ringKrullDim A := by
  let P : PrimeSpectrum A := ⟨I, inferInstance⟩
  have h1 : I.height = Order.height P := PrimeSpectrum.height_eq_orderHeight P
  have h2 : ringKrullDim (A ⧸ I) = (Order.coheight P : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
    rfl
  have : Nonempty (PrimeSpectrum A) := ⟨P⟩
  rw [h1, h2, ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  norm_cast
  exact le_iSup (fun a : PrimeSpectrum A => Order.height a + Order.coheight a) P


open IsLocalRing TensorProduct in
theorem _root_.GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient (B : Type) [CommRing B]
    [IsNoetherianRing B] (p : Ideal B) [p.IsPrime]
    (hp : IsRegularLocalRing (Localization.AtPrime p)) :
    ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q →
      IsRegularLocalRing
        (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) →
      IsRegularLocalRing (Localization.AtPrime q) := by
  classical
  have hmfg : (maximalIdeal (Localization.AtPrime p)).FG := IsNoetherian.noetherian _
  obtain ⟨U, hUc, hU⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hmfg
  choose f hf using fun u : Localization.AtPrime p => IsLocalization.surj p.primeCompl u
  let T : Finset B := U.image fun u => (f u).1
  have hTp : ∀ t ∈ T, t ∈ p := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p, ← hf u]
    exact Ideal.mul_mem_right _ _ (hU ▸ Ideal.subset_span hu)
  have hTspan : p.map (algebraMap B (Localization.AtPrime p)) =
      Ideal.span (algebraMap B (Localization.AtPrime p) '' T) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [← hU]
      change Ideal.span _ ≤ _
      rw [Ideal.span_le]
      intro u hu
      have hunit := IsLocalization.map_units (Localization.AtPrime p) (f u).2
      have e : u = algebraMap B _ (f u).1 * ↑hunit.unit⁻¹ := by
        rw [Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec]; exact hf u
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨(f u).1, Finset.mem_image_of_mem _ hu, rfl⟩)
    · rw [Ideal.span_le]
      rintro _ ⟨t, ht, rfl⟩
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ (hTp t ht)
  obtain ⟨V, hV⟩ := (IsNoetherian.noetherian p : p.FG)
  have hc : ∀ v ∈ V, ∃ c ∈ p.primeCompl, c * v ∈ Ideal.span (T : Set B) := by
    intro v hv
    rw [← IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p),
      Ideal.map_span, ← hTspan]
    exact Ideal.mem_map_of_mem _ (hV ▸ Ideal.subset_span hv)
  choose! c hcp hcT using hc
  have hg : ∀ x ∈ p, (∏ v ∈ V, c v) * x ∈ Ideal.span (T : Set B) := by
    have : Ideal.span {∏ v ∈ V, c v} * p ≤ Ideal.span (T : Set B) := by
      rw [← hV, Ideal.span_mul_span', Ideal.span_le]
      rintro _ ⟨a, ha, v, hv, rfl⟩
      rw [Set.mem_singleton_iff.mp ha, ← Finset.prod_erase_mul V c hv]
      change (∏ x ∈ V.erase v, c x) * c v * v ∈ Ideal.span (T : Set B)
      rw [mul_assoc]
      exact Ideal.mul_mem_left _ _ (hcT v hv)
    exact Ideal.span_singleton_mul_le_iff.mp this
  refine ⟨∏ v ∈ V, c v, p.primeCompl.prod_mem fun v hv => hcp v hv, ?_⟩
  intro q _ hpq hgq hreg
  have hdisj : Disjoint (q.primeCompl : Set B) p :=
    Set.disjoint_left.mpr fun x hxq hxp => hxq (hpq hxp)
  have hI : p.map (algebraMap B (Localization.AtPrime q)) =
      Ideal.span (algebraMap B (Localization.AtPrime q) '' T) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hu : IsUnit (algebraMap B (Localization.AtPrime q) (∏ v ∈ V, c v)) :=
        IsLocalization.map_units (Localization.AtPrime q) (⟨_, hgq⟩ : q.primeCompl)
      have h2 : algebraMap B (Localization.AtPrime q) ((∏ v ∈ V, c v) * x) ∈
          Ideal.span (algebraMap B (Localization.AtPrime q) '' T) := by
        rw [← Ideal.map_span]; exact Ideal.mem_map_of_mem _ (hg x hx)
      rw [map_mul] at h2
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h2
    · rw [← Ideal.map_span]
      exact Ideal.map_mono (Ideal.span_le.mpr fun t ht => hTp t ht)
  have hIprime : (p.map (algebraMap B (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj
  have hIcard : (p.map (algebraMap B (Localization.AtPrime q))).spanFinrank ≤ T.card := by
    rw [hI, ← Finset.coe_image]
    exact (_root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le _).trans Finset.card_image_le
  have hTcard : (T.card : WithBot ℕ∞) ≤ (p.map (algebraMap B (Localization.AtPrime q))).height := by
    have h1 : (p.map (algebraMap B (Localization.AtPrime q))).height = p.height := by
      rw [← IsLocalization.height_under q.primeCompl,
        IsLocalization.under_map_of_isPrime_disjoint q.primeCompl _ ‹_› hdisj]
    have h2 : (p.height : WithBot ℕ∞) = (maximalIdeal (Localization.AtPrime p)).spanFinrank := by
      rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
        hp.spanFinrank_maximalIdeal]
    rw [h1, h2]
    exact_mod_cast (Finset.card_image_le.trans hUc.le)
  have := hreg.toIsLocalRing
  have hA := spanFinrank_maximalIdeal_le_add (Localization.AtPrime q)
    (p.map (algebraMap B (Localization.AtPrime q))) (IsNoetherian.noetherian _)
    (IsNoetherian.noetherian _)
  have hd := hreg.spanFinrank_maximalIdeal
  have hdim := height_add_ringKrullDim_quotient_le' (Localization.AtPrime q)
    (p.map (algebraMap B (Localization.AtPrime q)))
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc ((maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((T.card + (maximalIdeal (Localization.AtPrime q ⧸
          p.map (algebraMap B (Localization.AtPrime q)))).spanFinrank : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast hA.trans (by omega)
    _ = (T.card : WithBot ℕ∞) + ringKrullDim (Localization.AtPrime q ⧸
          p.map (algebraMap B (Localization.AtPrime q))) := by
        push_cast; rw [hd]
    _ ≤ (p.map (algebraMap B (Localization.AtPrime q))).height + ringKrullDim
          (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
        gcongr
    _ ≤ ringKrullDim (Localization.AtPrime q) := hdim

end GlobalTheory.RegularAscent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueIdempotentStatement
section
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_idempotent' : ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ] [Nontrivial Λ], ∃ x : Λ, x * x - x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) ∧ (∀ y : Λ, ∃ c : A, x * y * x - c • x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ)) ∧ ∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * x * b i - 1 ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) := by
  first | (exact @GlobalTheory.AzumayaResidue.exists_residue_idempotent) | (exact GlobalTheory.AzumayaResidue.exists_residue_idempotent) | (intros; apply GlobalTheory.AzumayaResidue.exists_residue_idempotent  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootOfUnitZeroDimensionalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_root_of_unit_zero_dimensional : ∀ (R : Type) [CommRing R] [Ring.KrullDimLE 0 R] (q : ℕ), 0 < q → IsUnit (q : R) → ∀ u : Rˣ, (∀ m : Ideal R, m.IsMaximal → ∃ x : R, x ^ q - (u : R) ∈ m) → ∃ v : Rˣ, v ^ q = u := by
  first | (exact @GlobalTheory.exists_unit_pow_eq_of_krullDimLE_zero) | (exact GlobalTheory.exists_unit_pow_eq_of_krullDimLE_zero) | (intros; apply GlobalTheory.exists_unit_pow_eq_of_krullDimLE_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzCexpNegForm
section
open scoped Matrix Nat

namespace GlobalTheory.GaussComplexForm

theorem exists_schwartz_cexp_neg_form : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) ∧ ∀ x p, fderiv ℝ (⇑g) x p = -(Q x p + Q p x) * g x := by
  intro V _ _ _ Q c hc hQ
  set B : V →L[ℝ] V →L[ℝ] ℂ := -Q with hBdef
  have hBapp : ∀ x y, B x y = -(Q x y) := fun x y => rfl
  have hB : ∀ x, (B x x).re ≤ -(c * ‖x‖ ^ 2) := by
    intro x; rw [hBapp, Complex.neg_re]; linarith [hQ x]
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : V => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : V => Complex.exp (B y y)) :=
    Complex.contDiff_exp.comp hq
  refine ⟨⟨fun y => Complex.exp (B y y), hg, ?_⟩, fun x => ?_, fun x p => ?_⟩
  · intro k n
    obtain ⟨C, hC⟩ := GlobalTheory.GaussExpSeries.exists_bound_poly_mul_exp c hc (k + 2 * n)
    refine ⟨n ! * (2 * (‖B‖ + 1)) ^ n * C, fun x => ?_⟩
    have hx0 := norm_nonneg x
    have hB0 := norm_nonneg B
    have hfb := GlobalTheory.GaussExpSeries.norm_iteratedFDeriv_gauss_le B c hB n x
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : V => Complex.exp (B y y)) x‖
        ≤ (1 + ‖x‖) ^ k * (n ! * Real.exp (-(c * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n) := by
          gcongr
          linarith
      _ = n ! * (2 * (‖B‖ + 1)) ^ n * ((1 + ‖x‖) ^ (k + 2 * n) * Real.exp (-(c * ‖x‖ ^ 2))) := by
          rw [show (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n = (2 * (‖B‖ + 1)) ^ n * (1 + ‖x‖) ^ (2 * n) by
            rw [mul_pow, pow_mul], pow_add]; ring
      _ ≤ n ! * (2 * (‖B‖ + 1)) ^ n * C := by gcongr; exact hC ‖x‖ hx0
  · show Complex.exp (B x x) = _
    rw [hBapp]
  · have h1 := (B.hasFDerivAt (x := x)).clm_apply (hasFDerivAt_id x)
    have h2 : HasFDerivAt (fun y : V => Complex.exp (B y y)) _ x := h1.cexp
    show fderiv ℝ (fun y : V => Complex.exp (B y y)) x p = -(Q x p + Q p x) * Complex.exp (B x x)
    rw [h2.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, id, smul_eq_mul, hBapp]
    ring

end GlobalTheory.GaussComplexForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularPosDefAdjointActionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_posDef_form_adjoint_rep_of_posDef : ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ a, σ (σ a) = a) → ∀ (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ) (ρ0 : R →+* Matrix (Fin m) (Fin m) ℤ), 1 ≤ m → B0.transpose = B0 → (B0.map (Int.cast : ℤ → ℝ)).PosDef → (∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (σ a)) → ∃ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℤ) (ρ : R →+* Matrix (Fin r) (Fin r) ℤ), 1 ≤ r ∧ b.transpose = b ∧ (b.map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit b.det ∧ ∀ a, (ρ a).transpose * b = b * ρ (σ a) := by
  first | exact @GlobalTheory.exists_unimodular_posDef_adjoint_action | exact GlobalTheory.exists_unimodular_posDef_adjoint_action | (intros; apply GlobalTheory.exists_unimodular_posDef_adjoint_action <;> assumption)
end

