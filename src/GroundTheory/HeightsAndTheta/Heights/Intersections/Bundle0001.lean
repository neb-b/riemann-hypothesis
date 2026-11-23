module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.CardLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open IsLocalRing

universe u v

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem card_eq_card_residueField_of_isSimpleModule (N : Type v) [AddCommGroup N] [Module R N]
    [IsSimpleModule R N] : Nat.card N = Nat.card (ResidueField R) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R N›
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact Nat.card_congr e.toEquiv

theorem card_eq_pow_of_length_eq (n : ℕ) : ∀ (M : Type v) [AddCommGroup M] [Module R M],
    Module.length R M = n → Nat.card M = Nat.card (ResidueField R) ^ n := by
  induction n with
  | zero =>
    intro M _ _ h
    have : Subsingleton M := Module.length_eq_zero_iff.mp (by exact_mod_cast h)
    rw [pow_zero]
    exact Nat.card_eq_one_iff_unique.mpr ⟨this, ⟨0⟩⟩
  | succ n ih =>
    intro M _ _ h
    have hfin : IsFiniteLength R M := Module.length_ne_top_iff.mp (by rw [h]; exact ENat.natCast_ne_top _)
    obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfin
    have hnt : Nontrivial M := Module.length_pos_iff.mp (by rw [h]; exact_mod_cast Nat.succ_pos n)
    obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule R M)).resolve_left top_ne_bot
    have hs : IsSimpleModule R N := (isSimpleModule_iff_isAtom).mpr hN
    have hlen := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
    rw [h, Module.length_eq_one] at hlen
    have hq : Module.length R (M ⧸ N) = n := by
      have hne : Module.length R (M ⧸ N) ≠ ⊤ := by
        intro ht
        rw [ht] at hlen
        exact ENat.natCast_ne_top _ (hlen.trans (add_top _))
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
      rw [← hm] at hlen ⊢
      have : n + 1 = 1 + m := by exact_mod_cast hlen
      congr 1
      omega
    rw [Submodule.card_eq_card_quotient_mul_card N, card_eq_card_residueField_of_isSimpleModule (R := R) N, ih (M ⧸ N) hq,
      pow_succ, mul_comm]

theorem card_eq_card_residueField_pow_length (M : Type v) [AddCommGroup M] [Module R M]
    (h : Module.length R M ≠ ⊤) :
    Nat.card M = Nat.card (ResidueField R) ^ (Module.length R M).toNat := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
  rw [← hn, ENat.toNat_natCast]
  exact card_eq_pow_of_length_eq n M hn.symm

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.LocQuotCard
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

theorem isLocalization_of_mem_iff {O F : Type*} [CommRing O] [Field F] (φ : O →+* F) (hφ : Function.Injective φ)
    (L : Subring F) [Algebra O L] (hL : ∀ x : O, ((algebraMap O L x : L) : F) = φ x) (m : Ideal O) [m.IsPrime]
    (h : ∀ y : F, y ∈ L ↔ ∃ x s : O, s ∉ m ∧ y * φ s = φ x) :
    IsLocalization.AtPrime L m := by
  refine (isLocalization_iff m.primeCompl L).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    have hs0 : φ s ≠ 0 := fun h0 => hs (by rw [(map_eq_zero_iff φ hφ).1 h0]; exact m.zero_mem)
    refine IsUnit.of_mul_eq_one ⟨(φ s)⁻¹, (h _).2 ⟨1, s, hs, by rw [map_one, inv_mul_cancel₀ hs0]⟩⟩ ?_
    apply Subtype.ext
    simp only [Subring.coe_mul, hL, Subring.coe_one]
    exact mul_inv_cancel₀ hs0
  · intro z
    obtain ⟨x, s, hs, hxs⟩ := (h z).1 z.2
    exact ⟨⟨x, ⟨s, hs⟩⟩, Subtype.ext (by simp only [Subring.coe_mul, hL]; exact hxs)⟩
  · intro x y hxy
    have h1 := congrArg Subtype.val hxy
    rw [hL, hL] at h1
    exact ⟨1, by rw [hφ h1]⟩

theorem card_quot_map_eq_card_localization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
    (p : Ideal (R ⧸ I)) [p.IsPrime] [IsLocalization.AtPrime S (p.comap (Ideal.Quotient.mk I))] :
    Nat.card (S ⧸ I.map (algebraMap R S)) = Nat.card (Localization.AtPrime p) := by
  have hM : Algebra.algebraMapSubmonoid (R ⧸ I) (p.comap (Ideal.Quotient.mk I)).primeCompl = p.primeCompl := by
    ext x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨r', hr', he⟩
      rw [← he]
      exact hr'
    · intro hx
      exact ⟨r, hx, rfl⟩
  have : IsLocalization p.primeCompl (S ⧸ I.map (algebraMap R S)) := hM ▸ inferInstance
  exact Nat.card_congr (IsLocalization.algEquiv p.primeCompl _ (Localization.AtPrime p)).toEquiv

theorem card_quot_span_eq_card_localization {O L : Type*} [CommRing O] [CommRing L] (ψ : O →+* L) (b : O)
    (m : Ideal O) [m.IsPrime] (p : Ideal (O ⧸ Ideal.span {b})) [p.IsPrime]
    (hm : m = p.comap (Ideal.Quotient.mk _)) (h : @IsLocalization O _ m.primeCompl L _ ψ.toAlgebra) :
    Nat.card (L ⧸ Ideal.span {ψ b}) = Nat.card (Localization.AtPrime p) := by
  subst hm
  let _ := ψ.toAlgebra
  rw [← card_quot_map_eq_card_localization (S := L) (Ideal.span {b}) p, Ideal.map_span, Set.image_singleton,
    RingHom.algebraMap_toAlgebra]

theorem log_card_eq_sum_log_card_localization (A : Type*) [CommRing A] [Finite A] [Fintype (PrimeSpectrum A)] :
    Real.log (Nat.card A) = ∑ p : PrimeSpectrum A, Real.log (Nat.card (Localization.AtPrime p.asIdeal)) := by
  have hA : Nat.card A = ∏ p : PrimeSpectrum A, Nat.card (Localization.AtPrime p.asIdeal) := by
    rw [Nat.card_congr (PrimeSpectrum.toPiLocalizationEquiv A).toEquiv, Nat.card_pi]
  have h0 : Nat.card A ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  rw [hA, Finset.prod_ne_zero_iff] at h0
  rw [hA, Nat.cast_prod, Real.log_prod fun p _ => by exact_mod_cast h0 p (Finset.mem_univ _)]

theorem finsum_mem_eq_sum_of_injective {α β : Type*} [Fintype β] (s : Set α) (f : α → ℝ) (g : β → α)
    (hg : Function.Injective g) (hs : ∀ x, g x ∈ s) (hf : ∀ a ∈ s, f a ≠ 0 → a ∈ Set.range g) :
    ∑ᶠ a ∈ s, f a = ∑ x, f (g x) := by
  have hS : s ∩ Function.support f = Set.range g ∩ Function.support f := by
    ext a
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hf a h1 h2, h2⟩
    · rintro ⟨⟨x, rfl⟩, h2⟩
      exact ⟨hs x, h2⟩
  rw [← finsum_mem_inter_support, hS, finsum_mem_inter_support, finsum_mem_range hg, finsum_eq_sum_of_fintype]

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleMultiHomogGrad
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

section Graded

variable {σ τ R M : Type*} [CommRing R] [AddCommMonoid M]

theorem aeval_weightedHomogeneousComponent_of_weights (w : σ → M) (ω : τ → M)
    (e : σ → MvPolynomial τ R) (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v)) (m : M)
    (p : MvPolynomial σ R) :
    aeval e (weightedHomogeneousComponent w m p) = weightedHomogeneousComponent ω m (aeval e p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have hmon : IsWeightedHomogeneous ω (aeval e (monomial d c)) (Finsupp.weight w d) := by
      rw [aeval_monomial, Finsupp.weight_apply, algebraMap_eq]
      have := (isWeightedHomogeneous_C ω c).mul (IsWeightedHomogeneous.prod d.support
        (fun v => e v ^ d v) (fun v => d v • w v) (fun v _ => (he v).pow (d v)))
      rw [zero_add] at this
      exact this
    by_cases hdm : Finsupp.weight w d = m
    · have hmon' : IsWeightedHomogeneous ω (aeval e (monomial d c)) m := hdm ▸ hmon
      rw [(isWeightedHomogeneous_monomial _ d c hdm).weightedHomogeneousComponent_same,
        hmon'.weightedHomogeneousComponent_same]
    · rw [(isWeightedHomogeneous_monomial w d c
        (m := Finsupp.weight w d) rfl).weightedHomogeneousComponent_ne m
        (Ne.symm hdm), hmon.weightedHomogeneousComponent_ne m (Ne.symm hdm), map_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

end Graded

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StAdjoinIndepRelfinrank
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def AdjoinIndepRelfinrank.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (L₀ L : IntermediateField F Ω) (ι : Type) (t : ι → Ω),
    L₀ ≤ L → AlgebraicIndependent L t →
      IntermediateField.relfinrank (L₀ ⊔ IntermediateField.adjoin F (Set.range t))
          (L ⊔ IntermediateField.adjoin F (Set.range t)) =
        IntermediateField.relfinrank L₀ L

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StChartPrimElt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Polynomial

def ChartPrimElt.Statement : Prop :=
  ∀ (Φ : Type) [Field Φ] [CharZero Φ] (Φ' : Type) [Field Φ'] [Algebra Φ Φ'] (Q : Type) [Fintype Q]
    (r : Q → Φ'),
    FiniteDimensional Φ (IntermediateField.adjoin Φ (Set.range r)) →
    ∃ (τ : MvPolynomial Q Φ) (g : Q → Φ[X]) (u : Φ[X]),
      (minpoly Φ (MvPolynomial.aeval r τ)).natDegree =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range r)) ∧
      (∀ q, aeval (MvPolynomial.aeval r τ) (g q) = r q) ∧
      minpoly Φ (MvPolynomial.aeval r τ) ∣ u * derivative (minpoly Φ (MvPolynomial.aeval r τ)) - 1 ∧
      minpoly Φ (MvPolynomial.aeval r τ) ∣ MvPolynomial.aeval g τ - X ∧
      ∀ q, r q ≠ 0 → ∃ h : Φ[X], minpoly Φ (MvPolynomial.aeval r τ) ∣ h * g q - 1

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StChartSpecCount
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def ChartSpecCount.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Φ : Type) [Field Φ] [CharZero Φ] (Φ' : Type) [Field Φ'] [Algebra Φ Φ']
    (φ : R →+* Φ) (Q : Type) [Fintype Q] (r : Q → Φ'),
    (∀ c : Φ, ∃ f g : R, φ g ≠ 0 ∧ c = φ f / φ g) →
    FiniteDimensional Φ (IntermediateField.adjoin Φ (Set.range r)) →
    ∃ E : R, φ E ≠ 0 ∧ ∀ ψ : R →+* ℂ, RingHom.ker φ ≤ RingHom.ker ψ → ψ E ≠ 0 →
      {y : Q → ℂ | ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0}.Finite ∧
      {y : Q → ℂ | ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0}.ncard =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range r)) ∧
      ∀ y : Q → ℂ, (∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0) → ∀ q, r q ≠ 0 → y q ≠ 0

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StFinrankAdjoinRange
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def FinrankAdjoinRange.Statement : Prop :=
  ∀ (F Φ Ω : Type) [Field F] [Field Φ] [Field Ω] [Algebra F Φ] [Algebra F Ω] [Algebra Φ Ω] [IsScalarTower F Φ Ω]
    (S : Set Ω),
    Module.finrank Φ (IntermediateField.adjoin Φ S) =
      IntermediateField.relfinrank (IsScalarTower.toAlgHom F Φ Ω).fieldRange
        ((IsScalarTower.toAlgHom F Φ Ω).fieldRange ⊔ IntermediateField.adjoin F S)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StIntClosureLocFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def IntClosureLocFinite.Statement : Prop :=
  ∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (S : Finset L), Subfield.closure (S : Set L) = ⊤ →
    ∀ (A : Subring F) (T : Finset F), Subring.closure (T : Set F) ≤ A →
    (∀ z ∈ A, ∃ b ∈ Subring.closure (T : Set F), ∃ c ∈ Subring.closure (T : Set F),
      c ≠ 0 ∧ c⁻¹ ∈ A ∧ z * c = b) →
    letI := (φ.comp A.subtype).toAlgebra
    letI : Module A L := Algebra.toModule
    ∃ t : Finset L, ∀ x : L, IsIntegral A x → x ∈ Submodule.span A (t : Set L)

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocAwaySpec
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def LocAwaySpec.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Φ : Type) [Field Φ] (φ : R →+* Φ) (S : Finset Φ),
    (∀ c : Φ, ∃ f g : R, φ g ≠ 0 ∧ c = φ f / φ g) →
    ∃ (E : R) (hE : IsUnit (φ E)),
      (∀ c ∈ S, c ∈ Set.range (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ)) ∧
      ∀ (B : Type) [CommRing B] (ψ : R →+* B) (hψ : IsUnit (ψ E)), RingHom.ker φ ≤ RingHom.ker ψ →
        RingHom.ker (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ≤
          RingHom.ker (IsLocalization.Away.lift E hψ : Localization.Away E →+* B)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StRankAdjoinFrac
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

abbrev adjoinInclAlgebra (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω} (h : S ⊆ T) :
    Algebra (Algebra.adjoin F S) (Algebra.adjoin F T) :=
  (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom.toAlgebra

def RankAdjoinFrac.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (S T : Set Ω) (h : S ⊆ T),
    letI := adjoinInclAlgebra F h
    Module.finrank (Algebra.adjoin F S) (Algebra.adjoin F T) =
      IntermediateField.relfinrank (IntermediateField.adjoin F S) (IntermediateField.adjoin F T)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StRankFracDegree
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def RankFracDegree.Statement : Prop :=
  ∀ (F Ω A B : Type) [Field F] [Field Ω] [Algebra F Ω] [CommRing A] [CommRing B] [Algebra A B]
    (L₀ L : IntermediateField F Ω) (f : A →+* Ω) (g : B →+* Ω),
    Function.Injective f → Function.Injective g → (∀ a, g (algebraMap A B a) = f a) →
    (∀ a, f a ∈ L₀) → (∀ b, g b ∈ L) →
    L₀.toSubfield ≤ Subfield.closure (Set.range f) → L.toSubfield ≤ Subfield.closure (Set.range g) →
    Module.Finite A B → Module.finrank A B = IntermediateField.relfinrank L₀ L

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StRelAlgClosureFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def RelAlgClosureFinite.Statement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (S : Finset L),
    IntermediateField.adjoin K (S : Set L) = ⊤ → FiniteDimensional K (algebraicClosure K L)

end GroundTheory.Heights₂.Heights.Inter
end
end

