module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalRingCardinality.DataLevel

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAdicCompletionLocalizationProd
section
open IsLocalRing TensorProduct

namespace GlobalTheory.CompletionFactor

theorem exists_ringEquiv_prod_of_isIdempotentElem {S : Type*} [CommRing S] {e : S}
    (he : IsIdempotentElem e) :
    ∃ ε : S ≃+* (S ⧸ Ideal.span {1 - e}) × (S ⧸ Ideal.span {e}),
      ∀ x, (ε x).1 = Ideal.Quotient.mk _ x := by
  have hc : IsCoprime (Ideal.span {1 - e}) (Ideal.span {e} : Ideal S) := by
    rw [Ideal.isCoprime_span_singleton_iff]
    exact ⟨1, 1, by ring⟩
  have hb : (⊥ : Ideal S) = Ideal.span {1 - e} ⊓ Ideal.span {e} := by
    rw [← Ideal.mul_eq_inf_of_isCoprime hc, Ideal.span_singleton_mul_span_singleton, sub_mul,
      one_mul, he.eq, sub_self, Ideal.span_singleton_zero]
  refine ⟨(RingEquiv.quotientBot S).symm.trans ((Ideal.quotEquivOfEq hb).trans
    (Ideal.quotientInfEquivQuotientProd _ _ hc)), fun x => ?_⟩
  rfl

theorem exists_local_factor {B S D : Type*} [CommRing B] [HenselianLocalRing B] [CommRing S]
    [Algebra B S] [Module.Finite B S] [CommRing D] [IsLocalRing D] (φ : S →+* D)
    (hφ : maximalIdeal B ≤ (maximalIdeal D).comap (φ.comp (algebraMap B S))) :
    ∃ e : S, IsIdempotentElem e ∧ IsLocalRing (S ⧸ Ideal.span {1 - e}) ∧
      ∃ ψ : (S ⧸ Ideal.span {1 - e}) →+* D, IsLocalHom ψ ∧
        ∀ x, ψ (Ideal.Quotient.mk _ x) = φ x := by
  have hq : ((maximalIdeal D).comap φ).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap B S)
      (fun x => Algebra.IsIntegral.isIntegral x)
    rw [Ideal.comap_comap, ← (maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hφ]
    infer_instance
  obtain ⟨e, he, H⟩ := exists_idempotent_notMem_iff_of_henselian B ((maximalIdeal D).comap φ)
  have hl := isLocalRing_quotient_one_sub he _ H
  have h1 : φ e = 1 := by
    refine (IsIdempotentElem.iff_eq_one_of_isUnit ?_).1 (he.map φ)
    have := (H _ hq).2 rfl
    rwa [Ideal.mem_comap, notMem_maximalIdeal] at this
  have h0 : ∀ a ∈ Ideal.span {1 - e}, φ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp [h1]
  refine ⟨e, he, hl, Ideal.Quotient.lift _ φ h0, ⟨fun r hr => ?_⟩, fun x => rfl⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hm := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span {1 - e}))
    Ideal.Quotient.mk_surjective (K := maximalIdeal _)
  have h : (maximalIdeal _).comap (Ideal.Quotient.mk (Ideal.span {1 - e})) =
      (maximalIdeal D).comap φ := by
    rw [← H _ hm, ← one_sub_mem_iff_notMem_of_isIdempotentElem he, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
    exact zero_mem _
  rw [← notMem_maximalIdeal, ← Ideal.mem_comap, h, Ideal.mem_comap, notMem_maximalIdeal]
  exact hr

theorem bijective_of_complete_quotient {T C A R : Type*} [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] [CommRing C] [Algebra T C] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra C A] (𝔫 : Ideal C) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫]
    (h𝔫 : 𝔫.comap (algebraMap T C) = maximalIdeal T)
    [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (π : (AdicCompletion (maximalIdeal T) T ⊗[T] C) →+* R) (hπ : Function.Surjective π)
    (ψ : R →+* AdicCompletion (maximalIdeal A) A) [IsLocalHom ψ]
    (hψ : ∀ c : C, ψ (π (1 ⊗ₜ[T] c)) =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c)) :
    Function.Bijective ψ := by
  let β₀ : C →+* R := π.comp (Algebra.TensorProduct.includeRight (R := T)).toRingHom
  have hβ₀ : ∀ c, β₀ c = π (1 ⊗ₜ[T] c) := fun c => rfl
  have hu : ∀ s : 𝔫.primeCompl, IsUnit (β₀ s) := fun s => by
    refine IsUnit.of_map ψ _ ?_
    rw [hβ₀, hψ]
    exact (IsLocalization.map_units A s).map _
  let β : A →+* R := IsLocalization.lift hu
  have hβ : ∀ c, β (algebraMap C A c) = π (1 ⊗ₜ[T] c) := fun c => IsLocalization.lift_eq hu c
  have hψβ : ψ.comp β = algebraMap A (AdicCompletion (maximalIdeal A) A) := by
    refine IsLocalization.ringHom_ext 𝔫.primeCompl (RingHom.ext fun c => ?_)
    simp only [RingHom.comp_apply, hβ, hψ]
  have hβm : ∀ a ∈ maximalIdeal A, β a ∈ maximalIdeal R := fun a ha => by
    by_contra h
    rw [notMem_maximalIdeal] at h
    have h2 : IsUnit ((ψ.comp β) a) := h.map ψ
    rw [hψβ] at h2
    exact notMem_maximalIdeal.2 (IsUnit.of_map _ _ h2) ha
  obtain ⟨χ, hχ, -⟩ := exists_extend_adicCompletion β (maximalIdeal A) (maximalIdeal R) (k := 1)
    (by rw [pow_one, Ideal.map_le_iff_le_comap]; exact hβm)
  have h₁ : ψ.comp χ = RingHom.id _ := by
    refine adicCompletion_ringHom_ext (maximalIdeal A).fg_of_isNoetherianRing
      (maximalIdeal (AdicCompletion (maximalIdeal A) A)) (k := 1) ?_ ?_
    · rw [pow_one, RingHom.comp_assoc, hχ, hψβ, AdicCompletion.maximalIdeal_eq_map]
    · rw [RingHom.comp_assoc, hχ, hψβ, RingHom.id_comp]
  have hC : ∀ c : C, χ (ψ (π (1 ⊗ₜ[T] c))) = π (1 ⊗ₜ[T] c) := fun c => by
    rw [hψ, ← RingHom.comp_apply, hχ, hβ]
  have hT : ∀ t : T, (algebraMap T (AdicCompletion (maximalIdeal T) T) t) ⊗ₜ[T] (1 : C) =
      1 ⊗ₜ[T] algebraMap T C t := fun t => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]
  have hL : π.comp Algebra.TensorProduct.includeLeftRingHom =
      ((χ.comp ψ).comp π).comp Algebra.TensorProduct.includeLeftRingHom := by
    refine adicCompletion_ringHom_ext (maximalIdeal T).fg_of_isNoetherianRing
      (maximalIdeal R) (k := 1) ?_ ?_
    · rw [pow_one, Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply,
        Algebra.TensorProduct.includeLeftRingHom_apply, hT, ← hβ]
      apply hβm
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff A 𝔫, ← Ideal.mem_comap, h𝔫]
      exact ht
    · refine RingHom.ext fun t => ?_
      simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, hT, hC]
  have h₂ : ∀ x, χ (ψ (π x)) = π x := by
    intro x
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a c =>
      have e1 : a ⊗ₜ[T] c = (a ⊗ₜ[T] (1 : C)) * (1 ⊗ₜ[T] c) := by simp
      have e2 : π (a ⊗ₜ[T] (1 : C)) = χ (ψ (π (a ⊗ₜ[T] (1 : C)))) := congr($hL a)
      rw [e1, map_mul, map_mul, map_mul, ← e2, hC]
  refine Function.bijective_iff_has_inverse.2 ⟨χ, fun r => ?_, fun y => congr($h₁ y)⟩
  obtain ⟨x, rfl⟩ := hπ r
  exact h₂ x

theorem exists_ringEquiv_completion_prod : ∀ (T C A : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [CommRing C] [Algebra T C] [Module.Finite T C] [CommRing A] [IsLocalRing A] [Algebra C A] (𝔫 : Ideal C) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫], 𝔫.comap (algebraMap T C) = maximalIdeal T → ∃ (S' : Type) (_ : CommRing S') (e : (AdicCompletion (maximalIdeal T) T ⊗[T] C) ≃+* (AdicCompletion (maximalIdeal A) A × S')), ∀ c : C, (e ((1 : AdicCompletion (maximalIdeal T) T) ⊗ₜ[T] c)).1 = algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c) := by
  intro T C A _ _ _ _ _ _ _ _ _ 𝔫 _ _ h𝔫
  have hCn : IsNoetherianRing C := IsNoetherianRing.of_finite T C
  have hAn : IsNoetherianRing A := IsLocalization.isNoetherianRing 𝔫.primeCompl A hCn
  have hTn := AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)
  let g : C →+* AdicCompletion (maximalIdeal A) A := (algebraMap A _).comp (algebraMap C A)
  have hg : maximalIdeal T ≤ (maximalIdeal _).comap (g.comp (algebraMap T C)) := by
    intro t ht
    rw [Ideal.mem_comap, AdicCompletion.maximalIdeal_eq_map]
    refine Ideal.mem_map_of_mem _ (?_ : algebraMap C A (algebraMap T C t) ∈ maximalIdeal A)
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff A 𝔫, ← Ideal.mem_comap, h𝔫]
    exact ht
  obtain ⟨α, hα, -⟩ := exists_extend_adicCompletion (g.comp (algebraMap T C)) (maximalIdeal T)
    (maximalIdeal _) (k := 1) (by rw [pow_one, Ideal.map_le_iff_le_comap]; exact hg)
  obtain ⟨φ, hφa, hφc⟩ : ∃ φ : (AdicCompletion (maximalIdeal T) T ⊗[T] C) →+*
      AdicCompletion (maximalIdeal A) A,
      φ.comp (algebraMap (AdicCompletion (maximalIdeal T) T) _) = α ∧
        ∀ c, φ (1 ⊗ₜ[T] c) = g c := by
    letI : Algebra T (AdicCompletion (maximalIdeal A) A) := (g.comp (algebraMap T C)).toAlgebra
    let α' : AdicCompletion (maximalIdeal T) T →ₐ[T] AdicCompletion (maximalIdeal A) A :=
      { α with commutes' := fun t => congr($hα t) }
    let g' : C →ₐ[T] AdicCompletion (maximalIdeal A) A := { g with commutes' := fun t => rfl }
    refine ⟨(Algebra.TensorProduct.lift α' g' fun _ _ => .all _ _).toRingHom,
      RingHom.ext fun a => ?_, fun c => ?_⟩
    · change Algebra.TensorProduct.lift α' g' (fun _ _ => .all _ _) (a ⊗ₜ[T] 1) = α' a
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    · change Algebra.TensorProduct.lift α' g' (fun _ _ => .all _ _) (1 ⊗ₜ[T] c) = g' c
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hH := henselianLocalRing_of_henselianRing (AdicCompletion (maximalIdeal T) T)
  obtain ⟨e, he, hl, ψ, hψl, hψ⟩ := exists_local_factor (B := AdicCompletion (maximalIdeal T) T) φ
    (by
      rw [hφa, AdicCompletion.maximalIdeal_eq_map (R := T), Ideal.map_le_iff_le_comap,
        Ideal.comap_comap, hα]
      exact hg)
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local
    (AdicCompletion (maximalIdeal T) T)
    ((AdicCompletion (maximalIdeal T) T ⊗[T] C) ⧸ Ideal.span {1 - e})
  have hψc : ∀ c : C, ψ (Ideal.Quotient.mk _ (1 ⊗ₜ[T] c)) =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c) := fun c => by
    rw [hψ, hφc]; rfl
  have hb := bijective_of_complete_quotient 𝔫 h𝔫 _ Ideal.Quotient.mk_surjective ψ hψc
  obtain ⟨ε, hε⟩ := exists_ringEquiv_prod_of_isIdempotentElem he
  refine ⟨_, inferInstance, ε.trans ((RingEquiv.ofBijective ψ hb).prodCongr (RingEquiv.refl _)),
    fun c => ?_⟩
  rw [← hψc, ← hε]
  rfl

end GlobalTheory.CompletionFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumCentralIdempotentOfIrrCharacterEqSimple
section
open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

theorem zOf_character {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) :
    GlobalTheory.GLq.zOf τ.character = Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ := by
  unfold GlobalTheory.GLq.zOf Formalism.IrreducibleCountingLemmas.TYPES.zIdem
  rw [FDRep.char_one]
  rfl

theorem zOf_coeff {G : Type} [Group G] [Fintype G] (χ : G → ℂ) (y : G) :
    (GlobalTheory.GLq.zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  classical
  unfold GlobalTheory.GLq.zOf
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem character_eq_zero_of_finrank {G : Type} [Group G] (τ : FDRep ℂ G)
    (h : Module.finrank ℂ τ.V = 0) (x : G) : τ.character x = 0 := by
  have : Subsingleton τ.V := Module.finrank_zero_iff.mp h
  unfold FDRep.character
  rw [Subsingleton.elim (τ.ρ x) 0]
  exact map_zero _

theorem character_eq_of_zOf_eq {G : Type} [Group G] [Fintype G] (σ τ : FDRep ℂ G)
    (h : GlobalTheory.GLq.zOf σ.character = GlobalTheory.GLq.zOf τ.character) : σ.character = τ.character := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hy : ∀ y : G, σ.character 1 * σ.character y = τ.character 1 * τ.character y := by
    intro y
    have h1 := zOf_coeff σ.character y⁻¹
    have h2 := zOf_coeff τ.character y⁻¹
    rw [h, h2, inv_inv] at h1
    field_simp at h1
    first | exact h1.symm | linear_combination (-1 : ℂ) * h1
  have h1 := hy 1
  rw [FDRep.char_one, FDRep.char_one] at h1
  have h2 : Module.finrank ℂ σ.V * Module.finrank ℂ σ.V = Module.finrank ℂ τ.V * Module.finrank ℂ τ.V := by
    exact_mod_cast h1
  have h3 : Module.finrank ℂ σ.V = Module.finrank ℂ τ.V := Nat.mul_self_inj.mp h2
  funext y
  by_cases h0 : Module.finrank ℂ τ.V = 0
  · rw [character_eq_zero_of_finrank τ h0, character_eq_zero_of_finrank σ (h3.trans h0)]
  · have h4 := hy y
    rw [FDRep.char_one, FDRep.char_one, h3] at h4
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr h0) h4

theorem finsum_zOf_eq_finsum_zIdem {G : Type} [Group G] [Fintype G] (Q : (G → ℂ) → Prop) :
    ∑ᶠ χ ∈ {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ}, GlobalTheory.GLq.zOf χ =
      ∑ᶠ (z : MonoidAlgebra ℂ G) (_ : ∃ τ : FDRep ℂ G, CategoryTheory.Simple τ ∧
        Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z ∧ Q τ.character), z := by
  have hinj : Set.InjOn (GlobalTheory.GLq.zOf (G := G)) {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ} := by
    rintro a ⟨⟨V, -, hV⟩, -⟩ b ⟨⟨U, -, hU⟩, -⟩ hab
    obtain rfl : V.character = a := funext hV
    obtain rfl : U.character = b := funext hU
    exact character_eq_of_zOf_eq V U hab
  rw [← finsum_mem_image (f := fun z : MonoidAlgebra ℂ G => z) hinj]
  refine finsum_congr fun z => ?_
  have hiff : (z ∈ GlobalTheory.GLq.zOf '' {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ}) =
      ∃ τ : FDRep ℂ G, CategoryTheory.Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z ∧ Q τ.character := by
    apply propext
    constructor
    · rintro ⟨a, ⟨⟨V, hs, hV⟩, hQ⟩, rfl⟩
      obtain rfl : V.character = a := funext hV
      exact ⟨V, hs, (zOf_character V).symm, hQ⟩
    · rintro ⟨V, hs, rfl, hQ⟩
      exact ⟨V.character, ⟨⟨V, hs, fun _ => rfl⟩, hQ⟩, zOf_character V⟩
  rw [hiff]

end GlobalTheory.SerCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsOfSemilinear
section
open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.DefLatBC

section Csd

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem csum_coords (u v : Fin S.dim → K) :
    S.csum (S.basis.equivFun.symm u : S.Cl → S.V) (S.basis.equivFun.symm v : S.Cl → S.V) =
      ∑ i, ∑ j, star (u i) * S.H i j * v j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul, CSD.csum, CSD.H,
    Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, map_sum, map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [starRingEnd_apply]
  ring

theorem mem_nabLat_iff (x : Fin S.dim → K) :
    x ∈ S.nabLat ↔ ∀ c, (S.basis.equivFun.symm x : S.Cl → S.V) c ∈ S.Nab c := by
  simp [CSD.nabLat, valLatF, Submodule.mem_pi, CSD.I]

end Csd

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

theorem forms_of_semilinear (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0')
    (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (L : B.S.Forms →+ B'.S.Forms)
    (hsm : ∀ (a : K) (f : B.S.Forms), L (a • f) = φ a • L f)
    (hli : LinearIndependent K' (fun k => L (B.S.basis k)))
    (hsp : ⊤ ≤ Submodule.span K' (Set.range fun k => L (B.S.basis k)))
    (hcs : ∀ f g : B.S.Forms, B'.S.csum (L f : B'.S.Cl → B'.S.V) (L g) = φ (B.S.csum f g))
    (hact : ∀ (g : G) (f : B.S.Forms), B'.r (e g) (L f) = L (B.r g f))
    (hnab : ∀ f' : B'.S.Forms, (∀ c, (f' : B'.S.Cl → B'.S.V) c ∈ B'.S.Nab c) ↔
      f' ∈ Submodule.span (𝓞 K') (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}))
    (hZ : Z' = Submodule.span K' (L '' (Z : Set B.S.Forms))) :
    ∃ C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K', Function.Bijective C.mulVec ∧
      Cᴴ * B'.S.H * C = B.S.H.map φ ∧
      (∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ) ∧
      B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) ∧
      B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
  classical
  set C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K' := Matrix.of fun i k => B'.S.basis.repr (L (B.S.basis k)) i with hCdef

  have hcol : ∀ k, B'.S.basis.equivFun.symm (fun i => C i k) = L (B.S.basis k) := by
    intro k
    rw [LinearEquiv.symm_apply_eq]
    ext i
    simp [hCdef]
  have hC : ∀ y, C *ᵥ y = B'.S.basis.equivFun (∑ k, y k • L (B.S.basis k)) := by
    intro y
    ext i
    simp [hCdef, Matrix.mulVec, dotProduct, mul_comm]
  have hLsum : ∀ x : Fin B.S.dim → K, L (B.S.basis.equivFun.symm x) = ∑ k, φ (x k) • L (B.S.basis k) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Basis.equivFun_symm_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => hsm _ _
  have hT : ∀ x : Fin B.S.dim → K, C *ᵥ (fun k => φ (x k)) = B'.S.basis.equivFun (L (B.S.basis.equivFun.symm x)) := by
    intro x
    rw [hC, hLsum]
  have hTf : ∀ f : B.S.Forms, C *ᵥ (fun k => φ (B.S.basis.repr f k)) = ⇑(B'.S.basis.repr (L f)) := by
    intro f
    have := hT (B.S.basis.equivFun f)
    simpa using this
  refine ⟨C, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro y₁ y₂ h
    have h0 : ∑ k, (y₁ - y₂) k • L (B.S.basis k) = 0 := by
      have : C *ᵥ (y₁ - y₂) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
      rw [hC] at this
      exact (LinearEquiv.map_eq_zero_iff _).mp this
    have := Fintype.linearIndependent_iff.mp hli _ h0
    funext k
    exact sub_eq_zero.mp (this k)
  ·
    intro y
    have hmem : B'.S.basis.equivFun.symm y ∈ Submodule.span K' (Set.range fun k => L (B.S.basis k)) := hsp trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K').mp hmem
    refine ⟨c, ?_⟩
    rw [hC, hc, LinearEquiv.apply_symm_apply]
  ·
    ext a b
    have h1 := hcs (B.S.basis a) (B.S.basis b)
    rw [← hcol a, ← hcol b, csum_coords] at h1
    simp only [Matrix.map_apply, CSD.H, Matrix.of_apply] at h1 ⊢
    rw [← h1, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Matrix.of_apply]
  ·
    intro g
    have hv : ∀ f : B.S.Forms, (B'.S.actMat B'.r (e g) * C) *ᵥ (fun k => φ (B.S.basis.repr f k)) =
        (C * (B.S.actMat B.r g).map φ) *ᵥ (fun k => φ (B.S.basis.repr f k)) := by
      intro f
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTf]
      have h2 : (B.S.actMat B.r g).map φ *ᵥ (fun k => φ (B.S.basis.repr f k)) =
          fun k => φ (B.S.basis.repr (B.r g f) k) := by
        funext k
        rw [show (fun k => φ (B.S.basis.repr f k)) = φ ∘ (B.S.basis.repr f) from rfl, ← RingHom.map_mulVec φ]
        simp only [CSD.actMat, LinearMap.toMatrix_mulVec_repr]
      rw [h2, hTf]
      simp only [CSD.actMat, LinearMap.toMatrix_mulVec_repr, hact]
    ext i k
    have hs : (fun j => φ (B.S.basis.repr (B.S.basis k) j)) = Pi.single k 1 := by
      funext j
      by_cases h : j = k
      · subst h; simp
      · simp [Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]
    have := congrFun (hv (B.S.basis k)) i
    rw [hs, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
    exact this
  ·
    let eO := (B'.S.basis.equivFun).restrictScalars (𝓞 K')
    have himg : (fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)) =
        eO '' (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨L (B.S.basis.equivFun.symm x), ⟨_, (mem_nabLat_iff _ _).mp hx, rfl⟩, (hT x).symm⟩
      · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
        refine ⟨B.S.basis.equivFun f, (mem_nabLat_iff _ _).mpr (by simpa using hf), ?_⟩
        show C *ᵥ (fun k => φ (B.S.basis.equivFun f k)) = _
        rw [hT, LinearEquiv.symm_apply_apply]
        rfl
    ext y
    rw [himg, ← LinearEquiv.coe_coe, Submodule.span_image, Submodule.mem_map_equiv, ← hnab, mem_nabLat_iff]
    rfl
  ·
    rw [hZ, BlockDat.coord, BlockDat.coord, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
    congr 1
    refine Set.image_congr fun f _ => ?_
    rw [hT]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end GlobalTheory.Mem.R3.DefLatBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LabelMapLabelOfClassFunctionLabel
section
open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

theorem getElem_of_canonList_eq {g : ℕ} [Fact g.Prime] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (Q : List (GlobalTheory.GLq.Pc g))
    (h : canonList b lam = Q) (c : Fin s) (hc : (c : ℕ) < Q.length) :
    Q[(c : ℕ)] = ⟨Fintype.card {i // b i = c},
      fun x => (Formalism.IrreducibleCountingLemmas.TYPES.transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩ := by
  subst h
  have e : (List.finRange s)[(c : ℕ)]'(by simp) = c := by simp
  simp only [canonList, List.getElem_map]
  rw [e]

theorem hasLabelO_of_hasLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), (∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → CategoryTheory.Simple V → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) → P = O.lab d V) → (∀ (d : ℕ) (χ : GlobalTheory.GLq.Gn g d → ℂ), GlobalTheory.GLq.IsCusp χ → ∃ V : FDRep ℂ (GL (Fin d) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = χ x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0)) → (∀ (Q : List (GlobalTheory.GLq.Pc g)), (∀ p ∈ Q, 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x) → ∃ (b : Fin (GlobalTheory.GLq.degL Q) → Fin Q.length) (lam : ∀ c : Fin Q.length, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b ∧ (∀ c, CategoryTheory.Simple (lam c) ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) (lam c)) ∧ GlobalTheory.SerCmp.canonList b lam = Q) → ∀ (r : ℕ) (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]), CategoryTheory.Simple τ → GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f → Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f := by
  intro g _ L C O hU hReal hTr hCon hSurj r τ f hτ hL
  obtain ⟨Q, hQ, hdeg, hf, hip⟩ := hL
  subst hdeg
  have hQScusp : ∀ p ∈ (Q.map Prod.snd), 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have hc : GlobalTheory.GLq.IsCusp q.2.2 := (hQ q hq).2.1
    exact ⟨hc.1, hReal _ _ hc⟩
  obtain ⟨b, lam, hb, hlam, hcan⟩ := hSurj (Q.map Prod.snd) hQScusp
  have key : ∀ c : Fin (Q.map Prod.snd).length, ∀ hcQ : (c : ℕ) < Q.length,
      Formalism.IrreducibleCountingLemmas.TYPES.labO O (lam c) = (Q[(c : ℕ)]'hcQ).1 := by
    intro c hcQ
    have hcusp := hQ _ (List.getElem_mem hcQ)
    have h2 : (Q[(c : ℕ)]'hcQ).2 = (Q.map Prod.snd)[(c : ℕ)] := by simp
    rw [h2, getElem_of_canonList_eq b lam (Q.map Prod.snd) hcan c c.2] at hcusp
    exact (hU _ _ _ hcusp.2.1.1 (Formalism.L2.PT.simple_transp _ (hlam c).1)
      (Formalism.L2.PT.isCuspidal_transp _ (hlam c).2) hcusp).symm
  refine ⟨(Q.map Prod.snd).length, b, lam, hb, hlam, ?_, ?_⟩
  · rw [hCon _ _ b lam τ hτ]
    have htr : (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam)
        (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) = GlobalTheory.GLq.hcL (Q.map Prod.snd) (GlobalTheory.GLq.degL (Q.map Prod.snd)) := by
      funext x
      rw [hTr _ _ b lam hb x, hcan]
    rw [htr]
    exact hip
  · have hlen : (Q.map Prod.fst).length = (Q.map Prod.snd).length := by simp
    rw [hf, ← Fin.prod_univ_getElem (Q.map Prod.fst)]
    refine Fintype.prod_equiv (finCongr hlen) _ _ (fun c => ?_)
    have hcQ : (c : ℕ) < Q.length := by simpa using c.2
    rw [key _ hcQ]
    simp

end GlobalTheory.SerCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocLEqIntVOfDvdUnitStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_locL_iff_forall_mem_intV_of_not_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Fin n → Prop) (π c : 𝓞 E) (T : ℕ),
    (T : 𝓞 F) ∉ v.asIdeal → π * c = (T : 𝓞 E) →
    (∀ y, y ∈ Λ ↔ ∀ a, ∃ r : 𝓞 E, y a = r ∧ (P a → π ∣ r)) → ∀ (y : Fin n → E ⊗[F] v.adicCompletion F),
    (y ∈ Formalism.L2.Herm.locL v Λ ↔ ∀ a, y a ∈ Formalism.BasicNotions.intV E v) := by
  first | exact @GlobalTheory.locL_eq_intV_of_dvd_unit | exact GlobalTheory.locL_eq_intV_of_dvd_unit | (intros; apply GlobalTheory.locL_eq_intV_of_dvd_unit <;> assumption)
end

