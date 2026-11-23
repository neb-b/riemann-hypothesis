module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualLatticeStandardAtRationalPrime
section
open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory

theorem selfDual_standard_at_rational_prime : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (p : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K) (L : Submodule (𝓞 K) (n → K)) (t : 𝓞 K), (∀ x, σ (σ x) = x) → (∀ x : 𝓞 K, ∃ m : ℤ, (x : K) * σ x = m) → p.Prime → (p : 𝓞 K) ∈ 𝔭.asIdeal → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∑ i, x i * σ (y i) ∈ (algebraMap (𝓞 K) K).range) → t ∉ 𝔭.asIdeal → (∀ x ∈ L, ∀ i, (t : K) * x i ∈ (algebraMap (𝓞 K) K).range) → (∀ j, (Pi.single j (t : K) : n → K) ∈ L) → ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, ∀ i, (s : K) * x i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ v : n → K, (∀ i, v i ∈ (algebraMap (𝓞 K) K).range) → (s : K) • v ∈ L := by
  intro K _ _ σ n _ _ p 𝔭 α β L t hσ hN hp hp𝔭 hα hβ hβα hL ht h1 h2
  have hint : ∀ x ∈ (algebraMap (𝓞 K) K).range, σ x ∈ (algebraMap (𝓞 K) K).range := by
    rintro _ ⟨x, rfl⟩
    have : IsIntegral ℤ (σ (algebraMap (𝓞 K) K x)) :=
      (RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom
    exact ⟨⟨_, this⟩, rfl⟩
  obtain ⟨t', ht'⟩ := hint (t : K) ⟨t, rfl⟩
  have ht'' : (t' : K) = σ t := ht'
  have h1' : ∀ x ∈ L, ∀ j, (t' : K) * x j ∈ (algebraMap (𝓞 K) K).range := by
    intro x hx j
    have := (hL x).1 hx _ (h2 j)
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [Pi.single_eq_of_ne hb]) (by simp)] at this
    rw [ht'', mul_comm]
    simpa only [Pi.single_eq_same] using this
  have h2' : ∀ j, (Pi.single j (t' : K) : n → K) ∈ L := by
    intro j
    rw [hL]
    intro y hy
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [Pi.single_eq_of_ne hb]) (by simp)]
    rw [Pi.single_eq_same, ht'', ← map_mul]
    exact hint _ (h1 y hy j)
  set a : 𝓞 K := β * t + α * t' with ha
  have haK : (a : K) = β * t + α * t' := by simp [ha]
  have ha𝔭 : a ∉ 𝔭.asIdeal := by
    intro h
    have h' : β * t ∈ 𝔭.asIdeal := by
      have := 𝔭.asIdeal.sub_mem h (𝔭.asIdeal.mul_mem_right t' hα)
      simpa [ha] using this
    rcases 𝔭.isPrime.mem_or_mem h' with h | h
    · exact hβ h
    · exact ht h
  have hσa : σ a = a := by
    rw [haK, map_add (f := _), map_mul, map_mul, hβα, ht'', hσ, hσ]
    ring
  have ha1 : ∀ x ∈ L, ∀ j, (a : K) * x j ∈ (algebraMap (𝓞 K) K).range := by
    intro x hx j
    have : (a : K) * x j = β * (t * x j) + α * (t' * x j) := by rw [haK]; ring
    rw [this]
    exact add_mem (mul_mem ⟨β, rfl⟩ (h1 x hx j)) (mul_mem ⟨α, rfl⟩ (h1' x hx j))
  have ha2 : ∀ j, (Pi.single j (a : K) : n → K) ∈ L := by
    intro j
    have : (Pi.single j (a : K) : n → K)
        = β • (Pi.single j (t : K) : n → K) + α • (Pi.single j (t' : K) : n → K) := by
      ext i
      by_cases h : i = j
      · subst h
        simp [haK, Algebra.smul_def]
      · simp [Pi.single_eq_of_ne h]
    rw [this]
    exact add_mem (L.smul_mem _ (h2 j)) (L.smul_mem _ (h2' j))
  obtain ⟨m, hm⟩ := hN a
  rw [hσa] at hm
  have hmO : a * a = (m : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    simpa using hm
  obtain ⟨e, he⟩ : ∃ e : ℤ, ((m.natAbs : ℕ) : ℤ) = e * m := by
    rcases Int.natAbs_eq m with h | h
    · exact ⟨1, by omega⟩
    · exact ⟨-1, by omega⟩
  have hs : ((m.natAbs : ℕ) : K) = (e : K) * (a * a) := by
    rw [hm]
    have := congrArg (Int.cast : ℤ → K) he
    rwa [Int.cast_natCast, Int.cast_mul] at this
  refine ⟨m.natAbs, ?_, ?_, ?_⟩
  · rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    obtain ⟨c, hc⟩ := Int.natCast_dvd.2 h
    have : a * a ∈ 𝔭.asIdeal := by
      rw [hmO, hc]
      push_cast
      exact 𝔭.asIdeal.mul_mem_right _ hp𝔭
    rcases 𝔭.isPrime.mem_or_mem this with h | h <;> exact ha𝔭 h
  · intro x hx i
    have : ((m.natAbs : ℕ) : K) * x i = (e : K) * a * (a * x i) := by rw [hs]; ring
    rw [this]
    exact mul_mem (mul_mem (intCast_mem _ e) ⟨a, rfl⟩) (ha1 x hx i)
  · intro v hv
    choose w hw using hv
    have : ((m.natAbs : ℕ) : K) • v
        = ∑ j, ((e : 𝓞 K) * w j * a) • (Pi.single j (a : K) : n → K) := by
      ext i
      rw [Finset.sum_apply, Finset.sum_eq_single i
        (by intro b _ hb; simp [Pi.single_eq_of_ne hb.symm]) (by simp)]
      rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, hs, ← hw i, Algebra.smul_def (_ : 𝓞 K),
        smul_eq_mul]
      simp only [map_mul, map_intCast]
      change _ = (e : K) * _ * (a : K) * (a : K)
      ring
    rw [this]
    exact L.sum_mem fun j _ => L.smul_mem _ (ha2 j)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRelativeDimOfTrdeg
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.RelDimFibCrit

end GlobalTheory.RelDimFibCrit

namespace GlobalTheory.RelDimFibCrit

open AlgebraicGeometry CategoryTheory Limits in
private lemma specMap_residueFieldMap_conj_eq_ofHom_map {R S : CommRingCat.{0}} (φ : R ⟶ S)
    (p : PrimeSpectrum S) :
    (Scheme.Spec.residueFieldIso R ((Spec.map φ) p)).inv ≫ (Spec.map φ).residueFieldMap p ≫
      (Scheme.Spec.residueFieldIso S p).hom =
      CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) := by
  haveI : ((Spec.map φ) p).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have key : CommRingCat.ofHom (algebraMap R ((Spec.map φ) p).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R ((Spec.map φ) p)).inv ≫ (Spec.map φ).residueFieldMap p ≫
      (Scheme.Spec.residueFieldIso S p).hom =
      CommRingCat.ofHom (algebraMap R ((Spec.map φ) p).asIdeal.ResidueField) ≫
      CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) := by
    rw [reassoc_of% Scheme.Spec.algebraMap_residueFieldIso_inv]
    erw [Scheme.residue_residueFieldMap_assoc (Spec.map φ) p]
    erw [Scheme.Spec.residue_residueFieldIso_hom]
    erw [Scheme.Hom.germ_stalkMap_assoc]
    erw [Spec.germ_stalkMapIso_hom_assoc]
    erw [Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    erw [Ideal.ResidueField.map_algebraMap]
    rw [← IsScalarTower.algebraMap_apply]
  ext1
  apply Ideal.ResidueField.ringHom_ext
  exact congr_arg CommRingCat.Hom.hom key

open AlgebraicGeometry CategoryTheory Limits in
private lemma residueFieldCongr_hom_hom_comp {Y : Scheme.{0}} {a b : Y} {Z : CommRingCat.{0}}
    (h : a = b) (h' : b = a) (g : Y.residueField a ⟶ Z) :
    (Y.residueFieldCongr h).hom ≫ (Y.residueFieldCongr h').hom ≫ g = g := by
  subst h
  simp [Scheme.residueFieldCongr_refl]

open AlgebraicGeometry CategoryTheory Limits in
private lemma trdeg_le_of_ringEquiv {K L K' L' : Type} [CommRing K] [CommRing L] [CommRing K']
    [CommRing L'] [Nontrivial K'] [Algebra K L] [Algebra K' L'] (e₁ : K ≃+* K') (e₂ : L ≃+* L')
    (h : (algebraMap K' L').comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap K L)) :
    Algebra.trdeg K L ≤ Algebra.trdeg K' L' :=
  ciSup_le' fun s ↦ (s.2.ringHom_of_comp_eq e₁ e₂ e₁.surjective e₂.injective h).cardinalMk_le_trdeg

open AlgebraicGeometry CategoryTheory Limits in
private lemma trdeg_eq_of_ringEquiv {K L K' L' : Type} [Field K] [CommRing L] [Field K']
    [CommRing L'] [Algebra K L] [Algebra K' L'] (e₁ : K ≃+* K') (e₂ : L ≃+* L')
    (h : (algebraMap K' L').comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap K L)) :
    Algebra.trdeg K L = Algebra.trdeg K' L' := by
  refine le_antisymm (trdeg_le_of_ringEquiv e₁ e₂ h) (trdeg_le_of_ringEquiv e₁.symm e₂.symm ?_)
  ext a
  have := congr($h (e₁.symm a))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply] at this
  simp [this]


open AlgebraicGeometry CategoryTheory Limits in
theorem _root_.GlobalTheory.RelDimFibCrit.trdeg_affine {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (p : PrimeSpectrum Γ(X, V)) :
    @Algebra.trdeg (Y.residueField (f (hV.fromSpec p))) (X.residueField (hV.fromSpec p)) _ _
      (f.residueFieldMap (hV.fromSpec p)).hom.toAlgebra =
    @Algebra.trdeg (p.asIdeal.comap (f.appLE U V e).hom).ResidueField p.asIdeal.ResidueField _ _
      (Ideal.ResidueField.map _ p.asIdeal (f.appLE U V e).hom rfl).toAlgebra := by
  obtain ⟨p, rfl⟩ : ∃ p' : Spec Γ(X, V), p' = p := ⟨p, rfl⟩
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime (p : PrimeSpectrum Γ(X, V))
  set φ := f.appLE U V e
  haveI := hU.isOpenImmersion_fromSpec
  haveI := hV.isOpenImmersion_fromSpec
  have h₁ : hU.fromSpec ((Spec.map φ) p) = f (hV.fromSpec p) :=
    congr($(hU.SpecMap_appLE_fromSpec f hV e) p)
  set q : Spec Γ(Y, U) := (Spec.map φ) p
  let eL := (asIso (hV.fromSpec.residueFieldMap p) ≪≫
    Scheme.Spec.residueFieldIso _ p).commRingCatIsoToRingEquiv
  let eK := (Y.residueFieldCongr h₁.symm ≪≫ asIso (hU.fromSpec.residueFieldMap q) ≪≫
    Scheme.Spec.residueFieldIso _ q).commRingCatIsoToRingEquiv
  have hsq : (Y.residueFieldCongr h₁.symm).hom ≫ hU.fromSpec.residueFieldMap q ≫
      (Scheme.Spec.residueFieldIso _ q).hom ≫
        CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) =
      f.residueFieldMap (hV.fromSpec p) ≫ hV.fromSpec.residueFieldMap p ≫
        (Scheme.Spec.residueFieldIso _ p).hom := by
    erw [← specMap_residueFieldMap_conj_eq_ofHom_map]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc (hU.fromSpec.residueFieldMap q),
      ← Scheme.residueFieldMap_comp, ← Category.assoc (f.residueFieldMap _),
      ← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr (hU.SpecMap_appLE_fromSpec f hV e)]
    exact (congrArg _ (Category.assoc _ _ _)).trans (residueFieldCongr_hom_hom_comp _ _ _)
  refine @trdeg_eq_of_ringEquiv _ _ _ _ _ _ _ _ (RingHom.toAlgebra _) (RingHom.toAlgebra _) eK eL ?_
  ext a
  exact congr((CommRingCat.Hom.hom $hsq) a)

end GlobalTheory.RelDimFibCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanValuationLe
section
namespace GlobalTheory.SpanValuationBound

open IsDedekindDomain

theorem span_valuation_le {L : Type} [Field L] [NumberField L] {S : Set L}
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) {γ : WithZero (Multiplicative ℤ)}
    (hS : ∀ x ∈ S, (HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ) :
    ∀ x ∈ Submodule.span (NumberField.RingOfIntegers L) S,
      (HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => simp
  | add y z _ _ hy hz =>
    exact le_trans (Valuation.map_add _ y z) (max_le hy hz)
  | smul a y _ hy =>
    rw [Algebra.smul_def, map_mul]
    calc (HeightOneSpectrum.valuation L w) (algebraMap _ L a) * (HeightOneSpectrum.valuation L w) y
        ≤ 1 * γ := mul_le_mul' (HeightOneSpectrum.valuation_le_one w a) hy
      _ = γ := one_mul γ

theorem main : ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {S : Set L} (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {γ : WithZero (Multiplicative ℤ)}, (∀ x ∈ S, (IsDedekindDomain.HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ) → ∀ x ∈ Submodule.span (NumberField.RingOfIntegers L) S, (IsDedekindDomain.HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ :=
  @fun _ _ _ _ w _ h => span_valuation_le w h

end GlobalTheory.SpanValuationBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace GlobalTheory.LocalRingGeneralisation

theorem flat_fromSpecStalk (X : Scheme.{0}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have h₂ : IsOpenImmersion (IsAffineOpen.fromSpec hU) := IsAffineOpen.isOpenImmersion_fromSpec hU
  have h₃ : Flat (IsAffineOpen.fromSpec hU) := inferInstance
  exact MorphismProperty.comp_mem @Flat _ _ this h₃

theorem isIso_stalkMap_fromSpecStalk (X : Scheme.{0}) (x : X) (y : Spec (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap y) := by
  have := flat_fromSpecStalk X x
  have hs : SurjectiveOnStalks (X.fromSpecStalk x) := inferInstance
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, (X.fromSpecStalk x).stalkMap_surjective y⟩
  have hl : IsLocalHom ((X.fromSpecStalk x).stalkMap y).hom := inferInstance
  have h := Flat.stalkMap (X.fromSpecStalk x) y
  algebraize [((X.fromSpecStalk x).stalkMap y).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk ((X.fromSpecStalk x) y))
    ((Spec (X.presheaf.stalk x)).presheaf.stalk y)) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := X.presheaf.stalk ((X.fromSpecStalk x) y)) (B := (Spec (X.presheaf.stalk x)).presheaf.stalk y)
  exact FaithfulSMul.algebraMap_injective _ _

end GlobalTheory.LocalRingGeneralisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubrepTopToSubmodule
section
namespace GlobalTheory.SubrepTopBot

open Representation

theorem subrep_bot_toSubmodule {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

theorem subrep_top_toSubmodule {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

theorem main : ∀ {G : Type} [inst : Group G] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] (ρ : Representation ℂ G V), Representation.IsIrreducible ρ ↔ Nontrivial V ∧ ∀ (U : Submodule ℂ V), (∀ (g : G), ∀ v ∈ U, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro G _ V _ _ ρ
  have hbot := subrep_bot_toSubmodule ρ
  have htop := subrep_top_toSubmodule ρ
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
      rw [← Submodule.nontrivial_iff ℂ]
      refine ⟨⟨⊥, ⊤, fun e => hne ?_⟩⟩
      apply Subrepresentation.toSubmodule_injective
      rw [hbot, htop]; exact e
    · intro U hU
      let S : Subrepresentation ρ := ⟨U, fun g v hv => hU g v hv⟩
      rcases h.eq_bot_or_eq_top S with e | e
      · left
        have := congrArg Subrepresentation.toSubmodule e
        rw [hbot] at this; exact this
      · right
        have := congrArg Subrepresentation.toSubmodule e
        rw [htop] at this; exact this
  · rintro ⟨hV, hU⟩
    haveI : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⟨⊥, ⊤, fun e => ?_⟩⟩
      have := congrArg Subrepresentation.toSubmodule e
      rw [hbot, htop] at this
      exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) this
    refine { eq_bot_or_eq_top := ?_ }
    intro S
    rcases hU S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with e | e
    · left; apply Subrepresentation.toSubmodule_injective; rw [hbot]; exact e
    · right; apply Subrepresentation.toSubmodule_injective; rw [htop]; exact e

end GlobalTheory.SubrepTopBot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem sum_log_embedding_add_finsum_log_adicAbv_eq_zero
    (F : Type) [Field F] [NumberField F] (N : F) (hN : N ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
        Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)).Finite ∧
      (∑ σ : F →+* ℂ, Real.log ‖σ N‖) +
        ∑ᶠ v : HeightOneSpectrum (𝓞 F),
          Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) = 0 := by
  have hfun : (fun v : HeightOneSpectrum (𝓞 F) => NumberField.HeightOneSpectrum.adicAbv F v N) =
      (fun w : FinitePlace F => w N) ∘ (FinitePlace.equivHeightOneSpectrum (K := F)).symm := by
    funext v
    simp only [Function.comp, FinitePlace.equivHeightOneSpectrum_symm_apply,
      FinitePlace.norm_embedding]
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      NumberField.HeightOneSpectrum.adicAbv F v N).Finite := by
    rw [hfun, Function.mulSupport_comp_eq_preimage]
    exact Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
      (FinitePlace.hasFiniteMulSupport hN)
  have hpos : ∀ v : HeightOneSpectrum (𝓞 F), 0 < NumberField.HeightOneSpectrum.adicAbv F v N :=
    fun v => (NumberField.HeightOneSpectrum.adicAbv F v).pos hN
  have hprod : ∏ᶠ v : HeightOneSpectrum (𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v N =
      ((|Algebra.norm ℚ N|⁻¹ : ℚ) : ℝ) := by
    rw [← FinitePlace.prod_eq_inv_abs_norm hN,
      ← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm]
    exact congrArg finprod hfun
  have hsub : (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)) ⊆ hfin.toFinset := by
    intro v hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h
    exact hv (by simp only [h, Real.log_one])
  refine ⟨hfin.toFinset.finite_toSet.subset hsub, ?_⟩
  have h1 : ∑ᶠ v : HeightOneSpectrum (𝓞 F),
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) =
      - Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ) := by
    rw [finsum_eq_sum_of_support_subset _ hsub, ← Real.log_prod (fun v _ => (hpos v).ne'),
      ← finprod_eq_prod_of_mulSupport_subset _ (by simp), hprod, Rat.cast_inv, Real.log_inv]
  have h2 : ∑ σ : F →+* ℂ, Real.log ‖σ N‖ = Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ) := by
    have h := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ N)
    simp only [norm_prod] at h
    rw [← Real.log_prod (fun σ _ => by simpa using hN)]
    congr 1
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun σ : F →+* ℂ => ‖σ N‖)
      (fun σ : F →ₐ[ℚ] ℂ => ‖σ N‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← h]
    simp [← Complex.norm_ratCast]
  rw [h1, h2, add_neg_cancel]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoOfForallIntegral
section
namespace GlobalTheory.TendstoOfIntegrals

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology

theorem tendsto_of_forall_integral {L : Type} [Field L] [NumberField L] {ι : Type} {l : Filter ι}
    (f : ι → FiniteAdeleRing (NumberField.RingOfIntegers L) L)
    (b : FiniteAdeleRing (NumberField.RingOfIntegers L) L)
    (hf : ∀ (i : ι) (v : HeightOneSpectrum (NumberField.RingOfIntegers L)),
      (f i : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v ∈
        v.adicCompletionIntegers L)
    (hb : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers L),
      (b : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v ∈
        v.adicCompletionIntegers L)
    (hl : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers L),
      Tendsto (fun i ↦ (f i : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) →
        a.adicCompletion L) v) l
        (𝓝 ((b : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v))) :
    Tendsto f l (𝓝 b) := by

  let A : (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → Set (v.adicCompletion L) :=
    fun v ↦ (v.adicCompletionIntegers L : Set (v.adicCompletion L))
  let g : ι → (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → A v :=
    fun i v ↦ ⟨_, hf i v⟩
  let c : (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → A v := fun v ↦ ⟨_, hb v⟩
  have hg : Tendsto g l (𝓝 c) :=
    tendsto_pi_nhds.2 fun v ↦ tendsto_subtype_rng.2 (hl v)
  have hemb := RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦ v.adicCompletion L)
    (A := A) (𝓕 := cofinite)
  exact (hemb.continuous.tendsto c).comp hg

end GlobalTheory.TendstoOfIntegrals

theorem GlobalTheory.TendstoOfIntegrals.target_check : ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {ι : Type} {l : Filter ι} (f : ι → IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers L) L) (b : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers L) L), (∀ (i : ι) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), (f i : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers L v) → (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), (b : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers L v) → (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), Filter.Tendsto (fun (i : ι) ↦ (f i : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v) l (nhds ((b : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v))) → Filter.Tendsto f l (nhds b) := by
  intro L _ _ ι l f b hf hb hl
  exact GlobalTheory.TendstoOfIntegrals.tendsto_of_forall_integral f b hf hb hl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeAevalLeOfLinear
section
namespace GlobalTheory.AevalTotalDegreeLinear

open MvPolynomial

theorem totalDegree_aeval_le_of_linear {κ : Type} (f : κ → MvPolynomial κ ℂ)
    (hf : ∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) (P : MvPolynomial κ ℂ) :
    MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P)
      ≤ MvPolynomial.totalDegree P := by
  classical
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun s hs => ?_
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  have hprod : totalDegree (s.prod fun i k => f i ^ k) ≤ s.sum fun _ k => k := by
    rw [Finsupp.prod, Finsupp.sum]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine (totalDegree_pow _ _).trans ?_
    calc s i * totalDegree (f i) ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
      _ = s i := mul_one _
  refine hprod.trans ?_
  exact Finset.le_sup (f := fun s : κ →₀ ℕ => s.sum fun _ e => e) hs

theorem main : ∀ {κ : Type} (f : κ → MvPolynomial κ ℂ), (∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial κ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => totalDegree_aeval_le_of_linear f hf P

end GlobalTheory.AevalTotalDegreeLinear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperTriangularMul
section
namespace GlobalTheory.UpperTriangularMul

theorem upperTriangular_mul :
    ∀ {n : ℕ} {R : Type} [inst : CommRing R] {M N : Matrix (Fin n) (Fin n) R},
      (∀ (a i : Fin n), i < a → M a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → N a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → (M * N) a i = (0 : R)) ∧
        ∀ (i : Fin n), (M * N) i i = M i i * N i i := by
  intro n R _ M N hM hN
  refine ⟨fun a i hia => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j a with h | h
    · rw [hM a j h, zero_mul]
    · rw [hN j i (lt_of_lt_of_le hia h), mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hM i j h, zero_mul]
    · rw [hN j i h, mul_zero]

end GlobalTheory.UpperTriangularMul
end

