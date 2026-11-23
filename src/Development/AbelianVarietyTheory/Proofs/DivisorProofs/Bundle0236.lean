module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsFiniteFlatRankOfFiniteFlatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0195
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChartLocalizationFiniteTypeFormallyUnramifiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0178
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0198

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenAffineHilbertChartBasicLocus
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff.Locus

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r N : ℕ}

theorem secs_props {T : Scheme.{0}} (y : (functor A B r).obj (op T)) (U : T.Opens)
    (hU : IsAffineOpen U) :
    (letI := ((proj y).app U).hom.toAlgebra;
    Module.Finite Γ(T, U) Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) ∧
      Module.Flat Γ(T, U) Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) ∧
      ∀ q : PrimeSpectrum Γ(T, U), Module.rankAtStalk Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) q = r) := by
  obtain ⟨h1, h2, h3⟩ := y.2.2
  have hV : IsAffineOpen ((proj y) ⁻¹ᵁ U) := hU.preimage (proj y)
  have hpb := GlobalTheory.isPullback_fromSpec_app_preimage_of_affine (proj y) hU hV
  have hfin : IsFinite (Spec.map ((proj y).app U)) := MorphismProperty.of_isPullback hpb h1
  have hflat : Flat (Spec.map ((proj y).app U)) := MorphismProperty.of_isPullback hpb h2
  have h1' : ((proj y).app U).hom.Finite := (IsFinite.SpecMap_iff _).1 hfin
  have h2' : ((proj y).app U).hom.Flat := Flat.SpecMap_iff.1 hflat
  letI := ((proj y).app U).hom.toAlgebra
  haveI : Module.Finite Γ(T, U) Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) := h1'
  haveI : Module.Flat Γ(T, U) Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) := h2'
  refine ⟨inferInstance, inferInstance, fun q => ?_⟩
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb q
  rw [h3] at e
  rw [← Scheme.Hom.finrank_SpecMap_algebraMap]
  exact e

theorem isOpen_bad_compl (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) (hU : IsAffineOpen U) :
    IsOpen (bad e σ y U)ᶜ := by
  letI := ((proj y).app U).hom.toAlgebra
  haveI := (secs_props y U hU).1
  exact (Module.isClosed_support (R := Γ(T, U))).isOpen_compl

theorem isCompact_bad_compl (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) (hU : IsAffineOpen U) :
    IsCompact (bad e σ y U)ᶜ := by
  letI := ((proj y).app U).hom.toAlgebra
  obtain ⟨h1, h2, h3⟩ := secs_props y U hU
  exact GlobalTheory.T.free_module_complement_support_compact _ _ r h3 (gens e σ y U)

theorem basic_iff (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) :
    Basic A B e σ y ↔ ∀ U : T.affineOpens, bad e σ y U = ∅ := by
  refine forall_congr' fun U => ?_
  letI := ((proj y).app U).hom.toAlgebra
  obtain ⟨h1, h2, h3⟩ := secs_props y U U.2
  have hf : (fun c : Fin r → Γ(T, U) => ∑ k, ((proj y).app U).hom (c k) * gens e σ y U k) =
      Fintype.linearCombination Γ(T, U) (gens e σ y U) := by
    ext c
    simp [Fintype.linearCombination_apply, Algebra.smul_def]
    rfl
  change Function.Bijective (fun c : Fin r → Γ(T, U) =>
    ∑ k, ((proj y).app U).hom (c k) * gens e σ y U k) ↔ _
  rw [hf]
  refine ⟨fun hb => ?_, fun hb => GlobalTheory.T.linearCombination_bijective_of_rankAtStalk_eq _ _ r h3 _ hb⟩
  show Module.support _ _ = ∅
  rw [Module.support_eq_empty_iff, Submodule.Quotient.subsingleton_iff,
    ← Fintype.range_linearCombination, LinearMap.range_eq_top]
  exact hb.2

theorem appLE_congr_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V (e ▸ h) := by
  subst e; rfl

theorem gens_pbMap (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T T' : Scheme.{0}}
    (a : T' ⟶ T) (y : (functor A B r).obj (op T)) (U : T.Opens) (U' : T'.Opens)
    (hleG : proj ((functor A B r).map a.op y) ⁻¹ᵁ U' ≤ pbMap a y ⁻¹ᵁ (proj y ⁻¹ᵁ U)) (k : Fin r) :
    ((pbMap a y).appLE (proj y ⁻¹ᵁ U) _ hleG).hom (gens e σ y U k) =
      gens e σ ((functor A B r).map a.op y) U' k := by
  simp only [gens]
  rw [← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE]
  rw [appLE_congr_eq (pbMap_fst a y)]

theorem bad_nat (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T T' : Scheme.{0}}
    (a : T' ⟶ T) (y : (functor A B r).obj (op T)) (U : T.Opens) (hU : IsAffineOpen U)
    (U' : T'.Opens) (hU' : IsAffineOpen U') (h : U' ≤ a ⁻¹ᵁ U) (x : T') (hx : x ∈ U') :
    hU'.primeIdealOf ⟨x, hx⟩ ∈ bad e σ ((functor A B r).map a.op y) U' ↔
      hU.primeIdealOf ⟨a x, h hx⟩ ∈ bad e σ y U := by
  have sq := isPullback_pbMap a y
  have hleG : proj ((functor A B r).map a.op y) ⁻¹ᵁ U' ≤ pbMap a y ⁻¹ᵁ (proj y ⁻¹ᵁ U) := by
    intro z hz
    show (pbMap a y ≫ proj y) z ∈ U
    rw [sq.w, Scheme.Hom.comp_apply]
    exact h hz
  haveI : IsFinite (proj y) := y.2.2.1
  have hP := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq inferInstance hU hU' h hleG
  have fin : ((proj y).app U).hom.Finite := (secs_props y U hU).1
  have H := GlobalTheory.T.mem_support_quotient_span_iff_of_isPushout' _ _ _ _ _ _ _ _ hP fin (gens e σ y U) (hU'.primeIdealOf ⟨x, hx⟩)
  rw [IsAffineOpen.comap_primeIdealOf_appLE U hU U' hU' h hx] at H
  have hg : (fun i => ((pbMap a y).appLE (proj y ⁻¹ᵁ U) _ hleG).hom (gens e σ y U i)) =
      gens e σ ((functor A B r).map a.op y) U' := funext (gens_pbMap e σ a y U U' hleG)
  rw [hg] at H
  exact H

theorem map_id_apply' {T : Scheme.{0}} (y : (functor A B r).obj (op T)) :
    (functor A B r).map (𝟙 T).op y = y := by
  rw [op_id, CategoryTheory.Functor.map_id_apply]

theorem bad_local (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U₁ U₂ : T.Opens) (h₁ : IsAffineOpen U₁) (h₂ : IsAffineOpen U₂)
    (x : T) (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂) :
    h₁.primeIdealOf ⟨x, hx₁⟩ ∈ bad e σ y U₁ ↔ h₂.primeIdealOf ⟨x, hx₂⟩ ∈ bad e σ y U₂ := by
  obtain ⟨U₀, hU₀, hx₀, hle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) (show x ∈ U₁ ⊓ U₂ from ⟨hx₁, hx₂⟩)
  have k₁ := bad_nat e σ (𝟙 T) y U₁ h₁ U₀ hU₀ (fun z hz => (hle hz).1) x hx₀
  have k₂ := bad_nat e σ (𝟙 T) y U₂ h₂ U₀ hU₀ (fun z hz => (hle hz).2) x hx₀
  rw [map_id_apply'] at k₁ k₂
  exact k₁.symm.trans k₂

theorem primeIdealOf_fromSpec {T : Scheme.{0}} {U : T.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(T, U)) (h : hU.fromSpec q ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec q, h⟩ = q :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)

theorem mem_goodSet_iff (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) (hU : IsAffineOpen U) (x : T) (hx : x ∈ U) :
    x ∈ goodSet e σ y ↔ hU.primeIdealOf ⟨x, hx⟩ ∉ bad e σ y U := by
  constructor
  · intro hmem
    obtain ⟨U₁, q, hq, rfl⟩ := Set.mem_iUnion.mp hmem
    have h₁ : IsAffineOpen (U₁ : T.Opens) := U₁.2
    have hx₁ : h₁.fromSpec q ∈ (U₁ : T.Opens) := by
      rw [← SetLike.mem_coe, ← h₁.range_fromSpec]; exact ⟨q, rfl⟩
    have key : h₁.primeIdealOf ⟨h₁.fromSpec q, hx₁⟩ = q := primeIdealOf_fromSpec h₁ q hx₁
    rw [← bad_local e σ y U₁ U h₁ hU _ hx₁ hx, key]
    exact hq
  · intro hq
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, _, hq, hU.fromSpec_primeIdealOf _⟩

theorem goodSet_map (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T T' : Scheme.{0}}
    (a : T' ⟶ T) (y : (functor A B r).obj (op T)) (x : T') :
    x ∈ goodSet e σ ((functor A B r).map a.op y) ↔ a x ∈ goodSet e σ y := by
  obtain ⟨U, hU, hxU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) (show a x ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨U', hU', hxU', hle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T'.isBasis_affineOpens) (show x ∈ a ⁻¹ᵁ U from hxU)
  rw [mem_goodSet_iff e σ _ U' hU' x hxU', mem_goodSet_iff e σ y U hU (a x) hxU,
    bad_nat e σ a y U hU U' hU' hle x hxU']

theorem isOpenMap_fromSpec {T : Scheme.{0}} {U : T.Opens} (hU : IsAffineOpen U) :
    IsOpenMap hU.fromSpec :=
  hU.fromSpec.isOpenEmbedding.isOpenMap

theorem isOpen_goodSet (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) : IsOpen (goodSet e σ y) :=
  isOpen_iUnion fun U => isOpenMap_fromSpec U.2 _ (isOpen_bad_compl e σ y U U.2)

theorem basic_iff_goodSet (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) : Basic A B e σ y ↔ goodSet e σ y = Set.univ := by
  rw [basic_iff, Set.eq_univ_iff_forall]
  constructor
  · intro h x
    obtain ⟨U, hU, hxU, -⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) (show x ∈ (⊤ : T.Opens) from trivial)
    rw [mem_goodSet_iff e σ y U hU x hxU, h ⟨U, hU⟩]
    exact Set.notMem_empty _
  · intro h U
    refine Set.eq_empty_iff_forall_notMem.mpr fun q hq => ?_
    have hU : IsAffineOpen (U : T.Opens) := U.2
    have hx : hU.fromSpec q ∈ (U : T.Opens) := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨q, rfl⟩
    have := (mem_goodSet_iff e σ y U hU _ hx).mp (h _)
    rw [primeIdealOf_fromSpec hU q hx] at this
    exact this hq

theorem exists_basic_locus : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0})
    (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)), ∃ W : Z.Opens,
      (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Z), Set.range a ⊆ (W : Set Z) ↔
        GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map a.op y)) ∧
      (CompactSpace Z → IsCompact (W : Set Z)) := by
  intro A B _ _ _ N r e σ Z y
  refine ⟨⟨goodSet e σ y, isOpen_goodSet e σ y⟩, fun Z' a => ?_, fun hZ => ?_⟩
  · rw [basic_iff_goodSet, Set.eq_univ_iff_forall, Set.range_subset_iff]
    exact forall_congr' fun x => (goodSet_map e σ a y x).symm
  · have hcov : Set.univ ⊆ ⋃ U : Z.affineOpens, ((U : Z.Opens) : Set Z) := by
      intro x _
      obtain ⟨U, hU, hxU, -⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens) (show x ∈ (⊤ : Z.Opens) from trivial)
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ (fun U : Z.affineOpens => U.1.isOpen) hcov
    have heq : goodSet e σ y = ⋃ U ∈ t, U.2.fromSpec '' (bad e σ y U)ᶜ := by
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
        refine Set.mem_iUnion₂.mpr ⟨U, hUt, _, (mem_goodSet_iff e σ y U U.2 x hxU).mp hx, ?_⟩
        exact U.2.fromSpec_primeIdealOf _
      · exact Set.iUnion₂_subset fun U _ => Set.subset_iUnion
          (fun U : Z.affineOpens => U.2.fromSpec '' (bad e σ y U)ᶜ) U
    show IsCompact (goodSet e σ y)
    rw [heq]
    exact t.isCompact_biUnion fun U _ =>
      (isCompact_bad_compl e σ y U U.2).image U.2.fromSpec.continuous

end GlobalTheory.HilbAff.Locus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyPowMulEqOneStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_poly_pow_mul_eq_one' : ∀ (n l : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), 0 < l → IsUnit B → ∃ p : ℂ[X], (aeval B p) ^ l * B = 1 := by
  first | (exact @GlobalTheory.exists_poly_pow_mul_eq_one) | (exact GlobalTheory.exists_poly_pow_mul_eq_one) | (intros; apply GlobalTheory.exists_poly_pow_mul_eq_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyVanishingOfFibre
section
open IsLocalRing

namespace GlobalTheory.DenseSec
open TensorProduct

theorem exists_poly_vanishing_of_fibre : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω], IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ Q : MvPolynomial (Fin g) Ω, Q ≠ 0 ∧ ∀ a : A →ₐ[R] Ω, a h ≠ 0 → GlobalTheory.DenseSec.pt a f = 0 → MvPolynomial.eval (fun i => a (t i)) Q = 0 := by
  intro R _ A _ _ g t h hE Ω _ _ hirr f hf
  have hN : (nilradical (TensorProduct R Ω A)).IsPrime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.1 hirr
  have kill : ∀ (a : A →ₐ[R] Ω) (x : TensorProduct R Ω A), x ∈ nilradical (TensorProduct R Ω A) → GlobalTheory.DenseSec.pt a x = 0 := by
    intro a x hx
    exact ((mem_nilradical.1 hx).map (GlobalTheory.DenseSec.pt a)).eq_zero
  have pth : ∀ (a : A →ₐ[R] Ω) (x : A), GlobalTheory.DenseSec.pt a (1 ⊗ₜ[R] x) = a x := by
    intro a x
    simp [GlobalTheory.DenseSec.pt]
  have ptw : ∀ (a : A →ₐ[R] Ω) (w : Ω), GlobalTheory.DenseSec.pt a (w ⊗ₜ[R] 1) = w := by
    intro a w
    simp [GlobalTheory.DenseSec.pt]
  by_cases h1 : (1 ⊗ₜ[R] h : TensorProduct R Ω A) ∈ nilradical (TensorProduct R Ω A)
  · refine ⟨1, one_ne_zero, fun a ha _ => ?_⟩
    exact absurd (by rw [← pth a h]; exact kill a _ h1) ha
  set N := nilradical (TensorProduct R Ω A)
  set u : TensorProduct R Ω A ⧸ N := Ideal.Quotient.mk N (1 ⊗ₜ[R] h)
  have hu : u ≠ 0 := by
    simpa [u, Ideal.Quotient.eq_zero_iff_mem] using h1
  letI : IsDomain (TensorProduct R Ω A ⧸ N) := Ideal.Quotient.isDomain N
  have hle : Submonoid.powers u ≤ nonZeroDivisors (TensorProduct R Ω A ⧸ N) := powers_le_nonZeroDivisors_of_noZeroDivisors hu
  letI : IsDomain (Localization.Away u) := IsLocalization.isDomain_localization hle
  obtain ⟨hFT, hFU⟩ := GlobalTheory.T.etaleChart_localization_finiteType_formallyUnramified R A g t h hE Ω N
  letI : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away u) :=
    (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
  have hf' : algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N f) ≠ 0 := by
    intro h0
    rw [map_eq_zero_iff _ (IsLocalization.injective (Localization.Away u) hle), Ideal.Quotient.eq_zero_iff_mem] at h0
    exact hf (mem_nilradical.1 h0)
  obtain ⟨Q, hQ, d, hd⟩ := _root_.GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified (MvPolynomial (Fin g) Ω) (Localization.Away u) _ hf'
  refine ⟨Q, hQ, fun a ha hfa => ?_⟩
  let φ : TensorProduct R Ω A ⧸ N →+* Ω := Ideal.Quotient.lift N (GlobalTheory.DenseSec.pt a).toRingHom (fun x hx => kill a x hx)
  have hφu : IsUnit (φ u) := by
    simp only [φ, u, Ideal.Quotient.lift_mk]
    exact isUnit_iff_ne_zero.2 (by simpa [pth] using ha)
  let χ : Localization.Away u →+* Ω := IsLocalization.Away.lift u hφu
  have hχ : ∀ x : TensorProduct R Ω A, χ (algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N x)) = GlobalTheory.DenseSec.pt a x := by
    intro x
    simp [χ, φ, IsLocalization.Away.lift]
  have hP : χ.comp (algebraMap (MvPolynomial (Fin g) Ω) (Localization.Away u)) = MvPolynomial.eval₂Hom (RingHom.id Ω) (fun i => a (t i)) := by
    apply MvPolynomial.ringHom_ext
    · intro w
      show χ (MvPolynomial.aeval _ (MvPolynomial.C w)) = _
      have e : algebraMap Ω (TensorProduct R Ω A ⧸ N) w = Ideal.Quotient.mk N (w ⊗ₜ[R] 1) := rfl
      rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply Ω (TensorProduct R Ω A ⧸ N) (Localization.Away u), e, hχ, ptw]
      simp
    · intro i
      show χ (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, hχ, pth]
      simp
  have := congrArg χ hd
  rw [← RingHom.comp_apply, hP, map_mul, hχ, hfa, zero_mul] at this
  exact this

end GlobalTheory.DenseSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularNearOfRegularQuotientPrimeStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_near_of_regular_quotient_prime : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (p : Ideal B) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) → IsRegularLocalRing (Localization.AtPrime q) := by
  first | exact @GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient | exact GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient | (intros; apply GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondOrderNbhd
section
open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

theorem step_single {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C}
    {ρ₁ ρ₂ : Hol W →+* C} (a : Fin g) (e : C) (he : e ∈ J) (h2 : e * e = 0)
    (h : ∀ x, ρ₂ x = ρ₁ x + ρ₁ (dw a x) * e) : Step J ρ₁ ρ₂ := by
  refine ⟨Pi.single a e, fun c ↦ ?_, fun c d ↦ ?_, fun x ↦ ?_⟩
  · by_cases hc : c = a
    · subst hc; simpa using he
    · simp [hc]
  · by_cases hc : c = a
    · by_cases hd : d = a
      · subst hc; subst hd; simpa using h2
      · simp [hd]
    · simp [hc]
  · rw [h, Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [hc]
    · simp

theorem exists_second_order_nbhd : ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (K : Charts F) (k : K.K) (a b : Fin g), ∃ (T : K.Obj) (φ₀ φ₁ φ₂ φ₃ : K.triv k ⟶ T) (e₁ e₂ : T.C), φ₀.deg = 0 ∧ φ₁.deg = 0 ∧ φ₂.deg = 0 ∧ φ₃.deg = 0 ∧ e₁ ∈ T.J ∧ e₂ ∈ T.J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x : Hol (K.W k), φ₁.φ x = φ₀.φ x + φ₀.φ (dw a x) * e₁) ∧ (∀ x : Hol (K.W k), φ₂.φ x = φ₀.φ x + φ₀.φ (dw b x) * e₂) ∧ (∀ x : Hol (K.W k), φ₃.φ x = φ₁.φ x + φ₁.φ (dw b x) * e₂) ∧ (∀ x : Hol (K.W k), φ₃.φ x = φ₂.φ x + φ₂.φ (dw a x) * e₁) ∧ ∀ x : Hol (K.W k), φ₀.φ x * e₁ * e₂ = 0 → x = 0 := by
  intro I _ g Λ _ F K k a b
  obtain ⟨C, _, J, φ₀, φ₁, φ₂, φ₃, e₁, e₂, hJ, h1, h2, h11, h22, H1, H2, H3, H4, H5⟩ :=
    _root_.GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd (Hol (K.W k)) (dw a) (dw b) (_root_.GlobalTheory.AnPer.dw_comm I g (K.W k) a b)
  let T : K.Obj :=
    { k := k, C := C, alg := (φ₀.comp (K.cst k)).toAlgebra, J := J, nil := hJ, ρ := φ₀, ρ_cst := fun _ ↦ rfl }
  have hs : T.ρ.comp (K.sh (K.le_refl k)) = φ₀ := RingHom.ext fun f ↦ congrArg φ₀ (K.sh_refl _ f)
  have c0 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₀ := by rw [hs]; exact Relation.ReflTransGen.refl
  have c1 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₁ := Relation.ReflTransGen.tail c0 (step_single a e₁ h1 h11 H1)
  have c2 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₂ := Relation.ReflTransGen.tail c0 (step_single b e₂ h2 h22 H2)
  have c3 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₃ := Relation.ReflTransGen.tail c1 (step_single b e₂ h2 h22 H3)
  have a1 : ∀ f, φ₁ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H1, dw_cst]; simp
  have a2 : ∀ f, φ₂ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H2, dw_cst]; simp
  have a3 : ∀ f, φ₃ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H3, dw_cst, a1]; simp
  exact ⟨T, fromTriv T (K.le_refl k) φ₀ (fun _ ↦ rfl) c0, fromTriv T (K.le_refl k) φ₁ a1 c1,
    fromTriv T (K.le_refl k) φ₂ a2 c2, fromTriv T (K.le_refl k) φ₃ a3 c3, e₁, e₂, rfl, rfl, rfl, rfl,
    h1, h2, h11, h22, H1, H2, H3, H4, H5⟩

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointOfGeometricallyDomain
section
open scoped TensorProduct

namespace GlobalTheory.SepPoint

theorem exists_sepBasis (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    (hB : Algebra.FiniteType k B)
    (hH : ∀ p : ℕ, p.Prime → CharP k p → ∀ s : Finset (FractionRing B),
      LinearIndepOn k _root_.id (s : Set (FractionRing B)) →
        LinearIndepOn k (· ^ p) (s : Set (FractionRing B))) :
    ∃ s : Finset (FractionRing B), IsTranscendenceBasis k ((↑) : s → FractionRing B) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set (FractionRing B)))
        (FractionRing B) := by
  haveI : Algebra.EssFiniteType k B := inferInstance
  haveI : Algebra.EssFiniteType B (FractionRing B) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType k (FractionRing B) := Algebra.EssFiniteType.comp k B _
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField k _
  · haveI : ExpChar k p := .prime hp.out
    exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      p hp.out (hH p hp.out hpk)

theorem core (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : IsTranscendenceBasis k ((↑) : s → F))
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F)
    (B : Subalgebra k F) (hB : B.FG) : Nonempty (B →ₐ[k] SeparableClosure k) := by
  obtain ⟨T, rfl⟩ := hB
  haveI : IsIntegrallyClosed (Algebra.adjoin k (s : Set F)) := isIntegrallyClosed_adjoin k F s hs.1
  obtain ⟨θ, hθ, H, hH0, U, V, hUV, hT⟩ := GlobalTheory.T.exists_primitive_element_separability_certificate k F s hs hsep T
  obtain ⟨ev, hev⟩ := exists_ev k F s hs.1 H hH0
  let R := Algebra.adjoin k (s : Set F)
  let f := minpoly R θ
  let e : R →+* SeparableClosure k := (ev : R →+* SeparableClosure k)
  have hmon : f.Monic := minpoly.monic hθ
  have hsepa : (f.map e).Separable := by
    have h1 := congrArg (Polynomial.map e) hUV
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C] at h1
    refine ⟨Polynomial.C (e H)⁻¹ * U.map e, Polynomial.C (e H)⁻¹ * V.map e, ?_⟩
    rw [Polynomial.derivative_map, mul_assoc, mul_assoc, ← mul_add, h1, ← Polynomial.C_mul,
      inv_mul_cancel₀ (show e H ≠ 0 from hev), Polynomial.C_1]
  have hdeg : (f.map e).degree ≠ 0 := by
    rw [hmon.degree_map]
    exact (minpoly.degree_pos hθ).ne'
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root _ hdeg hsepa
  have hr' : Polynomial.eval₂ (ev : R →+* SeparableClosure k) r f = 0 := by
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at hr
  obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.extend_alg_hom_adjoin_integral_root k F (SeparableClosure k) R θ hθ ev r hr'
  have hHS : (H : F) ∈ Algebra.adjoin k (insert θ (R : Set F)) :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ H.2)
  exact GlobalTheory.T.nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero k F (SeparableClosure k) _ ψ ⟨H, hHS⟩
    (by rw [hψ _ H.2 hHS]; exact hev) (T : Set F) hT

theorem exists_sepPoint : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B],
    Algebra.FiniteType k B →
    (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K →
      IsDomain (K ⊗[k] B)) →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  intro k B _ _ _ hB hK
  haveI : IsDomain (k ⊗[k] B) := hK k inferInstance inferInstance
  haveI : IsDomain B := (Algebra.TensorProduct.lid k B).symm.toMulEquiv.isDomain
  obtain ⟨s, hs, hsep⟩ := exists_sepBasis k B hB
    (fun p hp hpk => GlobalTheory.T.linearIndepOn_frob_pow_of_isDomain_tensor_insep k B p hp hpk hK)
  let g : B →ₐ[k] FractionRing B := IsScalarTower.toAlgHom k B (FractionRing B)
  have hfg : g.range.FG := by
    rw [← Algebra.map_top]
    exact hB.out.map g
  obtain ⟨ψ⟩ := core k (FractionRing B) s hs hsep g.range hfg
  exact _root_.GlobalTheory.exists_finite_separable_point_of_separableClosure_point k B hB ⟨ψ.comp g.rangeRestrict⟩

end GlobalTheory.SepPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallConjFixedOfValuationStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_conjFixed_of_valuation : ∀ (K : GlobalTheory.UnitLemma.UQ) (k : ℕ), 1 ≤ k → ∃ t : K.O, K.Small t ∧ GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k := by
  first | exact @GlobalTheory.UnitLemma.exists_small_val | exact GlobalTheory.UnitLemma.exists_small_val | (intros; apply GlobalTheory.UnitLemma.exists_small_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulDvdOfLocalizationAtPrimeTensorStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_dvd_of_localization_atPrime_tensor' : ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    (Q : Ideal O) [Q.IsPrime] (b : R) (m : O ⊗[R] C),
    (∃ m' : Localization.AtPrime Q ⊗[R] C,
      (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C m = algebraMap R (Localization.AtPrime Q) b • m') →
    ∃ s ∉ Q, ∃ m' : O ⊗[R] C, s • m = algebraMap R O b • m' := by
  first | (exact @GlobalTheory.exists_smul_dvd_of_localization_atPrime_tensor) | (exact GlobalTheory.exists_smul_dvd_of_localization_atPrime_tensor) | (intros; apply GlobalTheory.exists_smul_dvd_of_localization_atPrime_tensor  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorInductionCharStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorInduction_char' : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ χ : G → ℂ, IsChar ℂ ℂ χ → ∃ X : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X ∧ (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  first | (exact @GlobalTheory.Shin.TensorInd.exists_tensorInduction_char) | (exact GlobalTheory.Shin.TensorInd.exists_tensorInduction_char) | (intros; apply GlobalTheory.Shin.TensorInd.exists_tensorInduction_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRegroupCommutativeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_doubleCoset_regroup_commutative : ∀ (G : Type) [Group G] (T Γ C K' : Subgroup G) (φ : G → ℂ), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → C ≤ T → (∀ x : G, T ⊓ K'.map (MulAut.conj x).toMonoidHom ≤ C ∧ (T ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0) → (∀ t ∈ T, ∀ k ∈ K', ∀ x, φ (t * x * k) = φ x) → ∑ᶠ q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G), ((Nat.card ((Γ ⊓ T) ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out q) = (Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (Γ ⊓ C : Subgroup G) : ℂ) * ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K' : Set G), (((T ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * φ (Quotient.out q) := by
  first | exact @GlobalTheory.finsum_doubleCoset_regroup | exact GlobalTheory.finsum_doubleCoset_regroup | (intros; apply GlobalTheory.finsum_doubleCoset_regroup <;> assumption)
end

