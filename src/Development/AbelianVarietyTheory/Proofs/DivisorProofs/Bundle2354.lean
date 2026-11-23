module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2301
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelRelAmpleAndPrincipalAbelianLocus
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroShortGeneratorSectionImageModel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModelGen

theorem basicOpen_sum_le {X : Scheme.{0}} {U : X.Opens} {ι : Type} (t : Finset ι) (f : ι → Γ(X, U)) :
    X.basicOpen (∑ j ∈ t, f j) ≤ ⨆ j ∈ t, X.basicOpen (f j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    intro x hx
    have hxU : x ∈ U := X.basicOpen_le _ hx
    rw [Scheme.mem_basicOpen _ _ _ hxU, map_add (f := _)] at hx
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hx with h | h
    · have : x ∈ X.basicOpen (f a) := (Scheme.mem_basicOpen _ _ _ hxU).2 h
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, TopologicalSpace.Opens.mem_iSup.2 ⟨Finset.mem_insert_self a t, this⟩⟩
    · have : x ∈ X.basicOpen (∑ j ∈ t, f j) := (Scheme.mem_basicOpen _ _ _ hxU).2 h
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (ih this)
      obtain ⟨hjt, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, TopologicalSpace.Opens.mem_iSup.2 ⟨Finset.mem_insert_of_mem hjt, hj⟩⟩

theorem exists_mem_nonzeroLocus_of_isShortGen : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen Nm W w abelian₂ → ∀ x : X, ∃ (j : Fin n) (hj : w j ∈ W), x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s ⟨w j, hj⟩) := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev n w abelian₂ hg x
  have hx : x ∈ (⨆ v, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s v)) := by rw [hM.bpf]; trivial
  obtain ⟨v, hv⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hw : ∀ j, w j ∈ W := fun j => (hg.gen _).2 (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 ((hg.gen (v : V)).1 v.2)
  have hsum : (v : V) = ∑ j, ((c j : 𝓞 K)) • ((⟨w j, hw j⟩ : W) : V) := by
    rw [← hc]; refine Finset.sum_congr rfl fun j _ => ?_
    simp [Int.cast_smul_eq_zsmul]
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hv
  rw [_root_.GlobalTheory.ImageModel.sec_linear K V Ω Nm W ev D X p L ψ s hM hev n (fun j => (c j : 𝓞 K)) (fun j => ⟨w j, hw j⟩) v hsum k] at hk
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (basicOpen_sum_le _ _ hk)
  obtain ⟨-, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
  rw [Scheme.basicOpen_mul] at hj
  exact ⟨j, hw j, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hj.2⟩⟩

end GlobalTheory.ImageModelGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormBasicOpenFiniteFreeBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.NormBC

open TensorProduct

theorem norm_map_of_basis {A A' B B' : Type} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B'] (ρ : A →+* A') (ψ : B →+* B')
    (hc : ∀ a, ψ (algebraMap A B a) = algebraMap A' B' (ρ a)) {J : Type} [Fintype J] [DecidableEq J]
    (e : Module.Basis J A B) (e' : Module.Basis J A' B') (he : ∀ i, ψ (e i) = e' i) (f : B) :
    Algebra.norm A' (ψ f) = ρ (Algebra.norm A f) := by
  rw [Algebra.norm_eq_matrix_det e, Algebra.norm_eq_matrix_det e', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul]
  have h : ψ f * e' j = ∑ k, ρ (e.repr (f * e j) k) • e' k := by
    rw [← he j, ← map_mul]
    conv_lhs => rw [← e.sum_repr (f * e j)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Algebra.smul_def, map_mul, hc, he]
  rw [h, e'.repr_sum_self]

theorem exists_basis_of_ringEquiv {S₀ A T₀ B : Type} [CommRing S₀] [CommRing A] [CommRing T₀]
    [CommRing B] [Algebra S₀ A] [Algebra S₀ T₀] [Algebra A B] {J : Type}
    (c : Module.Basis J S₀ T₀) (Φ : A ⊗[S₀] T₀ ≃+* B) (hΦ : ∀ a, Φ (a ⊗ₜ 1) = algebraMap A B a) :
    ∃ e : Module.Basis J A B, ∀ i, e i = Φ (1 ⊗ₜ c i) := by
  let L : A ⊗[S₀] T₀ ≃ₗ[A] B := Φ.toAddEquiv.toLinearEquiv (fun a x => by
    show Φ (a • x) = a • Φ x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← hΦ]
    rfl)
  exact ⟨(Algebra.TensorProduct.basis A c).map L, fun i => by
    simp [L, Algebra.TensorProduct.basis_apply]⟩

theorem exists_basis_Gamma {R R₁ : Type} [CommRing R] [CommRing R₁] [Algebra R R₁] {J : Type}
    [Fintype J] (c' : Module.Basis J R R₁) :
    letI := ((spMap (algebraMap R R₁)).appLE ⊤ ⊤ le_top).hom.toAlgebra
    Nonempty (Module.Basis J Γ(Sp R, ⊤) Γ(Sp R₁, ⊤)) := by
  letI := ((spMap (algebraMap R R₁)).appLE ⊤ ⊤ le_top).hom.toAlgebra
  let σ : Γ(Sp R, ⊤) ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let σ₁ : Γ(Sp R₁, ⊤) ≃+* R₁ := (Scheme.ΓSpecIso (CommRingCat.of R₁)).commRingCatIsoToRingEquiv
  have hnat : ∀ a, σ₁ (algebraMap Γ(Sp R, ⊤) Γ(Sp R₁, ⊤) a) = algebraMap R R₁ (σ a) := fun a => by
    have h := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R R₁)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    rw [AffDesc.appTop_eq_appLE] at h
    exact h
  let E : Γ(Sp R₁, ⊤) ≃ₗ[Γ(Sp R, ⊤)] (J → Γ(Sp R, ⊤)) :=
    { toFun := fun y i => σ.symm (c'.repr (σ₁ y) i)
      invFun := fun g => σ₁.symm (∑ i, σ (g i) • c' i)
      map_add' := fun y y' => by funext i; simp
      map_smul' := fun a y => by
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [Algebra.smul_def, map_mul, hnat, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
          smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
      left_inv := fun y => by
        simp only [RingEquiv.apply_symm_apply, c'.sum_repr, RingEquiv.symm_apply_apply]
      right_inv := fun g => by
        funext i
        simp only [RingEquiv.apply_symm_apply, c'.repr_sum_self, RingEquiv.symm_apply_apply] }
  exact ⟨Module.Basis.ofEquivFun E⟩

theorem mem_primeIdealOf_iff' {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (s : Γ(X, U)) : s ∈ (hU.primeIdealOf x).asIdeal ↔ x.1 ∉ X.basicOpen s := by
  have h : (hU.primeIdealOf x : Spec Γ(X, U)) ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen s ↔
      x.1 ∈ X.basicOpen s := by
    conv_rhs => rw [← hU.fromSpec_primeIdealOf x]
    rfl
  rw [← h, hU.fromSpec_preimage_basicOpen]
  exact not_not.symm

end GlobalTheory.Mum.NormBC

namespace GlobalTheory.Mum.NormBC

open TensorProduct

theorem exists_norm_basicOpen : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁]
    [Module.Finite R R₁] [Module.Free R R₁] (X X₁ : Scheme.{0}) (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁)
    (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) → ∀ (V : X.Opens),
    IsCompact (V : Set X) → IsQuasiSeparated (V : Set X) → ∀ f : Γ(X₁, b ⁻¹ᵁ V), ∃ n : Γ(X, V),
    ∀ x : X, x ∈ X.basicOpen n ↔ x ∈ V ∧ ∀ z : X₁, b z = x → z ∈ X₁.basicOpen f := by
  intro R R₁ _ _ _ _ _ X X₁ p p₁ b H V hVc hVq f
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨0, fun x => ?_⟩
    exact absurd (Subsingleton.elim _ _ : (p x).asIdeal = ⊤) (p x).isPrime.ne_top
  let c' := Module.Free.chooseBasis R R₁
  letI a0 : Algebra Γ(Sp R, ⊤) Γ(Sp R₁, ⊤) :=
    ((spMap (algebraMap R R₁)).appLE ⊤ ⊤ le_top).hom.toAlgebra
  obtain ⟨c⟩ := exists_basis_Gamma c'
  letI aX : ∀ U : X.Opens, Algebra Γ(Sp R, ⊤) Γ(X, U) := fun U => (p.appLE ⊤ U le_top).hom.toAlgebra
  letI aB : ∀ U : X.Opens, Algebra Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) :=
    fun U => (b.appLE U (b ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  have key : ∀ U : X.Opens, IsIso (pushoutSection H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
      (show b ⁻¹ᵁ U = b ⁻¹ᵁ U ⊓ p₁ ⁻¹ᵁ ⊤ by simp)) →
      ∃ e : Module.Basis (Module.Free.ChooseBasisIndex R R₁) Γ(X, U) Γ(X₁, b ⁻¹ᵁ U),
        ∀ i, e i = (p₁.appLE ⊤ (b ⁻¹ᵁ U) (by simp)).hom (c i) := by
    intro U hU
    let Φ := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(X, U) Γ(Sp R₁, ⊤)).isoPushout.hom ≫
      pushoutSection H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
        (show b ⁻¹ᵁ U = b ⁻¹ᵁ U ⊓ p₁ ⁻¹ᵁ ⊤ by simp)
    have : IsIso Φ := by dsimp only [Φ]; infer_instance
    let Φe : Γ(X, U) ⊗[Γ(Sp R, ⊤)] Γ(Sp R₁, ⊤) ≃+* Γ(X₁, b ⁻¹ᵁ U) :=
      (asIso Φ).commRingCatIsoToRingEquiv
    have fΦ : ∀ a t, Φe (a ⊗ₜ t) =
        (b.appLE U (b ⁻¹ᵁ U) le_rfl).hom a * (p₁.appLE ⊤ (b ⁻¹ᵁ U) (by simp)).hom t :=
      fun a t => AffDesc.isoPushout_desc_tmul _ _ _ a t
    obtain ⟨e, he⟩ := exists_basis_of_ringEquiv c Φe (fun a => by rw [fΦ, map_one, _root_.mul_one]; rfl)
    exact ⟨e, fun i => by rw [he, fΦ, map_one, _root_.one_mul]⟩
  haveI : Module.Flat R R₁ := inferInstance
  haveI : Flat (spMap (algebraMap R R₁)) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  obtain ⟨e, he⟩ := key V (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H le_top le_top _
    (isAffineOpen_top _) (isAffineOpen_top _) hVc hVq)
  refine ⟨Algebra.norm Γ(X, V) f, fun x => ?_⟩
  by_cases hxV : x ∈ V
  swap
  · exact ⟨fun h => absurd (X.basicOpen_le _ h) hxV, fun h => absurd h.1 hxV⟩
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  have hUV' : U ≤ V := hUV
  haveI : IsAffineHom b := MorphismProperty.of_isPullback H.flip inferInstance
  have hU₁ : IsAffineOpen (b ⁻¹ᵁ U) := hU.preimage b
  obtain ⟨e', he'⟩ := key U (isIso_pushoutSection_of_isAffineOpen H le_top le_top _
    (isAffineOpen_top _) (isAffineOpen_top _) hU)
  have hUV₁ : b ⁻¹ᵁ U ≤ b ⁻¹ᵁ V := b.preimage_mono hUV'
  let ρ := X.presheaf.map (homOfLE hUV').op
  let ψ := X₁.presheaf.map (homOfLE hUV₁).op
  have hn : Algebra.norm Γ(X, U) (ψ.hom f) = ρ.hom (Algebra.norm Γ(X, V) f) := by
    refine norm_map_of_basis ρ.hom ψ.hom (fun a => ?_) e e' (fun i => ?_) f
    · change (b.appLE V _ le_rfl ≫ X₁.presheaf.map _).hom a = (X.presheaf.map _ ≫ b.appLE U _ le_rfl).hom a
      rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
    · rw [he, he']
      exact congrArg (fun φ => CommRingCat.Hom.hom φ (c i)) (Scheme.Hom.appLE_map p₁ _ _)
  haveI : Module.Free Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) := Module.Free.of_basis e'
  haveI : Module.Finite Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) := Module.Finite.of_basis e'
  have I := _root_.GlobalTheory.Mum.norm_not_mem_iff Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) (ψ.hom f) (hU.primeIdealOf ⟨x, hxU⟩)
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec b hU hU₁ le_rfl
  have hpt : ∀ Q, b (hU₁.fromSpec Q) = hU.fromSpec (Spec.map (b.appLE U (b ⁻¹ᵁ U) le_rfl) Q) :=
    fun Q => by rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
  have hfib : (∀ Q : PrimeSpectrum Γ(X₁, b ⁻¹ᵁ U),
      Q.asIdeal.comap (algebraMap Γ(X, U) Γ(X₁, b ⁻¹ᵁ U)) = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal →
        ψ.hom f ∉ Q.asIdeal) ↔ ∀ z : X₁, b z = x → z ∈ X₁.basicOpen f := by
    constructor
    · intro h z hz
      have hzU : z ∈ b ⁻¹ᵁ U := by show b z ∈ U; rw [hz]; exact hxU
      have hzf : z ∈ X₁.basicOpen (ψ.hom f) := by
        by_contra hcon
        have hm := (mem_primeIdealOf_iff' hU₁ ⟨z, hzU⟩ (ψ.hom f)).2 hcon
        refine h _ ?_ hm
        have e1 : hU.fromSpec (Spec.map (b.appLE U (b ⁻¹ᵁ U) le_rfl) (hU₁.primeIdealOf ⟨z, hzU⟩)) =
            hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) :=
          (hpt _).symm.trans (by rw [hU₁.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]; exact hz)
        exact congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective e1)
      rw [Scheme.basicOpen_res] at hzf
      exact hzf.2
    · intro h Q hQ hfQ
      have hz := h (hU₁.fromSpec Q) ((hpt Q).trans ((congrArg hU.fromSpec (PrimeSpectrum.ext hQ)).trans
        (hU.fromSpec_primeIdealOf ⟨x, hxU⟩)))
      have hzU : hU₁.fromSpec Q ∈ b ⁻¹ᵁ U := by
        have : hU₁.fromSpec Q ∈ Set.range hU₁.fromSpec := ⟨Q, rfl⟩
        rwa [hU₁.range_fromSpec] at this
      have hz' : hU₁.fromSpec Q ∈ X₁.basicOpen (ψ.hom f) := by
        rw [Scheme.basicOpen_res]; exact ⟨hzU, hz⟩
      have hz'' : Q ∈ hU₁.fromSpec ⁻¹ᵁ X₁.basicOpen (ψ.hom f) := hz'
      rw [hU₁.fromSpec_preimage_basicOpen] at hz''
      exact hz'' hfQ
  have hbx : x ∈ X.basicOpen (Algebra.norm Γ(X, V) f) ↔
      Algebra.norm Γ(X, U) (ψ.hom f) ∉ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    rw [mem_primeIdealOf_iff', not_not, hn, Scheme.basicOpen_res]
    exact ⟨fun h => ⟨hxU, h⟩, fun h => h.2⟩
  rw [hbx, I, hfib]
  exact ⟨fun h => ⟨hxV, h⟩, fun h => h.2⟩

end GlobalTheory.Mum.NormBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqZeroOfIsIntegral
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HodgeMin

open GlobalTheory.CechPic

theorem exists_norm {K Ω : Type} [Field K] [Field Ω] (κ : K →+* Ω) {σ : Ω} (h0 : σ ≠ 0) (hσ : κ.IsIntegralElem σ) :
    ∃ (d : ℕ) (ν : K), 1 ≤ d ∧ ν ≠ 0 ∧ ∀ (R : Type) [CommRing R] (φ : R →+* K) (tr : K),
      ((κ.comp φ).IsIntegralElem (κ tr * σ) → φ.IsIntegralElem (tr ^ d * ν)) ∧
      ((κ.comp φ).IsIntegralElem (κ tr * σ)⁻¹ → φ.IsIntegralElem (tr ^ d * ν)⁻¹) := by
  letI := κ.toAlgebra
  let E := IntermediateField.adjoin K {σ}
  have : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hσ
  let s : E := IntermediateField.AdjoinSimple.gen K σ
  have key : ∀ (R : Type) [CommRing R] (φ : R →+* K) (x : E), (κ.comp φ).IsIntegralElem (x : Ω) →
      φ.IsIntegralElem (Algebra.norm K x) := by
    intro R _ φ x ⟨P, hP, e⟩
    letI := φ.toAlgebra
    letI := ((algebraMap K E).comp φ).toAlgebra
    have : IsScalarTower R K E := .of_algebraMap_eq fun _ => rfl
    refine Algebra.isIntegral_norm (R := R) K ⟨P, hP, (algebraMap E Ω).injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero]
    exact e
  have hn : ∀ tr : K, Algebra.norm K (algebraMap K E tr * s) = tr ^ Module.finrank K E * Algebra.norm K s := fun tr => by
    rw [map_mul, Algebra.norm_algebraMap]
  refine ⟨Module.finrank K E, Algebra.norm K s, Module.finrank_pos, Algebra.norm_ne_zero_iff.2 fun h => h0 (congrArg Subtype.val h),
    fun R _ φ tr => ⟨fun h => hn tr ▸ key R φ _ h, fun h => ?_⟩⟩
  rw [← hn, ← Algebra.norm_inv]
  exact key R φ _ h

theorem exists_section {S : Scheme.{0}} [IsIntegral S] [GlobalTheory.IsNormalScheme S] (U : S.Opens) (hU : genericPoint S ∈ U)
    (x : S.functionField) (h : ∀ (V : S.Opens) (hV : genericPoint S ∈ V), IsAffineOpen V → V ≤ U →
      (S.presheaf.germ V _ hV).hom.IsIntegralElem x) : ∃ a : Γ(S, U), (S.presheaf.germ U _ hU).hom a = x := by
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  refine GlobalTheory.IsNormalScheme.exists_germToFunctionField_eq_of_locally U x fun y hy => ?_
  obtain ⟨_, ⟨(V : S.Opens), hV, rfl⟩, hyV, hVU⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  obtain ⟨s, hs⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (R := Γ(S, V)) (A := S.functionField) (x := x)
    (h V _ hV hVU)
  exact ⟨V, this, s, hyV, hVU, hs⟩

theorem exists_nsmul_eq_zero_of_isIntegral {S W : Scheme.{0}} (p : W ⟶ S) [IsIntegral S] [GlobalTheory.IsNormalScheme S]
    [UniversallyClosed p] [Surjective p] (c : Pic S) (h : pull p c = 0) : ∃ d : ℕ, 1 ≤ d ∧ d • c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hL p)).1 h
  let ξ := genericPoint S
  have hξ : ∀ (V : S.Opens) (y : S), y ∈ V → ξ ∈ V := fun V y hy =>
    ((genericPoint_spec S).specializes (Set.mem_univ y)).mem_open V.isOpen hy
  obtain ⟨w, hw⟩ := p.surjective ξ
  have hsp : p w ⤳ ξ := hw ▸ specializes_rfl
  have hw' : ∀ {V : S.Opens}, ξ ∈ V → p w ∈ V := fun h => hw ▸ h
  let ρ : W.presheaf.stalk w →+* W.residueField w := (W.residue w).hom
  let κ : S.functionField →+* W.residueField w := ρ.comp (S.presheaf.stalkSpecializes hsp ≫ p.stalkMap w).hom
  have hκ : ∀ (V : S.Opens) (hV : ξ ∈ V), κ.comp (S.presheaf.germ V ξ hV).hom =
      (ρ.comp (W.presheaf.germ (p ⁻¹ᵁ V) w (hw' hV)).hom).comp (p.app V).hom := fun V hV => by
    have e : S.presheaf.germ V ξ hV ≫ S.presheaf.stalkSpecializes hsp ≫ p.stalkMap w =
        p.app V ≫ W.presheaf.germ (p ⁻¹ᵁ V) w (hw' hV) := by
      rw [S.presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
    exact congrArg (fun q => ρ.comp q.hom) e
  let σ : L.ι → W.residueField w := fun i => ρ (gm (𝟙 W) w _ (t.s fun _ => i)).val
  let tr : L.ι → L.ι → S.functionField := fun i j => (gm (𝟙 S) ξ _ (L.g i j)).val
  have hσ0 : ∀ i, σ i ≠ 0 := fun i => ((gm (𝟙 W) w _ (t.s fun _ => i)).isUnit.map ρ).ne_zero
  have hσ : ∀ i j, ξ ∈ L.U i → ξ ∈ L.U j → σ i = κ (tr i j) * σ j := fun i j hi hj => by
    have e := (isGen_iff_germ t).1 ht w (fun _ => i) (fun _ => j) (mem_pull.2 (hw' hi)) (mem_pull.2 (hw' hj))
    rw [gm_pull_g L p (𝟙 W) w _ _ (mem_pull.2 (hw' hi)) (mem_pull.2 (hw' hj)), Category.id_comp] at e
    refine (congrArg (fun u => ρ u.val) e).trans ((map_mul ρ _ _).trans (congrArg (· * σ j) ?_))
    have hij : ξ ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
    rw [gm_val p w _ (hw' hij)]
    refine (RingHom.congr_fun (hκ _ hij) _).symm.trans (congrArg κ ?_)
    exact (gm_val (𝟙 S) ξ _ hij _).symm
  have hint : ∀ i (V : S.Opens) (hV : ξ ∈ V), IsAffineOpen V → V ≤ L.U i → ∀ u : Γ(W, (L.pull p).U fun _ => i)ˣ,
      (κ.comp (S.presheaf.germ V ξ hV).hom).IsIntegralElem (ρ (gm (𝟙 W) w _ u).val) := fun i V hV ha hle u => by
    have l : p ⁻¹ᵁ V ≤ (L.pull p).U fun _ => i := fun x hx => mem_pull.2 (hle hx)
    rw [hκ, ← gm_res (𝟙 W) w l (hw' hV), gm_val (𝟙 W) w _ (hw' hV)]
    exact RingHom.IsIntegralElem.map (GenPush.isIntegral_app_of_universallyClosed p V ha (res l u).val)
      (ρ.comp (W.presheaf.germ (p ⁻¹ᵁ V) w (hw' hV)).hom)
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ξ
  obtain ⟨d, ν, hd, hν, H⟩ := exists_norm κ (hσ0 i₀) (by
    obtain ⟨_, ⟨(V : S.Opens), hV, rfl⟩, hyV, hVU⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hi₀ (L.U i₀).isOpen
    exact RingHom.IsIntegralElem.of_comp (hint i₀ V hyV hV hVU _))
  have ex : ∀ i, ∃ a : Γ(S, L.U i)ˣ, ξ ∈ L.U i → (gm (𝟙 S) ξ _ a).val = tr i i₀ ^ d * ν := fun i => by
    by_cases hi : ξ ∈ L.U i
    swap
    · exact ⟨1, fun h => (hi h).elim⟩
    obtain ⟨a, ha⟩ := exists_section (L.U i) hi (tr i i₀ ^ d * ν) fun V hV hV' hle =>
      (H _ _ _).1 (hσ i i₀ hi hi₀ ▸ hint i V hV hV' hle _)
    obtain ⟨b, hb⟩ := exists_section (L.U i) hi (tr i i₀ ^ d * ν)⁻¹ fun V hV hV' hle => (H _ _ _).2 (by
      have := hint i V hV hV' hle (t.s fun _ => i)⁻¹
      rwa [map_inv, map_units_inv ρ, show ρ _ = σ i from rfl, hσ i i₀ hi hi₀] at this)
    have hab : a * b = 1 := germ_injective_of_isIntegral S ξ hi (by
      refine (map_mul (S.presheaf.germ _ ξ hi).hom a b).trans ?_
      rw [ha, hb, map_one]
      exact mul_inv_cancel₀ (mul_ne_zero (pow_ne_zero _ (gm (𝟙 S) ξ _ (L.g i i₀)).ne_zero) hν))
    exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, fun _ => (gm_val (𝟙 S) ξ _ hi _).trans ha⟩
  choose a ha using ex
  have hg : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (a i) =
      L.g i j ^ d * res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (a j) := fun i j => by
    by_cases hij : ξ ∈ L.U i ⊓ L.U j
    swap
    · exact unit_ext fun y hy => (hij (hξ _ y hy)).elim
    have e : gm (𝟙 S) ξ _ (res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (a i)) =
        gm (𝟙 S) ξ _ (L.g i j ^ d * res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (a j)) := by
      rw [map_mul, map_pow, gm_res _ ξ _ hij, gm_res _ ξ _ hij]
      apply Units.ext
      rw [Units.val_mul, Units.val_pow_eq_pow_val, ha i hij.1, ha j hij.2, ← _root_.mul_assoc, ← mul_pow]
      exact congrArg (fun u => u.val ^ d * ν) (gm_cocycle hL (𝟙 S) ξ hij.1 hij.2 hi₀).symm
    have e' := congrArg Units.val e
    rw [gm_val _ ξ _ hij, gm_val _ ξ _ hij] at e'
    exact Units.ext (germ_injective_of_isIntegral S ξ hij e')
  refine ⟨d, hd, ?_⟩
  rw [← cls_lbPow hL d (isLB_lbPow hL d), cls_eq_zero_iff]
  refine ⟨⟨fun J => res (LB.wchart_le L (fun _ : PUnit => 𝟙 S) J PUnit.unit) (a (J PUnit.unit))⟩,
    (isGen_iff_germ _).2 fun y J J' hJ hJ' => ?_⟩
  have m : y ∈ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) := ⟨Set.mem_iInter.1 hJ PUnit.unit, Set.mem_iInter.1 hJ' PUnit.unit⟩
  have e := congrArg (gm (𝟙 S) y _) (hg (J PUnit.unit) (J' PUnit.unit))
  rw [map_mul, map_pow, gm_res _ y _ m, gm_res _ y _ m] at e
  refine (gm_res (𝟙 S) y _ hJ _).trans (e.trans (congrArg₂ (· * ·) ?_ (gm_res (𝟙 S) y _ hJ' _).symm))
  refine Eq.trans ?_ (gm_linComb L (fun _ : PUnit => 𝟙 S) (fun _ => (d : ℤ)) (𝟙 S) y J J' hJ hJ').symm
  rw [Fintype.prod_unique, zpow_natCast, Category.id_comp]

theorem exists_nsmul_eq_zero {S W : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (hS : Geo.Tor.IsNormalScheme S) (p : W ⟶ S)
    [UniversallyClosed p] [Surjective p] (c : Pic S) (h : pull p c = 0) : ∃ d : ℕ, 1 ≤ d ∧ d • c = 0 := by
  have := GlobalTheory.IsNormalScheme.of_pred hS
  have := Fintype.ofFinite (irreducibleComponents S)
  choose d hd H using fun C : irreducibleComponents S =>
    exists_nsmul_eq_zero_of_isIntegral (pullback.snd p (IsNormalScheme.component C).ι) (pull (IsNormalScheme.component C).ι c)
      (by rw [← pull_comp, ← pullback.condition, pull_comp, h, map_zero])
  refine ⟨∏ C, d C, Finset.prod_pos (s := Finset.univ) (f := d) fun C _ => hd C, ?_⟩
  obtain ⟨L, hL, e⟩ := cls_surj ((∏ C, d C) • c)
  rw [← e]
  refine (cls_eq_iff hL (LB.isLB_triv S)).2 (DisjointCoverLB.lbIso_of_disjoint_cover S _ IsNormalScheme.component
    (fun a b y ha hb => Subtype.ext (IsNormalScheme.eq_of_mem_irreducibleComponents a.2 b.2 ha hb))
    (fun y => ⟨⟨_, irreducibleComponent_mem_irreducibleComponents y⟩, mem_irreducibleComponent⟩) L _ hL (LB.isLB_triv S)
    fun C => (cls_eq_iff (pull_isLB hL _) (pull_isLB (LB.isLB_triv S) _)).1 ?_)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ C)
  rw [cls_pull hL, cls_pull (LB.isLB_triv S), e, map_nsmul, hk, mul_comm, mul_smul, H, smul_zero]
  exact (map_zero _).symm

theorem exists_common_cover {R : Type} [CommRing R] [IsDedekindDomain R] [CharZero R] {Z S S' U : Scheme.{0}} (z : Z ⟶ Sp R)
    (π : S ⟶ Z) (π' : S' ⟶ Z) [LocallyOfFiniteType (π ≫ z)] [QuasiSeparated π] [IsProper π'] [IsLocallyNoetherian S']
    (hS' : Geo.Tor.IsNormalScheme S') (a : U ⟶ S) (k : U ⟶ S') [IsOpenImmersion k] (w : a ≫ π = k ≫ π')
    (hd : Dense (a '' {x | ((a ≫ π ≫ z) x).asIdeal = ⊥}))
    {A : Over U} [GrpObj A] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ G'.left} (hφ : IsGrpPullback A G a φ) (hψ : IsGrpPullback A G' k ψ) :
    ∃ (W : Scheme.{0}) (p : W ⟶ S) (p' : W ⟶ S') (H : Over W) (_ : GrpObj H) (α : H.left ⟶ G.left) (β : H.left ⟶ G'.left),
      IsProper p ∧ Surjective p ∧ p ≫ π = p' ≫ π' ∧ IsGrpPullback H G p α ∧ IsGrpPullback H G' p' β := by
  let K := FractionRing R
  let b : Sp K ⟶ Sp R := spMap (algebraMap R K)
  have : IsPreimmersion b := IsPreimmersion.of_isLocalization (R := CommRingCat.of R) (S := K) (nonZeroDivisors R)
  have : Flat b := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors R)))
  let T := pullback (a ≫ π ≫ z) b
  let t : T ⟶ U := pullback.fst _ _
  have := GlobalTheory.IsNormalScheme.of_pred hS'
  have : QuasiCompact k := inferInstance
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (t ≫ k)
  have : GlobalTheory.IsNormalScheme T := GlobalTheory.IsNormalScheme.of_isIso_stalkMap (t ≫ k)
  have : IsLocallyNoetherian T := AmpUniq.isLocallyNoetherian_of_isPreimmersion (t ≫ k)
  let f : T ⟶ pullback π π' := pullback.lift (t ≫ a) (t ≫ k) (by simp [w])
  have hf₁ : f ≫ pullback.fst π π' = t ≫ a := pullback.lift_fst _ _ _
  have hf₂ : f ≫ pullback.snd π π' = t ≫ k := pullback.lift_snd _ _ _
  have : IsPreimmersion (f ≫ pullback.snd π π') := hf₂ ▸ inferInstance
  have : IsPreimmersion f := AmpUniq.isPreimmersion_of_comp f (pullback.snd π π')
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)
  have : IsLocallyNoetherian (pullback π π') := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst π π')
  have : QuasiCompact (f ≫ pullback.snd π π') := hf₂ ▸ inferInstance
  have : QuasiCompact f := .of_comp f (pullback.snd π π')
  have : Flat (f ≫ pullback.fst π π' ≫ π ≫ z) := by
    rw [reassoc_of% hf₁, pullback.condition]; infer_instance
  have : IsFinite f.fromNormalization := AmpUniq.isFinite_fromNormalization_graph f (pullback.fst π π' ≫ π ≫ z)
  let u := f.toNormalization
  let p := f.fromNormalization ≫ pullback.fst π π'
  let p' := f.fromNormalization ≫ pullback.snd π π'
  have hu₁ : u ≫ p = t ≫ a := by simp [u, p, hf₁]
  have hu₂ : u ≫ p' = t ≫ k := by simp [u, p', hf₂]
  have : IsPreimmersion (u ≫ p') := hu₂ ▸ inferInstance
  have : IsPreimmersion u := AmpUniq.isPreimmersion_of_comp u p'
  have : Flat u := AmpUniq.flat_of_isPreimmersion u
  have hN := GlobalTheory.IsNormalScheme.pred f.normalization
  have : IsLocallyNoetherian f.normalization := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsDominant (u ≫ p) := by
    rw [hu₁]
    refine ⟨hd.mono ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have : x ∈ Set.range t := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨closedPoint K, PrimeSpectrum.ext ?_⟩
      refine Eq.trans ?_ hx.symm
      change Ideal.comap (algebraMap R K) (maximalIdeal K) = ⊥
      rw [maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]
    obtain ⟨y, rfl⟩ := this
    exact ⟨y, by simp⟩
  have : IsDominant p := .of_comp u p
  have lift : ∀ {Y : Scheme.{0}} {B : Over Y} [GrpObj B] (q : f.normalization ⟶ Y) {c : U ⟶ Y} {χ : A.left ⟶ B.left},
      IsGrpPullback A B c χ → u ≫ q = t ≫ c →
      ∃ χ', IsGrpPullback ((Over.pullback t).obj A) ((Over.pullback q).obj B) u χ' := by
    intro Y B _ q c χ h e
    have h' := ((isGrpPullback_pullback A t).comp h).congr e.symm rfl
    exact ⟨pullback.lift _ _ (h'.1.w.trans (Category.assoc _ _ _).symm), (isGrpPullback_pullback B q).cancel
      (h'.congr rfl (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)⟩
  obtain ⟨_, a₁⟩ := lift p hφ hu₁
  obtain ⟨_, a₂⟩ := lift p' hψ hu₂
  obtain ⟨e, _⟩ := HodgeGenDesc.exists_iso_of_extensions u hN (IsSemiAbelian.pullback p G hG)
    (IsSemiAbelian.pullback p' G' hG') a₁ a₂
  exact ⟨f.normalization, p, p', (Over.pullback p).obj G, inferInstance, _, _, inferInstance,
    surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range, by simp [p, p', pullback.condition],
    isGrpPullback_pullback G p,
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G' p')).congr (Category.id_comp _) rfl⟩

end GlobalTheory.HodgeMin

end
end

