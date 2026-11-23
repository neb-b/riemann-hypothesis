module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2157
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralPullbackRationalSaturationModelOpen
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.UPoinc GlobalTheory.ZH

namespace GlobalTheory.UPoinc

theorem isReduced_of_flat_isPreimmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f] [IsReduced Y] :
    IsReduced X := by
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have hfl := Flat.stalkMap f x
    have hs := f.stalkMap_surjective x
    letI := (f.stalkMap x).hom.toAlgebra
    haveI : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := hfl
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
    have hi : Function.Injective (f.stalkMap x).hom :=
      FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
    exact isReduced_of_injective (RingEquiv.ofBijective _ ⟨hi, hs⟩).symm (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X

theorem isIntegral_pullback_toRat : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap R.val.toRingHom) → IsIntegral (pullback u₀ (spMap (toRat R))) ∧ ∃ pt : Sp Ω ⟶ pullback u₀ (spMap (toRat R)), pt ≫ pullback.fst _ _ ≫ U₀.ι = M.pt ∧ Dense (Set.range pt) := by
  intro o Ω _ _ _ _ M U₀ R u₀ hne hgen
  haveI := M.integral
  letI := (toRat R).toAlgebra
  haveI := isLocalization_ratHull R
  haveI : IsPreimmersion (spMap (toRat R)) :=
    IsPreimmersion.of_isLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ))
  haveI : Flat (spMap (toRat R)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2
    (IsLocalization.flat (ratHull R) (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ)))
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (show w ∈ (⊤ : (Sp Ω).Opens) from trivial)
  have hx := IsOpenImmersion.lift_fac U₀.ι M.pt hr
  have w : IsOpenImmersion.lift U₀.ι M.pt hr ≫ u₀ = spMap (ratHull R).val.toRingHom ≫ spMap (toRat R) :=
    (hgen _ hx).trans (spMap_val_toRat R).symm
  let pt := pullback.lift _ _ w
  let j : pullback u₀ (spMap (toRat R)) ⟶ M.Z := pullback.fst _ _ ≫ U₀.ι
  have hpt : pt ≫ j = M.pt := by rw [← Category.assoc, pullback.lift_fst, hx]
  haveI : IsPreimmersion j := inferInstance
  haveI : Flat j := inferInstance
  haveI := isReduced_of_flat_isPreimmersion j
  have hj : ∀ y, j (pt y) = genericPoint M.Z := fun y => by
    rw [← Scheme.Hom.comp_apply, hpt]
    exact M.gen.le ⟨y, rfl⟩
  have hg : IsGenericPoint (pt default) Set.univ := by
    refine isGenericPoint_iff_specializes.2 fun z => ⟨fun _ => trivial, fun _ => ?_⟩
    rw [← j.isEmbedding.isInducing.specializes_iff, hj]
    exact genericPoint_specializes _
  haveI : IrreducibleSpace (pullback u₀ (spMap (toRat R)) :) :=
    (irreducibleSpace_def _).2 hg.isIrreducible
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, pt, hpt, ?_⟩
  exact Dense.mono (Set.singleton_subset_iff.2 ⟨default, rfl⟩) (dense_iff_closure_eq.2 hg)

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoBaseChangeOverBasicOpenOfTensorBijective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LocIso

theorem isPullback_resLE_opensRange {W W' Y Z T S : Scheme.{0}} (π : Z ⟶ Y) (s : Z ⟶ T) (b : Y ⟶ S)
    (c : T ⟶ S) (i : W ⟶ Y) [IsOpenImmersion i] (k : W' ⟶ Z) (p : W' ⟶ W)
    (h₁ : IsPullback k p π i) (h₂ : IsPullback p (k ≫ s) (i ≫ b) c) :
    IsPullback (π.resLE i.opensRange (π ⁻¹ᵁ i.opensRange) le_rfl) ((π ⁻¹ᵁ i.opensRange).ι ≫ s)
      (i.opensRange.ι ≫ b) c := by
  let e : W ≅ i.opensRange.toScheme := IsOpenImmersion.isoOfRangeEq i i.opensRange.ι (by simp)
  have he : e.hom ≫ i.opensRange.ι = i := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hR : IsPullback (π.resLE i.opensRange (π ⁻¹ᵁ i.opensRange) le_rfl) (π ⁻¹ᵁ i.opensRange).ι
      i.opensRange.ι π := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; exact isPullback_morphismRestrict π _
  have hW : IsPullback (p ≫ e.hom) k i.opensRange.ι π := by
    refine IsPullback.of_iso h₁.flip (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [he]
  let φ := IsPullback.isoIsPullback _ _ hW hR
  refine IsPullback.of_iso h₂ φ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (IsPullback.isoIsPullback_hom_fst _ _ hW hR).symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, IsPullback.isoIsPullback_hom_snd]
  · simp [← he]
  · simp

theorem isLocalization_tensor (R R' C' : Type) [CommRing R] [CommRing R'] [CommRing C'] [Algebra R R']
    [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (C : Subalgebra R C') (f g : C)
    (hcok : ∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val
      (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _))
    (hker : ∀ t : TensorProduct R C R', (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C')
      fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) :
    letI : Algebra (TensorProduct R C R') (Localization.Away (algebraMap C C' (f * g))) :=
      ((algebraMap C' _).comp (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C')
        fun _ _ => Commute.all _ _).toRingHom).toAlgebra
    IsLocalization (Submonoid.powers ((f * g) ⊗ₜ[R] (1 : R'))) (Localization.Away (algebraMap C C' (f * g))) := by
  set Φ := Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _ with hΦdef
  letI : Algebra (TensorProduct R C R') (Localization.Away (algebraMap C C' (f * g))) :=
    ((algebraMap C' _).comp Φ.toRingHom).toAlgebra
  have hΦ : ∀ c : C, Φ (c ⊗ₜ[R] (1 : R')) = algebraMap C C' c := fun c => by simp [Φ]
  have halg : ∀ t, algebraMap (TensorProduct R C R') (Localization.Away (algebraMap C C' (f * g))) t =
      algebraMap C' _ (Φ t) := fun t => rfl
  have hpow : ∀ n : ℕ, ((f * g) ⊗ₜ[R] (1 : R')) ^ n = ((g ^ n) ⊗ₜ[R] (1 : R')) * ((f ^ n) ⊗ₜ[R] (1 : R')) := by
    intro n
    rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_pow, one_pow, _root_.mul_one, _root_.mul_comm (g ^ n)]
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [halg, map_pow, hΦ, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit _).pow n
  · intro z
    obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (algebraMap C C' (f * g))) z
    obtain ⟨k, t, ht⟩ := hcok a
    refine ⟨⟨t * ((g ^ k) ⊗ₜ[R] (1 : R')), ⟨((f * g) ⊗ₜ[R] (1 : R')) ^ (m + k), m + k, rfl⟩⟩, ?_⟩
    rw [halg, halg, map_pow Φ, hΦ, map_mul Φ, hΦ, ht, pow_add, map_mul (algebraMap C' _), ← _root_.mul_assoc, hz,
      ← map_mul (algebraMap C' _)]
    refine congrArg (algebraMap C' _) ?_
    have hco : ∀ c : C, algebraMap C C' c = (c : C') := fun _ => rfl
    simp only [hco, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    ring
  · intro x y hxy
    rw [halg, halg] at hxy
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap C C' (f * g))) hxy
    have h0 : Φ (((f * g) ⊗ₜ[R] (1 : R')) ^ m * (x - y)) = 0 := by
      rw [map_mul, map_pow, hΦ, map_sub, mul_sub]
      exact sub_eq_zero.mpr hm
    obtain ⟨n, hn⟩ := hker _ h0
    refine ⟨⟨((f * g) ⊗ₜ[R] (1 : R')) ^ (n + m), n + m, rfl⟩, ?_⟩
    change ((f * g) ⊗ₜ[R] (1 : R')) ^ (n + m) * x = ((f * g) ⊗ₜ[R] (1 : R')) ^ (n + m) * y
    rw [← sub_eq_zero, ← mul_sub, pow_add, hpow, _root_.mul_assoc, _root_.mul_assoc, hn, mul_zero]

theorem exists_smooth_basicOpen_iso : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X : Over (Sp R)) (Z : Scheme.{0}) (π : Z ⟶ X.left) (s : Z ⟶ Sp R') (hX : π ≫ X.hom = s ≫ spMap (algebraMap R R')) (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (C : Subalgebra R C') (j : Sp C' ⟶ Z) (l : Sp C ⟶ X.left) [IsOpenImmersion l], IsPullback j (spMap (algebraMap C C')) π l → j ≫ s = spMap (algebraMap R' C') → l ≫ X.hom = spMap (algebraMap R C) → ∀ f g : C, (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) → (∀ t : TensorProduct R C R', (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) → Algebra.Smooth R (Localization.Away g) → ∀ q : Sp C, f ∉ q.asIdeal → g ∉ q.asIdeal → ∃ V : X.left.Opens, l q ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ s) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap (algebraMap R R'))) := by
  intro R R' _ _ _ X Z π s hX C' _ _ _ _ C j l _ hP hj hl f g hcok hker hsm q hf hg
  let A := Localization.Away (f * g)
  let A' := Localization.Away (algebraMap C C' (f * g))
  let φ : A →+* A' := IsLocalization.Away.map A A' (algebraMap C C') (f * g)
  have hφ : φ.comp (algebraMap C A) = (algebraMap C' A').comp (algebraMap C C') := IsLocalization.map_comp _
  have hLoc : IsPushout (CommRingCat.ofHom (algebraMap C C')) (CommRingCat.ofHom (algebraMap C A))
      (CommRingCat.ofHom (algebraMap C' A')) (CommRingCat.ofHom φ) := by
    have : IsLocalization ((Submonoid.powers (f * g)).map (algebraMap C C')) A' := by
      rw [Submonoid.map_powers]; infer_instance
    exact CommRingCat.isPushout_of_isLocalization _ _ hφ (Submonoid.powers (f * g))
  haveI : IsOpenImmersion (spMap (algebraMap C A)) := IsOpenImmersion.of_isLocalization (f * g)
  have h₁ : IsPullback (spMap (algebraMap C' A') ≫ j) (spMap φ) π (spMap (algebraMap C A) ≫ l) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ hLoc).paste_horiz hP
  have hRing : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R' A')) := by
    let Φ := Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _
    letI : Algebra (TensorProduct R C R') A' := ((algebraMap C' A').comp Φ.toRingHom).toAlgebra
    have hL := isLocalization_tensor R R' C' C f g hcok hker
    have Q1 := CommRingCat.isPushout_tensorProduct R C R'
    have : IsLocalization ((Submonoid.powers (f * g)).map
        (Algebra.TensorProduct.includeLeftRingHom : C →+* TensorProduct R C R')) A' := by
      rw [Submonoid.map_powers]; exact hL
    have H : φ.comp (algebraMap C A) = (algebraMap (TensorProduct R C R') A').comp
        Algebra.TensorProduct.includeLeftRingHom := by
      rw [hφ]
      ext c
      simp [RingHom.algebraMap_toAlgebra, Φ]
    have Q2 := CommRingCat.isPushout_of_isLocalization (S := TensorProduct R C R') (Rₘ := A) (Sₘ := A')
      Algebra.TensorProduct.includeLeftRingHom φ H (Submonoid.powers (f * g))
    have Q := (Q1.flip.paste_vert Q2).flip
    convert Q using 1
    · ext r; simp [RingHom.algebraMap_toAlgebra, Φ, ← IsScalarTower.algebraMap_apply]
  have hs : (spMap (algebraMap C' A') ≫ j) ≫ s = spMap (algebraMap R' A') := by
    rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hb : (spMap (algebraMap C A) ≫ l) ≫ X.hom = spMap (algebraMap R A) := by
    rw [Category.assoc, hl, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h₂ : IsPullback (spMap φ) ((spMap (algebraMap C' A') ≫ j) ≫ s)
      ((spMap (algebraMap C A) ≫ l) ≫ X.hom) (spMap (algebraMap R R')) := by
    rw [hs, hb]; exact isPullback_SpecMap_of_isPushout _ _ _ _ hRing
  have hG := isPullback_resLE_opensRange π s X.hom (spMap (algebraMap R R')) _ _ _ h₁ h₂
  refine ⟨(spMap (algebraMap C A) ≫ l).opensRange, ?_, isAffineOpen_opensRange _, ?_, ?_⟩
  · obtain ⟨w, hw⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C A)) := by
      rw [PrimeSpectrum.localization_away_comap_range A (f * g)]
      exact fun h => (q.isPrime.mem_or_mem h).elim hf hg
    refine ⟨w, ?_⟩
    first
      | exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg l hw)
      | exact (Scheme.comp_base_apply _ _ _).trans (congrArg l hw)
      | exact congrArg l hw
  · let B := Localization.Away (algebraMap C (Localization.Away g) f)
    haveI : Algebra.Smooth R B := Algebra.Smooth.comp R (Localization.Away g) B
    haveI : Algebra.Smooth R A :=
      Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (f * g)) B A).restrictScalars R)
    haveI : Smooth (spMap (algebraMap R A)) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
    let e := IsOpenImmersion.isoOfRangeEq (spMap (algebraMap C A) ≫ l)
      (spMap (algebraMap C A) ≫ l).opensRange.ι (by simp)
    have hfac : e.hom ≫ (spMap (algebraMap C A) ≫ l).opensRange.ι = spMap (algebraMap C A) ≫ l :=
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have : (spMap (algebraMap C A) ≫ l).opensRange.ι ≫ X.hom = e.inv ≫ spMap (algebraMap R A) := by
      calc _ = e.inv ≫ (e.hom ≫ (spMap (algebraMap C A) ≫ l).opensRange.ι) ≫ X.hom := by simp
        _ = _ := by rw [hfac, hb]
    rw [this]; infer_instance
  · convert (inferInstance : IsIso hG.isoPullback.hom)
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hG.isoPullback_hom_fst.symm
    · exact (pullback.lift_snd _ _ _).trans hG.isoPullback_hom_snd.symm

end GlobalTheory.Mum.LocIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoFinitePieceFlatConnectedChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FlatChartDeg

theorem isIso_app_of_flat {X Y S T : Scheme.{0}} {p : X ⟶ S} {f : T ⟶ S} {g : Y ⟶ X} {q : Y ⟶ T}
    (H : IsPullback g q p f) [Flat f] [QuasiCompact p] [QuasiSeparated p]
    (hp : ∀ V : S.Opens, IsIso (p.app V)) (U : T.Opens) : IsIso (q.app U) := by
  refine GlobalTheory.ProperFunctions.isIso_app_of_isBasis q
    (fun V : {V : T.affineOpens // ∃ W : S.affineOpens, V.1 ≤ f ⁻¹ᵁ W.1} ↦ V.1.1) ?_ ?_ U
  · rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (u := (U ⊓ f ⁻¹ᵁ W : T.Opens))
        ⟨hx, hxW⟩ (U ⊓ f ⁻¹ᵁ W).2
    exact ⟨V, ⟨⟨⟨V, hV⟩, ⟨W, hW⟩, fun y hy ↦ (hVU hy).2⟩, rfl⟩, hxV, fun y hy ↦ (hVU hy).1⟩
  · rintro ⟨V, W, hVW⟩
    have : IsAffine V.1 := V.2
    have : IsAffine W.1 := W.2
    have H1 := (isPullback_morphismRestrict q V.1).flip.paste_horiz H
    have hw : ((q ⁻¹ᵁ V.1).ι ≫ g) ≫ p = (q ∣_ V.1 ≫ f.resLE W.1 V.1 hVW) ≫ W.1.ι := by
      rw [H1.w, Category.assoc, Scheme.Hom.resLE_comp_ι]
    let H2 := (isPullback_morphismRestrict p W.1).flip
    have : IsIso (p ∣_ W.1).appTop := by
      rw [morphismRestrict_appTop]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hp (W.1.ι ''ᵁ ⊤)) (by rw [eqToHom_op]; exact Functor.map_isIso _ _)
    refine GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback (p := p ∣_ W.1) (f := f.resLE W.1 V.1 hVW)
      (g := H2.lift _ _ hw) (IsPullback.of_right ?_ (H2.lift_snd _ _ _) H2)
    rw [H2.lift_fst, Scheme.Hom.resLE_comp_ι]
    exact H1

theorem preconnectedSpace_of_surjective_appTop {Z T : Scheme.{0}} (r : Z ⟶ T) [PreconnectedSpace T]
    (hr : Function.Bijective r.appTop.hom) : PreconnectedSpace Z := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  obtain ⟨e, he, hes⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen Z s hs
  obtain ⟨e, rfl⟩ := hr.2 e
  have he' : e * e = e := hr.1 (by rw [map_mul, he])
  have h1 : T.basicOpen e ⊓ T.basicOpen (1 - e) = ⊥ := by
    rw [← Scheme.basicOpen_mul, mul_sub, _root_.mul_one, he', sub_self, Scheme.basicOpen_zero]
  have h2 : T.basicOpen e ⊔ T.basicOpen (1 - e) = ⊤ := by
    refine top_le_iff.mp ?_
    have := T.basicOpen_add_le e (1 - e)
    rwa [add_sub_cancel, T.basicOpen_of_isUnit isUnit_one] at this
  have hcl : IsClopen (T.basicOpen e : Set T) := by
    refine ⟨⟨?_⟩, (T.basicOpen e).2⟩
    have : (T.basicOpen e : Set T)ᶜ = T.basicOpen (1 - e) := by
      ext x
      constructor
      · intro hx
        have : x ∈ T.basicOpen e ⊔ T.basicOpen (1 - e) := by rw [h2]; trivial
        exact (TopologicalSpace.Opens.mem_sup.mp this).resolve_left hx
      · intro hx hx'
        have : x ∈ T.basicOpen e ⊓ T.basicOpen (1 - e) := ⟨hx', hx⟩
        rw [h1] at this
        exact this
    rw [this]
    exact (T.basicOpen (1 - e)).2
  have h3 : s = r ⁻¹' (T.basicOpen e : Set T) := by
    rw [← hes]
    exact congrArg (fun O : Z.Opens => (O : Set Z)) (Scheme.preimage_basicOpen_top r e).symm
  rcases isClopen_iff.mp hcl with h | h
  · left; rw [h3, h, Set.preimage_empty]
  · right; rw [h3, h, Set.preimage_univ]

theorem isIso_of_isAffineHom {Z T : Scheme.{0}} (f : Z ⟶ T) [IsAffineHom f] (hf : ∀ V : T.Opens, IsIso (f.app V)) :
    IsIso f := by
  rw [← MorphismProperty.isomorphisms.iff, IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    _ (iSup_affineOpens_eq_top T)]
  intro V
  have : IsAffine V.1 := V.2
  have : IsAffine (f ⁻¹ᵁ V.1) := V.2.preimage f
  have : IsIso (f ∣_ V.1).appTop := by
    rw [morphismRestrict_appTop]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hf (V.1.ι ''ᵁ ⊤)) (by rw [eqToHom_op]; exact Functor.map_isIso _ _)
  refine (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme) (arrowIsoSpecΓOfIsAffine _)).2 ?_
  exact inferInstanceAs (IsIso (Spec.map (f ∣_ V.1).appTop))

theorem flat_affineSpace (S : Scheme.{0}) (n : ℕ) : Flat (𝔸(Fin n; S) ↘ S) := by
  have hF : MorphismProperty.IsStableUnderBaseChange @Flat.{0} := inferInstance
  refine hF.of_isPullback (IsPullback.of_hasPullback _ _).flip ?_
  have := isIso_of_isTerminal specULiftZIsTerminal.{0} terminalIsTerminal (terminal.from _)
  have : Flat (Spec.map (CommRingCat.ofHom (MvPolynomial.C : ULift.{0} ℤ →+* MvPolynomial (Fin n) (ULift.{0} ℤ)))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2
      ((RingHom.flat_algebraMap_iff (R := ULift ℤ) (S := MvPolynomial (Fin n) (ULift ℤ))).2 inferInstance)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C))]
  infer_instance

theorem exists_geometricPoint (Z : Scheme.{0}) (z : Z) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (s : Sp Ω ⟶ Z), ∀ y, s y = z := by
  refine ⟨AlgebraicClosure (Z.residueField z), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z)))) ≫
      Z.fromSpecResidueField z, fun y => ?_⟩
  rw [Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

theorem isIso_finite_piece : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Flat h → PreconnectedSpace T → p ∈ W → pullback.fst τ h p = x → IsFinite (W.ι ≫ pullback.snd τ h) → (∀ w ∈ W, pullback.snd τ h w = pullback.snd τ h p → w = p) → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ T), Set.range t = {pullback.snd τ h p} → ∃! w : Sp Ω ⟶ W.toScheme, w ≫ W.ι ≫ pullback.snd τ h = t) → IsIso (W.ι ≫ pullback.snd τ h) := by
  intro R _ _ _ _ S X π U a b g τ c hπ hπs hπb hUft hUsep ha haO hτ hc1 hc2 hc x hx hinj hsurj T h W p hh hT hpW hpx hfin hone huniq
  let α := 𝔸(Fin g; Sp R) ↘ Sp R
  have hbπ : b ≫ π = a ≫ τ ≫ α := by
    rw [← hc2, Category.assoc, ← pullback.condition, ← Category.assoc, hc1, Category.assoc]
  let s₁ := pullback.fst π (h ≫ α)
  let s₂ := pullback.snd π (h ≫ α)
  have HS : IsPullback s₁ s₂ π (h ≫ α) := .of_hasPullback _ _
  let m : pullback π (h ≫ α) ⟶ pullback α π := pullback.lift (s₂ ≫ h) s₁ (by rw [Category.assoc, HS.w])
  have Hm : IsPullback m s₂ (pullback.fst α π) h := by
    refine IsPullback.of_right (h₁₂ := pullback.snd α π) (v₁₃ := π) (h₂₂ := α) ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback α π).flip
    rw [pullback.lift_snd]
    exact HS
  let x₁ := pullback.fst a (pullback.fst τ h)
  let x₂ := pullback.snd a (pullback.fst τ h)
  have HX : IsPullback x₁ x₂ a (pullback.fst τ h) := .of_hasPullback _ _
  have HX' : IsPullback x₁ (x₂ ≫ pullback.snd τ h) (a ≫ τ) h := HX.paste_vert (.of_hasPullback τ h)
  let n : pullback a (pullback.fst τ h) ⟶ pullback π (h ≫ α) := pullback.lift (x₁ ≫ b) (x₂ ≫ pullback.snd τ h) (by
    rw [Category.assoc, hbπ, ← Category.assoc a, ← Category.assoc x₁, HX'.w, Category.assoc])
  have hn1 : n ≫ s₁ = x₁ ≫ b := pullback.lift_fst _ _ _
  have hn2 : n ≫ s₂ = x₂ ≫ pullback.snd τ h := pullback.lift_snd _ _ _
  have Hn : IsPullback x₁ n c m := by
    refine IsPullback.of_bot (v₂₁ := s₂) (v₂₂ := pullback.fst α π) (h₃₁ := h) ?_ ?_ Hm
    · rw [hn2, hc1]
      exact HX'
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hc1, pullback.lift_fst, HX'.w, ← hn2, Category.assoc]
      · rw [Category.assoc, Category.assoc, hc2, pullback.lift_snd, hn1]
  have : Etale n := MorphismProperty.of_isPullback Hn hc
  let w₁ := pullback.fst x₂ W.ι
  let w₂ := pullback.snd x₂ W.ι
  have HW₀ : IsPullback w₁ w₂ x₂ W.ι := .of_hasPullback _ _
  have HW : IsPullback (w₁ ≫ x₁) w₂ a (W.ι ≫ pullback.fst τ h) := HW₀.paste_horiz HX
  have hq1 : (w₁ ≫ n) ≫ s₁ = (w₁ ≫ x₁) ≫ b := by rw [Category.assoc, hn1, Category.assoc]
  have hq2 : (w₁ ≫ n) ≫ s₂ = w₂ ≫ W.ι ≫ pullback.snd τ h := by
    rw [Category.assoc, hn2, ← Category.assoc, HW₀.w, Category.assoc]
  have hqe : Etale (w₁ ≫ n) := inferInstance
  have : IsProper w₂ := MorphismProperty.of_isPullback HW ha
  have : IsProper s₂ := MorphismProperty.of_isPullback HS hπ
  have : IsProper ((w₁ ≫ n) ≫ s₂) := by rw [hq2]; infer_instance
  have : IsProper (w₁ ≫ n) := IsProper.of_comp _ s₂
  have := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified (w₁ ≫ n)
  have hqf : IsFinite (w₁ ≫ n) := IsFinite.of_isProper_of_locallyQuasiFinite _
  have : Flat α := flat_affineSpace _ _
  have hs₂ := GlobalTheory.Mum.app_bijective_of_flat_baseChange R S T _ π (h ≫ α) s₂ s₁ inferInstance inferInstance hπb
    inferInstance HS.flip
  have hconn := preconnectedSpace_of_surjective_appTop s₂ (hs₂ ⊤)
  have hs₂s : Surjective s₂ := MorphismProperty.of_isPullback HS hπs
  obtain ⟨z, hz⟩ := s₂.surjective (pullback.snd τ h p)
  obtain ⟨Ω, _, _, s, hs⟩ := exists_geometricPoint _ z
  obtain ⟨o⟩ : Nonempty (Sp Ω) := inferInstance
  have hrange : ∀ {Y : Scheme.{0}} (u : Sp Ω ⟶ Y) (y : Y), (∀ o', u o' = y) → Set.range u = {y} := by
    intro Y u y hu
    ext y'
    constructor
    · rintro ⟨o', rfl⟩
      exact hu o'
    · rintro rfl
      exact ⟨o, hu o⟩
  obtain ⟨w, hw, hwu⟩ := huniq Ω (s ≫ s₂) (hrange _ _ fun o' => by rw [Scheme.Hom.comp_apply, hs, hz])
  have hwp : ∀ o', W.ι (w o') = p := fun o' => by
    refine hone _ (w o').2 ?_
    change pullback.snd τ h (W.ι (w o')) = _
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply, hs, hz]
  have hξ : Set.range (w ≫ W.ι ≫ pullback.fst τ h) = {x} := hrange _ _ fun o' => by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hwp, hpx]
  obtain ⟨y, hy1, hy2⟩ := hsurj Ω (w ≫ W.ι ≫ pullback.fst τ h) (s ≫ s₁) hξ (by
    rw [← hτ, Category.assoc s, HS.w, ← Category.assoc s, ← hw]
    simp only [Category.assoc]
    rw [pullback.condition_assoc])
  have hiso : IsIso (w₁ ≫ n) := by
    refine GlobalTheory.Mum.isIso_of_finite_etale_of_existsUnique_lift _ _ _ hqf hqe hconn Ω s ⟨HW.lift y w hy1, ?_, ?_⟩
    · apply HS.hom_ext
      · rw [Category.assoc, hq1, HW.lift_fst_assoc, hy2]
      · rw [Category.assoc, hq2, HW.lift_snd_assoc, hw]
    · intro y' hy'
      have e1 : y' ≫ w₂ = w := hwu _ (by
        change (y' ≫ w₂) ≫ _ = _
        rw [Category.assoc, ← hq2, ← hy', Category.assoc y'])
      have e2 : (y' ≫ w₁ ≫ x₁) ≫ a = w ≫ W.ι ≫ pullback.fst τ h := by
        rw [Category.assoc, HW.w, ← e1, Category.assoc]
      apply HW.hom_ext
      · rw [HW.lift_fst]
        refine hinj Ω _ _ (by rw [e2]; exact hξ) (e2.trans hy1.symm) ?_
        rw [hy2, Category.assoc, ← hq1, ← hy', Category.assoc y']
      · rw [HW.lift_snd, e1]
  have hw₂ := isIso_app_of_flat HW (fun V => (ConcreteCategory.isIso_iff_bijective _).mpr (haO V))
  refine isIso_of_isAffineHom _ fun V => ?_
  have h1 : IsIso ((w₂ ≫ W.ι ≫ pullback.snd τ h).app V) := by
    rw [← hq2, Scheme.Hom.comp_app]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ ((ConcreteCategory.isIso_iff_bijective _).mpr (hs₂ V))
      (inferInstanceAs (IsIso ((w₁ ≫ n).app (s₂ ⁻¹ᵁ V))))
  rw [Scheme.Hom.comp_app] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (hw₂ ((W.ι ≫ pullback.snd τ h) ⁻¹ᵁ V)) h1

end GlobalTheory.Mum.FlatChartDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoFlagModelFlagBundleOverModuli
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.VarFlag

theorem isIso_restrict_Vo : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (h : GlobalTheory.CompHS.Y₀ X Z ⟶ C.Y.X) [IsProper h], (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) (z ≫ h)) → IsIso (h ∣_ GlobalTheory.VarFlag.Vo C) := by
  intro E _ _ _ H Dw l Xo c Y X Z hF C hT B j _ f hπ hB h _ hU hH
  have := C.Y.isNormalScheme
  have hN := GlobalTheory.IsNormalScheme.pred (GlobalTheory.VarFlag.Vo C).toScheme
  have : IsLocallyNoetherian C.Y.X := LocallyOfFiniteType.isLocallyNoetherian C.Y.str
  refine GlobalTheory.isIso_of_isProper_of_existsUnique_field_point _ _ _ inferInstance inferInstance hN inferInstance
    fun K _ w => ?_
  have hp : ∀ s, (w ≫ (GlobalTheory.VarFlag.Vo C).ι) s ∈ GlobalTheory.VarFlag.Vo C := fun s => by
    rw [Scheme.Hom.comp_apply]; exact (w s).2
  obtain ⟨z₀, hz₀⟩ := _root_.GlobalTheory.VarFlag.exists_rel_of_mem_Vo X Z hF C hT B j f hπ hB K _ hp
  have e₀ : z₀ ≫ h = w ≫ (GlobalTheory.VarFlag.Vo C).ι := (hU K z₀).unique (hH K z₀) hz₀
  have P := (isPullback_morphismRestrict h (GlobalTheory.VarFlag.Vo C)).flip
  refine ⟨P.lift z₀ w e₀, P.lift_snd _ _ _, fun y hy => ?_⟩
  apply P.hom_ext
  · rw [P.lift_fst]
    have ey : (y ≫ (h ⁻¹ᵁ GlobalTheory.VarFlag.Vo C).ι) ≫ h = w ≫ (GlobalTheory.VarFlag.Vo C).ι := by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy]
    have hr := hH K (y ≫ (h ⁻¹ᵁ GlobalTheory.VarFlag.Vo C).ι)
    rw [ey] at hr
    have := _root_.GlobalTheory.VarFlag.rel_unique X C hF hT K _ _ _ hp hr hz₀
    exact (cancel_mono (GlobalTheory.CompHS.inc₀ X Z)).1 this
  · rw [P.lift_snd]; exact hy

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfEtaleOfSurjectiveOfUniversallyInjectiveAl
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isIso_of_etale_of_surjective_of_universallyInjective :
    ∀ (X Z : Scheme.{0}) (h : X ⟶ Z), Etale h → Surjective h → UniversallyInjective h → IsIso h := by
  intro X Z h het hs hui
  have hd : Surjective (pullback.diagonal h) := (UniversallyInjective.iff_diagonal h).1 hui
  have : IsIso (pullback.diagonal h) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hd⟩
  have : Mono h := (pullback.isIso_diagonal_iff h).1 this
  have : IsOpenImmersion h := IsOpenImmersion.of_flat_of_mono h
  exact (isIso_iff_isOpenImmersion_and_surjective h).2 ⟨this, hs⟩

end GlobalTheory.Mum
end

