module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2472
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2428

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackSemiAbelianDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.FibLat

theorem exists_common_pullback_dvr : ∀ (Y : Scheme.{0}) (G : Over Y) [GrpObj G], IsSemiAbelian G → ∀ (V : Type) [CommRing V] [IsDomain V] (Gu : Over (Sp V)) [GrpObj Gu], IsSemiAbelian Gu → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (fV : V →+* V') (ξ : Sp V' ⟶ Y) (AK : Over (Sp (FractionRing V'))) [GrpObj AK] (α : AK.left ⟶ Gu.left) (Ψ : AK.left ⟶ G.left), IsGrpPullback AK Gu (spMap ((algebraMap V' (FractionRing V')).comp fV)) α → IsGrpPullback AK G (spMap (algebraMap V' (FractionRing V')) ≫ ξ) Ψ → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left) (ω : AK.left ⟶ G'.left), IsGrpPullback G' Gu (spMap fV) β ∧ IsGrpPullback G' G ξ β' ∧ ω ≫ G'.hom = AK.hom ≫ spMap (algebraMap V' (FractionRing V')) ∧ ω ≫ β = α ∧ ω ≫ β' = Ψ ∧ ∀ (F : Gu ⟶ Gu) (f : G ⟶ G) (eK : AK ⟶ AK), eK.left ≫ α = α ≫ F.left → eK.left ≫ Ψ = Ψ ≫ f.left → ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ F.left ∧ F'.left ≫ β' = β' ≫ f.left := by
  intro Y G _ hG V _ _ Gu _ hGu V' _ _ _ fV ξ AK _ α Ψ hα hΨ
  let j : Sp (FractionRing V') ⟶ Sp V' := spMap (algebraMap V' (FractionRing V'))
  have hα' : IsGrpPullback AK Gu (j ≫ spMap fV) α := by
    have := hα; rwa [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp] at this
  have hG'p := isGrpPullback_pullback Gu (spMap fV)
  have hG''p := isGrpPullback_pullback G ξ
  let ω : AK.left ⟶ ((Over.pullback (spMap fV)).obj Gu).left :=
    pullback.lift α (AK.hom ≫ j) (by rw [hα'.1.w, Category.assoc])
  have hωf : ω ≫ pullback.fst Gu.hom (spMap fV) = α := pullback.lift_fst _ _ _
  have hωs : ω ≫ ((Over.pullback (spMap fV)).obj Gu).hom = AK.hom ≫ j := pullback.lift_snd _ _ _
  have hω : IsGrpPullback AK ((Over.pullback (spMap fV)).obj Gu) j ω :=
    IsGrpPullback.cancel hG'p (IsGrpPullback.congr hα' rfl hωf.symm) hωs
  let ω'' : AK.left ⟶ ((Over.pullback ξ).obj G).left :=
    pullback.lift Ψ (AK.hom ≫ j) (by rw [hΨ.1.w, Category.assoc])
  have hω''f : ω'' ≫ pullback.fst G.hom ξ = Ψ := pullback.lift_fst _ _ _
  have hω''s : ω'' ≫ ((Over.pullback ξ).obj G).hom = AK.hom ≫ j := pullback.lift_snd _ _ _
  have hω'' : IsGrpPullback AK ((Over.pullback ξ).obj G) j ω'' :=
    IsGrpPullback.cancel hG''p (IsGrpPullback.congr hΨ rfl hω''f.symm) hω''s
  have hG' : IsSemiAbelian ((Over.pullback (spMap fV)).obj Gu) := IsSemiAbelian.pullback _ _ hGu
  have hG'' : IsSemiAbelian ((Over.pullback ξ).obj G) := IsSemiAbelian.pullback _ _ hG
  obtain ⟨E, ⟨hE, hEω⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec V')
    (GlobalTheory.IsGenericPointHom.fractionField V' (FractionRing V')) hG' hG'' hω hω''
  haveI := hE
  let β' := E.hom.left ≫ pullback.fst G.hom ξ
  have hβ' : IsGrpPullback ((Over.pullback (spMap fV)).obj Gu) G ξ β' :=
    IsGrpPullback.congr ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso E).comp hG''p) (Category.id_comp _) rfl
  have hωβ' : ω ≫ β' = Ψ := by
    show ω ≫ E.hom.left ≫ pullback.fst G.hom ξ = Ψ
    rw [← Category.assoc, hEω, hω''f]
  refine ⟨(Over.pullback (spMap fV)).obj Gu, inferInstance, pullback.fst _ _, β', ω, hG'p, hβ', hωs, hωf, hωβ', ?_⟩
  intro F f eK hF hf
  let F' := (Over.pullback (spMap fV)).map F
  have hF'f : F'.left ≫ pullback.fst Gu.hom (spMap fV) = pullback.fst Gu.hom (spMap fV) ≫ F.left :=
    pullback.lift_fst _ _ _
  refine ⟨F', hF'f, ?_⟩
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hG'
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V' (FractionRing V')
  haveI : IsSchemeTheoreticallyDominant ω := .of_isPullback hω.1.flip
  have key : ω ≫ F'.left = eK.left ≫ ω := by
    apply pullback.hom_ext
    · rw [Category.assoc, hF'f, ← Category.assoc, hωf, Category.assoc, hωf, hF]
    · have e1 : F'.left ≫ ((Over.pullback (spMap fV)).obj Gu).hom = ((Over.pullback (spMap fV)).obj Gu).hom := Over.w F'
      have e2 : eK.left ≫ AK.hom = AK.hom := Over.w eK
      show (ω ≫ F'.left) ≫ ((Over.pullback (spMap fV)).obj Gu).hom = (eK.left ≫ ω) ≫ ((Over.pullback (spMap fV)).obj Gu).hom
      rw [Category.assoc, e1, hωs, Category.assoc, hωs, ← Category.assoc, e2]
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ ω ?_
  · have e1 : F'.left ≫ ((Over.pullback (spMap fV)).obj Gu).hom = ((Over.pullback (spMap fV)).obj Gu).hom := Over.w F'
    have e2 : f.left ≫ G.hom = G.hom := Over.w f
    rw [Category.assoc, hβ'.1.w, ← Category.assoc, e1, Category.assoc, e2, hβ'.1.w]
  · rw [← Category.assoc, key, Category.assoc, hωβ', ← Category.assoc, hωβ', hf]

end GlobalTheory.Poinc.FibLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonScalingDescendsToFractionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.Mum.GalDesc

open GlobalTheory.FieldBaseChange

theorem exists_algebraMap_eq_of_fixed {K F : Type} [Field K] [CharZero K] [Field F] [Algebra K F] [IsAlgClosure K F]
    (x : F) (h : ∀ σ : F →ₐ[K] F, σ x = x) : ∃ k : K, algebraMap K F k = x := by
  haveI := IsAlgClosure.isGalois K F
  have hx : x ∈ IntermediateField.fixedField (⊥ : IntermediateField K F).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ _
    exact h σ.toAlgHom
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hx
  exact IntermediateField.mem_bot.1 hx

variable {K F : Type} [Field K] [Field F] [Algebra K F] {V W : Type} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module F W]

theorem linearIndependent_image {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) :
    LinearIndependent F (fun i => a (Module.Basis.ofVectorSpace K V i)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have key : ∀ ℓ : F →ₗ[K] K, ℓ (g i) = 0 := by
    intro ℓ
    obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
    have h0 : ∑ j ∈ s, ℓ (g j) • Module.Basis.ofVectorSpace K V j = 0 := by
      have := congrArg Λ hg
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero, Finset.sum_congr rfl fun j _ => hΛ (g j) _] at this
      exact this
    exact linearIndependent_iff'.1 (Module.Basis.ofVectorSpace K V).linearIndependent s _ h0 i hi
  let e := Module.Basis.ofVectorSpace K F
  apply e.repr.injective
  ext j
  simpa using key (e.coord j)

theorem span_image {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) :
    ⊤ ≤ Submodule.span F (Set.range fun i => a (Module.Basis.ofVectorSpace K V i)) := by
  rw [← ha.span, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (Module.Basis.ofVectorSpace K V).linearCombination_repr v, Finsupp.linearCombination_apply,
    Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def extBasis {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) :
    Module.Basis (Module.Basis.ofVectorSpaceIndex K V) F W :=
  Module.Basis.mk (linearIndependent_image ha) (span_image ha)

theorem extBasis_apply {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) (i) :
    extBasis ha i = a (Module.Basis.ofVectorSpace K V i) := Module.Basis.mk_apply _ _ _

theorem repr_semilinear {Idx : Type} (B : Module.Basis Idx F W) (τ : F →+* F) (g : W →ₛₗ[τ] W)
    (hg : ∀ i, g (B i) = B i) (w : W) (i : Idx) : B.repr (g w) i = τ (B.repr w i) := by
  classical
  have hw : w ∈ Submodule.span F (Set.range B) := B.span_eq ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [hg, B.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | smul c x _ hx =>
    rw [map_smulₛₗ, map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, hx,
      map_mul]

theorem exists_scale [CharZero K] [IsAlgClosure K F] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a)
    (g : ∀ σ : F →ₐ[K] F, W →ₛₗ[(σ : F →+* F)] W) (hg : ∀ σ v, g σ (a v) = a v)
    {Ix : Type} (T : Ix → W) (c : (F →ₐ[K] F) → Fˣ) (hT : ∀ σ i, g σ (T i) = (c σ : F) • T i) :
    ∃ u : Fˣ, ∀ i, ∃ v, a v = (u : F) • T i := by
  classical
  set B := extBasis ha
  have hgB : ∀ σ j, g σ (B j) = B j := fun σ j => by rw [extBasis_apply, hg]
  have fix : ∀ w : W, (∀ σ, g σ w = w) → ∃ v, a v = w := by
    intro w hw
    have : ∀ j, ∃ k : K, algebraMap K F k = B.repr w j := fun j =>
      exists_algebraMap_eq_of_fixed _ fun σ => by
        have e := repr_semilinear B (σ : F →+* F) (g σ) (hgB σ) w j
        rw [hw σ] at e
        exact e.symm
    choose k hk using this
    refine ⟨∑ j ∈ (B.repr w).support, k j • Module.Basis.ofVectorSpace K V j, ?_⟩
    conv_rhs => rw [← B.linearCombination_repr w, Finsupp.linearCombination_apply, Finsupp.sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulₛₗ, hk, extBasis_apply]
  by_cases h0 : ∀ i, T i = 0
  · exact ⟨1, fun i => ⟨0, by rw [map_zero, h0 i, smul_zero]⟩⟩
  push_neg at h0
  obtain ⟨i₀, hi₀⟩ := h0
  have : B.repr (T i₀) ≠ 0 := fun h => hi₀ (B.repr.injective (h.trans (map_zero _).symm))
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 this
  set m0 := B.repr (T i₀) j with hm0
  have hm00 : m0 ≠ 0 := by simpa using hj
  have hσm : ∀ σ : F →ₐ[K] F, σ m0 = (c σ : F) * m0 := fun σ => by
    have := repr_semilinear B (σ : F →+* F) (g σ) (hgB σ) (T i₀) j
    rw [hT, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
    exact this.symm
  refine ⟨(Units.mk0 m0 hm00)⁻¹, fun i => fix _ fun σ => ?_⟩
  rw [map_smulₛₗ, hT, smul_smul]
  congr 1
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0, RingHom.coe_coe, map_inv₀, hσm]
  field_simp
end GlobalTheory.Mum.GalDesc

namespace GlobalTheory.Mum

open GlobalTheory.FieldBaseChange GlobalTheory.Mum.GalDesc

theorem exists_common_scale_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))) (N : ℕ) (Ix : Type) (T : Ix → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) (a : (Kb R →ₐ[FractionRing R] Kb R) → (Kb R)ˣ), (∀ σ i, ∃ t', SecTw σ (T i) t' ∧ ∀ j, t'.f j = liftFun A.A _ (fnF (Kb R) (a σ).val) * (T i).f j) → ∃ c : (Kb R)ˣ, ∀ i, ∃ Φ : H0 A.L N, ∀ t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N, (∀ j, t''.f j = liftFun A.A _ (fnF (Kb R) c.val) * (T i).f j) → Agree A.L t'' Φ := by
  intro R _ _ _ hB A N Ix T a hT
  haveI : CharZero R := hB.2
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  let π : A.A.left ⟶ Spec (CommRingCat.of (FractionRing R)) := A.A.hom
  let π' := (fst (TFK (R := R) (Kb R)) A.A).left
  let p := (snd (TFK (R := R) (Kb R)) A.A).left
  have H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R)))) :=
    (IsPullback.of_hasPullback _ _).flip
  haveI : TopologicalSpace.NoetherianSpace A.A.left := by
    have := A.isAb.proper
    have : IsLocallyNoetherian A.A.left := LocallyOfFiniteType.isLocallyNoetherian A.A.hom
    have : CompactSpace A.A.left := QuasiCompact.compactSpace_of_compactSpace A.A.hom
    have : IsNoetherian A.A.left := {}
    infer_instance
  let ε : Fin 1 → ℤ := fun _ => (N : ℤ)
  let aM := pullOver A.L ε (π := π) (π' := π') (φ := fun _ => 𝟙 A.A.left) (φ' := fun _ => p) H.w
    (fun _ => (Category.comp_id _).symm)
  have hext : IsExtension aM := isExtension_pullOver H A.isLB ε _

  have hσ : ∀ σ : Kb R →ₐ[FractionRing R] Kb R, spMap (σ : Kb R →+* Kb R) ≫ (TFK (R := R) (Kb R)).hom =
      (TFK (R := R) (Kb R)).hom := fun σ => by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
  let m : (Kb R →ₐ[FractionRing R] Kb R) → ((TFK (R := R) (Kb R) ⊗ A.A).left ⟶ (TFK (R := R) (Kb R) ⊗ A.A).left) :=
    fun σ => ((Over.homMk (spMap (σ : Kb R →+* Kb R)) (hσ σ) : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R)) ▷ A.A).left
  have hm₁ : ∀ σ, m σ ≫ π' = π' ≫ Spec.map (CommRingCat.ofHom (σ : Kb R →+* Kb R)) := fun σ => by
    simp only [m, π', ← Over.comp_left, whiskerRight_fst]; rfl
  have hm₂ : ∀ σ, m σ ≫ p = p := fun σ => by
    simp only [m, p, ← Over.comp_left, whiskerRight_snd]
  let g : ∀ σ : Kb R →ₐ[FractionRing R] Kb R, SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε) →ₛₗ[(σ : Kb R →+* Kb R)]
      SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε) :=
    fun σ => pullOver A.L ε (π := π') (π' := π') (p := m σ) (φ := fun _ => p) (φ' := fun _ => p) (hm₁ σ)
      (fun _ => (hm₂ σ).symm)

  have hg : ∀ σ v, g σ (aM v) = aM v := fun σ v => sec_ext' A.isLB fun y J hJ => by
    rw [sval_pullOver (hm₁ σ) (fun _ => (hm₂ σ).symm) _ _ hJ, sval_pullOver H.w (fun _ => (Category.comp_id _).symm) _ _ hJ,
      sval_pullOver H.w (fun _ => (Category.comp_id _).symm) _ _ hJ, Category.assoc, hm₂]
  let T' : Ix → SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε) := T

  have hsmul : ∀ (c : Kb R) (s t : SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε)),
      (∀ j, t.f j = liftFun A.A _ (fnF (Kb R) c) * s.f j) → t = c • s := fun c s t ht =>
    SecOver.ext _ _ fun j => (ht j).trans rfl
  have hT' : ∀ σ i, g σ (T' i) = ((a σ : (Kb R)ˣ) : Kb R) • T' i :=
    fun σ i => by
    obtain ⟨t', htw, ht'⟩ := hT σ i
    rw [← hsmul _ _ t' ht']
    refine sec_ext' A.isLB fun y J hJ => ?_
    rw [sval_pullOver (hm₁ σ) (fun _ => (hm₂ σ).symm) _ _ hJ]
    refine (htw _ (𝟙 _) (𝟙 _ ≫ m σ) (by rw [Category.assoc, hm₂]) ?_ y J hJ).symm
    rw [Category.assoc, hm₁, Category.id_comp, Category.id_comp]; rfl
  obtain ⟨u, hu⟩ := exists_scale hext g hg T' a hT'
  refine ⟨u, fun i => ?_⟩
  obtain ⟨v, hv⟩ := hu i
  refine ⟨v, fun t'' ht'' => ?_⟩
  have e : t'' = aM v := (hsmul _ (T' i) t'' ht'').trans hv.symm
  intro Z q q' hq z J hJ
  rw [show t'' = aM v from e, sval_pullOver H.w (fun _ => (Category.comp_id _).symm) _ _ hJ, hq, Category.comp_id]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjUniversalTripleIdentification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UGalTrans

open GlobalTheory.CechPic GlobalTheory.Poinc.GalTrans

theorem exists_twist_along_genericAutomorphism {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S S' : ThetaSys o Ω} (ρ : S.Real)
    (ρ' : S'.Real) (l' : S.Gam → S'.Gam) (h' : USame ρ ρ' l' (RingHom.id _)) (σ τ : Ω →+* Ω)
    (hτ : τ.comp σ = RingHom.id _) (hσ : σ.comp τ = RingHom.id _) (a : S.Gam → S.Gam)
    (P₀ : PolAV (Sp Ω)) (b : P₀.A.left ⟶ ρ.P.A.left) (t : P₀.A.left ⟶ P₀.A.left)
    (hb : IsGrpPullback P₀.A ρ.P.A (spMap S.R.val.toRingHom) b)
    (ht : IsGrpPullback P₀.A P₀.A (spMap σ) t) (lb : LBIso P₀.L (ρ.P.L.pull b)) (lt : LBIso P₀.L (P₀.L.pull t))
    (hp : ∀ x (w w' : Sp Ω ⟶ P₀.A.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left →
      w' ≫ t = spMap σ ≫ w → w' ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt (a x)).left)
    {B : Scheme.{0}} {v : Sp Ω ⟶ B} {r : B ⟶ Sp S'.R} (hv : v ≫ r = spMap S'.R.val.toRingHom)
    (G : Over B) [GrpObj G] (α : G.left ⟶ ρ'.P.A.left) (hα : IsGrpPullback G ρ'.P.A r α)
    {Y : Scheme.{0}} (N : LB Y) (hN : N.IsLB) (β : G.left ⟶ Y) (hL : LBIso (ρ'.P.L.pull α) (N.pull β)) :
    ∃ (P₁ : PolAV (Sp Ω)) (e : P₁.A.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ P₁.A.left) (k₀ : P₁.A.left ⟶ G.left),
      IsGrpPullback P₁.A P₀.A (spMap σ) e ∧ IsGrpPullback P₀.A P₁.A (spMap τ) j ∧ IsGrpPullback P₁.A G v k₀ ∧
      e ≫ j = 𝟙 _ ∧ LBIso (ρ.P.L.pull b) (N.pull (j ≫ k₀ ≫ β)) ∧
      ∀ x (w : Sp Ω ⟶ P₀.A.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left →
        ∃ w₀ : Sp Ω ⟶ P₁.A.left, w₀ ≫ P₁.A.hom = 𝟙 _ ∧ w₀ ≫ e = spMap σ ≫ w ∧
          w₀ ≫ k₀ ≫ α = spMap S'.R.val.toRingHom ≫ (ρ'.pt (l' (a x))).left := by
  obtain ⟨P₁, a₁, a₁', ha₁, ha₁', la₁, la₁', hp₁⟩ := h'
  rw [RingHom.id_comp] at ha₁ hp₁
  have := mono_val S.R S.frac
  have : Mono b := (MorphismProperty.monomorphisms Scheme).of_isPullback hb.1.flip (.infer_property _)
  obtain ⟨κ, hκ, lκ, eκ⟩ := exists_factor ρ.P P₀ P₁ (Category.id_comp _) hb ha₁ lb la₁
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by simp [spMap]
  have e₁ : spMap τ ≫ spMap σ = 𝟙 (Sp Ω) := (sp_comp hτ).trans hid
  have e₂ : spMap σ ≫ spMap τ = 𝟙 (Sp Ω) := (sp_comp hσ).trans hid
  have he : IsGrpPullback P₁.A P₀.A (spMap σ) (κ ≫ t) := (hκ.comp ht).congr (Category.id_comp _) rfl
  have le := lb_comp P₁.isLB P₀.isLB P₀.isLB lκ lt
  have : IsIso (spMap σ) := ⟨_, e₂, e₁⟩
  have : Mono (κ ≫ t) := (MorphismProperty.monomorphisms Scheme).of_isPullback he.1.flip (.infer_property _)
  have : IsMonHom (Iso.refl P₀.A).hom := inferInstanceAs (IsMonHom (𝟙 P₀.A))
  obtain ⟨j, hj, lj, ej⟩ := exists_factor P₀ P₁ P₀ (ψ := 𝟙 _) e₁ he (isGrpPullback_of_iso (Iso.refl P₀.A)) le
    ((iso_iff P₀.isLB P₀.isLB _).2 (by rw [GlobalTheory.CechPic.pull_id]; try rfl))
  have w₁ : a₁' ≫ ρ'.P.A.hom = (P₁.A.hom ≫ v) ≫ r := by rw [ha₁'.1.w, Category.assoc, hv]
  have k₁ := hα.1.lift_fst _ _ w₁
  have k₂ := hα.1.lift_snd _ _ w₁
  generalize hα.1.lift _ _ w₁ = k₀ at k₁ k₂
  have hs : ∀ x, (ρ.pt x).left ≫ ρ.P.A.hom = 𝟙 _ := fun x => Over.w (ρ.pt x)
  refine ⟨P₁, κ ≫ t, j, k₀, he, hj, hα.cancel (ha₁'.congr hv.symm k₁.symm) k₂, ?_, ?_, fun x w hw => ?_⟩
  · rw [← cancel_mono (κ ≫ t), Category.assoc, ej, Category.comp_id, Category.id_comp]
  · have c₁ := (iso_iff (pull_isLB ρ'.P.isLB α) hN β).1 hL
    rw [cls_pull ρ'.P.isLB] at c₁
    rw [iso_iff (pull_isLB ρ.P.isLB b) hN, cls_pull ρ.P.isLB, ← (iso_iff P₀.isLB ρ.P.isLB _).1 lb,
      (iso_iff P₀.isLB P₁.isLB _).1 lj, (iso_iff P₁.isLB ρ'.P.isLB _).1 la₁', ← k₁, pull_comp, pull_comp, pull_comp, c₁]
  · obtain ⟨u, f₁, f₁'⟩ := hp₁ (a x)
    have k₃ : w ≫ P₀.A.hom = 𝟙 _ := by
      rw [← cancel_mono (spMap S.R.val.toRingHom), Category.assoc, ← hb.1.w, reassoc_of% hw, hs]
      simp
    have c₂ : (spMap σ ≫ w) ≫ P₀.A.hom = 𝟙 _ ≫ spMap σ := by rw [Category.assoc, k₃]; simp
    have k₄ := ht.1.lift_fst _ _ c₂
    generalize ht.1.lift _ _ c₂ = w' at k₄
    have k₅ : u ≫ κ = w' := by
      rw [← cancel_mono b, Category.assoc, eκ, f₁, hp x w w' hw k₄]
    refine ⟨u, ?_, by rw [reassoc_of% k₅, k₄], by rw [k₁, f₁']⟩
    rw [← cancel_mono (spMap S.R.val.toRingHom), Category.assoc, ← ha₁.1.w, reassoc_of% f₁, hs]
    simp

theorem exists_conj_uWit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (a : D.X.S.Gam ≃+ D.X.S.Gam), D.GalLab σ a → ∀ (c₀ : D.X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra D.X.o₁ D.X.Ω₁) (fg : R'.FG) (frac : ∀ x : D.X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * D.X.S.th x ∈ R') (hev : ∀ x k, c₀ * D.X.S.ev x k ∈ R') (ρ' : (D.X.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame D.X.ρ ρ' (fun x => x) (RingHom.id _) → spMap (ratHull R').val.toRingHom ≫ u' = D.X.uΩ → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∃ (wi : UWit D.X) (W₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj W₀) (e : W₀.left ⟶ wi.G.left) (k₀ : W₀.left ⟶ G.left), IsGrpPullback W₀ wi.G (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) e ∧ IsGrpPullback W₀ G (spMap (ratHull R').val.toRingHom) k₀ ∧ e ≫ wi.β = k₀ ≫ β ∧ ∀ x (w : Sp D.X.Ω₁ ⟶ wi.G.left), w ≫ wi.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left → ∃ w₀ : Sp D.X.Ω₁ ⟶ W₀.left, w₀ ≫ W₀.hom = 𝟙 _ ∧ w₀ ≫ e = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ w ∧ w₀ ≫ k₀ ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt (a x)).left := by
  intro E _ _ _ H Dw l Xo cf C X₁ D σ a hG c₀ hc R' fg frac hth hev ρ' u' hs hu G _ α β hα hβ hL
  obtain ⟨P₀, b, t, hb, ht, lb, lt, hp⟩ := hG
  obtain ⟨P₁, e, j, k₀, he, hj, hk, ej, hL', hpt⟩ := exists_twist_along_genericAutomorphism D.X.ρ ρ' _ hs (σ : D.X.Ω₁ →+* D.X.Ω₁)
    (σ.symm : D.X.Ω₁ →+* D.X.Ω₁) (RingHom.ext fun x => σ.symm_apply_apply x) (RingHom.ext fun x => σ.apply_symm_apply x)
    a P₀ b t hb ht lb lt hp (spMap_val_toRat R') G α hα _ Xo.univ.t.PP.isLB β hL
  have h₁ : spMap (σ.symm : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.uΩ = D.X.uΩ := by
    rw [D.pt, ← Category.assoc, sp_comp (RingHom.ext fun x => σ.symm.commutes x)]
  have hβ' : IsGrpPullback P₀.A Xo.univ.t.G (D.X.uΩ ≫ pullback.fst _ _) (j ≫ k₀ ≫ β) :=
    (hj.comp (hk.comp hβ)).congr (by rw [← Category.assoc _ u', hu, ← Category.assoc, h₁]) rfl
  exact ⟨{ G := P₀.A, α := b, β := j ≫ k₀ ≫ β, hα := hb, hβ := hβ', hL := hL' }, P₁.A, inferInstance, e, k₀, he, hk,
    by rw [reassoc_of% ej], hpt⟩

end GlobalTheory.UPoinc.UGalTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeProductTwistedSectionsVanishing
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem prod_tφ_eq {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X)
    {U : Type} [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ k, h (tφ D a β k) ^ tε n j k =
      h (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (n - 1) * h ((toUnit D.P.A ≫ D.c β) * 𝟙 D.P.A : D.P.A ⟶ D.P.A).left *
        (h (toUnit D.P.A ≫ D.c β).left)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left * h a.left ^ j := by
  rw [Fin.prod_univ_five, _root_.mul_comm (toUnit D.P.A ≫ D.c β)]
  simp only [← zpow_neg_one]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (zpow_one _)) rfl)
    (zpow_one _)) rfl

theorem exists_isProdT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j n' j' : ℤ)
    (β β' : D.X) (f : SecT D a n j β) (g : SecT D a n' j' β') :
    ∃ p : SecT D a (n + n') (j + j') (β + β'), IsProdT f g p := by
  have hadd : toUnit D.P.A ≫ D.c (β + β') = (toUnit D.P.A ≫ D.c β) * (toUnit D.P.A ≫ D.c β') := by
    rw [D.c_add]; exact MonObj.comp_mul _ _ _
  have hu := DVR.pullGen_isGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t D.cub.isGen
    (lift (toUnit _ ≫ D.c β) (lift (toUnit _ ≫ D.c β') (𝟙 D.P.A)) : D.P.A ⟶ G3 D.P.A).left
  obtain ⟨p, hp⟩ := exists_sec D.P.isLB (φ' := tφ D a (β + β')) (ε' := tε (n + n') (j + j')) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) (prod_tφ_eq D a n j β h) (prod_tφ_eq D a n' j' β' h)))
        (prod_cub (toUnit D.P.A ≫ D.c β) (toUnit D.P.A ≫ D.c β') (𝟙 D.P.A) h))).trans ?_
      rw [prod_tφ_eq, hadd]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec f g) (genSec _ hu))
  refine ⟨p, fun Z x z J hJ => (hp Z x z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ) ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val (val_pull hJ _ _ _)))))⟩

theorem exists_prodT_van : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (β β' : D.toPre.X) (f : SecT D.toPre a n j β) (g : SecT D.toPre a n' j' β'), ∃ p : SecT D.toPre a n'' j'' (β + β'), IsProdT f g p ∧ ∀ e, (Van (maximalIdeal R) f e ∨ Van (maximalIdeal R) g e) → Van (maximalIdeal R) p e := by
  intro R _ _ _ _ D a n j n' j' n'' j'' hn hj β β' f g
  subst hn hj
  obtain ⟨p, hp⟩ := exists_isProdT D.toPre a n j n' j' β β' f g
  refine ⟨p, hp, fun e he Z x z J hJ => ?_⟩
  rw [hp Z _ z J hJ]
  rcases he with he | he
  · rw [he Z x z J hJ, zero_mul, zero_mul]
  · rw [he Z x z J hJ, mul_zero, zero_mul]

end GlobalTheory.TwFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantRestrictionPointClosures
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem clo_restrict_dominant : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X) (y : Y), ∃ g : clo y ⟶ clo (π y), g ≫ cloι (π y) = cloι y ≫ π ∧ g (genericPoint _) = genericPoint _ ∧ ∀ w : clo y, g.residueDegree w = π.residueDegree (cloι y w) := by
  intro X Y π y
  set i := cloι (π y)
  set j := cloι y
  have hi : i (genericPoint (clo (π y))) = π y := cloι_genericPoint _
  have hj : j (genericPoint (clo y)) = y := cloι_genericPoint _
  have hr : Set.range i = closure {π y} := by
    have h₁ := (genericPoint_spec (clo (π y))).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  have : Surjective (Limits.pullback.snd i (j ≫ π)) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr]
    refine Set.eq_univ_of_forall fun w => ?_
    have := ((genericPoint_specializes w).map (j ≫ π).continuous)
    rw [Set.mem_preimage]
    have e : (j ≫ π) (genericPoint (clo y)) = π y := by
      rw [Scheme.Hom.comp_apply, hj]
    rw [e] at this
    exact this.mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd i (j ≫ π))
  refine ⟨inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π), ?_, ?_, ?_⟩
  · rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]
  · apply i.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc,
      Scheme.Hom.comp_apply, hj, hi]
  · intro w
    have e₁ := GlobalTheory.CurveDegreesCompare.residueDegree_comp (inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π)) i w
    have e₂ := GlobalTheory.CurveDegreesCompare.residueDegree_comp j π w
    rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc,
      GlobalTheory.Published.residueDegree_of_isClosedImmersion i, one_mul] at e₁
    rw [GlobalTheory.Published.residueDegree_of_isClosedImmersion j, mul_one] at e₂
    rw [← e₁, e₂]

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantInverseThetaExpansionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_inverse_thetaExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → CharZero R → ∀ (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (w₀ : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w₀.IsGen → ∀ lab : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A), (∀ p, QkToAkU U.toUnifPre F N p (lab p)) → ∃ E, Eqv D.toPre A F N lab E ∧ ∀ s, U.ExpandsF F N w₀ (E s) s := by
  first | exact @GlobalTheory.Mum.exists_eqv_expandsF | exact GlobalTheory.Mum.exists_eqv_expandsF | (intros; apply GlobalTheory.Mum.exists_eqv_expandsF <;> assumption)
end

