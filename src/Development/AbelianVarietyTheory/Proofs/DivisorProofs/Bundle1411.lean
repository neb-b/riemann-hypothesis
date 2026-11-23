module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1348
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExtendsUnramified
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnramifiedClosure

theorem injective_of_map_maximalIdeal {R W : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra R W]
    (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    Function.Injective (algebraMap R W) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hp : (RingHom.ker (algebraMap R W)).IsPrime := RingHom.ker_isPrime _
  have hm : RingHom.ker (algebraMap R W) = maximalIdeal R := IsLocalRing.eq_maximalIdeal (hp.isMaximal hne)
  apply IsDiscreteValuationRing.not_a_field W
  rw [← h, ← hm]
  exact (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl

variable (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K']
  [IsScalarTower R W K'] [IsScalarTower R K K']

theorem isLocalization (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    IsLocalization (Algebra.algebraMapSubmonoid W (nonZeroDivisors R)) K' := by
  have hinj := injective_of_map_maximalIdeal h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖW : Irreducible (algebraMap R W ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← h,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton]
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, r, hr, rfl⟩
    refine IsUnit.mk0 _ ?_
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact fun h0 => nonZeroDivisors.ne_zero hr (hinj (by rw [map_zero]; exact h0))
  · intro z
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := W) z
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖW
    refine ⟨⟨x * ↑u⁻¹, ⟨algebraMap R W (ϖ ^ n), ϖ ^ n,
      mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hϖ.ne_zero), rfl⟩⟩, ?_⟩
    have hu : algebraMap W K' ↑u * algebraMap W K' ↑u⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hp : algebraMap W K' (algebraMap R W ϖ) ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact hϖW.ne_zero
    have hu0 : algebraMap W K' ↑u ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact u.ne_zero
    simp only [map_pow, map_mul]
    field_simp
    linear_combination (-(algebraMap W K' x)) * hu
  · intro x y hxy
    exact ⟨1, by simpa using IsFractionRing.injective W K' hxy⟩

theorem isPushout (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    Algebra.IsPushout R K W K' := by
  haveI := isLocalization R W K' h
  constructor
  exact (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K _).1
    (isLocalizedModule_iff_isLocalization.2 this)

theorem isPullback_spec (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    IsPullback (spMap (algebraMap K K')) (spMap (algebraMap W K')) (spMap (algebraMap R K))
      (spMap (algebraMap R W)) := by
  haveI := isPushout R K W K' h
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout R K W K')

theorem flat_spec (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    Flat (spMap (algebraMap R W)) := by
  have hinj := injective_of_map_maximalIdeal h
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  refine GlobalTheory.ringHom_flat_of_injective_of_isUnit (algebraMap R W) (algebraMap W (FractionRing W))
    (IsFractionRing.injective W (FractionRing W)) fun t ht => IsUnit.mk0 _ ?_
  rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact fun h0 => ht (hinj (by rw [h0, map_zero]))

end GlobalTheory.UnramifiedClosure

namespace GlobalTheory.UnramifiedClosure

theorem schDom_spMap {A B : Type} [CommRing A] [CommRing B] [IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (spMap φ) := by
  haveI : IsDominant (spMap φ) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

end GlobalTheory.UnramifiedClosure

open GlobalTheory.UnramifiedClosure in
theorem GlobalTheory.UnramifiedClosure.closure_baseChange : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ (P : Over (Sp R)), QuasiSeparated P.hom → ∀ (A : Over (Sp K)), QuasiCompact A.hom → ∀ (G : Over (Sp W)), QuasiCompact G.hom → Flat G.hom → ∀ (e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A) (iA : A.left ⟶ P.left) (hA : iA ≫ P.hom = A.hom ≫ spMap (algebraMap R K)), IsClosedImmersion (pullback.lift iA A.hom hA) → ∀ (iG : G.left ⟶ P.left) (hG : iG ≫ P.hom = G.hom ≫ spMap (algebraMap R W)), IsClosedImmersion (pullback.lift iG G.hom hG) → e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ iA = pullback.fst G.hom (spMap (algebraMap W K')) ≫ iG → ∃ (X : Over (Sp R)) (a : A.left ⟶ X.left) (g : G.left ⟶ X.left), IsPullback a A.hom X.hom (spMap (algebraMap R K)) ∧ IsPullback g G.hom X.hom (spMap (algebraMap R W)) ∧ e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm P hP A hAq G hGq hGf e iA hA hcA iG hG hcG hcomp

  have hjp : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hjf : Flat (spMap (algebraMap R K)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have hjW : Flat (spMap (algebraMap R W)) := flat_spec R W hm
  have hsq := isPullback_spec R K W K' hm
  have hqc : QuasiCompact iA := by
    have : QuasiCompact (iA ≫ P.hom) := by rw [hA]; infer_instance
    exact QuasiCompact.of_comp iA P.hom
  have hdom : IsSchemeTheoreticallyDominant iA.toImage := GlobalTheory.isSchemeTheoreticallyDominant_toImage iA
  let X : Over (Sp R) := Over.mk (iA.imageι ≫ P.hom)
  have hXh : X.hom = iA.imageι ≫ P.hom := rfl
  have hXa : iA.toImage ≫ X.hom = A.hom ≫ spMap (algebraMap R K) := by
    rw [hXh, Scheme.Hom.toImage_imageι_assoc, hA]
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0} :=
    ⟨fun f g hf hg ↦ @IsClosedImmersion.comp _ _ _ f g hf hg⟩

  let t : A.left ⟶ pullback X.hom (spMap (algebraMap R K)) := pullback.lift iA.toImage A.hom hXa
  let mK : pullback X.hom (spMap (algebraMap R K)) ⟶ pullback P.hom (spMap (algebraMap R K)) :=
    pullback.map _ _ _ _ iA.imageι (𝟙 _) (𝟙 _) (Category.comp_id _) (by simp)
  have hmK : IsClosedImmersion mK :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance rfl (by simp)
  have htm : t ≫ mK = pullback.lift iA A.hom hA := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst,
        Scheme.Hom.toImage_imageι]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd,
        Category.comp_id]
  have : IsClosedImmersion (t ≫ mK) := htm ▸ hcA
  have ht : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t mK
  have hpb : IsPullback (𝟙 A.left) t iA.toImage (pullback.fst X.hom (spMap (algebraMap R K))) :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, pullback.lift_fst]⟩
  have htd : IsSchemeTheoreticallyDominant t := .of_isPullback hpb
  have : IsIso t := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr t.ker_eq_bot
  have hIa : IsPullback iA.toImage A.hom X.hom (spMap (algebraMap R K)) :=
    IsPullback.of_iso_pullback ⟨hXa⟩ (asIso t) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

  have hAK : IsPullback (pullback.fst A.hom (spMap (algebraMap K K')))
      (pullback.snd A.hom (spMap (algebraMap K K')) ≫ spMap (algebraMap W K'))
      (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W)) :=
    (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))).paste_vert hsq
  let mW : pullback X.hom (spMap (algebraMap R W)) ⟶ pullback P.hom (spMap (algebraMap R W)) :=
    pullback.map _ _ _ _ iA.imageι (𝟙 _) (𝟙 _) (Category.comp_id _) (by simp)
  have hmW : IsClosedImmersion mW :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance rfl (by simp)
  let n : pullback (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W)) ⟶
      pullback X.hom (spMap (algebraMap R W)) :=
    pullback.map _ _ _ _ iA.toImage (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hXa]) (by simp)
  have hL : IsPullback (pullback.fst (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W))) n
      iA.toImage (pullback.fst X.hom (spMap (algebraMap R W))) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback X.hom (spMap (algebraMap R W)))
    have h1 : n ≫ pullback.snd X.hom (spMap (algebraMap R W)) =
        pullback.snd (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W)) := by
      rw [pullback.lift_snd, Category.comp_id]
    rw [h1, hXa]
    exact IsPullback.of_hasPullback _ _
  have hn : IsSchemeTheoreticallyDominant n := .of_isPullback hL
  have hsd : IsSchemeTheoreticallyDominant (spMap (algebraMap W K')) :=
    schDom_spMap _ (IsFractionRing.injective W K')
  have hu : IsSchemeTheoreticallyDominant (pullback.fst G.hom (spMap (algebraMap W K'))) :=
    inferInstance
  have he : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let v : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback X.hom (spMap (algebraMap R W)) :=
    e.hom.left ≫ hAK.isoPullback.hom ≫ n
  have hv : IsSchemeTheoreticallyDominant v := inferInstance
  let cG : G.left ⟶ pullback P.hom (spMap (algebraMap R W)) := pullback.lift iG G.hom hG
  have hes : e.hom.left ≫ pullback.snd A.hom (spMap (algebraMap K K')) =
      pullback.snd G.hom (spMap (algebraMap W K')) := Over.w e.hom
  have hcomm : pullback.fst G.hom (spMap (algebraMap W K')) ≫ cG = v ≫ mW := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← hcomp]
      simp only [v, mW, n, pullback.map, Category.assoc]
      simp only [pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc,
        IsPullback.isoPullback_hom_fst_assoc, Scheme.Hom.toImage_imageι]
    · rw [Category.assoc, pullback.lift_snd]
      simp only [v, mW, n, Category.assoc]
      rw [pullback.lift_snd, Category.comp_id (pullback.snd X.hom (spMap (algebraMap R W))),
        pullback.lift_snd,
        Category.comp_id (pullback.snd (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W))),
        IsPullback.isoPullback_hom_snd, reassoc_of% hes]
      exact pullback.condition
  have hker : mW.ker = cG.ker := by
    have h1 : (pullback.fst G.hom (spMap (algebraMap W K')) ≫ cG).ker = cG.ker := by
      rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    have h2 : (v ≫ mW).ker = mW.ker := by
      rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [← h1, ← h2, hcomm]
  let ψ : G.left ⟶ pullback X.hom (spMap (algebraMap R W)) := IsClosedImmersion.lift mW cG hker.le
  have hψ : ψ ≫ mW = cG := IsClosedImmersion.lift_fac _ _ _
  have : IsIso ψ := IsClosedImmersion.isIso_lift mW cG hker
  have hψs : ψ ≫ pullback.snd X.hom (spMap (algebraMap R W)) = G.hom := by
    have h := congrArg (· ≫ pullback.snd P.hom (spMap (algebraMap R W))) hψ
    simp only [Category.assoc] at h
    rwa [pullback.lift_snd, Category.comp_id, pullback.lift_snd] at h
  have hIg : IsPullback (ψ ≫ pullback.fst X.hom (spMap (algebraMap R W))) G.hom X.hom
      (spMap (algebraMap R W)) :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, reassoc_of% hψs]⟩
      (asIso ψ) rfl hψs
  refine ⟨X, iA.toImage, ψ ≫ pullback.fst X.hom (spMap (algebraMap R W)), hIa, hIg, ?_⟩
  rw [← cancel_mono iA.imageι]
  have h3 : pullback.fst X.hom (spMap (algebraMap R W)) ≫ iA.imageι =
      mW ≫ pullback.fst P.hom (spMap (algebraMap R W)) := (pullback.lift_fst _ _ _).symm
  simp only [Category.assoc]
  simp only [h3, ← Category.assoc, hψ, Scheme.Hom.toImage_imageι]
  simpa only [Category.assoc, cG, pullback.lift_fst] using hcomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsDIffDOp
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.EvAt0.PolEv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Gen

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem at_symm (M : Model σ X W) (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    At (evI F) (M.co.e.symm (fun i => liftA (a i), fun i => liftA (b i))) := by
  intro c hc
  rw [← map_smul]
  have : c • ((fun i => liftA (a i), fun i => liftA (b i)) : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) = 0 := by
    ext i <;> simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] <;>
      exact smul_liftA hc _
  rw [this, map_zero]

theorem arc_liftA {κ : Type} (a : κ → mixedEmbedding.mixedSpace F) : arc (fun i => liftA (a i)) = a := by
  funext i; exact evI_liftA (a i)

theorem actsD_iff_dOp {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hu : At (evI F) u) (f f₁ : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.HeisDer.derEx F E σ _ _ _ ψ _ _ M.co hψ
  have e : D u f = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
    ext x
    rw [(hD u hu f).2 x, dOp_apply]
    rfl
  have h1 : ActsD (evI F) (M.heisLine ψ u) f (D u f) :=
    (_root_.GlobalTheory.RealLift.actsLaws F _ f (D u f) (D u f)).1 _ (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr])
      (hD u hu f).1
  rw [← e]
  exact ⟨fun h2 => (_root_.GlobalTheory.RealLift.actsLaws F _ f f₁ (D u f)).2.2.1 _ h2 h1, fun h2 => h2 ▸ h1⟩

theorem isGauss_iff {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (g : SInf F (Fin n × Fin d)) : M.IsGauss ψ τ g ↔ GaussD M τ g := by
  refine exists_congr fun ε => forall₂_congr fun u u' => forall₃_congr fun hu hu' _ => ⟨fun H => ?_, fun H f f' hf hf' => ?_⟩
  · exact H _ _ ((actsD_iff_dOp hψ M u hu _ _).2 rfl) ((actsD_iff_dOp hψ M u' hu' _ _).2 rfl)
  · rw [(actsD_iff_dOp hψ M u hu _ _).1 hf, (actsD_iff_dOp hψ M u' hu' _ _).1 hf']
    exact H

theorem pol_eq {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    M.Pol ψ τ = sInf {N | (∀ f₀, GaussD M τ f₀ → f₀ ∈ N) ∧
      ∀ (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F), ∀ f ∈ N, dOp a b f ∈ N} := by
  unfold Model.Pol
  congr 1
  ext N
  simp only [Set.mem_setOf_eq]
  refine and_congr (forall_congr' fun f₀ => imp_congr_left (isGauss_iff hψ M τ f₀)) ⟨fun H a b f hf => ?_, fun H u hu f hf f₁ h1 => ?_⟩
  · have hu := at_symm M a b
    refine H _ hu f hf _ ((actsD_iff_dOp hψ M _ hu _ _).2 ?_)
    rw [LinearEquiv.apply_symm_apply, arc_liftA, arc_liftA]
  · rw [(actsD_iff_dOp hψ M u hu _ _).1 h1]
    exact H _ _ f hf

theorem dOp_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ) :
    dOp a b f ∈ M.Pol ψ τ := by
  rw [pol_eq hψ] at hf ⊢
  exact Submodule.mem_sInf.2 fun N hN => hN.2 a b f (Submodule.mem_sInf.1 hf N hN)

theorem gauss_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {f : SInf F (Fin n × Fin d)} (hf : GaussD M τ f) : f ∈ M.Pol ψ τ := by
  rw [pol_eq hψ]
  exact Submodule.mem_sInf.2 fun N hN => hN.1 f hf

end Gen

end GlobalTheory.ThK.EvAt0.PolEv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineLineMorphismConstantOfConstOnNonzero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstAffineLine

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem spMap_section {k : Type} [Field k] (φ : Polynomial k →+* k)
    (hφ : φ.comp (algebraMap k (Polynomial k)) = RingHom.id k) :
    spMap φ ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _ := by
  rw [spMap_comp', hφ, spMap_id']

theorem eq_of_const_nonzero : ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsSeparated q] [LocallyOfFiniteType q] (f : Sp (Polynomial k) ⟶ Y), f ≫ q = spMap (algebraMap k (Polynomial k)) → (∀ c : k, c ≠ 0 → spMap (Polynomial.evalRingHom c) ≫ f = spMap (Polynomial.evalRingHom 1) ≫ f) → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f = spMap b.toRingHom ≫ f := by
  intro k _ _ Y q _ _ f hq hc a b
  have h1 : (Polynomial.evalRingHom (1 : k)).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
    ext x; simp
  have hs1 := spMap_section _ h1
  set f' := spMap (algebraMap k (Polynomial k)) ≫ spMap (Polynomial.evalRingHom (1 : k)) ≫ f with hf'
  have hlft : LocallyOfFiniteType (f ≫ q) := by
    rw [hq]; exact HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  have key : f = f' := by
    refine ext_of_apply_eq (K := k) q
      ((PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) : Set (PrimeSpectrum (Polynomial k))))
      (PrimeSpectrum.basicOpen _).isOpen.isLocallyClosed ?_ ?_ ?_
    · refine IsOpen.dense (X := PrimeSpectrum (Polynomial k)) (PrimeSpectrum.basicOpen _).isOpen
        ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
      simp [PrimeSpectrum.mem_basicOpen, Polynomial.X_ne_zero]
    · intro x hx hcl
      have hp := pointOfClosedPoint_comp (f ≫ q) x hcl
      have hpx := pointOfClosedPoint_apply (f ≫ q) x hcl (IsLocalRing.closedPoint k)
      generalize pointOfClosedPoint (f ≫ q) x hcl = p at hp hpx
      rw [hq] at hp
      obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = p := ⟨Spec.preimage p, Spec.map_preimage p⟩
      have hφ : φ.hom.comp (algebraMap k (Polynomial k)) = RingHom.id k := by
        have := Spec.map_injective (show Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)) ≫ φ)
          = Spec.map (𝟙 _) by rw [Spec.map_comp, Spec.map_id]; exact hp)
        simpa using congrArg CommRingCat.Hom.hom this
      have hev : φ = CommRingCat.ofHom (Polynomial.evalRingHom (φ.hom Polynomial.X)) := by
        apply CommRingCat.hom_ext
        apply Polynomial.ringHom_ext
        · intro a
          rw [Polynomial.algebraMap_eq] at hφ
          simpa using RingHom.congr_fun hφ a
        · simp
      have hc0 : φ.hom Polynomial.X ≠ 0 := by
        intro h0
        rw [← hpx] at hx
        apply (PrimeSpectrum.mem_basicOpen _ _).1 hx
        show φ.hom Polynomial.X ∈ IsLocalRing.maximalIdeal k
        rw [h0]; exact zero_mem _
      have e : Spec.map φ ≫ f = Spec.map φ ≫ f' := by
        rw [hf', reassoc_of% hp, hev]
        exact hc _ hc0
      rw [← hpx]
      exact congrArg (fun g : Sp k ⟶ Y => g (IsLocalRing.closedPoint k)) e
    · rw [hf', Category.assoc, Category.assoc, hq, hs1, Category.comp_id]
  have ha : ∀ a : Polynomial k →ₐ[k] k,
      spMap a.toRingHom ≫ f = spMap (Polynomial.evalRingHom (1 : k)) ≫ f := by
    intro a
    have hsa : spMap a.toRingHom ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _ :=
      spMap_section _ (by
        ext x; have := a.commutes x; rw [Polynomial.algebraMap_eq] at this; simpa using this)
    conv_lhs => rw [key]
    rw [hf', reassoc_of% hsa]
  rw [ha a, ha b]

end GlobalTheory.ConstAffineLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchSchwartzL2BoundedIntertwinerContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

theorem realcont : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (L : ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)))
    (A : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ) (C : ℝ≥0∞), C ≠ ⊤ →
      (∀ f, ∫⁻ z, ‖A f z‖ₑ ^ 2 ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2) →
      (∀ v (f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ), ⇑f' = GlobalTheory.WeilAdm.schrInf D.host.F ψ v ⇑f →
        ⇑(A f') = GlobalTheory.WeilAdm.schrInf D.host.F ψ (L v) ⇑(A f)) →
      Continuous A := by
  intro D ps hψ κ _ L A C hC hA hI
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨β, hβ1, hβ2⟩ := _root_.GlobalTheory.StdCharLin.stdChar_mixed_linear D ps θ hψ hθ
  have hnd : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0 := by
    intro a ha
    have ha' : (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a ≠ 0 := by
      intro h
      apply ha
      calc
        a = (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a) :=
          ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).apply_symm_apply a).symm
        _ = (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F) 0 := congrArg _ h
        _ = 0 := map_zero _
    obtain ⟨b, hb⟩ := _root_.GlobalTheory.InfTraceNondeg.realTrace_nondeg D θ hθ _ ha'
    refine ⟨InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F b, ?_⟩
    rw [hβ2, map_mul, RingEquiv.symm_apply_apply]
    simpa using hb
  obtain ⟨n, Q, P, hQP⟩ := _root_.GlobalTheory.WeilAdm.RealModel.exists_model D.host.F ps β hβ1 hnd κ
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.lintegral_sq_comp_linearEquiv_mixed D.host.F κ n Q
  let CQ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q
  let CQi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q.symm
  have hCQ : ∀ f, ⇑(CQ f) = ⇑f ∘ ⇑Q := fun f => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q f
  have hCQi : ∀ g, ⇑(CQi g) = ⇑g ∘ ⇑Q.symm := fun g => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q.symm g
  have hQQ : ∀ f, CQi (CQ f) = f := fun f => by
    ext z; rw [hCQi, hCQ]; simp
  have hQQ' : ∀ g, CQ (CQi g) = g := fun g => by
    ext z; rw [hCQ, hCQi]; simp
  let A' : GlobalTheory.RealWeil.Sch (Fin n) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin n) := CQ.toLinearMap ∘ₗ A ∘ₗ CQi.toLinearMap
  have hA'apply : ∀ g, A' g = CQ (A (CQi g)) := fun g => rfl
  let L' : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) := P.trans (L.trans P.symm)
  have hbound : ∀ g, ∫⁻ x, ‖A' g x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
    intro g
    have e1 : ∫⁻ x, ‖A' g x‖ₑ ^ 2 = c * ∫⁻ z, ‖A (CQi g) z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hA'apply, hCQ, Function.comp_apply]
    have e2 : ∫⁻ x, ‖g x‖ₑ ^ 2 = c * ∫⁻ z, ‖CQi g z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hCQi, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [e1, e2, ← mul_assoc, mul_comm C c, mul_assoc]
    exact mul_le_mul' le_rfl (hA _)
  have hint : ∀ w (g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑g →
      ⇑(A' g') = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' g) := by
    intro w g g' hg
    have h1 : ⇑(CQi g') = schrInf D.host.F ps (P w) ⇑(CQi g) := by
      have := congrArg (fun u => u ∘ ⇑Q.symm) (hQP w ⇑(CQi g))
      simp only [Function.comp_assoc, ContinuousLinearEquiv.self_comp_symm, Function.comp_id] at this
      rw [this, hCQi, hg, ← hCQ, hQQ']
    have h2 := hI (P w) (CQi g) (CQi g') h1
    have hL' : P (L' w) = L (P w) := P.apply_symm_apply _
    have h3 : ⇑(A (CQi g')) = schrInf D.host.F ps (P (L' w)) ⇑(A (CQi g)) := by
      rw [h2]
      exact congrArg (fun v => schrInf D.host.F ps v ⇑(A (CQi g))) hL'.symm
    calc ⇑(A' g') = ⇑(A (CQi g')) ∘ ⇑Q := hCQ _
      _ = schrInf D.host.F ps (P (L' w)) ⇑(A (CQi g)) ∘ ⇑Q := congrArg (· ∘ ⇑Q) h3
      _ = GlobalTheory.RealWeil.rhoFun (L' w) (⇑(A (CQi g)) ∘ ⇑Q) := hQP _ _
      _ = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' g) := congrArg (GlobalTheory.RealWeil.rhoFun (L' w)) (hCQ _).symm
  have hcont : Continuous A' :=
    _root_.GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound (Fin n) L' A' C hC hbound (_root_.GlobalTheory.RealWeil.DRhoTransfer.dRho_intertwine (Fin n) L'.toLinearMap A' C hC hbound hint)
  have hAeq : ⇑A = fun f => CQi (A' (CQ f)) := by
    funext f
    rw [hA'apply, hQQ, hQQ]
  rw [hAeq]
  exact CQi.continuous.comp (hcont.comp CQ.continuous)

end GlobalTheory.WeilAdm
end
end

