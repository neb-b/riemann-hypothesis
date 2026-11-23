module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GroupActionHaarScalingContinuous
section
open CategoryTheory Limits
open scoped TensorProduct

namespace GlobalTheory.IndEtaleComp

theorem isIndEtale_of_model (X E Y G F : Type) [CommRing X] [CommRing E] [CommRing Y] [CommRing G]
    [CommRing F] [Algebra X E] [Algebra X Y] [Algebra E Y] [IsScalarTower X E Y]
    [Algebra.Etale X E] [Algebra E G] [Algebra.Etale E G] [Algebra Y F]
    (e : Y ⊗[E] G ≃ₐ[Y] F) (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap X Y)) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale ((algebraMap Y F).comp (algebraMap X Y)) := by
  have h1 := GlobalTheory.IndEtaleCancel.isIndEtale_of_etale_of_isIndEtale X E Y h
  have h2 := GlobalTheory.isIndEtale_tensorProduct_left E Y G h1
  letI : Algebra G F :=
    ((e : Y ⊗[E] G →+* F).comp (Algebra.TensorProduct.includeRight : G →ₐ[E] Y ⊗[E] G).toRingHom).toAlgebra
  let e' : G ⊗[E] Y ≃ₐ[G] F :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm E G Y).toRingEquiv.trans e.toRingEquiv)
      (fun g => rfl)
  have h3 := GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e' h2
  have h4 : RingHom.Etale ((algebraMap E G).comp (algebraMap X E)) :=
    RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.2 inferInstance)
      (RingHom.etale_algebraMap.2 inferInstance)
  have h5 := GlobalTheory.EtC.isIndEtale_comp_etale _ h4 _ h3
  have h6 : (algebraMap Y F).comp (algebraMap X Y) =
      (algebraMap G F).comp ((algebraMap E G).comp (algebraMap X E)) := by
    ext x
    change _ = e ((1 : Y) ⊗ₜ[E] algebraMap E G (algebraMap X E x))
    rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply E Y (Y ⊗[E] G),
      e.commutes, ← IsScalarTower.algebraMap_apply X E Y]
    rfl
  rw [h6]
  exact h5

theorem isIndEtale_etale_comp {X Y F : Type} [CommRing X] [CommRing Y] [CommRing F]
    (f : X →+* Y) (g : Y →+* F) (hf : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale f) (hg : g.Etale) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp f) := by
  have hf' := hf
  obtain ⟨J, _, _, D, s, t, hs, hj⟩ := hf'
  letI : Algebra Y F := g.toAlgebra
  haveI : Algebra.Etale Y F := hg
  obtain ⟨i, G, _, _, hG, ⟨e⟩⟩ :=
    GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit J D (Cocone.mk (CommRingCat.of Y) t) hs F
  letI : Algebra (D.obj i) Y := (t.app i).hom.toAlgebra
  letI : Algebra X (D.obj i) := (s.app i).hom.toAlgebra
  letI : Algebra X Y := f.toAlgebra
  haveI : Algebra.Etale X (D.obj i) := (hj i).1
  haveI : IsScalarTower X (D.obj i) Y := IsScalarTower.of_algebraMap_eq (fun x =>
    (congrArg (fun φ : CommRingCat.of X ⟶ CommRingCat.of Y => φ.hom x) (hj i).2).symm)
  exact isIndEtale_of_model X (D.obj i) Y G F e hf

theorem isIndEtale_comp : ∀ (X Y Z : Type) [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale f → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale g → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp f) := by
  intro X Y Z _ _ _ f g hf hg
  have hp : RingHom.toMorphismProperty @RingHom.Etale ≤
      MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} := by
    intro X Y f hf
    refine CommRingCat.isFinitelyPresentable_hom f ?_
    letI := f.hom.toAlgebra
    haveI : Algebra.Etale X Y := hf
    exact RingHom.finitePresentation_algebraMap.2 inferInstance
  obtain ⟨J, _, _, D, s, t, hs, hj⟩ := hg
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
  rw [← MorphismProperty.ind_ind hp]
  refine ⟨J, inferInstance, inferInstance, D, (Functor.const J).map (CommRingCat.ofHom f) ≫ s, t, hs,
    fun j => ⟨?_, ?_⟩⟩
  · exact isIndEtale_etale_comp (F := D.obj j) f (s.app j).hom hf (hj j).1
  · have h2 := (hj j).2
    show CommRingCat.ofHom f ≫ s.app j ≫ t.app j = CommRingCat.ofHom (g.comp f)
    rw [h2]
    rfl

end GlobalTheory.IndEtaleComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfEtaleOfIsIndEtale
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC IsLocalRing

namespace GlobalTheory.StalkNoeth

theorem noeth_of_directed_subrings : ∀ (S : Type) [CommRing S] [IsLocalRing S] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S), Monotone R → (∀ x : S, ∃ i, x ∈ R i) → (∀ i, IsNoetherianRing (R i)) → (∀ i, ((maximalIdeal S).comap (R i).subtype).map (R i).subtype = maximalIdeal S) → (∀ i (J : Ideal (R i)), (J.map (R i).subtype).comap (R i).subtype = J) → IsNoetherianRing S :=
  GlobalTheory.T.isNoetherianRing_of_directed_pure_union'

theorem isIndEtale_of_etale_of_isIndEtale : ∀ (A W O : Type) [CommRing A] [CommRing W] [CommRing O] [Algebra A W] [Algebra A O] [Algebra W O] [IsScalarTower A W O] [Algebra.Etale A W], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O) → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) :=
  GlobalTheory.T.isIndEtale_over_etale_of_isIndEtale

noncomputable def stageHom {A W O : Type} [CommRing A] [CommRing W] [CommRing O] [IsLocalRing O] [Algebra A W] [Algebra A O]
    (v : W →ₐ[A] O) : Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O)) →+* O :=
  IsLocalization.lift (M := ((maximalIdeal O).comap (v : W →+* O)).primeCompl) (g := (v : W →+* O))
    (fun y => by by_contra hy; exact y.2 hy)

theorem stageHom_algebraMap {A W O : Type} [CommRing A] [CommRing W] [CommRing O] [IsLocalRing O] [Algebra A W] [Algebra A O]
    (v : W →ₐ[A] O) (w : W) : stageHom v (algebraMap W _ w) = v w :=
  IsLocalization.lift_eq _ _

theorem stage_props {A W O : Type} [CommRing A] [CommRing W] [CommRing O] [IsLocalRing O] [Algebra A W] [Algebra A O]
    [Algebra.Etale A W] (hO : IndEt A O) (v : W →ₐ[A] O) :
    (∀ J : Ideal (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))), (J.map (stageHom v)).comap (stageHom v) = J) ∧
      (maximalIdeal (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O)))).map (stageHom v) = maximalIdeal O := by
  set q := (maximalIdeal O).comap (v : W →+* O) with hq
  letI : Algebra W O := (v : W →+* O).toAlgebra
  haveI : IsScalarTower A W O := IsScalarTower.of_algebraMap_eq (fun a => (v.commutes a).symm)
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) := isIndEtale_of_etale_of_isIndEtale A W O hO
  letI : Algebra (Localization.AtPrime q) O := (stageHom v).toAlgebra
  haveI : IsScalarTower W (Localization.AtPrime q) O :=
    IsScalarTower.of_algebraMap_eq (fun w => (stageHom_algebraMap v w).symm)
  have h2 : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Localization.AtPrime q) O) :=
    GlobalTheory.StrictHensUnion.indEtale_over_localization W (Localization.AtPrime q) O q.primeCompl h1
  haveI : IsLocalHom (algebraMap (Localization.AtPrime q) O) := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨⟨w, y⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl a
    rw [IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime q) q]
    have hu : IsUnit (v (y : W)) := by
      by_contra hy
      exact y.2 hy
    have h3 : algebraMap (Localization.AtPrime q) O (IsLocalization.mk' (Localization.AtPrime q) w y) * v y = v w := by
      rw [← stageHom_algebraMap v (y : W), ← stageHom_algebraMap v w]
      change stageHom v _ * stageHom v _ = stageHom v _
      rw [← map_mul, IsLocalization.mk'_spec]
    have h4 : IsUnit (v w) := h3 ▸ ha.mul hu
    intro hw
    exact hw h4
  obtain ⟨hfl, hmax, -⟩ := GlobalTheory.IndEtaleLocal.flat_map_maximalIdeal_isSeparable (Localization.AtPrime q) O h2
  haveI : Module.FaithfullyFlat (Localization.AtPrime q) O := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨fun J => Ideal.comap_map_eq_self_of_faithfullyFlat J, hmax⟩

theorem stage_le {A W W' O : Type} [CommRing A] [CommRing W] [CommRing W'] [CommRing O] [IsLocalRing O] [Algebra A W]
    [Algebra A W'] [Algebra A O] (v : W →ₐ[A] O) (v' : W' →ₐ[A] O) (k : W →ₐ[A] W') (hk : v'.comp k = v) :
    (stageHom v).range ≤ (stageHom v').range := by
  have hle : ((maximalIdeal O).comap (v : W →+* O)).primeCompl ≤
      ((maximalIdeal O).comap (v' : W' →+* O)).primeCompl.comap (k : W →+* W') := by
    intro y hy
    change v' (k y) ∉ maximalIdeal O
    rw [← AlgHom.comp_apply, hk]
    exact hy
  let ψ := IsLocalization.map (S := Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) (Localization.AtPrime ((maximalIdeal O).comap (v' : W' →+* O))) (k : W →+* W') hle
  have hψ : (stageHom v').comp ψ = stageHom v := by
    refine IsLocalization.ringHom_ext (S := Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) ((maximalIdeal O).comap (v : W →+* O)).primeCompl ?_
    ext w
    simp only [RingHom.comp_apply, ψ, IsLocalization.map_eq, stageHom_algebraMap]
    rw [← hk]
    rfl
  rw [← hψ]
  rintro _ ⟨x, rfl⟩
  exact ⟨ψ x, rfl⟩

theorem isNoetherianRing_of_indEt : ∀ (A O : Type) [CommRing A] [IsNoetherianRing A] [CommRing O] [IsLocalRing O]
    [Algebra A O], IndEt A O → IsNoetherianRing O := by
  intro A O _ _ _ _ _ hO
  let ι := {T : Subring O // ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W) (v : W →ₐ[A] O),
    T = (stageHom v).range}
  have fac : ∀ (Z : Type) [CommRing Z] [Algebra A Z] [Algebra.FinitePresentation A Z] (g : Z →ₐ[A] O),
      ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W) (u : Z →ₐ[A] W) (v : W →ₐ[A] O),
        v.comp u = g := fun Z _ _ _ g => GlobalTheory.IndEtaleLocal.exists_etale_factor hO g
  have mem : ∀ x : O, ∃ T : ι, x ∈ T.1 := by
    intro x
    obtain ⟨W, _, _, _, u, v, huv⟩ := fac (Polynomial A) (Polynomial.aeval x)
    refine ⟨⟨_, W, inferInstance, inferInstance, inferInstance, v, rfl⟩, algebraMap W _ (u Polynomial.X), ?_⟩
    rw [stageHom_algebraMap]
    have := DFunLike.congr_fun huv Polynomial.X
    simpa using this
  haveI : Nonempty ι := ⟨(mem 0).choose⟩
  haveI : IsDirected ι (· ≤ ·) := by
    refine ⟨fun T1 T2 => ?_⟩
    obtain ⟨T1, W1, _, _, _, v1, rfl⟩ := T1
    obtain ⟨T2, W2, _, _, _, v2, rfl⟩ := T2
    haveI : Algebra.FinitePresentation A (TensorProduct A W1 W2) := Algebra.FinitePresentation.trans A W1 _
    obtain ⟨W3, _, _, _, u, v3, huv⟩ := fac (TensorProduct A W1 W2) (Algebra.TensorProduct.productMap v1 v2)
    refine ⟨⟨_, W3, inferInstance, inferInstance, inferInstance, v3, rfl⟩, ?_, ?_⟩
    · exact stage_le v1 v3 (u.comp Algebra.TensorProduct.includeLeft) (by
        rw [← AlgHom.comp_assoc, huv]; exact Algebra.TensorProduct.productMap_left v1 v2)
    · exact stage_le v2 v3 (u.comp Algebra.TensorProduct.includeRight) (by
        rw [← AlgHom.comp_assoc, huv]; exact Algebra.TensorProduct.productMap_right v1 v2)
  refine noeth_of_directed_subrings O ι (fun T => T.1) (fun _ _ h => h) mem ?_ ?_ ?_
  · rintro ⟨T, W, _, _, _, v, rfl⟩
    haveI : IsNoetherianRing W := Algebra.FiniteType.isNoetherianRing A W
    haveI : IsNoetherianRing (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) :=
      IsLocalization.isNoetherianRing ((maximalIdeal O).comap (v : W →+* O)).primeCompl _ inferInstance
    exact isNoetherianRing_range (stageHom v)
  · rintro ⟨T, W, _, _, _, v, rfl⟩
    obtain ⟨-, hmax⟩ := stage_props hO v
    refine le_antisymm Ideal.map_comap_le ?_
    conv_lhs => rw [← hmax]
    rw [Ideal.map_le_iff_le_comap]
    intro l hl
    have h1 : stageHom v l ∈ maximalIdeal O := hmax.le (Ideal.mem_map_of_mem _ hl)
    have h2 : (⟨stageHom v l, l, rfl⟩ : (stageHom v).range) ∈ (maximalIdeal O).comap (stageHom v).range.subtype := h1
    exact Ideal.mem_map_of_mem _ h2
  · rintro ⟨T, W, _, _, _, v, rfl⟩ J
    obtain ⟨hc, -⟩ := stage_props hO v
    refine le_antisymm ?_ Ideal.le_comap_map
    intro x hx
    obtain ⟨y, rfl⟩ := (stageHom v).rangeRestrict_surjective x
    have hJ : J = (J.comap (stageHom v).rangeRestrict).map (stageHom v).rangeRestrict :=
      (Ideal.map_comap_of_surjective _ (stageHom v).rangeRestrict_surjective J).symm
    have h2 : stageHom v y ∈ (J.comap (stageHom v).rangeRestrict).map (stageHom v) := by
      rw [hJ, Ideal.map_map] at hx
      exact hx
    have h3 := (hc (J.comap (stageHom v).rangeRestrict)).le h2
    exact h3

theorem isNoetherianRing_of_isStalk : ∀ (B : Type) [CommRing B] [Algebra.FiniteType ℤ B] (O : Type) [CommRing O]
    [IsLocalRing O] (s : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of B)), IsStalk O s → IsNoetherianRing O := by
  intro B _ _ O _ _ s hs
  obtain ⟨_, -, hind, -⟩ := isStalk_affine B O s hs
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  exact isNoetherianRing_of_indEt B O hind

end GlobalTheory.StalkNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemEtaleTopologyOfPullbackFiniteEtale
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem mem_etaleTopology_of_pullback_finite : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (T : Sieve X), T.pullback f ∈ Scheme.etaleTopology Z → (∀ {V : Scheme.{0}} (v : V ⟶ X), IsEmpty (pullback f v : Scheme.{0}) → T v) → T ∈ Scheme.etaleTopology X := by
  intro Z X f _ _ T hT hE
  let U : X.Opens := ⟨(Set.range f.base)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩
  have hU : IsEmpty (pullback f U.ι : Scheme.{0}) := by
    refine ⟨fun p => ?_⟩
    have h1 : (pullback.snd f U.ι ≫ U.ι).base p = (pullback.fst f U.ι ≫ f).base p := by
      rw [pullback.condition]
    have h2 : (pullback.snd f U.ι ≫ U.ι).base p ∈ U := by
      rw [Scheme.Hom.comp_base, TopCat.comp_app]
      have hr := U.range_ι
      exact (Set.ext_iff.1 hr _).1 ⟨_, rfl⟩
    rw [h1, Scheme.Hom.comp_base, TopCat.comp_app] at h2
    exact h2 ⟨_, rfl⟩
  have hTU : T U.ι := hE U.ι hU
  let V : Bool → Scheme.{0} := fun b => Bool.rec U.toScheme Z b
  let j : ∀ b, V b ⟶ X := fun b => match b with
    | true => f
    | false => U.ι
  have hmem : Presieve.ofArrows V j ∈ Scheme.etalePrecoverage X := by
    refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun b => ?_⟩
    · by_cases hx : x ∈ Set.range f.base
      · obtain ⟨z, rfl⟩ := hx
        exact ⟨true, z, rfl⟩
      · exact ⟨false, ⟨x, hx⟩, rfl⟩
    · cases b
      · change Etale U.ι
        infer_instance
      · change Etale f
        infer_instance
  refine Scheme.etaleTopology.transitive (Precoverage.generate_mem_toGrothendieck hmem) _ ?_
  rintro W g ⟨Y, h, k, ⟨b⟩, rfl⟩
  rw [Sieve.pullback_comp]
  refine Scheme.etaleTopology.pullback_stable h ?_
  cases b
  · change T.pullback U.ι ∈ _
    rw [Sieve.pullback_eq_top_of_mem _ hTU]
    exact Scheme.etaleTopology.top_mem _
  · exact hT

end GlobalTheory.EtC.Tr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeParametersBoundedLatticeEigenfunction
section
noncomputable section

namespace GlobalTheory.SatakeBound

open GlobalTheory.LatHecke

theorem esymm_map_mul (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (fun x => c * x)).esymm k = c ^ k * s.esymm k := by
  rw [Multiset.esymm, Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map,
    ← Multiset.sum_map_mul_left]
  congr 1
  apply Multiset.map_congr rfl
  intro t ht
  rw [Multiset.mem_powersetCard] at ht
  rw [Function.comp_apply]
  have := Multiset.prod_map_mul (m := t) (f := fun _ => c) (g := fun x => x)
  rw [this, Multiset.map_const', Multiset.prod_replicate, Multiset.map_id', ht.2]

noncomputable def recSeq (s : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => -∑ k ∈ Finset.range (n + 1), s (k + 1) * recSeq s (n - k)
decreasing_by all_goals omega

theorem cast_tri (k : ℕ) : (((k * (k - 1) / 2 : ℕ)) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  rcases k with _ | j
  · simp
  · have h2 : 2 ∣ (j + 1) * j := by rw [mul_comm]; exact (Nat.even_mul_succ_self j).two_dvd
    rw [Nat.add_sub_cancel, Nat.cast_div h2 (by norm_num)]
    push_cast; ring

theorem main : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : Lat O K r → E) (α : Multiset ℂ)
    (C : ℝ), α.card = r → φ ≠ 0 → (∀ L, ‖φ L‖ ≤ C) →
    (∀ k ≤ r, ∀ L, heckeElem k φ L =
      ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • φ L) →
    ∀ a ∈ α, ‖a‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  intro O K _ _ _ _ _ _ _ r E _ _ φ α C hcard hφ hC hT x hx
  have hq1 : (1 : ℝ) < (qRes O : ℝ) := by exact_mod_cast one_lt_qRes (O := O)
  have hq0 : (0 : ℝ) < (qRes O : ℝ) := by linarith
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [Multiset.card_eq_zero] at hcard
    subst hcard
    simp at hx
  obtain ⟨L0, hL0⟩ : ∃ L0, φ L0 ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    exact hφ (funext h)

  set d : ℕ → ℂ := fun k => if k ≤ r then
    (((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k else 0 with hd_def
  have hd : ∀ k L, heckeElem k φ L = d k • φ L := by
    intro k L
    by_cases hk : k ≤ r
    · rw [hT k hk L, hd_def]; simp only [hk, if_true]
    · rw [heckeElem_eq_zero (by omega), hd_def]; simp only [hk, if_false, zero_smul]
  have hlin : ∀ (c : ℂ) k L, heckeElem k (fun M => c • φ M) L = (c * d k) • φ L := by
    intro c k L
    rw [heckeElem_eq_sum, ← Finset.smul_sum, ← heckeElem_eq_sum, hd, smul_smul]
  set s : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * d k with hs_def
  set a : ℕ → ℂ := recSeq s with ha_def

  have hA : ∀ n, heckeAll n φ = fun L => a n • φ L := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    rcases n with _ | m
    · funext L
      rw [heckeAll_zero, ha_def, recSeq, one_smul]
    · funext L
      have hid := _root_.GlobalTheory.HeckeSeries.heckeSeries_identity O K r E φ (m + 1) L (by omega)
      rw [Finset.sum_range_succ'] at hid
      have key : ∀ k ∈ Finset.range (m + 1),
          ((-1 : ℂ) ^ (k + 1) * (qRes O : ℂ) ^ ((k + 1) * (k + 1 - 1) / 2)) •
            heckeElem (k + 1) (heckeAll (m + 1 - (k + 1)) φ) L = (s (k + 1) * a (m - k)) • φ L := by
        intro k hk
        rw [show m + 1 - (k + 1) = m - k by omega, ih (m - k) (by omega), hlin, smul_smul]
        congr 1
        rw [hs_def]
        ring
      have h0 : ((-1 : ℂ) ^ 0 * (qRes O : ℂ) ^ (0 * (0 - 1) / 2)) = 1 := by simp
      rw [Finset.sum_congr rfl key, h0, one_smul, heckeElem_zero, ← Finset.sum_smul] at hid
      show heckeAll (m + 1) φ L = recSeq s (m + 1) • φ L
      rw [recSeq, neg_smul]
      exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hid)

  set c : ℝ := (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) with hc_def
  have hc0 : 0 < c := Real.rpow_pos_of_pos hq0 _
  set β : Multiset ℂ := α.map (fun y => (c : ℂ) * y) with hβ_def
  have hβs : ∀ k, (-1 : ℂ) ^ k * β.esymm k = s k := by
    intro k
    rw [hβ_def, esymm_map_mul, hs_def, hd_def]
    by_cases hk : k ≤ r
    · simp only [hk, if_true]
      have hreal : c ^ k = (qRes O : ℝ) ^ (k * (k - 1) / 2) *
          (qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) := by
        rw [hc_def, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast (qRes O : ℝ),
          ← Real.rpow_add hq0, cast_tri]
        congr 1
        ring
      have hcomp : (c : ℂ) ^ k = (qRes O : ℂ) ^ (k * (k - 1) / 2) *
          (((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_pow, hreal, Complex.ofReal_mul, Complex.ofReal_pow,
          Complex.ofReal_natCast]
      rw [hcomp]
      ring
    · simp only [hk, if_false, mul_zero]
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [hcard]; omega)]
      simp
  have hrel : ∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [hβs]
    rw [Finset.sum_range_succ']
    have hs0 : s 0 = 1 := by
      rw [hs_def, hd_def]; simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    have ha1 : a (m + 1 - 0) = -∑ k ∈ Finset.range (m + 1), s (k + 1) * a (m - k) := by
      rw [Nat.sub_zero, ha_def, recSeq]
    rw [hs0, ha1]
    have : ∀ k ∈ Finset.range (m + 1), s (k + 1) * a (m + 1 - (k + 1)) = s (k + 1) * a (m - k) := by
      intro k _; rw [show m + 1 - (k + 1) = m - k by omega]
    rw [Finset.sum_congr rfl this]
    ring

  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC L0)
  have hnL0 : 0 < ‖φ L0‖ := norm_pos_iff.mpr hL0
  have hbound : ∀ n, ‖a n‖ ≤ (C / ‖φ L0‖) * ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n := by
    intro n
    have h1 : ‖a n‖ * ‖φ L0‖ = ‖heckeAll n φ L0‖ := by
      rw [hA n, norm_smul]
    have h2 : ‖heckeAll n φ L0‖ ≤ (subIdx n L0).ncard * C := by
      rw [heckeAll_eq_sum, Set.ncard_eq_toFinset_card _ (subIdx_finite n L0)]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun M _ => hC M).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 := _root_.GlobalTheory.SubIdxCount.ncard_subIdx_le O K r n L0
    rw [show C / ‖φ L0‖ * ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n =
        C * (((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n) / ‖φ L0‖ by ring,
      le_div_iff₀ hnL0, h1]
    calc ‖heckeAll n φ L0‖ ≤ (subIdx n L0).ncard * C := h2
      _ ≤ (((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n) * C :=
          mul_le_mul_of_nonneg_right h3 hC0
      _ = C * (((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n) := by ring
  have hB : 0 < (qRes O : ℝ) ^ (r - 1) := pow_pos hq0 _
  have hrec := _root_.GlobalTheory.norm_le_of_recurrence_growth β a (C / ‖φ L0‖) ((qRes O : ℝ) ^ (r - 1)) r hB
    (by rw [ha_def, recSeq]) hrel hbound
  have hxb := hrec ((c : ℂ) * x) (Multiset.mem_map_of_mem _ hx)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le] at hxb
  have hcc : (qRes O : ℝ) ^ (r - 1) = c * c := by
    rw [hc_def, ← Real.rpow_add hq0, ← Real.rpow_natCast, Nat.cast_sub hr]
    congr 1
    push_cast
    ring
  rw [hcc] at hxb
  exact le_of_mul_le_mul_left hxb hc0

end GlobalTheory.SatakeBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitByBaseChangeStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitBy_baseChange' : ∀ {Z X V T : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ} {s : Fin m → (V ⟶ Z)}, GlobalTheory.EtC.Tr.SplitBy f y s → ∀ (w : T ⟶ V), GlobalTheory.EtC.Tr.SplitBy f (w ≫ y) (fun j => w ≫ s j) := by
  first | (exact @GlobalTheory.EtC.Tr.splitBy_baseChange) | (exact GlobalTheory.EtC.Tr.splitBy_baseChange) | (intros; apply GlobalTheory.EtC.Tr.splitBy_baseChange  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfIsEmptyPullback
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splits_of_isEmpty_pullback : ∀ {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X),
    IsEmpty (pullback f y : Scheme.{0}) → GlobalTheory.EtC.Tr.Splits f y := by
  intro Z X V f y hE
  have hP : IsInitial (pullback f y) := isInitialOfIsEmpty
  refine ⟨0, Fin.elim0, fun j => j.elim0, ?_⟩
  refine ⟨⟨hP.to _, ?_, hP.hom_ext _ _⟩⟩
  apply Sigma.hom_ext
  intro j
  exact j.elim0

end GlobalTheory.EtC.Tr
end

