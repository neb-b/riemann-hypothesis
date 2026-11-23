module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.AmpleDominates

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {X : Scheme.{0}} {M N : LB X}

theorem eventually_isGenerated {R : Type} [CommRing R] (f : X ⟶ Sp R) [IsProper f] (hM : IsAmpleLB M)
    (hN : N.IsLB) : ∀ᶠ t : ℕ in Filter.atTop, IsGenerated (LB.div (lbPow M t) N) := by
  obtain ⟨d, hd, m, s, hs⟩ := hM.exists_veryAmpleBy f
  have hH := isLB_lbPow hM.isLB d
  have hD : ∀ i, (LB.div (lbPow M i) N).IsLB := fun i => LB.isLB_div (isLB_lbPow hM.isLB i) hN
  choose t₀ ht₀ using fun i => TwistGen.twist_generated R X f _ m s hH hs _ (hD i)
  refine Filter.eventually_atTop.2 ⟨d * (Finset.range d).sup fun i => (t₀ i).toNat, fun t ht => ?_⟩
  have h₁ : (t₀ (t % d)).toNat ≤ t / d :=
    (Finset.le_sup (f := fun i => (t₀ i).toNat) (Finset.mem_range.2 (Nat.mod_lt t hd))).trans
      ((Nat.le_div_iff_mul_le hd).2 (by rwa [Nat.mul_comm]))
  obtain ⟨n, u, hu⟩ := ht₀ (t % d) (t / d : ℕ) (Int.toNat_le.1 h₁)
  have hG : IsGenerated (tw (LB.div (lbPow M (t % d)) N) (lbPow M d) (t / d : ℕ)) := ⟨_, u, hu⟩
  refine hG.of_lbIso (hD t) ((cls_eq_iff (hD t) hG.isLB).1 ?_)
  have e : cls _ hG.isLB = cls _ (hD (t % d)) - cls _ (isLB_pw hH (-((t / d : ℕ) : ℤ))) :=
    cls_div (hD _) (isLB_pw hH _) _
  rw [e, AmpleStabFinite.cls_pw hH, cls_div (isLB_lbPow hM.isLB t) hN, cls_div (isLB_lbPow hM.isLB _) hN,
    cls_lbPow hM.isLB, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  generalize cls M hM.isLB = a
  generalize cls N hN = b
  conv_lhs => rw [← Nat.mod_add_div t d]
  simp only [add_nsmul, mul_nsmul, neg_zsmul, natCast_zsmul]
  abel

theorem eventually_isAmpleLB {R : Type} [CommRing R] (f : X ⟶ Sp R) [IsProper f] (hM : IsAmpleLB M)
    (hN : N.IsLB) : ∀ᶠ t : ℕ in Filter.atTop, IsAmpleLB (LB.div (lbPow M t) N) := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 (eventually_isGenerated f hM hN)
  refine Filter.eventually_atTop.2 ⟨a + 1, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hG := ha k (by omega)
  have h₀ := LB.isLB_div (isLB_lbPow hM.isLB (k + 1)) hN
  have h₁ := LB.isLB_div h₀ hM.isLB
  refine hM.tensor_isGenerated hG h₀ ((cls_eq_zero_iff (LB.isLB_div h₁ hG.isLB)).1 ?_)
  rw [cls_div h₁ hG.isLB, cls_div h₀ hM.isLB, cls_div (isLB_lbPow hM.isLB _) hN,
    cls_div (isLB_lbPow hM.isLB _) hN, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  simp only [add_nsmul, one_nsmul]
  abel

theorem exists_sec_ne_zero [Nonempty X] {L : LB X} (h : IsGenerated L) : ∃ s : L.Sec, ∃ j, s.f j ≠ 0 := by
  obtain ⟨s, hs⟩ := h.exists_mem (Classical.arbitrary X)
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hs
  refine ⟨s, j, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hj
  exact hj

theorem eventually_sec_and_relAmple : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M N : LB P.A.left), M.IsLB → N.IsLB → Out.RelAmple P.A M → ∀ᶠ t : ℕ in Filter.atTop, (∃ s : (LB.div (lbPow M t) N).Sec, ∃ j, s.f j ≠ 0) ∧ Out.RelAmple P.A (LB.div (lbPow M t) N) := by
  intro K _ _ P M N hM hN h
  have := P.isAb.proper
  have := polAV_isIntegral_of_isAlgClosed K P
  have hA := isAmpleLB_of_relAmple_of_isAffine P.A hM h
  filter_upwards [eventually_isGenerated P.A.hom hA hN, eventually_isAmpleLB P.A.hom hA hN] with t h₁ h₂
  exact ⟨exists_sec_ne_zero h₁, (relAmple_iff_isAmpleLB_of_isAffine P.A h₂.isLB).2 h₂⟩

end GlobalTheory.AmpleDominates
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.LevelMap

theorem of_baseChange (P : MorphismProperty Scheme.{0})
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    {X₀ X₁ S₀ S₁ T : Scheme.{0}} (s₀ : X₀ ⟶ S₀) (s₁ : X₁ ⟶ S₁) (k : S₁ ⟶ S₀) (r : X₁ ⟶ X₀)
    (hr : r ≫ s₀ = s₁ ≫ k) (i₀ : T ⟶ S₀) (i₁ : T ⟶ S₁) (hi : i₁ ≫ k = i₀)
    [Surjective i₁] [Flat i₁] [QuasiCompact i₁]
    (rF : pullback s₁ i₁ ⟶ pullback s₀ i₀) (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r)
    (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _) (h : P rF) : P (pullback.lift r s₁ hr) := by
  subst hi
  let p : pullback s₀ (i₁ ≫ k) ⟶ pullback s₀ k :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i₁) (by simp [pullback.condition])
  have hp : IsPullback p (pullback.snd _ _) (pullback.snd s₀ k) i₁ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback s₀ k)
    have : p ≫ pullback.fst s₀ k = pullback.fst _ _ := pullback.lift_fst _ _ _
    rw [this]
    exact IsPullback.of_hasPullback _ _
  have hq : IsPullback (pullback.fst s₁ i₁) rF (pullback.lift r s₁ hr) p := by
    refine IsPullback.of_bot ?_ ?_ hp
    · rw [h₂, pullback.lift_snd]
      exact IsPullback.of_hasPullback _ _
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, h₁]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, reassoc_of% h₂, pullback.condition]
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := P)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hq.flip ⟨⟨?_, ?_⟩, ?_⟩ h
  · exact MorphismProperty.of_isPullback (P := @Surjective) hp.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hp.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip ‹_›

theorem isFinite_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsFinite : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := isAffineHom_descendsAlong_fpqc.{0}
  refine ⟨fun {A X Y Z fst snd f g} H hf hfst => ?_⟩
  have a2 : IsAffineHom g := MorphismProperty.of_isPullback_of_descendsAlong (P := @IsAffineHom) H hf inferInstance
  have a3 : UniversallyClosed g :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H hf inferInstance
  have a4 : LocallyOfFiniteType g :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) H hf inferInstance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩

theorem surjective_spMap {K L : Type} [Field K] [Field L] (k : K →+* L) : Surjective (spMap k) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨y⟩ : Nonempty (Sp L) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  exact ⟨y, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩

theorem flat_spMap {K L : Type} [Field K] [Field L] (k : K →+* L) : Flat (spMap k) := by
  rw [Flat.SpecMap_iff]
  algebraize [k]
  exact (inferInstance : Module.Flat K L)

theorem finite_etale_spMap {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [FiniteDimensional ℚ L]
    (k : K →+* L) : IsFinite (spMap k) ∧ Etale (spMap k) := by
  algebraize [k]
  have : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun x => by simp
  have hf : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  constructor
  · rw [IsFinite.SpecMap_iff]
    exact hf
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ : Algebra.Etale K L)

theorem exists_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H), l₀.Dvd l₁ → ∃ (k : KA l₀ →+* KA l₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (hr : r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k), IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ LevComp (Xo l₁).univ (Xo l₀).univ r ν ∧ IsFinite (pullback.lift r _ hr) ∧ Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) ∧ IsFinite r ∧ Etale r ∧ Surjective r := by
  intro E _ _ _ H D Xo hN l₀ l₁ hd
  obtain ⟨r, k, ν, hk, hr, h1, h2, -, hc⟩ := hN l₀ l₁ (Xo l₀) (Xo l₁) hd
  obtain ⟨c₁⟩ : Nonempty (Coeff l₁) := inferInstance
  have hle : KA l₀ ≤ c₁.F := fun x hx => by
    have := c₁.le (k ⟨x, hx⟩).2
    rwa [hk] at this
  let c₀ : Coeff l₀ :=
    { F := c₁.F
      fin := c₁.fin
      conj := c₁.conj
      zeta_mem := by
        obtain ⟨e, he⟩ := LevelExist.zeta_eq_pow_of_dvd (a := l₀.M') (LevelExist.M'_pos l₁)
          (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _)) (hd.2.2.trans (Nat.dvd_lcm_right _ _)) : l₀.M' ∣ l₁.M')
        rw [he]
        exact pow_mem c₁.zeta_mem e
      le := hle }
  obtain ⟨rF, e1, e2, f1, f2, f3, -⟩ := hc c₀ c₁ rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c₁.F)).toRingHom = 𝟙 (Sp c₁.F) := by
    rw [← Spec.map_id]
    rfl
  have e2' : rF ≫ pullback.snd _ _ = pullback.snd _ _ := e2.trans ((congrArg _ hid).trans (Category.comp_id _))
  have hi : spMap (IntermediateField.inclusion c₁.le).toRingHom ≫ spMap k =
      spMap (IntermediateField.inclusion c₀.le).toRingHom := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact hk x
  have := surjective_spMap (IntermediateField.inclusion c₁.le).toRingHom
  have := flat_spMap (IntermediateField.inclusion c₁.le).toRingHom
  have := isFinite_descendsAlong_fpqc
  have g1 : IsFinite (pullback.lift r _ hr) := of_baseChange @IsFinite _ _ _ r hr _ _ hi rF e1 e2' f1
  have g2 : Etale (pullback.lift r _ hr) := of_baseChange @Etale _ _ _ r hr _ _ hi rF e1 e2' f2
  have g3 : Surjective (pullback.lift r _ hr) := of_baseChange @Surjective _ _ _ r hr _ _ hi rF e1 e2' f3
  have := c₁.fin
  have : FiniteDimensional ℚ (KA l₁) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion c₁.le).toLinearMap
      (IntermediateField.inclusion c₁.le).injective
  obtain ⟨k1, k2⟩ := finite_etale_spMap k
  have k3 := surjective_spMap k
  have hfac : pullback.lift r _ hr ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  refine ⟨k, r, ν, hr, hk, ⟨h1, h2⟩, g1, g2, g3, ?_, ?_, ?_⟩
  all_goals
    rw [← hfac]
    infer_instance

end GlobalTheory.LevelMap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeometricPointRootOfUnityEqOneOfIsDominant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory

theorem exists_geometricPoint_rootOfUnity_eq_one_of_isDominant :
    ∀ (X U V : Scheme.{0}) (j : U ⟶ X) (v : V ⟶ X), IsDominant j → IsOpenImmersion v → ∀ (ζ : Γ(V, ⊤)) (N : ℕ), ζ ^ N = 1 → ∀ (k : Type) [Field k] (y : Sp k ⟶ V), (N : k) ≠ 0 → y.appTop.hom ζ = 1 → ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (u : Sp K ⟶ U) (z : Sp K ⟶ V), z ≫ v = u ≫ j ∧ z.appTop.hom ζ = 1 := by
  intro X U V j v hj hv ζ N hζ k _ y hN hy
  classical
  set s : Γ(V, ⊤) := ∑ i ∈ Finset.range N, ζ ^ i with hs
  have hmul : s * (ζ - 1) = 0 := by rw [hs, geom_sum_mul, hζ, sub_self]
  have hys : y.appTop.hom s = (N : Γ(Sp k, ⊤)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hs, map_sum, map_pow, hy]
  have hunit : IsUnit (y.appTop.hom s) := by
    rw [hys]
    have h1 : IsUnit (N : k) := isUnit_iff_ne_zero.mpr hN
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    rwa [map_natCast] at h2
  have hpre : y ⁻¹ᵁ V.basicOpen s = ⊤ := by
    rw [Scheme.preimage_basicOpen_top]
    exact (Sp k).basicOpen_of_isUnit hunit
  have hne : ((V.basicOpen s : V.Opens) : Set V).Nonempty := by
    obtain ⟨p⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
    refine ⟨y p, ?_⟩
    have : p ∈ y ⁻¹ᵁ V.basicOpen s := by rw [hpre]; trivial
    exact this
  have hopen : IsOpen (v '' ((V.basicOpen s : V.Opens) : Set V)) :=
    v.isOpenEmbedding.isOpenMap _ (V.basicOpen s).isOpen
  obtain ⟨u₀, z₀, hz₀, hzu⟩ := j.denseRange.exists_mem_open hopen (hne.image _)
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := v) (g := j) z₀ u₀ hzu
  let P := pullback v j
  let K : Type := AlgebraicClosure (P.residueField w)
  let q : Sp K ⟶ P := spMap (algebraMap (P.residueField w) K) ≫ P.fromSpecResidueField w
  have hq : ∀ p, q p = w := by
    intro p
    simp only [q, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  refine ⟨K, inferInstance, inferInstance, q ≫ pullback.snd v j, q ≫ pullback.fst v j, ?_, ?_⟩
  · simp only [Category.assoc, pullback.condition]
  · set z := q ≫ pullback.fst v j with hz
    have hzs : z.appTop.hom s ≠ 0 := by
      intro h0
      obtain ⟨p⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
      have hp : p ∈ z ⁻¹ᵁ V.basicOpen s := by
        change z p ∈ V.basicOpen s
        rw [hz, Scheme.Hom.comp_apply, hq, hw1]
        exact hz₀
      rw [Scheme.preimage_basicOpen_top] at hp
      have : (Sp K).basicOpen (z.appTop.hom s) = ⊥ := by
        rw [h0]; exact (Sp K).basicOpen_zero _
      have hp' : p ∈ (Sp K).basicOpen (z.appTop.hom s) := hp
      rw [this] at hp'
      exact hp'
    haveI : IsDomain Γ(Sp K, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain
    have h := congrArg z.appTop.hom hmul
    rw [map_mul, map_zero, map_sub, map_one] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hzs)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueTwo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.GroupGlue

theorem exists_scheme {X : Scheme.{0}} {U V : X.Opens} {G₁ : Over U.toScheme} {G₂ : Over V.toScheme}
    {G₀ : Over (U ⊓ V).toScheme} {φ₁ : G₀.left ⟶ G₁.left} {φ₂ : G₀.left ⟶ G₂.left}
    (h₁ : IsPullback φ₁ G₀.hom G₁.hom (X.homOfLE inf_le_left))
    (h₂ : IsPullback φ₂ G₀.hom G₂.hom (X.homOfLE inf_le_right)) :
    ∃ (G : Over X) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsPullback ψ₁ G₁.hom G.hom U.ι ∧
      IsPullback ψ₂ G₂.hom G.hom V.ι ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ := by
  have : IsOpenImmersion φ₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₁.flip inferInstance
  have : IsOpenImmersion φ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₂.flip inferInstance
  have : IsOpenImmersion (pushout.inl φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.left))
  have : IsOpenImmersion (pushout.inr φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.right))
  have hc : ∀ z : (pushout φ₁ φ₂ : Scheme.{0}),
      z ∈ Set.range (pushout.inl φ₁ φ₂) ∨ z ∈ Set.range (pushout.inr φ₁ φ₂) := by
    intro z
    obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span φ₁ φ₂) z
    rcases i with _ | _ | _
    · refine Or.inl ⟨φ₁ x, Eq.trans ?_ hx⟩
      exact congrArg (fun g => g x) (colimit.w (span φ₁ φ₂) WalkingSpan.Hom.fst)
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩
  let π : pushout φ₁ φ₂ ⟶ X := pushout.desc (G₁.hom ≫ U.ι) (G₂.hom ≫ V.ι) (by
    rw [h₁.w_assoc, h₂.w_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι])
  have p1 : pushout.inl φ₁ φ₂ ≫ π = G₁.hom ≫ U.ι := pushout.inl_desc _ _ _
  have p2 : pushout.inr φ₁ φ₂ ≫ π = G₂.hom ≫ V.ι := pushout.inr_desc _ _ _
  have e1 (x : G₁.left) : π (pushout.inl φ₁ φ₂ x) = U.ι (G₁.hom x) := congrArg (fun g => g x) p1
  have e2 (x : G₂.left) : π (pushout.inr φ₁ φ₂ x) = V.ι (G₂.hom x) := congrArg (fun g => g x) p2
  have e3 (w : G₀.left) : pushout.inl φ₁ φ₂ (φ₁ w) = pushout.inr φ₁ φ₂ (φ₂ w) :=
    congrArg (fun g => g w) (pushout.condition (f := φ₁) (g := φ₂))
  refine ⟨Over.mk π, pushout.inl φ₁ φ₂, pushout.inr φ₁ φ₂, (IsOpenImmersion.isPullback _ _ _ _ p1 ?_).flip,
    (IsOpenImmersion.isPullback _ _ _ _ p2 ?_).flip, pushout.condition⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · have hy' : y.1 = (G₂.hom x).1 := hy.trans (e2 x)
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₂ x ⟨y.1, y.2, hy' ▸ (G₂.hom x).2⟩
          (Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hy'.symm))
        exact ⟨φ₁ z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨G₁.hom y, (e1 y).symm⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · have hy' : y.1 = (G₁.hom x).1 := hy.trans (e1 x)
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₁ x ⟨y.1, hy' ▸ (G₁.hom x).2, y.2⟩
          (Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hy'.symm))
        exact ⟨φ₂ z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨G₂.hom y, (e2 y).symm⟩

theorem exists_inf {X S : Scheme.{0}} {U V : X.Opens} (u : S ⟶ U) (v : S ⟶ V) (h : u ≫ U.ι = v ≫ V.ι) :
    ∃ w : S ⟶ (U ⊓ V : X.Opens), w ≫ X.homOfLE inf_le_left = u ∧ w ≫ X.homOfLE inf_le_right = v := by
  have hr : Set.range (u ≫ U.ι) ⊆ Set.range (U ⊓ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨(u z).2, ?_⟩
    rw [h]
    exact (v z).2
  refine ⟨IsOpenImmersion.lift _ _ hr, ?_, ?_⟩
  · rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]
  · rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac, h]

theorem exists_glue_two : ∀ (O : Type) [CommRing O] (X : Scheme.{0}) (U V : X.Opens) (G₁ : Over U.toScheme) [GrpObj G₁] (G₂ : Over V.toScheme) [GrpObj G₂] (G₀ : Over (U ⊓ V).toScheme) [GrpObj G₀] (a₁ : OAct O G₁) (a₂ : OAct O G₂) (a₀ : OAct O G₀) (φ₁ : G₀.left ⟶ G₁.left) (φ₂ : G₀.left ⟶ G₂.left), U ⊔ V = ⊤ → IsSemiAbelian G₁ → IsSemiAbelian G₂ → IsGrpPullback G₀ G₁ (X.homOfLE inf_le_left) φ₁ → IsGrpPullback G₀ G₂ (X.homOfLE inf_le_right) φ₂ → (∀ x, (a₀.act x).left ≫ φ₁ = φ₁ ≫ (a₁.act x).left ∧ (a₀.act x).left ≫ φ₂ = φ₂ ≫ (a₂.act x).left) → ∃ (G : Over X) (_ : GrpObj G) (a : OAct O G) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback G₁ G U.ι ψ₁ ∧ IsGrpPullback G₂ G V.ι ψ₂ ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ ∧ ∀ x, (a₁.act x).left ≫ ψ₁ = ψ₁ ≫ (a.act x).left ∧ (a₂.act x).left ≫ ψ₂ = ψ₂ ≫ (a.act x).left := by
  intro O _ X U V G₁ i₁ G₂ i₂ G₀ _ a₁ a₂ a₀ φ₁ φ₂ hUV s₁ s₂ h₁ h₂ ha
  obtain ⟨G, ψ₁, ψ₂, p₁, p₂, hφ⟩ := exists_scheme h₁.1 h₂.1
  have m₁ : Mono ψ₁ := by
    have : IsOpenImmersion ψ₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₁.flip inferInstance
    infer_instance
  have m₂ : Mono ψ₂ := by
    have : IsOpenImmersion ψ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₂.flip inferInstance
    infer_instance
  have base : ∀ {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ →
      ∃ w : S ⟶ (U ⊓ V : X.Opens), w ≫ X.homOfLE inf_le_left = u ∧ w ≫ X.homOfLE inf_le_right = v := by
    intro S u v a b h
    have e₁ : a.left ≫ G₁.hom = u := Over.w a
    have e₂ : b.left ≫ G₂.hom = v := Over.w b
    refine exists_inf u v ?_
    rw [← e₁, ← e₂, Category.assoc, Category.assoc, ← p₁.w, ← p₂.w, reassoc_of% h]
  have common : ∀ {S : Scheme.{0}} (w : S ⟶ (U ⊓ V : X.Opens))
      (a : Over.mk (w ≫ X.homOfLE inf_le_left) ⟶ G₁) (b : Over.mk (w ≫ X.homOfLE inf_le_right) ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → ∃ c : Over.mk w ⟶ G₀, a.left = c.left ≫ φ₁ ∧ b.left = c.left ≫ φ₂ := by
    intro S w a b h
    refine ⟨Over.homMk (h₁.1.lift a.left w (Over.w a)) (h₁.1.lift_snd _ _ _), (h₁.1.lift_fst _ _ _).symm, ?_⟩
    rw [← cancel_mono ψ₂, ← h, Category.assoc, ← hφ]
    exact (h₁.1.lift_fst_assoc _ _ _ _).symm
  have cm : ∀ {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a a' : Over.mk u ⟶ G₁) (b b' : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → a'.left ≫ ψ₁ = b'.left ≫ ψ₂ → (a * a').left ≫ ψ₁ = (b * b').left ≫ ψ₂ := by
    intro S u v a a' b b' h h'
    obtain ⟨w, rfl, rfl⟩ := base a b h
    obtain ⟨c, c₁, c₂⟩ := common w a b h
    obtain ⟨c', c₁', c₂'⟩ := common w a' b' h'
    have e₁ : (a * a').left = (c * c').left ≫ φ₁ := h₁.2 _ c c' a a' c₁ c₁'
    have e₂ : (b * b').left = (c * c').left ≫ φ₂ := h₂.2 _ c c' b b' c₂ c₂'
    rw [e₁, e₂, Category.assoc, Category.assoc, hφ]
  have ca : ∀ (x : O) {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → (a ≫ a₁.act x).left ≫ ψ₁ = (b ≫ a₂.act x).left ≫ ψ₂ := by
    intro x S u v a b h
    obtain ⟨w, rfl, rfl⟩ := base a b h
    obtain ⟨c, c₁, c₂⟩ := common w a b h
    rw [Over.comp_left, Over.comp_left, c₁, c₂]
    simp only [Category.assoc]
    rw [← reassoc_of% (ha x).1, ← reassoc_of% (ha x).2, hφ]
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec (motive := fun i => T i ⟶ X) U.ι V.ι i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by
    cases i
    · exact inferInstanceAs (IsOpenImmersion U.ι)
    · exact inferInstanceAs (IsOpenImmersion V.ι)
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    have hx : x ∈ U ⊔ V := hUV ▸ trivial
    rcases hx with hx | hx
    · exact ⟨false, ⟨x, hx⟩, rfl⟩
    · exact ⟨true, ⟨x, hx⟩, rfl⟩)
  let H : ∀ i : 𝒰.I₀, Over (𝒰.X i) := fun i => Bool.rec (motive := fun i => Over (T i)) G₁ G₂ i
  letI iH : ∀ i : 𝒰.I₀, GrpObj (H i) := fun i => Bool.rec (motive := fun i => GrpObj (H i)) i₁ i₂ i
  let ψ : ∀ i : 𝒰.I₀, (H i).left ⟶ G.left := fun i => Bool.rec (motive := fun i => (H i).left ⟶ G.left) ψ₁ ψ₂ i
  let α : ∀ i : 𝒰.I₀, OAct O (H i) := fun i => Bool.rec (motive := fun i => @OAct _ O _ (H i) (iH i)) a₁ a₂ i
  have hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i) := by
    rintro (_ | _)
    exacts [p₁, p₂]
  have same : ∀ (i : 𝒰.I₀) {S : Scheme.{0}} {u v : S ⟶ 𝒰.X i} (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i),
      a.left ≫ ψ i = b.left ≫ ψ i → u = v := fun i S u v a b h => by
    rw [← cancel_mono (𝒰.f i), base_eq hψ a, base_eq hψ b, h]
  have hm : MulCompat ψ := by
    have d : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a a' : Over.mk u ⟶ H i) (b b' : Over.mk v ⟶ H i),
        a.left ≫ ψ i = b.left ≫ ψ i → a'.left ≫ ψ i = b'.left ≫ ψ i →
          (a * a').left ≫ ψ i = (b * b').left ≫ ψ i := by
      intro i S u v a a' b b' h h'
      obtain rfl := same i a b h
      rw [pt_ext hψ h, pt_ext hψ h']
    rintro (_ | _) (_ | _) S u v a a' b b' h h'
    · exact d _ S u v a a' b b' h h'
    · exact cm a a' b b' h h'
    · exact (cm b b' a a' h.symm h'.symm).symm
    · exact d _ S u v a a' b b' h h'
  obtain ⟨iG, hG⟩ := exists_grpObj hm hψ
  obtain ⟨A, hA⟩ := exists_oAct hG α (by
    have d : ∀ (x : O) (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i),
        a.left ≫ ψ i = b.left ≫ ψ i → (a ≫ (α i).act x).left ≫ ψ i = (b ≫ (α i).act x).left ≫ ψ i := by
      intro x i S u v a b h
      obtain rfl := same i a b h
      rw [pt_ext hψ h]
    rintro x (_ | _) (_ | _) S u v a b h
    · exact d x _ S u v a b h
    · exact ca x a b h
    · exact (ca x b a h.symm).symm
    · exact d x _ S u v a b h)
  exact ⟨G, iG, A, ψ₁, ψ₂, isSemiAbelian_of_charts hG (by rintro (_ | _); exacts [s₁, s₂]), hG false, hG true, hφ,
    fun x => ⟨hA x false, hA x true⟩⟩

end GlobalTheory.GroupGlue
end
end

