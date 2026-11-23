module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2976
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2470
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2989
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicShearOfAdjoint
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_eq_nsmul_of_forall_ef_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {n : ℕ} (hn : 0 < n) (a : D.La) (h : ∀ b, (n : ℤ) ∣ D.EF a b) : ∃ e, a = n • e := by
  choose c hc using h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let ψ : D.La →+ ℤ := AddMonoidHom.mk' c fun x y => mul_left_cancel₀ hn' (by rw [mul_add, ← hc, ← hc, ← hc, map_add (f := _)])
  obtain ⟨e, he⟩ := D.unimod.2 ψ.toIntLinearMap
  refine ⟨e, D.unimod.1 (LinearMap.ext fun b => ?_)⟩
  rw [map_nsmul, he, hc, LinearMap.smul_apply, nsmul_eq_mul]
  rfl

theorem exists_shear_of_adjoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type}
    [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    ∀ σ w : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') → (∀ b ∈ Z', σ b = b) → (∀ a, ∃ e, y (σ a) = y a + n • e) →
    (∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e) → (∀ a b, D.EF (w a) b = D.EF a (σ b)) →
    (∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e) →
    ∃ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) ∧ (∀ z z' : Z, D.EF (t z) (t z') = 0) ∧
      ∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a := by
  intro E _ _ _ H D X _ _ y n N hn hNn hC Z Z' hO σ w hσZ hσb hσy hσN hw hsat
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNn hn
  obtain ⟨k, hk⟩ := hNn
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'

  have ha : ∀ z ∈ Z, ∃ e ∈ perp D Z', w z = z + N • e := by
    intro z hz
    obtain ⟨e, he⟩ := exists_eq_nsmul_of_forall_ef_dvd D hN (w z - z) fun b => by
      obtain ⟨b', hb', e, he⟩ := hσN b
      have h0 : D.EF z b' = 0 := by rw [ef_swap, hb' z hz, neg_zero]
      refine ⟨D.EF z e, ?_⟩
      simp only [map_sub, LinearMap.sub_apply, hw, he, map_add (f := _), map_nsmul, h0, nsmul_eq_mul]
      ring
    refine ⟨e, mem_perp.2 fun b hb => ?_, (sub_eq_iff_eq_add'.1 he)⟩
    have h1 : D.EF (w z - z) b = 0 := by rw [map_sub, LinearMap.sub_apply, hw, hσb b hb, sub_self]
    rw [he, map_nsmul, LinearMap.smul_apply, smul_eq_zero] at h1
    exact h1.resolve_left hN.ne'

  have hb : ∀ z a : D.La, (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (w z) a := by
    rintro z a ⟨e, he⟩
    obtain ⟨e₁, he₁⟩ := hσy a
    obtain ⟨e', -, he'⟩ := hsat (σ a) (hσZ a) ⟨e + e₁, by rw [he₁, he, smul_add]⟩
    refine ⟨D.EF z e', ?_⟩
    rw [hw, he', map_nsmul, nsmul_eq_mul]
  have hwy : ∀ z, ∃ e, y (w z) = n • e := fun z => hC.2 (w z) fun b hb' => hb z b hb'
  have hww : ∀ z z', (n : ℤ) ∣ D.EF (w z) (w z') := fun z z' => hb z (w z') (hwy z')
  obtain ⟨f, hf⟩ : ∃ f : Z → Z → ℤ, ∀ z z', (n : ℤ) * f z z' = D.EF (w z) (w z') :=
    ⟨fun z z' => D.EF (w z) (w z') / n, fun z z' => Int.mul_ediv_cancel' (hww _ _)⟩
  obtain ⟨β, hβ⟩ : ∃ β : LinearMap.BilinForm ℤ Z, ∀ a b, β a b = f a b :=
    ⟨LinearMap.mk₂ ℤ f
      (fun z₁ z₂ z' => mul_left_cancel₀ hnZ (by rw [mul_add, hf, hf, hf]; simp))
      (fun c z z' => mul_left_cancel₀ hnZ (by rw [smul_eq_mul, mul_left_comm, hf, hf]; simp))
      (fun z z₁ z₂ => mul_left_cancel₀ hnZ (by rw [mul_add, hf, hf, hf]; simp))
      (fun c z z' => mul_left_cancel₀ hnZ (by rw [smul_eq_mul, mul_left_comm, hf, hf]; simp)),
      fun _ _ => rfl⟩
  have hskew : ∀ a b, β a b = -β b a := fun a b => by
    rw [hβ, hβ]
    exact mul_left_cancel₀ hnZ (by rw [mul_neg, hf, hf, ef_swap])
  have hadj : ∀ (c : 𝓞 E) a b, β (c • a) b = β a (H.bar c • b) := fun c a b => by
    rw [hβ, hβ]
    exact mul_left_cancel₀ hnZ (by rw [hf, hf, Submodule.coe_smul, Submodule.coe_smul, w.map_smul, w.map_smul, D.adj])
  obtain ⟨c, hc⟩ := exists_skew_solve hO.2.2.1 β hskew hadj
  have ht : ∀ z : Z, (w ∘ₗ Z.subtype - n • (Z'.subtype ∘ₗ c)) z = w z - n • (c z : D.La) := fun z => rfl
  refine ⟨w ∘ₗ Z.subtype - n • (Z'.subtype ∘ₗ c), fun z => ?_, fun z z' => ?_, fun z a ha' => ?_⟩
  · obtain ⟨e₁, he₁, hwz⟩ := ha z z.2
    refine ⟨e₁ - k • (c z : D.La), sub_mem he₁ (nsmul_mem (hO.2.1 (c z).2) k), ?_⟩
    rw [ht, hwz, hk, smul_sub, mul_smul]
    abel
  · have e1 : D.EF (w z) (c z') = D.EF z (c z') := by rw [hw, hσb _ (c z').2]
    have e2 : D.EF (c z) (w z') = D.EF (c z) z' := by rw [ef_swap, hw, hσb _ (c z).2, ← ef_swap]
    have e3 : D.EF (c z) (c z') = 0 := hO.2.1 (c z).2 _ (c z').2
    have e4 : (n : ℤ) * β z z' = D.EF (w z) (w z') := by rw [hβ, hf]
    have e5 := hc z z'
    rw [ht, ht]
    simp only [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul, e1, e2, e3]
    linear_combination (-1 : ℤ) * e4 - (n : ℤ) * e5
  · rw [ht, map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact dvd_sub (hb z a ha') (dvd_mul_right _ _)

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryGenericFibreBoundaryChartStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelIsometry_genericFibre_boundaryChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I := by
  first | exact @GlobalTheory.LowDat.exists_xfLevel | exact GlobalTheory.LowDat.exists_xfLevel | (intros; apply GlobalTheory.LowDat.exists_xfLevel <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureNormalModelUnitaryModuliPoin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory GlobalTheory.USep GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.UCovSep.GenModel

theorem exists_genModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x₀ : Xo.XF c) (n : ℕ), n.Prime → Odd n → ∃ g₀ : ℕ, ∀ e : ℕ, ∃ (o₁ Ω : Type) (_ : CommRing o₁) (_ : Field Ω) (_ : Algebra o₁ Ω) (_ : ArithBase o₁ Ω) (ze : o₁ˣ) (uη : Sp Ω ⟶ Xo.XF c) (A₁ : PolAV (Sp Ω)) (_ : Out.Level A₁ (n ^ e) (unitOn (Units.map (algebraMap o₁ Ω).toMonoidHom ze))) (M : RatModel o₁ Ω) (U : C.Z.Opens) (g : M.Z ⟶ U.toScheme), A₁.g = g₀ ∧ IsUnit (n : o₁) ∧ (∀ w, uη w = x₀) ∧ UOver Xo c A₁ (RingHom.id Ω) uη ∧ M.pt ≫ g ≫ U.ι = uη ≫ C.i ∧ GlobalTheory.IsNormalScheme M.Z ∧ IsProjOver M.s ∧ IsFinite g ∧ Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z) := by
  intro E _ _ _ H Dw _ l Xo c C x₀ n hn ho
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
  obtain ⟨A, _, φ, j, P, _, hφ, hjs, hjo, hjx⟩ :=
    GlobalTheory.UPoinc.GSetup.exists_chart (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x₀
  let ev : A →+* P.ResidueField := algebraMap A P.ResidueField
  let y : Sp P.ResidueField ⟶ Xo.XF c := spMap ev ≫ j
  have hy : ∀ w, y w = x₀ := fun w => by
    have hp : spMap ev w = ⟨P, inferInstance⟩ := by
      refine PrimeSpectrum.ext ?_
      show Ideal.comap ev w.asIdeal = P
      rw [Subsingleton.elim w (⊥ : PrimeSpectrum P.ResidueField)]
      exact Ideal.ker_algebraMap_residueField _
    show j (spMap ev w) = x₀
    rw [hp, hjx]
  haveI : CharZero P.ResidueField := (ev.comp φ).charZero_iff (ev.comp φ).injective |>.1 inferInstance
  obtain ⟨A₀, -, hU₀⟩ := GlobalTheory.UPoinc.GSetup.exists_fibre Xo c y
  refine ⟨A₀.g, fun e => ?_⟩
  have hpos : 1 ≤ n ^ e := Nat.one_le_iff_ne_zero.2 (by have := hn.pos; positivity)
  obtain ⟨Ω, _, f, A₁, ψ, ze, hf, hA₁, hze, ⟨lev⟩⟩ := GlobalTheory.UPoinc.GSetup.exists_level_finite P.ResidueField A₀ _ hpos
  haveI : CharZero Ω := f.charZero_iff f.injective |>.1 inferInstance
  have hU₁ : UOver Xo c A₁ (RingHom.id Ω) (spMap f ≫ y) := by
    refine (uOver_baseChange_iff hA₁.2.1 (LBIso.symm hA₁.2.2) (RingHom.id Ω)).2 ?_
    rw [RingHom.id_comp]
    simpa only [RingHom.comp_id] using hU₀.comp f
  letI : Algebra C.o c.F := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  have hnF : C.b (n : C.o) ≠ 0 := by rw [map_natCast]; exact Nat.cast_ne_zero.2 hn.ne_zero
  have hno : (n : C.o) ≠ 0 := fun h => hnF (by rw [h, map_zero])
  have hle : Submonoid.powers (n : C.o) ≤ nonZeroDivisors C.o := powers_le_nonZeroDivisors_of_noZeroDivisors hno
  let o' := Localization.Away (n : C.o)
  haveI : IsDomain o' := IsLocalization.isDomain_localization hle
  haveI : IsDedekindDomain o' := IsLocalization.isDedekindDomain C.o hle o'
  let b' : o' →+* c.F := IsLocalization.Away.lift (n : C.o) (IsUnit.mk0 _ hnF)
  have hb' : b'.comp (algebraMap C.o o') = C.b := IsLocalization.Away.lift_comp _ _
  letI : Algebra o' c.F := b'.toAlgebra
  haveI : IsScalarTower C.o o' c.F := IsScalarTower.of_algebraMap_eq' hb'.symm
  haveI : IsFractionRing o' c.F := IsFractionRing.isFractionRing_of_isLocalization _ o' c.F hle
  let β : c.F →+* Ω := f.comp (ev.comp φ)
  obtain ⟨o₁, _, _, κ, ze₁, hded, hκ, hinj, hcomp, hze₁⟩ :=
    GlobalTheory.UPoinc.GSetup.exists_base_root o' c.F Ω β ze _ hpos hze
  have hft : Algebra.FiniteType ℤ o₁ := by
    have h₁ : (algebraMap ℤ C.o).FiniteType := RingHom.finiteType_algebraMap.2 C.ft
    have h₂ : (algebraMap C.o o').FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
    have h₃ := hκ.finiteType.comp (h₂.comp h₁)
    rw [RingHom.ext_int (κ.comp _) (algebraMap ℤ o₁)] at h₃
    exact RingHom.finiteType_algebraMap.1 h₃
  haveI : ArithBase o₁ Ω := ⟨hded, hft, inferInstance, hinj⟩
  have hun : IsUnit (n : o₁) := by
    simpa using (IsLocalization.Away.algebraMap_isUnit (S := o') (n : C.o)).map κ
  rw [← hze₁] at lev
  haveI : IsProper C.z := ThetaDescent.isProper_of_isProjOver C.proj
  haveI := C.iF_open
  haveI : SurjectiveOnStalks (spMap ev) :=
    (SurjectiveOnStalks.Spec_iff (φ := CommRingCat.ofHom ev)).2 (Ideal.surjectiveOnStalks_residueField P)
  let a : Sp o' ⟶ Sp C.o := spMap (algebraMap C.o o')
  haveI : IsOpenImmersion a := IsOpenImmersion.of_isLocalization (n : C.o)
  have hba : spMap b' ≫ a = spMap C.b := by rw [← hb']; exact (Spec.map_comp _ _).symm
  let inc : pullback C.z a ⟶ C.Z := pullback.fst _ _
  let gf : pullback C.z (spMap C.b) ⟶ pullback C.z a := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap b')
    (by rw [Category.assoc, hba, pullback.condition])
  have hgf : gf ≫ inc = pullback.fst _ _ := pullback.lift_fst _ _ _
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  haveI : IsPreimmersion (gf ≫ inc) := hgf ▸ inferInstance
  haveI : IsPreimmersion gf := IsPreimmersion.of_comp gf inc
  have hpz : (spMap f ≫ spMap ev ≫ j ≫ C.iF ≫ gf) ≫ pullback.snd _ _ = spMap ((algebraMap o₁ Ω).comp κ) := by
    simp only [Category.assoc, gf, pullback.lift_snd]
    rw [← Category.assoc C.iF, C.iF_over, ← Category.assoc j, hjs, hcomp]
    simp only [← Spec.map_comp]
    rfl
  have hst : ((spMap f ≫ spMap ev ≫ j ≫ C.iF ≫ gf).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
    rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (GlobalTheory.UPoinc.GSetup.finite_stalkMap_field f hf _)
      (RingHom.Finite.of_surjective _ (Scheme.Hom.stalkMap_surjective _ _))
  obtain ⟨M, π, hMn, hπ, hMp⟩ := GlobalTheory.Poinc.exists_ratModel_normalization o' o₁ Ω κ hκ _ (pullback.snd C.z a) inferInstance
    inferInstance inferInstance _ hpz hst
  have hMs : M.s ≫ spMap κ = π ≫ pullback.snd C.z a := by
    refine ext_of_isDominant_of_isSeparated (spMap (algebraMap ℤ o')) (specZIsTerminal.hom_ext _ _) M.pt ?_
    rw [← Category.assoc, M.pt_s, ← Category.assoc, hMp, hpz, ← Spec.map_comp]
    rfl
  have hproj : IsProjOver M.s :=
    GlobalTheory.FiniteOverProj.isProjOver_of_isFinite_over o' o₁ κ M.Z (pullback C.z a) (pullback.snd C.z a) π M.s
      (GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap C.o o') C.proj) hπ inferInstance hMs
  refine ⟨o₁, Ω, inferInstance, inferInstance, inferInstance, inferInstance, ze₁, spMap f ≫ y, A₁, lev, M,
    inc.opensRange, π ≫ inc.isoOpensRange.hom, hA₁.1, hun, fun w => hy _, hU₁, ?_,
    GlobalTheory.IsNormalScheme.of_pred hMn, hproj, inferInstance, ?_⟩
  · rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ← Category.assoc, hMp]
    simp only [y, Category.assoc, hgf]
  · rintro _ ⟨x, rfl⟩
    exact ⟨gf x, by rw [← Scheme.Hom.comp_apply, hgf]⟩

end GlobalTheory.UCovSep.GenModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelTorsionPointOfComesFromBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DivSol

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def mulPull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (n : ℕ) :
    IsPullDeg φ (mulDeg D n) (mulDeg D' n) where
  e := hD.e
  e_hom := hD.e_hom
  w := hD.w
  w_gen := hD.w_gen
  he := hD.he
  w_rig := hD.w_rig
  xe := hD.xe
  c_pr := fun (x : D'.X) => by
    have hx : hD.xe (n • x) = n • hD.xe x := map_nsmul hD.xe n x
    show (D'.c (n • x)).left ≫ _ = specOf φ ≫ (D.c (n • hD.xe x)).left
    rw [← hx]
    exact hD.c_pr (n • x)
  W := hD.W
  psiW := ⟨fun (χ : D.X) => hD.psiW.psi (n • χ), fun (χ : D.X) => hD.psiW.psi_gen (n • χ), fun (χ : D.X) => hD.psiW.psi_eq (n • χ)⟩
  g := hD.g
  g_comm := hD.g_comm
  psi_pr := fun (x : D'.X) => by
    have h := hD.psi_pr (n • x)
    have hx : hD.xe (n • x) = n • hD.xe x := map_nsmul hD.xe n x
    rw [hx] at h
    exact h

theorem mulDeg_psiEven (D : DegPre R) (n : ℕ) (h : D.PsiEven) : (mulDeg D n).PsiEven :=
  fun (a : D.X) => MulDeg.corr_even_degenerationData_negPoint D h (n • a) (n • (-a)) (neg_nsmul a n)

theorem mulDeg_tauBimult (D : DegPre R) (n : ℕ) (h : D.TauBimult) : (mulDeg D n).TauBimult :=
  fun (a a' b : D.X) => MulDeg.corr_bimultiplicative_degenerationData_sums D h (n • a) (n • a') (n • b) (n • (a + a')) (n • (a + a' + b)) (n • (a + b))
    (n • (a' + b)) (nsmul_add _ _ _) (by rw [nsmul_add, nsmul_add]) (nsmul_add _ _ _) (nsmul_add _ _ _)

theorem mulDeg_psiUnitOn (D : DegPre R) (n : ℕ) (h : ∀ y, PsiUnitOn D y Set.univ) :
    ∀ y, PsiUnitOn (mulDeg D n) y Set.univ :=
  fun (y : D.X) => h (n • y)

end GlobalTheory.DivSol

namespace GlobalTheory.DivSol

theorem exists_qkPt_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ y : P.D.toPre.X, ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', p₀.y = y := by
  intro E _ _ _ H D' l c L R _ _ _ _hB t P iw I _ s ε e _hbal hs hdf y
  obtain ⟨g, hD, hg, -, -⟩ := hdf
  obtain ⟨DR, hR, -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg polBaseChange_holds L.W R iw L.D ⊤
    (GlobalTheory.ArcPull.nonempty_psiOn_top L.D L.gen) trivial
  have hbiR : DR.TauBimult := GlobalTheory.tauBimult_of_isPullDeg globalFns_holds _ _ iw L.D DR hR L.bimult
  have hunR : ∀ y, PsiUnitOn DR y Set.univ := GlobalTheory.PullDegTop.psiUnitOn_univ hR L.gen
  have hevR : DR.PsiEven := GlobalTheory.PsiEvenPull.psiEven_pull globalFns_holds _ _ iw L.D DR hR L.even
  have hC : IsPullDeg (RingHom.id R) (mulDeg DR l.M') (GlobalTheory.PolDeg.rescale P.D.toPre g) :=
    (GlobalTheory.Mum.isPullDeg_unique_any L.W R iw (mulDeg L.D l.M') _ _ ⟨mulPull hR l.M'⟩ ⟨hD⟩).some
  obtain ⟨T, ib, β, ββ, w, hF⟩ := _root_.GlobalTheory.TInjBase.main (RingHom.id R) DR hbiR hunR l.M'
  let e' : P.D.toPre.X ≃+ (Fin T.r → ℤ) := hC.xe.trans ib
  let x : (Fin T.r → ℤ) ≃+ L.D.X := e'.symm.trans e.toAddEquiv
  have hx : ∀ a, x (e' a) = e a := fun a => by simp [x]
  let ε' : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ) := fun k =>
    LinearMap.mk₂ ℤ (fun u v => ε k (x u) (H.w0 • x v) + ε k (x v) (H.w0 • x u))
      (fun m₁ m₂ n => by simp only [map_add (f := _), smul_add, LinearMap.add_apply]; ring)
      (fun c m n => by
        simp only [map_zsmul, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
        rw [smul_comm H.w0 c (x m)]
        simp only [LinearMap.map_smul, smul_eq_mul]; ring)
      (fun m n₁ n₂ => by simp only [map_add (f := _), smul_add, LinearMap.add_apply]; ring)
      (fun c m n => by
        simp only [map_zsmul, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
        rw [smul_comm H.w0 c (x n)]
        simp only [LinearMap.map_smul, smul_eq_mul]; ring)
  have hne : ∀ i, algebraMap R (FractionRing R) (s i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hs i)
  have hgv : ∀ y, ((g y : (FractionRing R)ˣ) : FractionRing R) =
      (∏ k, algebraMap R (FractionRing R) (s k) ^ ((l.M' : ℤ) * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hg y, Units.val_inv_eq_inv_val, inv_inv]
  have hcoc : ∀ a a' : P.D.toPre.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing R)ˣ) : FractionRing R) =
      ∏ i, algebraMap R (FractionRing R) (s i) ^ ((l.M' : ℤ) * ε' i (e' a) (e' a')) := by
    intro a a'
    rw [Units.val_mul, Units.val_mul, hg (a + a'), hgv a, hgv a', ← Finset.prod_inv_distrib,
      ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ (hne i), ← zpow_add₀ (hne i)]
    congr 1
    simp only [ε', LinearMap.mk₂_apply, hx, map_add (f := _), smul_add, LinearMap.add_apply]
    ring
  obtain ⟨β', ββ', w', hF'⟩ := _root_.GlobalTheory.TInj.from_rescale_pull T l.M' (mulDeg DR l.M') (mulDeg_psiEven _ _ hevR)
    (mulDeg_tauBimult _ _ hbiR) (mulDeg_psiUnitOn _ _ hunR) ib β ββ w hF R (RingHom.id R) Function.injective_id
    P.D.toPre g hC s ε' e' (fun _ => rfl) hcoc
  obtain ⟨p, hp, -⟩ := GlobalTheory.TInj.exists_qkPt_tautPt T ε' l.M' R P.D.toPre (RingHom.id R) s e' β' ββ' w'
    P.D.tau_bimult hF' hs (FractionRing R) (e' y)
  exact ⟨p, by rw [hp]; simp⟩

end GlobalTheory.DivSol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionOppositeCongrMod
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_cell_section : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ σ : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') ∧ (∀ b ∈ Z', σ b = b) ∧ (∀ a, ∃ e, y (σ a) = y a + n • e) ∧
      ∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e := by
  intro E _ _ _ H D X _ _ _ y n N hn hN Z Z' h hker hsurj
  haveI := D.proj
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hN
    omega
  let mulN : X →ₗ[𝓞 E] X := N • LinearMap.id
  have hinj : Function.Injective mulN := by
    intro u v huv
    have h1 : N • u = N • v := by simpa [mulN] using huv
    have h2 : (N : ℤ) • (u - v) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, h1, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd (by exact_mod_cast h3) hN0
    · exact sub_eq_zero.1 h3
  let q : D.La →ₗ[𝓞 E] D.La := LinearMap.id - Z'.subtype ∘ₗ h.proj
  have hqa : ∀ a, q a = a - (h.proj a : D.La) := fun a => rfl
  have hq : ∀ a, q a ∈ perp D Z := fun a => by rw [hqa]; exact h.sub_proj_mem a
  have hrange : ∀ a, (y ∘ₗ q) a ∈ LinearMap.range mulN := fun a => by
    obtain ⟨e, he⟩ := (hker (q a)).2 ⟨q a, hq a, 0, by simp⟩
    exact ⟨e, by simp [mulN, he]⟩
  let ε : D.La →ₗ[𝓞 E] X :=
    (LinearEquiv.ofInjective mulN hinj).symm.toLinearMap ∘ₗ (y ∘ₗ q).codRestrict _ hrange
  have hε : ∀ a, N • ε a = y (q a) := by
    intro a
    have h2 := congrArg Subtype.val ((LinearEquiv.ofInjective mulN hinj).apply_symm_apply ⟨(y ∘ₗ q) a, hrange a⟩)
    rw [LinearEquiv.ofInjective_apply] at h2
    exact h2
  let muln : X →ₗ[𝓞 E] X := n • LinearMap.id
  let S : Submodule (𝓞 E) X := LinearMap.range muln
  let g : Z' →ₗ[𝓞 E] X ⧸ S := S.mkQ ∘ₗ y ∘ₗ Z'.subtype
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨x, rfl⟩ := S.mkQ_surjective x
    obtain ⟨b, hb, e, he⟩ := hsurj x
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply, he]
    rw [Submodule.Quotient.eq]
    exact ⟨e, by simp [mulN, muln]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g (S.mkQ ∘ₗ ε) hg
  have hs' : ∀ a, ∃ e, y (s a) = ε a + n • e := by
    intro a
    have h1 := LinearMap.congr_fun hs a
    simp only [g, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.subtype_apply] at h1
    rw [Submodule.Quotient.eq] at h1
    obtain ⟨e, he⟩ := h1
    refine ⟨e, ?_⟩
    have he' : n • e = y (s a) - ε a := by simpa [muln] using he
    rw [he']
    abel
  refine ⟨Z'.subtype ∘ₗ h.proj + N • (Z'.subtype ∘ₗ s ∘ₗ q), fun a => ?_, fun b hb => ?_, fun a => ?_, fun a => ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    exact add_mem (h.proj a).2 (Z'.nsmul_mem (s (q a)).2 N)
  · have hqb : q b = 0 := by rw [hqa, h.proj_of_mem hb, sub_self]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, hqb,
      map_zero, ZeroMemClass.coe_zero, smul_zero, add_zero]
    exact h.proj_of_mem hb
  · obtain ⟨e, he⟩ := hs' (q a)
    refine ⟨N • e, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add (f := _),
      map_nsmul]
    have hy : y (q a) = y a - y (h.proj a) := by rw [hqa, map_sub]
    have hqq : q (q a) = q a := by rw [hqa (q a), h.proj_of_perp (hq a), sub_zero]
    rw [he, smul_add, hε, hqq, hy, smul_comm N n e]
    abel
  · refine ⟨(h.proj a : D.La) - a, ?_, s (q a), ?_⟩
    · have := neg_mem (h.sub_proj_mem a)
      rwa [neg_sub] at this
    · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      abel

end GlobalTheory.LowFilt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeIsotropicPairStatement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oppositeIsotropicPair : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (Z : Submodule (𝓞 E) D.La), IsIsoSat D Z → ∃ Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' := by
  first | exact @GlobalTheory.LowFilt.Opp.exists_opp | exact GlobalTheory.LowFilt.Opp.exists_opp | (intros; apply GlobalTheory.LowFilt.Opp.exists_opp <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaClassSumTermsRootsOfUnity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.GSum.terms_and_sums : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ :=
  _root_.GlobalTheory.Poinc.GSumCls.main
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIndependenceLogDerivativesClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreIndependence_logDerivatives_closedFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m := by
  first | exact @GlobalTheory.FibreIndep.fibre_indep | exact GlobalTheory.FibreIndep.fibre_indep | (intros; apply GlobalTheory.FibreIndep.fibre_indep <;> assumption)
end

