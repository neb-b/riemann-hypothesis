module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqPtHomOfIsLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory

theorem exists_eq_ptHom_of_isLocalRing : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (A : Type) [CommRing A] [IsLocalRing A] (ρ : R →+* A) (x : Sp A ⟶ scheme W), x ≫ toSpec W = spMap ρ → ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), x = ptHom W ρ P h := by
  intro R _ W A _ _ ρ x hx
  have key : ∀ i : Fin 3, x (IsLocalRing.closedPoint A) ∈ coordOpen W i →
      ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), x = ptHom W ρ P h := by
    intro i hi
    have htop : x ⁻¹ᵁ coordOpen W i = ⊤ :=
      (IsLocalRing.closedPoint_mem_iff (R := A) (x ⁻¹ᵁ coordOpen W i)).mp hi
    have hr : Set.range x ⊆ Set.range (awayChart W i) := by
      rintro _ ⟨y, rfl⟩
      have hy : y ∈ x ⁻¹ᵁ coordOpen W i := htop.ge trivial
      rw [← opensRange_awayChart] at hy
      exact hy
    obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift (awayChart W i) x hr)
    have hx' : x = Spec.map (CommRingCat.ofHom g.hom) ≫ awayChart W i := by
      rw [CommRingCat.ofHom_hom, hg, IsOpenImmersion.lift_fac]
    rw [SpecMap_awayChart] at hx'
    have hρ : g.hom.comp (awayConst W i) = ρ := by
      rw [hx', ptHom_toSpec] at hx
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective hx)
    subst hρ
    exact ⟨_, _, hx'⟩
  have h : x (IsLocalRing.closedPoint A) ∈ coordOpen W 1 ⊔ coordOpen W 2 := by
    rw [coordOpen_one_sup_coordOpen_two]
    trivial
  rcases h with h | h
  · exact key 1 h
  · exact key 2 h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjOverOfPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
theorem _root_.GlobalTheory.exists_grpObj_over_of_points : ∀ (S : Scheme.{0}) (X : Over S) (e : 𝟙_ _ ⟶ X) (m : X ⊗ X ⟶ X) (n : X ⟶ X), (∀ (T : Over S) (x : T ⟶ X), lift (toUnit T ≫ e) x ≫ m = x) → (∀ (T : Over S) (x : T ⟶ X), lift (x ≫ n) x ≫ m = toUnit T ≫ e) → (∀ (T : Over S) (x y : T ⟶ X), lift x y ≫ m = lift y x ≫ m) → (∀ (T : Over S) (x y z : T ⟶ X), lift (lift x y ≫ m) z ≫ m = lift x (lift y z ≫ m) ≫ m) → ∃ G : GrpObj X, η[X] = e ∧ μ[X] = m ∧ (GrpObj.inv : X ⟶ X) = n ∧ IsCommMonObj X := by
  intro S X e m n hl hinv hcomm hassoc
  have hr : ∀ (T : Over S) (x : T ⟶ X), lift x (toUnit T ≫ e) ≫ m = x := fun T x => by
    rw [hcomm, hl]
  let M : MonObj X :=
    { one := e
      mul := m
      one_mul := by
        have : e ▷ X = lift (toUnit _ ≫ e) (snd _ _) := by
          apply hom_ext
          · simp only [whiskerRight_fst, lift_fst]
            rw [toUnit_unique (fst _ _) (toUnit _)]
          · simp only [whiskerRight_snd, lift_snd]
        rw [this, hl, leftUnitor_hom]
      mul_one := by
        have : X ◁ e = lift (fst _ _) (toUnit _ ≫ e) := by
          apply hom_ext
          · simp only [whiskerLeft_fst, lift_fst]
          · simp only [whiskerLeft_snd, lift_snd]
            rw [toUnit_unique (snd _ _) (toUnit _)]
        rw [this, hr, rightUnitor_hom]
      mul_assoc := by
        have h1 : m ▷ X = lift (lift (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _) ≫ m) (snd _ _) := by
          apply hom_ext
          · simp only [whiskerRight_fst, lift_fst]
            rw [← comp_lift, lift_fst_snd, Category.comp_id]
          · simp only [whiskerRight_snd, lift_snd]
        have h2 : (α_ X X X).hom ≫ X ◁ m =
            lift (fst _ _ ≫ fst _ _) (lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ m) := by
          apply hom_ext
          · simp only [Category.assoc, whiskerLeft_fst, associator_hom_fst, lift_fst]
          · simp only [Category.assoc, whiskerLeft_snd, lift_snd]
            have h3 : (α_ X X X).hom ≫ snd _ _ = lift (fst _ _ ≫ snd _ _) (snd _ _) := by
              apply hom_ext <;>
                simp only [lift_fst, lift_snd, Category.assoc, associator_hom_snd_fst,
                  associator_hom_snd_snd]
            rw [reassoc_of% h3]
        rw [h1, reassoc_of% h2, hassoc] }
  let G : GrpObj X :=
    { inv := n
      left_inv := by
        show lift n (𝟙 X) ≫ m = toUnit X ≫ e
        simpa using hinv X (𝟙 X)
      right_inv := by
        show lift (𝟙 X) n ≫ m = toUnit X ≫ e
        rw [hcomm]
        simpa using hinv X (𝟙 X) }
  refine ⟨G, rfl, rfl, rfl, ⟨?_⟩⟩
  have : (β_ X X).hom = lift (snd _ _) (fst _ _) := by
    apply hom_ext <;> simp only [braiding_hom_fst, braiding_hom_snd, lift_fst, lift_snd]
  rw [this]
  show lift (snd X X) (fst X X) ≫ m = m
  rw [hcomm, lift_fst_snd, Category.id_comp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPeriodPairOfLatticeInLine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_periodPair_of_lattice_in_line :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (w : Fin g → ℂ), g = 1 → w ≠ 0 → DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∃ L : PeriodPair, ∀ z : ℂ, z ∈ L.lattice ↔ z • w ∈ Λ := by
  intro g Λ w hg hw hdisc hspan
  subst hg
  have hw0 : w 0 ≠ 0 := by
    intro h
    apply hw
    funext j
    fin_cases j
    simpa using h

  obtain ⟨e, he⟩ : ∃ e : ℂ ≃L[ℝ] (Fin 1 → ℂ), ∀ z, e z = z • w := by
    let φ : ℂ →ₗ[ℝ] (Fin 1 → ℂ) :=
      { toFun := fun z => z • w
        map_add' := fun a b => add_smul a b w
        map_smul' := fun r z => by
          simp only [RingHom.id_apply]
          exact smul_assoc r z w }
    have hinj : Function.Injective φ := fun a b h => smul_left_injective ℂ hw h
    have hsurj : Function.Surjective φ := by
      intro y
      refine ⟨y 0 / w 0, ?_⟩
      funext j
      fin_cases j
      simp [φ, hw0]
    exact ⟨(LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun z => rfl⟩

  have : DiscreteTopology Λ := hdisc
  have : IsZLattice ℝ Λ := ⟨hspan⟩
  set Λ' := ZLattice.comap ℝ Λ e.toLinearMap with hΛ'
  have hrank : Module.finrank ℤ Λ' = 2 := by
    rw [ZLattice.rank ℝ Λ', Complex.finrank_real_complex]
  set b := Module.finBasisOfFinrankEq ℤ Λ' hrank with hb
  set bR := b.ofZLatticeBasis ℝ Λ' with hbR
  refine ⟨⟨bR 0, bR 1, ?_⟩, fun z => ?_⟩
  · have hv : ![bR 0, bR 1] = ⇑bR := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact bR.linearIndependent
  · have hr : ({bR 0, bR 1} : Set ℂ) = Set.range bR := by
      ext x
      simp [Fin.exists_fin_two, eq_comm]
    rw [PeriodPair.lattice]
    dsimp only
    rw [hr, hbR, Module.Basis.ofZLatticeBasis_span, ← SetLike.mem_coe, hΛ', ZLattice.coe_comap]
    simp [he]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUnitMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SameZeroScheme

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  change (X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom a = _
  rw [← X.presheaf.map_comp]
  rfl

theorem top_le_preimage {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    {A : CommRingCat.{0}} (φ : Γ(Y, U) ⟶ A) : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ V := by
  intro x _
  apply h
  have : hU.fromSpec (Spec.map φ x) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
  rw [hU.range_fromSpec] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
theorem appLE_spec {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    {A : CommRingCat.{0}} (φ : Γ(Y, U) ⟶ A) :
    (Spec.map φ ≫ hU.fromSpec).appLE V ⊤ (top_le_preimage hU h φ) =
      Y.presheaf.map (homOfLE h).op ≫ φ ≫ (Scheme.ΓSpecIso A).inv := by
  have h1 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ V := by
    rw [← hU.fromSpec_preimage_self]
    exact fun x hx => h hx
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) hU.fromSpec V ⊤ ⊤ h1 le_top,
    Scheme.ΓSpecIso_inv_naturality]
  have e1 : hU.fromSpec.appLE V ⊤ h1 =
      Y.presheaf.map (homOfLE h).op ≫ (Scheme.ΓSpecIso Γ(Y, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_of_le V h, Category.assoc, Category.assoc,
      ← Functor.map_comp]
    congr 1
  have e2 : (Spec.map φ).appLE ⊤ ⊤ le_top = (Spec.map φ).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  rw [e1, e2, Category.assoc]

theorem dvd_on_affine {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    (a b : Γ(Y, V))
    (H : ∀ (T : Scheme.{0}) (t : T ⟶ Y) (h : ⊤ ≤ t ⁻¹ᵁ V),
      (t.appLE V ⊤ h).hom a = 0 → (t.appLE V ⊤ h).hom b = 0) :
    resG Y h a ∣ resG Y h b := by
  let I : Ideal Γ(Y, U) := Ideal.span {resG Y h a}
  let φ : Γ(Y, U) ⟶ CommRingCat.of (Γ(Y, U) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have key := H _ _ (top_le_preimage hU h φ)
  rw [appLE_spec hU h φ] at key
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).commRingCatIsoToRingEquiv.symm.injective
  have ha : Ideal.Quotient.mk I (resG Y h a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hb := key (by
    change (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).inv.hom
      (Ideal.Quotient.mk I (resG Y h a)) = 0
    rw [ha]; exact map_zero _)
  have hb' : Ideal.Quotient.mk I (resG Y h b) = 0 :=
    hinj (hb.trans (map_zero _).symm)
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hb')

theorem exists_unit_mul (Y : Scheme.{0}) (V : Y.Opens) (a b : Γ(Y, V))
    (ha : ∀ (V' : Y.Opens) (h : V' ≤ V), resG Y h a ∈ nonZeroDivisors Γ(Y, V'))
    (H : ∀ (T : Scheme.{0}) (t : T ⟶ Y) (h : ⊤ ≤ t ⁻¹ᵁ V),
      (t.appLE V ⊤ h).hom a = 0 ↔ (t.appLE V ⊤ h).hom b = 0) :
    ∃ c : Γ(Y, V)ˣ, b = (c : Γ(Y, V)) * a := by
  let J := {U : Y.Opens // IsAffineOpen U ∧ U ≤ V}
  let W : J → Y.Opens := fun i => i.1
  have hW : ∀ i, W i ≤ V := fun i => i.2.2
  have hcov : ∀ y ∈ V, ∃ i, y ∈ W i := fun y hy => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
    exact ⟨⟨U, hU, hUV⟩, hyU⟩
  have hc : V ≤ iSup W := fun y hy => TopologicalSpace.Opens.mem_iSup.2 (hcov y hy)
  have hloc : ∀ i, ∃ c : Γ(Y, W i), IsUnit c ∧ resG Y (hW i) b = c * resG Y (hW i) a := fun i => by
    obtain ⟨c, hc⟩ := dvd_on_affine i.2.1 (hW i) a b fun T t h => (H T t h).1
    obtain ⟨d, hd⟩ := dvd_on_affine i.2.1 (hW i) b a fun T t h => (H T t h).2
    refine ⟨c, ?_, hc.trans (mul_comm _ _)⟩
    have e : (c * d) * resG Y (hW i) a = 1 * resG Y (hW i) a := by
      rw [_root_.one_mul]
      conv_rhs => rw [hd, hc]
      ring
    exact IsUnit.of_mul_eq_one d ((mul_cancel_right_mem_nonZeroDivisors (ha _ (hW i))).1 e)
  choose u hu hub using hloc
  have hh : ∀ i j, resG Y (inf_le_left : W i ⊓ W j ≤ W i) (u i) = resG Y inf_le_right (u j) := by
    intro i j
    have e₁ := congrArg (resG Y (inf_le_left : W i ⊓ W j ≤ W i)) (hub i)
    have e₂ := congrArg (resG Y (inf_le_right : W i ⊓ W j ≤ W j)) (hub j)
    rw [map_mul, res_res, res_res] at e₁ e₂
    exact (mul_cancel_right_mem_nonZeroDivisors (ha _ (inf_le_left.trans (hW i)))).1
      (e₁.symm.trans e₂)
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc u hh
  have hs' : ∀ i, resG Y (hW i) (show Γ(Y, V) from s) = u i := hs
  have hunit : IsUnit (show Γ(Y, V) from s) :=
    Y.toRingedSpace.isUnit_of_isUnit_germ V _ fun y hy => by
      obtain ⟨i, hi⟩ := hcov y hy
      have h1 := (hu i).map (Y.presheaf.germ (W i) y hi).hom
      rw [← hs' i] at h1
      have h2 := Y.presheaf.germ_res_apply (homOfLE (hW i)) y hi (show Γ(Y, V) from s)
      exact h2 ▸ h1
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]
  apply Y.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
  intro i
  change resG Y (hW i) b = resG Y (hW i) ((show Γ(Y, V) from s) * a)
  rw [map_mul, hs', hub]

end GlobalTheory.SameZeroScheme
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeOfGenericallySurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem surjective_of_generic_fibre_subset_range
    {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp V) [UniversallyClosed f] [Flat g]
    (h : ∀ y : Y, g y ∈ Set.range (spMap (algebraMap V K)) → y ∈ Set.range f) :
    Surjective f := by
  refine ⟨fun y => ?_⟩
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  let e : Sp V := (⊥ : PrimeSpectrum V)
  have hη : e ⤳ g y := (PrimeSpectrum.le_iff_specializes _ _).mp (bot_le (α := PrimeSpectrum V))
  obtain ⟨y', hy', hy''⟩ := Flat.generalizingMap g hη
  refine hy'.mem_closed hcl (h y' ?_)
  rw [hy'']
  refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap V K) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)

theorem isAbelianScheme_of_generically_surjective :
    ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
      [IsFractionRing V K] (B G : Over (Sp V)) [GrpObj B] [GrpObj G],
      IsAbelianScheme B → IsSemiAbelian G → ∀ ψ : B ⟶ G,
      (∀ x : G.left, G.hom x ∈ Set.range (spMap (algebraMap V K)) → x ∈ Set.range ψ.left) →
      IsAbelianScheme G := by
  intro V K _ _ _ _ _ _ B G _ _ hB hG ψ h
  have := hB.proper
  have := hG.smooth
  have := hG.separated
  have hw : ψ.left ≫ G.hom = B.hom := Over.w ψ
  have : IsProper (ψ.left ≫ G.hom) := hw ▸ hB.proper
  have : IsProper ψ.left := IsProper.of_comp ψ.left G.hom
  have : Surjective ψ.left := surjective_of_generic_fibre_subset_range ψ.left G.hom h
  have : UniversallyClosed G.hom := UniversallyClosed.of_comp_surjective ψ.left G.hom
  exact ⟨hG.comm, hG.smooth, ⟨⟩, hG.geomConnected⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

theorem GlobalTheory.WeierstrassCurve.isAbelianScheme_schemeOver :
    ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ →
      ∀ [GrpObj (schemeOver W)], IsCommMonObj (schemeOver W) → IsAbelianScheme (schemeOver W) := by
  intro R _ W hΔ _ hc
  have hs := smoothOfRelativeDimension_toSpec_of_isUnit W hΔ
  exact ⟨hc, SmoothOfRelativeDimension.smooth 1 (toSpec W), isProper_toSpec W,
    geometricallyConnected_toSpec W⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIsoAppLEOfOpensRange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.CoordFn

theorem isIso_appLE_of_opensRange {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) (hU : f.opensRange = U) (h : ⊤ ≤ f ⁻¹ᵁ U) : IsIso (f.appLE U ⊤ h) := by
  subst hU
  have h1 : IsIso (f.app f.opensRange) := Scheme.Hom.isIso_app f _ le_rfl
  have h2 : (⊤ : X.Opens) = f ⁻¹ᵁ f.opensRange := le_antisymm h le_top
  have h3 : IsIso (homOfLE h) := by
    have : homOfLE h = eqToHom h2 := rfl
    rw [this]; infer_instance
  rw [Scheme.Hom.appLE]
  infer_instance

theorem appLE_SpecMap_comp {Y : Scheme.{0}} {A B : CommRingCat.{0}} (f : Spec B ⟶ Y) (g : B ⟶ A)
    (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (p : Spec A ⟶ Y) (hp : p = Spec.map g ≫ f)
    (h' : ⊤ ≤ p ⁻¹ᵁ U) :
    p.appLE U ⊤ h' ≫ (Scheme.ΓSpecIso A).hom = f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom ≫ g := by
  subst hp
  have e1 : (Spec.map g).appTop = (Spec.map g).appLE ⊤ ⊤ le_top :=
    Scheme.Hom.app_eq_appLE (Spec.map g)
  have e2 := Scheme.Hom.appLE_comp_appLE (Spec.map g) f U ⊤ ⊤ h le_top
  rw [← Scheme.ΓSpecIso_naturality, e1, ← Category.assoc, e2]

theorem appLE_structure {Y : Scheme.{0}} {A B : CommRingCat.{0}} (f : Spec B ⟶ Y) (g : A ⟶ B)
    (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (t : Y ⟶ Spec A) (ht : f ≫ t = Spec.map g) :
    (Scheme.ΓSpecIso A).inv ≫ t.appLE ⊤ U le_top ≫ f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom = g := by
  have e2 := Scheme.Hom.appLE_comp_appLE f t ⊤ U ⊤ le_top h
  have e1 : ∀ (q : Spec B ⟶ Spec A) (hq : ⊤ ≤ q ⁻¹ᵁ ⊤), q = Spec.map g →
      q.appLE ⊤ ⊤ hq = (Spec.map g).appTop := by
    rintro _ _ rfl
    exact (Scheme.Hom.app_eq_appLE (Spec.map g)).symm
  rw [← Category.assoc (t.appLE ⊤ U le_top), e2, e1 _ _ ht, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]

theorem top_le_preimage {R : Type} [CommRing R] (W : WeierstrassCurve R) (i : Fin 3) :
    ⊤ ≤ awayChart W i ⁻¹ᵁ coordOpen W i := by
  rw [← opensRange_awayChart, Scheme.Hom.preimage_opensRange]

theorem surjective_eval₂Hom_awayCoord {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (i : Fin 3) :
    Function.Surjective (MvPolynomial.eval₂Hom (awayConst W i) (awayCoord W i)) := by
  intro x
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading W) (coord_mem W i) x
  rw [← evalHom_awayCoord]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨p, rfl⟩

theorem exists_coordFn : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), ∃ c : ∀ i j : Fin 3, Γ(scheme W, coordOpen W i), (∀ (i j : Fin 3) (A : Type) [CommRing A] (ρ : R →+* A) (P : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P) (h : ⊤ ≤ ptHom W ρ P hP ⁻¹ᵁ coordOpen W i), (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (((ptHom W ρ P hP).appLE (coordOpen W i) ⊤ h).hom (c i j)) * P i = P j) ∧ ∀ i, Function.Surjective (MvPolynomial.eval₂Hom (((toSpec W).appLE ⊤ (coordOpen W i) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) (c i)) := by
  intro R _ W
  let φ : ∀ i : Fin 3, Γ(scheme W, coordOpen W i) ⟶ CommRingCat.of (AwayRing W i) := fun i =>
    (awayChart W i).appLE (coordOpen W i) ⊤ (top_le_preimage W i) ≫ (Scheme.ΓSpecIso _).hom
  have hφ : ∀ i, Function.Bijective (φ i).hom := fun i => by
    have := isIso_appLE_of_opensRange (awayChart W i) _ (opensRange_awayChart W i)
      (top_le_preimage W i)
    have : IsIso (φ i) := by dsimp only [φ]; infer_instance
    exact ConcreteCategory.bijective_of_isIso (φ i)
  choose c hc using fun i j => (hφ i).2 (awayCoord W i j)
  refine ⟨c, ?_, ?_⟩
  · intro i j A _ ρ P hP h
    have hi : IsUnit (P i) := by
      rw [ptHom_preimage_coordOpen] at h
      have h1 : PrimeSpectrum.basicOpen (P i) = ⊤ := top_le_iff.mp h
      by_contra hn
      obtain ⟨m, hm, hx⟩ := exists_max_ideal_of_mem_nonunits hn
      have : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∈ PrimeSpectrum.basicOpen (P i) := by
        rw [h1]; trivial
      exact this hx
    have e := appLE_SpecMap_comp (awayChart W i)
      (CommRingCat.ofHom (awayEval W i ρ P hP.equation hi)) (coordOpen W i)
      (top_le_preimage W i) _ (ptHom_eq_awayChart W i ρ P hP hi) h
    have e2 := congrArg (fun k => k.hom (c i j)) e
    have e3 : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
        (((ptHom W ρ P hP).appLE (coordOpen W i) ⊤ h).hom (c i j)) =
        awayEval W i ρ P hP.equation hi ((φ i).hom (c i j)) := e2
    rw [e3, hc, awayEval_awayCoord_mul]
  · intro i
    have e := appLE_structure (awayChart W i) (CommRingCat.ofHom (awayConst W i)) (coordOpen W i)
      (top_le_preimage W i) (toSpec W) (awayChart_toSpec W i)
    have key : (φ i).hom.comp (MvPolynomial.eval₂Hom
        (((toSpec W).appLE ⊤ (coordOpen W i) le_top).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) (c i)) =
        MvPolynomial.eval₂Hom (awayConst W i) (awayCoord W i) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
        exact congrArg (fun k => k.hom r) e
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', hc]
    intro y
    obtain ⟨p, hp⟩ := surjective_eval₂Hom_awayCoord W i ((φ i).hom y)
    exact ⟨p, (hφ i).1 ((RingHom.congr_fun key p).trans hp)⟩

end GlobalTheory.CoordFn
end

