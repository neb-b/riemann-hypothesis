module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1108
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExtendingRationalGenericFibreMulInt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GenSecInt

open GlobalTheory.PrimSec GlobalTheory.AbLaw

variable {X XK : Scheme.{0}} [IsIntegral X] {f : X ⟶ Sp ℤ} {j : XK ⟶ X} {fK : XK ⟶ Sp ℚ}
  (H : IsPullback j fK f (spMap (algebraMap ℤ ℚ)))
include H

theorem app_injective_of_affine (hc : CharZero Γ(X, ⊤)) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (j.app U).hom := by
  by_cases hne : Nonempty U
  · letI := (j.app U).hom.toAlgebra
    haveI := isLocalization_app H hU
    haveI : CharZero Γ(X, U) :=
      ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hc
    refine IsLocalization.injective (M := (nonZeroDivisors ℤ).map (AbLaw.cst f U)) Γ(XK, j ⁻¹ᵁ U) ?_
    rintro _ ⟨π, hπ, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    have e : AbLaw.cst f U π = (π : Γ(X, U)) := map_intCast _ π
    rw [e, Ne, Int.cast_eq_zero]
    exact nonZeroDivisors.ne_zero hπ
  · haveI : Subsingleton Γ(X, U) := by
      have : U = ⊥ := by
        rw [eq_bot_iff]
        exact fun x hx => (hne ⟨⟨x, hx⟩⟩).elim
      subst this
      infer_instance
    exact fun a b _ => Subsingleton.elim a b

theorem app_injective (hc : CharZero Γ(X, ⊤)) (U : X.Opens) : Function.Injective (j.app U).hom := by
  intro a b h
  refine X.sheaf.eq_of_locally_eq' (fun V : {V : X.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ a b fun V => ?_
  · intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
  · apply app_injective_of_affine H hc V.1.2
    exact (app_rs j V.2 a).trans ((congrArg _ h).trans (app_rs j V.2 b).symm)

theorem exists_extension (hc : CharZero Γ(X, ⊤)) {U : X.Opens} (t : Γ(XK, j ⁻¹ᵁ U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U) (b : Γ(X, V)), x ∈ V ∧
      (j.app V).hom b = rs XK (pre_le j hV) t) :
    ∃ b : Γ(X, U), (j.app U).hom b = t := by
  choose V hV b hx hb using h
  have hcov : U ≤ ⨆ x : U, V x.1 x.2 := fun x hxU =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun x : U => V x.1 x.2) U
    (fun x => homOfLE (hV x.1 x.2)) hcov (fun x => b x.1 x.2) (fun x y => by
      apply app_injective H hc
      refine (app_rs j inf_le_left _).trans (Eq.trans ?_ (app_rs j inf_le_right _).symm)
      rw [hb, hb]
      exact (rs_rs _ _ _).trans (rs_rs _ _ _).symm)
  refine ⟨s, XK.sheaf.eq_of_locally_eq' (fun x : U => j ⁻¹ᵁ V x.1 x.2) (j ⁻¹ᵁ U)
    (fun x => homOfLE fun _ hy => hV x.1 x.2 hy) ?_ _ _ fun x => ?_⟩
  · intro y hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨j y, hy⟩, hx _ hy⟩
  · exact (app_rs j (hV x.1 x.2) s).symm.trans ((congrArg _ (hs x)).trans (hb x.1 x.2))

theorem exists_sec [CompactSpace X] (hc0 : CharZero Γ(X, ⊤)) (B : LB X) (hB : B.IsLB)
    (t : (B.pull j).Sec) : ∃ s : B.Sec, ∀ y : XK,
      j y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  have hx : ∀ x : X, ∃ (i : B.ι) (W : X.Opens), IsAffineOpen W ∧ x ∈ W ∧ W ≤ B.U i := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ i, B.U i from hB.cover ▸ trivial)
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hi (B.U i).isOpen
    exact ⟨i, W, hW, hxW, hWU⟩
  choose ci Wx hWa hxW hWle using hx
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (Wx x : Set X)) (fun x => (Wx x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  choose π b hπ hb using fun x => exists_numerator H (hWa x) (loc t (ci x) (hWle x))
  classical
  let c : ℤ := ∏ x ∈ S, π x
  have hc : algebraMap ℤ ℚ c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact Finset.prod_ne_zero_iff.2 fun x _ => hπ x
  have hb' : ∀ x ∈ S, ∃ b' : Γ(X, Wx x), (j.app (Wx x)).hom b' =
      AbLaw.cst fK (j ⁻¹ᵁ Wx x) (algebraMap ℤ ℚ c) * loc t (ci x) (hWle x) := by
    intro x hxS
    refine ⟨AbLaw.cst f (Wx x) (∏ y ∈ S.erase x, π y) * b x, ?_⟩
    rw [map_mul, app_cst H.w, hb, ← mul_assoc, ← map_mul, ← map_mul, Finset.prod_erase_mul _ _ hxS]
  choose! b' hb' using hb'
  have key : ∀ i, ∃ s : Γ(X, B.U i), (j.app (B.U i)).hom s =
      AbLaw.cst fK (j ⁻¹ᵁ B.U i) (algebraMap ℤ ℚ c) * loc t i le_rfl := by
    intro i
    refine exists_extension H hc0 _ fun x hx => ?_
    obtain ⟨z, hzS, hxz⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    have hV : B.U i ⊓ Wx z ≤ B.U i := inf_le_left
    have hk : B.U i ⊓ Wx z ≤ B.U (ci z) := inf_le_right.trans (hWle z)
    refine ⟨B.U i ⊓ Wx z, hV, rs X (le_inf hV hk) (B.g i (ci z)).val * rs X inf_le_right (b' z), ⟨hx, hxz⟩, ?_⟩
    rw [map_mul, app_rs j (inf_le_right : B.U i ⊓ Wx z ≤ Wx z) (b' z), hb' z hzS, map_mul, rs_cst,
      rs_loc t (ci z) (hWle z) (inf_le_right : B.U i ⊓ Wx z ≤ Wx z), map_mul, rs_cst,
      rs_loc t i le_rfl hV,
      loc_trans t i (ci z) (le_rfl.trans hV) hk]
    ring
  choose s hs using key
  have hunit : ∀ W : XK.Opens, IsUnit (AbLaw.cst fK W (algebraMap ℤ ℚ c)) := fun W =>
    (IsUnit.mk0 _ hc).map _
  refine ⟨⟨s, fun i k => ?_⟩, fun y => ?_⟩
  · apply app_injective H hc0
    change (j.app _).hom (rs X inf_le_left (s i)) = (j.app _).hom (_ * rs X inf_le_right (s k))
    rw [map_mul, app_rs, app_rs, hs, hs, map_mul, map_mul, rs_cst, rs_cst,
      rs_loc t _ _ inf_le_left, rs_loc t _ _ inf_le_right, loc_trans t i k _ inf_le_right, rs_self]
    ring
  · have hmem : ∀ i, y ∈ j ⁻¹ᵁ B.U i →
        (j y ∈ X.basicOpen (s i) ↔ y ∈ XK.basicOpen (t.f (fun _ => i))) := by
      intro i hy
      change y ∈ j ⁻¹ᵁ X.basicOpen (s i) ↔ _
      rw [Scheme.preimage_basicOpen]
      change y ∈ XK.basicOpen ((j.app (B.U i)).hom (s i)) ↔ _
      rw [hs, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (hunit _)]
      exact ⟨fun h => (mem_basicOpen_rs _ _ hy).1 h.2, fun h => ⟨hy, (mem_basicOpen_rs _ _ hy).2 h⟩⟩
    constructor
    · intro h
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ j ⁻¹ᵁ B.U i := X.basicOpen_le (s i) hi
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (hmem i hy).1 hi⟩
    · intro h
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ j ⁻¹ᵁ B.U (k PUnit.unit) := Set.mem_iInter.1 (XK.basicOpen_le (t.f k) hk) PUnit.unit
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k PUnit.unit, (hmem (k PUnit.unit) hy).2 hk⟩

end GlobalTheory.GenSecInt

theorem GlobalTheory.GenSecInt.main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : LB X), B.IsLB → ∀ t : (B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))).Sec, ∃ s : B.Sec, ∀ y : ↥(Limits.pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))), (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  intro k _ X _ p D h B hB t
  haveI := h.isNoetherian
  have H : IsPullback (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
      (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
      (p ≫ spMap (Int.castRingHom k)) (spMap (algebraMap ℤ ℚ)) := IsPullback.of_hasPullback _ _
  exact GlobalTheory.GenSecInt.exists_sec H h.charZero B hB t
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothFiniteTypeSubalgebraInRing
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem Place.exists_smooth_subalgebra : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ')) (S : Finset κ'),
    (∀ x ∈ S, x ∈ F.ring) → ∃ A : Subalgebra ℂ κ', Algebra.Smooth ℂ A ∧
      A.toSubring ≤ F.ring.toSubring ∧ (∀ x ∈ S, x ∈ A) ∧
      ∀ f : κ', ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a := by
  intro κ' _ _ F S hS
  classical
  let R := F.ring
  letI : Algebra ℂ R := F.const.toAlgebra
  haveI : IsScalarTower ℂ R κ' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType ℂ R := F.essFiniteType
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff ℂ R).mp inferInstance
  let R' : Subalgebra ℂ κ' :=
    { F.ring.toSubring with algebraMap_mem' := F.const_mem }
  let T : Set κ' := ((σ.image (fun x : R => (x : κ')) ∪ S : Finset κ') : Set κ')
  let A₀ : Subalgebra ℂ κ' := Algebra.adjoin ℂ T
  have hT : T ⊆ R' := by
    intro x hx
    simp only [T, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe] at hx
    rcases hx with ⟨y, -, rfl⟩ | hx
    · exact y.2
    · exact hS x hx
  have hA₀R : A₀ ≤ R' := Algebra.adjoin_le hT

  have memA₀ : ∀ x : R, x ∈ Algebra.adjoin ℂ (σ : Set R) → (x : κ') ∈ A₀ := by
    intro x hx
    have h1 : (IsScalarTower.toAlgHom ℂ R κ') x ∈
        (Algebra.adjoin ℂ (σ : Set R)).map (IsScalarTower.toAlgHom ℂ R κ') := ⟨x, hx, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    refine Algebra.adjoin_mono ?_ h1
    rintro _ ⟨y, hy, rfl⟩
    simp only [T, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe]
    exact Or.inl ⟨y, hy, rfl⟩
  have hfg : Algebra.FiniteType ℂ A₀ :=
    (Subalgebra.fg_iff_finiteType A₀).mp (Subalgebra.fg_adjoin_finset _)
  haveI : Algebra.FinitePresentation ℂ A₀ := Algebra.FinitePresentation.of_finiteType.mp hfg
  let ι : A₀ →+* R := (A₀.val.toRingHom).codRestrict R (fun x => hA₀R x.2)
  letI : Algebra A₀ R := ι.toAlgebra
  haveI : IsScalarTower ℂ A₀ R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let q : Ideal A₀ := (IsLocalRing.maximalIdeal R).comap ι
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : IsLocalization q.primeCompl R := by
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨t, ht⟩
      by_contra h; exact ht ((IsLocalRing.mem_maximalIdeal _).2 h)
    · intro r
      obtain ⟨t, htA, ht, h⟩ := hσ r
      refine ⟨⟨⟨_, memA₀ _ h⟩, ⟨⟨_, memA₀ _ htA⟩, fun hq => ?_⟩⟩, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).1 hq ht
    · intro x y e
      refine ⟨1, ?_⟩
      have : (x : κ') = y := congrArg (fun z : R => (z : κ')) e
      simp [Subtype.ext this]
  haveI : Algebra.FormallySmooth ℂ R := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ R
  haveI : Algebra.IsSmoothAt ℂ q := by
    have e := (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) R).restrictScalars ℂ
    exact Algebra.FormallySmooth.of_equiv e.symm
  obtain ⟨g, hgq, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth ℂ q
  have hgu : IsUnit (ι g) := by
    by_contra h; exact hgq ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hg0 : (g : κ') ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := hgu.exists_right_inv
    have := congrArg (fun x : R => (x : κ')) hu
    simp [ι, h0] at this
  have hgu' : IsUnit (A₀.val g) := (isUnit_iff_ne_zero).2 hg0
  let φ : Localization.Away g →ₐ[ℂ] κ' := IsLocalization.Away.liftAlgHom g hgu'

  have hφ : ∀ a : A₀, φ (algebraMap A₀ (Localization.Away g) a) = a := by
    intro a; simp [φ]
  have hginv : (g : κ')⁻¹ ∈ F.ring := by
    obtain ⟨u, hu⟩ := hgu.exists_right_inv
    have h1 : (g : κ') * (u : κ') = 1 := by
      have := congrArg (fun x : R => (x : κ')) hu; simpa [ι] using this
    rw [inv_eq_of_mul_eq_one_right h1]; exact u.2
  have hpow : ∀ s ∈ Submonoid.powers g, (s : κ') ≠ 0 ∧ (s : κ')⁻¹ ∈ F.ring := by
    rintro s ⟨n, rfl⟩
    refine ⟨by simpa using pow_ne_zero n hg0, ?_⟩
    simpa [inv_pow] using pow_mem hginv n
  have hrep : ∀ x : Localization.Away g, ∃ a : A₀, ∃ s ∈ Submonoid.powers g,
      φ x * (s : κ') = a := by
    intro x
    obtain ⟨⟨a, s, hs⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) x
    refine ⟨a, s, hs, ?_⟩
    have := congrArg φ e
    rw [map_mul, hφ, hφ] at this
    exact this
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s, hs⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) x
    have h1 := congrArg φ e
    rw [map_mul, hφ, hφ, hx, zero_mul] at h1
    have ha : a = 0 := Subtype.ext h1.symm
    rw [ha, map_zero] at e
    exact (IsLocalization.map_units (Localization.Away g) (⟨s, hs⟩ : Submonoid.powers g)).mul_left_eq_zero.1 e
  let A : Subalgebra ℂ κ' := φ.range
  haveI : Algebra.Smooth ℂ A := Algebra.Smooth.of_equiv (AlgEquiv.ofInjective φ hinj)
  have hA₀A : ∀ a ∈ A₀, a ∈ A := fun a ha => ⟨algebraMap A₀ _ ⟨a, ha⟩, hφ ⟨a, ha⟩⟩
  refine ⟨A, inferInstance, ?_, fun x hx => hA₀A x (Algebra.subset_adjoin ?_), ?_⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨a, s, hs, e⟩ := hrep x
    obtain ⟨hs0, hsi⟩ := hpow s hs
    have : φ x = a * (s : κ')⁻¹ := by rw [← e, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
    show φ x ∈ F.ring
    rw [this]; exact F.ring.mul_mem _ _ (hA₀R a.2) hsi
  · simp only [T, Finset.coe_union, Set.mem_union, Finset.mem_coe]; exact Or.inr hx
  · intro f
    have hfrac : ∃ a ∈ F.ring, ∃ b ∈ F.ring, b ≠ 0 ∧ f * b = a := by
      obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := F.ring) f
      have hb0 : (b : κ') ≠ 0 := fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h)
      refine ⟨a, a.2, b, b.2, hb0, ?_⟩
      rw [← e]
      exact div_mul_cancel₀ _ hb0
    obtain ⟨r1, hr1, r2, hr2, hr20, e⟩ := hfrac
    obtain ⟨t1, ht1A, ht1, h1⟩ := hσ ⟨r1, hr1⟩
    obtain ⟨t2, ht2A, ht2, h2⟩ := hσ ⟨r2, hr2⟩
    have unit_ne : ∀ t : R, IsUnit t → (t : κ') ≠ 0 := by
      intro t ht h0
      obtain ⟨u, hu⟩ := ht.exists_right_inv
      have := congrArg (fun x : R => (x : κ')) hu
      simp [h0] at this
    refine ⟨r1 * t1 * t2, hA₀A _ ?_, r2 * t2 * t1, hA₀A _ ?_, ?_, ?_⟩
    · simpa using A₀.mul_mem (memA₀ _ h1) (memA₀ _ ht2A)
    · simpa using A₀.mul_mem (memA₀ _ h2) (memA₀ _ ht1A)
    · exact mul_ne_zero (mul_ne_zero hr20 (unit_ne _ ht2)) (unit_ne _ ht1)
    · rw [← e]; ring

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpaceOfSignature
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem hasSignature_diag_signs (p q : ℕ) : Formalism.UG.HasSignature
    (Matrix.diagonal fun i : Fin (p + q) => (Examples₂.sgn (decide (p ≤ (i : ℕ))) : ℂ)) p q := by
  have hne : ∀ (i : Fin p) (j : Fin q), Fin.castAdd q i ≠ Fin.natAdd p j := fun i j h => by
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  refine ⟨(finSumFinEquiv (m := p) (n := q)).symm, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply,
      Matrix.one_apply, (Fin.castAdd_injective p q).eq_iff]
    simp [Examples₂.sgn, Nat.not_le.2 i.isLt]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₁₂,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (hne i j)]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₁,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (hne j i).symm]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply,
      Matrix.neg_apply, Matrix.one_apply, (Fin.natAdd_injective q p).eq_iff]
    split_ifs <;> simp [Examples₂.sgn]

theorem exists_isV : ∀ (D : D7) (ν q : ℕ), q ≤ ν → ∃ X : LSp D, X.IsV ν q := by
  intro D ν q h
  obtain ⟨p, rfl⟩ : ∃ p, ν = p + q := ⟨ν - q, by omega⟩
  refine ⟨⟨diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q, GlobalTheory.PlaceModel.latFrame _⟩, rfl, fun τ => ?_,
    fun τ => ?_, GlobalTheory.PlaceModel.isSelfDualC_latFrame _⟩
  · have hg : (diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q).gram.map τ =
        Matrix.diagonal fun i : Fin (p + q) => (Examples₂.sgn (decide (p ≤ (i : ℕ))) : ℂ) := by
      rw [diagSp_gram]
      ext i j
      change τ (if i = j then _ else 0) = if i = j then _ else 0
      by_cases hij : i = j <;> simp [hij, Examples₂.map_sgn]
    change Formalism.UG.HasSignature ((diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q).gram.map τ) p q
    rw [hg]
    exact hasSignature_diag_signs p q
  · rw [Nat.add_sub_cancel]
    rfl

end GlobalTheory.ChiGrid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBelowCMField
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitPlaceExists

theorem exists_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    ∃ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w := by
  intro E _ _ _
  obtain ⟨p, hp, hsplit⟩ := GlobalTheory.SplitRealPrime.exists_prime_isSplitAt E

  have hP : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible

  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have : x = 0 := (FaithfulSMul.algebraMap_injective ℤ (𝓞 E)) (by rw [hx, map_zero])
      rw [this]
      exact Ideal.zero_mem _)
  have hpQ : ((p : ℕ) : 𝓞 E) ∈ Q := by
    have h1 : ((p : ℤ)) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQ]
      exact Ideal.subset_span rfl
    rw [Ideal.mem_comap] at h1
    simpa using h1

  have hQ0 : Q ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int Q
  exact ⟨⟨Q, hQmax.isPrime, hQ0⟩, hsplit _ hpQ⟩

end GlobalTheory.SplitPlaceExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopologicalKrullDimClosurePointLe
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem closure_point_topologicalKrullDim : ∀ (X : Scheme.{0}) (n : ℕ) (z : X), topologicalKrullDim X = n → ∃ e : ℕ, e ≤ n ∧ topologicalKrullDim (closure ({z} : Set X)) = e ∧ ∀ x, z ⤳ x → x ≠ z → 1 ≤ e := by
  intro X n z hX
  set S : Set X := closure ({z} : Set X) with hS
  have hle : topologicalKrullDim S ≤ n := hX ▸ topologicalKrullDim_subspace_le X S
  have hzS : z ∈ S := subset_closure rfl
  haveI : Nonempty S := ⟨⟨z, hzS⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim S := Order.krullDim_nonneg_iff.mpr
    ⟨⟨closure {(⟨z, hzS⟩ : S)}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim S = e := by
    generalize topologicalKrullDim S = d at hle h0 ⊢
    induction d using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := hle
        exact absurd (WithBot.coe_le_coe.mp h') (by simp)
      | coe m => exact ⟨m, rfl⟩
  refine ⟨e, ?_, he, ?_⟩
  · rw [he] at hle; exact_mod_cast hle
  · intro x hzx hxz
    have hxS : x ∈ S := specializes_iff_mem_closure.mp hzx
    let x' : S := ⟨x, hxS⟩
    let z' : S := ⟨z, hzS⟩
    have hsp : z' ⤳ x' := (Topology.IsInducing.subtypeVal.specializes_iff).mp hzx
    have hns : ¬ x' ⤳ z' := fun h => hxz (congrArg Subtype.val (h.antisymm hsp).eq)
    let A : IrreducibleCloseds S := ⟨closure {x'}, isIrreducible_singleton.closure, isClosed_closure⟩
    let B : IrreducibleCloseds S := ⟨closure {z'}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hAB : A < B := by
      refine lt_of_le_of_ne ?_ ?_
      · show closure {x'} ⊆ closure {z'}
        exact specializes_iff_closure_subset.mp hsp
      · intro h
        apply hns
        have : closure ({x'} : Set S) = closure {z'} :=
          congrArg (fun C : IrreducibleCloseds S => (C : Set S)) h
        exact specializes_iff_closure_subset.mpr this.symm.subset
    have h1 : (1 : WithBot ℕ∞) ≤ topologicalKrullDim S := Order.one_le_krullDim_iff.mpr ⟨A, B, hAB⟩
    rw [he] at h1
    exact_mod_cast h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterPolyEqZeroOfIsHomogeneousNeDimStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interPoly_eq_zero_of_isHomogeneous_ne_dim : ∀ (F : Type) [Field F] (Y : Var F) (κ : Type) (gr : κ → Y.Dv) (k : ℕ) (P : MvPolynomial κ ℝ), P.IsHomogeneous k → k ≠ Y.dim → Y.interPoly gr P = 0 := by
  first | exact @GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous | exact GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous | (intros; apply GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous <;> assumption)
end

