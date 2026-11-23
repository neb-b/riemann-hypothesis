module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroSmoothLiftSystemPresents
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys.OfLift

theorem sec_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Smooth s] (U : X.affineOpens) :
    Algebra.Smooth R (Sec s U.1) := by
  have h := HasRingHomProperty.appLE @Smooth s ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h' : RingHom.Smooth ((s.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact RingHom.smooth_algebraMap.mp h'

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}
  {X₀ X : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

theorem surjective_spMap (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (hπ : Function.Surjective π) :
    Surjective (spMap π) := by
  constructor
  intro x
  have hx : (show PrimeSpectrum R from x) ∈ Set.range (PrimeSpectrum.comap π) := by
    refine (range_comap_of_surjective R₀ π hπ).ge ?_
    rw [hk]
    intro a ha
    have h2 : a ^ 2 = 0 := by
      have := Ideal.pow_mem_pow ha 2
      rwa [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact (show PrimeSpectrum R from x).2.mem_of_pow_mem 2 (by rw [h2]; exact zero_mem _)
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

variable (hpb : IsPullback i s₀ s (spMap π)) (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π))

def liftOpen (U : X₀.affineOpens) : X.affineOpens :=
  ⟨(GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose,
    (GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose_spec.1⟩

theorem preimage_liftOpen (U : X₀.affineOpens) : i ⁻¹ᵁ (liftOpen hpb hπ hn U).1 = U.1 :=
  (GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose_spec.2

theorem liftOpen_mono (hi : Function.Surjective i.base) {U V : X₀.affineOpens} (h : V ≤ U) :
    liftOpen hpb hπ hn V ≤ liftOpen hpb hπ hn U := by
  intro x hx
  obtain ⟨y, rfl⟩ := hi x
  have hy : y ∈ i ⁻¹ᵁ (liftOpen hpb hπ hn V).1 := hx
  rw [preimage_liftOpen] at hy
  have hy' : y ∈ i ⁻¹ᵁ (liftOpen hpb hπ hn U).1 := by
    rw [preimage_liftOpen]; exact h hy
  exact hy'

def pr (U : X₀.affineOpens) : GlobalTheory.CechDR.Pair i := ⟨(U, liftOpen hpb hπ hn U), (preimage_liftOpen hpb hπ hn U).ge⟩

end GlobalTheory.LiftSys.OfLift


open GlobalTheory.LiftSys.OfLift in
theorem GlobalTheory.LiftSys.exists_sys_presents : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsPullback i s₀ s (spMap π) → Smooth s → ∃ S : Sys I π s₀, Nonempty (S.Presents s i) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ X s i hpb hsm
  have hn : IsNilpotent (RingHom.ker π) := ⟨2, hk ▸ hI⟩
  haveI := surjective_spMap hI hk hπ
  have hi : Function.Surjective i.base :=
    (MorphismProperty.of_isPullback (P := @Surjective) hpb.flip ‹_›).surj
  let G : AffOp X₀ ⥤ AffOp X :=
    (Monotone.functor (f := liftOpen hpb hπ hn) fun _ _ h ↦ liftOpen_mono hpb hπ hn hi h).op
  let S : Sys I π s₀ :=
    { F := G ⋙ OAff s
      p := fun U ↦ GlobalTheory.CechDR.secPull s s₀ (pr hpb hπ hn U.unop)
      semi := fun U ↦ GlobalTheory.CechDR.semiHom_secPull hpb.w _
      nat := fun {U V} a b ↦ (congrArg (fun t ↦ t.hom b) (i.map_appLE (pr hpb hπ hn V.unop).2
          (homOfLE (liftOpen_mono hpb hπ hn hi (leOfHom a.unop))).op)).trans
        (congrArg (fun t ↦ t.hom b) (i.appLE_map (pr hpb hπ hn U.unop).2 (homOfLE (show V.unop.1 ≤ U.unop.1 from leOfHom a.unop)).op)).symm
      surj := fun U ↦ (GlobalTheory.CechDR.secPull_surjective_and_ker R R₀ I π hπ hk X₀ X s₀ s i hpb (pr hpb hπ hn U.unop) (preimage_liftOpen hpb hπ hn U.unop)).1
      ker := fun U b ↦ (GlobalTheory.CechDR.secPull_surjective_and_ker R R₀ I π hπ hk X₀ X s₀ s i hpb (pr hpb hπ hn U.unop) (preimage_liftOpen hpb hπ hn U.unop)).2 b
      smooth := fun U ↦ sec_smooth s _ }
  exact ⟨S, ⟨⟨fun U ↦ affPt s (liftOpen hpb hπ hn U.unop), fun U ↦ (liftOpen hpb hπ hn U.unop).2.isOpenImmersion_fromSpec, fun U ↦ affPt_w s _,
    fun U V a ↦ affPt_res s _, fun U ↦ GlobalTheory.CechDR.secPull_affPt s s₀ (pr hpb hπ hn U.unop),
    S.cover_of_surjective ⟨hi⟩ _ fun U ↦ GlobalTheory.CechDR.secPull_affPt s s₀ (pr hpb hπ hn U.unop)⟩⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubmersivePresentationAddZeroVariables
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchEnl

open MvPolynomial

theorem ker_aeval_zero_eq_span (D κ : Type) [CommRing D] :
    RingHom.ker (aeval (R := D) (fun _ : κ ↦ (0 : D))) = Ideal.span (Set.range X) := by
  apply le_antisymm
  · intro p hp
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra h
    push_neg at h
    have hm0 : m = 0 := by ext i; simpa using h i (Set.mem_univ i)
    subst hm0
    rw [RingHom.mem_ker] at hp
    have : aeval (R := D) (fun _ : κ ↦ (0 : D)) p = AddMonoidAlgebra.coeff p 0 := by
      first
        | (show MvPolynomial.eval (0 : κ → D) p = _
           exact congrFun (congrArg DFunLike.coe (MvPolynomial.eval_zero (R := D) (σ := κ))) p)
        | (rw [MvPolynomial.aeval_def]; simp [MvPolynomial.eval₂_eq, MvPolynomial.coeff_zero_eq_constantCoeff])
    exact (mem_support_iff.mp hm) (this ▸ hp)
  · rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    simp

noncomputable def zeroPre (D κ : Type) [CommRing D] :
    Algebra.PreSubmersivePresentation D D κ κ where
  val _ := 0
  σ' x := C x
  aeval_val_σ' x := by simp
  relation k := X k
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val]
    exact (ker_aeval_zero_eq_span D κ).symm
  map := id
  map_inj := Function.injective_id

theorem zeroPre_jacobian (D κ : Type) [CommRing D] [Finite κ] : (zeroPre D κ).jacobian = 1 := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have h1 : (zeroPre D κ).jacobiMatrix = 1 := by
    ext i j
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    simp [zeroPre, Matrix.one_apply, pderiv_X, Pi.single_apply, eq_comm]
  rw [h1]
  simp

end GlobalTheory.PinchEnl

theorem GlobalTheory.PinchEnl.exists_submersivePresentation_sum_zero : ∀ (R D ν σ κ : Type) [CommRing R] [CommRing D] [Algebra R D] [Finite ν] [Finite σ] [Finite κ] (P : Algebra.SubmersivePresentation R D ν σ), ∃ P' : Algebra.SubmersivePresentation R D (κ ⊕ ν) (κ ⊕ σ), P'.val = Sum.elim (fun _ ↦ 0) P.val := by
  intro R D ν σ κ _ _ _ _ _ _ P
  let Q : Algebra.SubmersivePresentation D D κ κ :=
    { __ := GlobalTheory.PinchEnl.zeroPre D κ
      jacobian_isUnit := by rw [GlobalTheory.PinchEnl.zeroPre_jacobian]; exact isUnit_one }
  refine ⟨Q.comp P, ?_⟩
  ext i
  rcases i with k | j
  · rfl
  · rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportingFormGapOffSmoothCone
section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.Gap

section Bound

variable {X : Type} [AddCommGroup X] {m : ℕ} {a : Fin m → X}

theorem exists_abs_apply_le (ha : Submodule.span ℤ (Set.range a) = ⊤) (x y : X) :
    ∃ C : ℕ, ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) →
      |β x y| ≤ C * ∑ i, β (a i) (a i) := by
  have hx : x ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top
  have hl : ∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → 0 ≤ ∑ i, β (a i) (a i) :=
    fun β hp => Finset.sum_nonneg fun i _ => hp _
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      refine ⟨1, fun β hs hp => ?_⟩
      have h1 := hp (a i + a j)
      have h2 := hp (a i - a j)
      simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply, hs (a j) (a i)] at h1 h2
      have h3 := Finset.single_le_sum (f := fun i => β (a i) (a i)) (fun i _ => hp _) (Finset.mem_univ i)
      have h4 := Finset.single_le_sum (f := fun i => β (a i) (a i)) (fun i _ => hp _) (Finset.mem_univ j)
      rw [abs_le]
      constructor <;> push_cast <;> linarith
    | zero => exact ⟨0, fun β _ _ => by simp⟩
    | add y z _ _ h1 h2 =>
      obtain ⟨C, hC⟩ := h1
      obtain ⟨C', hC'⟩ := h2
      refine ⟨C + C', fun β hs hp => ?_⟩
      rw [map_add (f := _), Nat.cast_add, add_mul]
      exact (abs_add_le _ _).trans (add_le_add (hC β hs hp) (hC' β hs hp))
    | smul n y _ h1 =>
      obtain ⟨C, hC⟩ := h1
      refine ⟨n.natAbs * C, fun β hs hp => ?_⟩
      rw [map_smul, smul_eq_mul, abs_mul, Nat.cast_mul, Int.natCast_natAbs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC β hs hp) (abs_nonneg _)
  | zero => exact ⟨0, fun β _ _ => by simp⟩
  | add x z _ _ h1 h2 =>
    obtain ⟨C, hC⟩ := h1
    obtain ⟨C', hC'⟩ := h2
    refine ⟨C + C', fun β hs hp => ?_⟩
    rw [map_add (f := _), LinearMap.add_apply, Nat.cast_add, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hC β hs hp) (hC' β hs hp))
  | smul n x _ h1 =>
    obtain ⟨C, hC⟩ := h1
    refine ⟨n.natAbs * C, fun β hs hp => ?_⟩
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, abs_mul, Nat.cast_mul, Int.natCast_natAbs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC β hs hp) (abs_nonneg _)

theorem exists_abs_lin_le [Module.Free ℤ X] [Module.Finite ℤ X] (ha : Submodule.span ℤ (Set.range a) = ⊤)
    (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    ∃ C : ℕ, ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) →
      |lam β| ≤ C * ∑ i, β (a i) (a i) := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let E : _ → _ → LinearMap.BilinForm ℤ X := fun i j => (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)
  have hE : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (b i) (b j) • E i j := fun β =>
    b.ext fun k => b.ext fun l => by
      simp [E, LinearMap.sum_apply, Finsupp.single_apply]
  choose C hC using exists_abs_apply_le ha
  refine ⟨∑ i, ∑ j, C (b i) (b j) * (lam (E i j)).natAbs, fun β hs hp => ?_⟩
  conv_lhs => rw [hE β]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul]
  push_cast
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, mul_right_comm]
  exact mul_le_mul_of_nonneg_right (hC _ _ β hs hp) (abs_nonneg _)

end Bound

section Fan

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem exists_ray_bound (hF : IsPolFanOn bar φ X) :
    ∃ M : ℕ, ∀ ρ : LinearMap.BilinForm ℤ X, IsCone bar φ ![ρ] → φ.evalZ ρ ≤ M := by
  obtain ⟨S, hS, h⟩ := hF.finite
  obtain ⟨M, hM⟩ := (hS.image fun β => φ.evalZ β).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_ge M
  refine ⟨N, fun ρ hρ => ?_⟩
  obtain ⟨e, he⟩ := h 1 _ hρ
  have h1 := hM ⟨_, he 0, rfl⟩
  simp only [evalZ_pull φ (r := e.toLinearMap) e.surjective, Matrix.cons_val_zero] at h1
  exact h1.trans hN

theorem exists_cone_nat [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (hF : IsPolFanOn bar φ X)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y) :
    ∃ (s : ℕ) (δ : Fin s → LinearMap.BilinForm ℤ X) (n : Fin s → ℕ), IsCone bar φ δ ∧ β = ∑ i, n i • δ i := by
  have hB : toReal β ∈ psdCone (bar := bar) (X := X) := by
    simpa using ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (by simp [hβ]) (by simp [hp]) (by simp)
  obtain ⟨m, γ, c, hγ, hc, hsum⟩ := hF.cover _ hB
  obtain ⟨nZ, hnZ⟩ := Cover.coeff_int hγ.mem hγ.basis hβ hsum
  have hn0 : ∀ i, 0 ≤ nZ i := fun i => by exact_mod_cast (hnZ i) ▸ hc i
  let n : Fin m → ℕ := fun i => (nZ i).toNat
  have hn : ∀ i, ((n i : ℤ) : ℝ) = c i := fun i => by simp [n, Int.toNat_of_nonneg (hn0 i), hnZ i]
  refine ⟨m, γ, n, hγ, LinearMap.ext₂ fun a b => ?_⟩
  have h1 := LinearMap.congr_fun₂ hsum a b
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ← hn] at h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul]
  exact_mod_cast h1

end Fan

theorem exists_gap : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a : Fin m → X), IsCone bar φ γ → Supports bar φ d γ a → ∀ lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ j, 0 ≤ lam (γ j)) → ∀ K : ℤ, ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (D * d : ℝ) * φ.evalZ β ≤ (D * ∑ i, β (a i) (a i) + lam β : ℤ)) ∧ ∀ (ρ : LinearMap.BilinForm ℤ X), IsCone bar φ ![ρ] → (∀ j, ρ ≠ γ j) → (D * d : ℝ) * φ.evalZ ρ + K ≤ (D * ∑ i, ρ (a i) (a i) + lam ρ : ℤ) := by
  intro O _ _ _ _ bar φ d X _ _ _ _ _ _ hF r m γ a hγ hS lam hlam K
  obtain ⟨C, hC⟩ := exists_abs_lin_le hS.span lam
  obtain ⟨M, hM⟩ := exists_ray_bound hF
  refine ⟨C + K.natAbs + C * d * M, fun D hD => ?_⟩
  have hray : ∀ ρ : LinearMap.BilinForm ℤ X, IsCone bar φ ![ρ] → (∀ j, ρ ≠ γ j) →
      (D * d : ℝ) * φ.evalZ ρ + (K.natAbs : ℕ) ≤ (D * ∑ i, ρ (a i) (a i) + lam ρ : ℤ) := by
    intro ρ hρ hne
    have hm : ρ ∈ balForms bar X := hρ.mem 0
    have hp : ∀ y, 0 ≤ ρ y y := hρ.nonneg 0
    obtain ⟨n, hn⟩ := hF.exists_nat hm hp
    have h1 := hS.le ρ hm hp
    have h2 : (d : ℝ) * φ.evalZ ρ ≠ (∑ i, ρ (a i) (a i) : ℤ) := fun he => by
      obtain ⟨k, c, hk, hc⟩ := hS.only ρ hm hp he
      obtain ⟨j, hj⟩ := intCone_face O bar φ X hF 1 r ![ρ] γ hρ hγ ![k] c (by simp [hk]) (by simpa using hc) 0
      exact hne j hj
    have h3 := hM ρ hρ
    have h4 := (abs_le.1 (hC ρ hm.1 hp)).1
    rw [hn] at h1 h2 h3 ⊢
    generalize ∑ i, ρ (a i) (a i) = L at *
    have h1' : (d : ℤ) * n ≤ L := by exact_mod_cast h1
    have h2' : (d : ℤ) * n ≠ L := by exact_mod_cast h2
    have h3' : (n : ℤ) ≤ M := by exact_mod_cast h3
    have hD' : (C : ℤ) + (K.natAbs : ℕ) + C * d * M ≤ D := by exact_mod_cast hD
    have h5 : 0 ≤ L - d * n - 1 := by omega
    have h6 : (C : ℤ) * d * n ≤ C * d * M := mul_le_mul_of_nonneg_left h3' (by positivity)
    have h7 : (0 : ℤ) ≤ C * d * M := by positivity
    have h8 : (0 : ℤ) ≤ (K.natAbs : ℕ) := by positivity
    have h9 : 0 ≤ ((D : ℤ) - C) * (L - d * n - 1) := mul_nonneg (by linarith) h5
    have : (D * d : ℤ) * n + (K.natAbs : ℕ) ≤ D * L + lam ρ := by nlinarith
    have h10 := (Int.cast_le (R := ℝ)).2 this
    rwa [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast,
      Int.cast_natCast] at h10
  refine ⟨fun β hβ hp => ?_, fun ρ hρ hne => le_trans ?_ (hray ρ hρ hne)⟩
  · obtain ⟨s, δ, n, hδ, rfl⟩ := exists_cone_nat hF hβ hp
    have hall : ∀ i, (D * d : ℝ) * φ.evalZ (δ i) ≤ (D * ∑ l, δ i (a l) (a l) + lam (δ i) : ℤ) := by
      intro i
      by_cases h : ∃ j, δ i = γ j
      · obtain ⟨j, hj⟩ := h
        rw [hj, mul_assoc, hS.eq j]
        have := hlam j
        exact_mod_cast (le_add_of_nonneg_right this)
      · push_neg at h
        have hc : IsCone bar φ ![δ i] := by
          have := hF.face _ _ δ ⟨fun _ : Fin 1 => i, fun _ _ _ => Subsingleton.elim _ _⟩ hδ
          convert this using 1
          funext u
          fin_cases u
          rfl
        exact le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) (hray _ hc h)
    rw [intCone_evalZ_sum hδ.linear, Finset.mul_sum]
    have e : (D * ∑ l, (∑ i, n i • δ i) (a l) (a l) + lam (∑ i, n i • δ i) : ℤ) =
        ∑ i, (n i : ℤ) * (D * ∑ l, δ i (a l) (a l) + lam (δ i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_nsmul, nsmul_eq_mul, mul_add,
        Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e, Int.cast_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Int.cast_mul, Int.cast_natCast, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hall i) (Nat.cast_nonneg _)
  · have : (K : ℝ) ≤ (K.natAbs : ℕ) := by
      have h := (Int.cast_le (R := ℝ)).2 (Int.le_natAbs : K ≤ (K.natAbs : ℕ))
      rwa [Int.cast_natCast] at h
    linarith

end GlobalTheory.Poinc.Gap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportingTupleSmoothConeCmField
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc NumberField

namespace GlobalTheory.Poinc

theorem exists_supports_cm : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (φ : InvFun (NumberField.RingOfIntegers E)) (X : Type) [AddCommGroup X]
    [Module (NumberField.RingOfIntegers E) X] [Module.Finite (NumberField.RingOfIntegers E) X]
    [Module.Projective (NumberField.RingOfIntegers E) X], IsPolFanOn H.bar φ X →
    ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone H.bar φ γ →
      ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧ Supports H.bar φ d γ a := by
  intro E _ _ _ H φ X _ _ _ _ hP r γ hγ
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  haveI : Module.Flat ℤ X := Module.Flat.trans ℤ (𝓞 E) X
  haveI : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨n, c, b, T, hc, hT, hbal, hsum0, hTpos⟩ := _root_.GlobalTheory.exists_cm_trace_tensor E H
  obtain ⟨P, hPbal, hPc, hPsq⟩ := _root_.GlobalTheory.Poinc.exists_avg_proj_balForms (𝓞 E) H.bar X n c b T hc hT hbal hsum0 hTpos
  have hpos : ∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → 0 < (ℓ ∘ₗ P) (sqForm l) := by
    intro l hl
    obtain ⟨hne, hpsd⟩ := hPsq l hl
    have hb := hPbal (sqForm l) fun x y => by simp [mul_comm]
    have h4 := hP.pos _ hb hpsd hne
    have h5 := h2 _ hb hpsd
    have h6 : (0 : ℝ) < ℓ (P (sqForm l)) := lt_of_lt_of_le (by positivity) h5
    exact_mod_cast h6
  obtain ⟨D, m, a, hD, hspan, hsum⟩ := _root_.GlobalTheory.Poinc.SumSqFunctional.sumsq_functional X (ℓ ∘ₗ P) hpos
  have key : ∀ β ∈ balForms H.bar X, ∑ i, β (a i) (a i) = ((D * c : ℕ) : ℤ) * ℓ β := by
    intro β hβ
    rw [hsum β hβ.1, LinearMap.comp_apply, hPc β hβ, map_zsmul, smul_eq_mul]
    push_cast; ring
  have hDc : (0 : ℝ) < ((D * c : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hD hc
  refine ⟨N * (D * c), m, a, Nat.mul_pos hN (Nat.mul_pos hD hc),
    ⟨hspan, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => ?_⟩⟩
  · rw [key β hβ]
    have := h2 β hβ hp
    push_cast at this hDc ⊢
    nlinarith
  · rw [key _ (hγ.mem j)]
    push_cast
    rw [h1 j]; ring
  · rw [key β hβ] at he
    refine h3 β hβ hp ?_
    push_cast at he hDc
    have : ((D : ℝ) * c) * (N * φ.evalZ β) = ((D : ℝ) * c) * ℓ β := by rw [← he]; ring
    exact mul_left_cancel₀ hDc.ne' this

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricRigidifiedTranslateAmpleKTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymTranslate

open GlobalTheory.CechPic (cls)

theorem exists_sym_translate : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (b : 𝟙_ _ ⟶ B), IsAbelianScheme B → M.IsLB → RelAmple B M → KTriv B M → (∃ t : LB.Gen (Theta B M), t.IsGen) → LBIso (M.pull (ι[B]).left) (M.pull ((toUnit B ≫ b ^ 2) * 𝟙 B).left) → ∃ L : LB B.left, L.IsLB ∧ Rigidified B L ∧ Out.Sym B L ∧ RelAmple B L ∧ KTriv B L ∧ LBIso (abelian₂ B L) (abelian₂ B M) := by
  intro A _ _ _ B _ _ M b hB hM hamp hK hT hiso
  have := hB.proper
  obtain ⟨c, hc⟩ := hT
  have hL' : (GlobalTheory.RigidTranslate.rigTransl M b).IsLB := LB.isLB_linComb hM _ _
  refine ⟨GlobalTheory.RigidTranslate.rigTransl M b, hL', GlobalTheory.RigidTranslate.rigidified_rigTransl hM, ?_,
    GlobalTheory.RigidTranslate.relAmple_rigTransl_of_section b hM hamp, GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ B M hM b hK, ?_⟩
  · have h2 : CechPic.pull (GrpObj.inv : B ⟶ B).left (cls M hM) =
        CechPic.pull ((toUnit B ≫ b ^ 2) * 𝟙 B).left (cls M hM) :=
      (CechPic.cls_eq_iff (pull_isLB hM _) (pull_isLB hM _)).2 hiso
    have h3 := congrArg (CechPic.pull (𝟙 B * (toUnit B ≫ b)⁻¹).left) h2
    rw [← CechPic.pull_comp, ← CechPic.pull_comp, ← Over.comp_left, ← Over.comp_left] at h3
    have e1 : (𝟙 B * (toUnit B ≫ b)⁻¹) ≫ (GrpObj.inv : B ⟶ B) =
        (GrpObj.inv : B ⟶ B) ≫ (𝟙 B * (toUnit B ≫ b)) := by
      rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv, inv_inv,
        Hom.inv_def, Category.id_comp]
    have e2 : (𝟙 B * (toUnit B ≫ b)⁻¹) ≫ ((toUnit B ≫ b ^ 2) * 𝟙 B) = 𝟙 B * (toUnit B ≫ b) := by
      rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, MonObj.comp_pow, sq,
        _root_.mul_comm (𝟙 B), _root_.mul_comm (𝟙 B), _root_.mul_assoc, mul_inv_cancel_left]
    rw [e1, e2, Over.comp_left, CechPic.pull_comp] at h3
    have e3 : (GrpObj.inv : B ⟶ B).left ≫ (toUnit B ≫ b).left = (toUnit B ≫ b).left := by
      rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
    have h4 : cls _ hL' = CechPic.pull (𝟙 B * (toUnit B ≫ b)).left (cls M hM) -
        CechPic.pull (toUnit B ≫ b).left (cls M hM) := by
      rw [CechPic.cls_linComb hM, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg]
      rfl
    refine GlobalTheory.RigSymSubring.sym_of_cls hL' ?_
    rw [h4, map_sub, h3, ← CechPic.pull_comp, e3]
  · have hΛ : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
    refine (CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) hΛ).1
      (((CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) (pull_isLB hΛ _)).2
        (GlobalTheory.RigidTranslate.lam_rigTransl hM c hc)).trans ?_)
    rw [CechPic.cls_pull hΛ]
    exact CechPic.pull_id _

end GlobalTheory.SymTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLineBundleTrivialBasicOpenOfTrivialFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLineBundle_trivial_basicOpen_of_trivial_fibre : (∀ (T : Type) [CommRing T] [IsLocalRing T] (e : T), (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T → ∀ (A : Over (Sp T)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ k : ℕ, IsUnit (k : T) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (f' : X' ⟶ Sp (T ⧸ Ideal.span {e})), IsPullback π f' A.hom (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → (∃ t : (M.pull π).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  first | (exact @GlobalTheory.TorsionSpread.triv_basicOpen_of_triv_fibre) | (exact GlobalTheory.TorsionSpread.triv_basicOpen_of_triv_fibre) | (intros; apply GlobalTheory.TorsionSpread.triv_basicOpen_of_triv_fibre <;> assumption)
end

