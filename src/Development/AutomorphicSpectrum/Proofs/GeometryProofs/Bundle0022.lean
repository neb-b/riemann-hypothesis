module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0020
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorBtOrder
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_scalar {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of A))
    (x : Spec (CommRingCat.of B) ⟶ X) (φ : A →+* B) (hw : x ≫ π = Spec.map (CommRingCat.ofHom φ))
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (hU : U ≤ π ⁻¹ᵁ ⊤) (b : A) :
    valAt x U h (π.appLE ⊤ U hU ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)) = φ b := by
  have h1 := Scheme.Hom.appLE_comp_appLE x π ⊤ U ⊤ hU h
  have h0 : ∀ (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (e : ⊤ ≤ q ⁻¹ᵁ ⊤),
      q = Spec.map (CommRingCat.ofHom φ) →
      q.appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    rintro q e rfl
    have : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e = (Spec.map (CommRingCat.ofHom φ)).appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [this]
    exact Scheme.ΓSpecIso_naturality _
  have h2 : (π.appLE ⊤ U hU ≫ x.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    rw [h1]
    exact h0 _ _ hw
  have h3 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)) h2
  simpa [valAt] using h3

theorem QFGroup.regularAt_scalar_mul (Γ : QFGroup R T) {f : T → FractionRing R} {g : Γ.G.left} (b : R)
    (H : Γ.RegularAt f g) : Γ.RegularAt (fun t => algebraMap R (FractionRing R) b * f t) g := by
  obtain ⟨U, hg, s, hs⟩ := H
  obtain ⟨π, hπ⟩ : ∃ π : Γ.G.left ⟶ Spec (CommRingCat.of R), π = Γ.G.hom := ⟨_, rfl⟩
  have hU : U ≤ π ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine ⟨U, hg, π.appLE ⊤ U hU ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * s, fun t h => ?_⟩
  have hw : (Γ.pt t).left ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
    rw [hπ]; exact Over.w (Γ.pt t)
  have h1 := valAt_scalar π (Γ.pt t).left (algebraMap R (FractionRing R)) hw U h hU b
  have h2 := hs t h
  show _ = algebraMap R (FractionRing R) b * f t
  rw [← h1, ← h2]
  simp [valAt, map_mul]

theorem QFGroup.compactSpace (Γ : QFGroup R T) : CompactSpace Γ.G.left := by
  obtain ⟨π, hπ⟩ : ∃ π : Γ.G.left ⟶ Spec (CommRingCat.of R), π = Γ.G.hom := ⟨_, rfl⟩
  have : QuasiCompact π := hπ ▸ Γ.quasiCompact
  exact QuasiCompact.compactSpace_of_compactSpace π

theorem QFGroup.exists_denom [Finite T] (Γ : QFGroup R T) (f : T → FractionRing R) :
    ∃ d : R, d ≠ 0 ∧ ∀ g, Γ.RegularAt (fun t => algebraMap R (FractionRing R) d * f t) g := by
  classical
  have := Γ.compactSpace
  have key : ∀ g : Γ.G.left, ∃ d : R, d ≠ 0 ∧ ∃ U : Γ.G.left.Opens, g ∈ U ∧
      ∀ g' ∈ U, Γ.RegularAt (fun t => algebraMap R (FractionRing R) d * f t) g' := by
    intro g
    have hreg : ∃ d : R, d ≠ 0 ∧ Γ.RegularAt (fun t => algebraMap R (FractionRing R) d * f t) g :=
      RegDenom.exists_denom_regularAt R T Γ f g
    obtain ⟨d, hd, U, hg, s, hs⟩ := hreg
    exact ⟨d, hd, U, hg, fun g' hg' => ⟨U, hg', s, hs⟩⟩
  choose d hd U hgU hU using key
  obtain ⟨F, hF⟩ := CompactSpace.elim_nhds_subcover (fun g => (U g : Set Γ.G.left))
    (fun g => (U g).isOpen.mem_nhds (hgU g))
  refine ⟨∏ x ∈ F, d x, Finset.prod_ne_zero_iff.2 fun x _ => hd x, fun g => ?_⟩
  have hg : g ∈ ⋃ x ∈ F, (U x : Set Γ.G.left) := by rw [hF]; trivial
  simp only [Set.mem_iUnion] at hg
  obtain ⟨x, hx, hgx⟩ := hg
  have h1 := Γ.regularAt_scalar_mul (∏ y ∈ F.erase x, d y) (hU x g hgx)
  have h2 : (∏ y ∈ F, d y) = (∏ y ∈ F.erase x, d y) * d x := (Finset.prod_erase_mul F d hx).symm
  rw [h2]
  simpa [map_mul, _root_.mul_assoc] using h1

end GlobalTheory.CompanionTheory.Ar.BT


open Classical in
theorem GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
    (Γ : QFGroup R T), ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ := by
  classical
  intro R _ _ T _ _ Γ
  have := Fintype.ofFinite T
  let δ : T → T → R := fun s h => if h = s then 1 else 0
  choose e he hreg using fun s : T =>
    Γ.exists_denom (fun h => algebraMap R (FractionRing R) (δ s h))
  have hmem : ∀ s, (∏ x, e x) • δ s ∈ Γ.btOrder ⊤ := by
    intro s
    refine Algebra.subset_adjoin ?_
    intro t g _
    have h1 := Γ.regularAt_scalar_mul (∏ y ∈ Finset.univ.erase (t⁻¹ * s), e y) (hreg (t⁻¹ * s) g)
    have h2 : (∏ y, e y) = (∏ y ∈ Finset.univ.erase (t⁻¹ * s), e y) * e (t⁻¹ * s) :=
      (Finset.prod_erase_mul _ e (Finset.mem_univ _)).symm
    have h3 : (fun h => algebraMap R (FractionRing R) (((∏ x, e x) • δ s) (t * h))) =
        fun h => algebraMap R (FractionRing R) (∏ y ∈ Finset.univ.erase (t⁻¹ * s), e y) *
          (algebraMap R (FractionRing R) (e (t⁻¹ * s)) *
            algebraMap R (FractionRing R) (δ (t⁻¹ * s) h)) := by
      funext h
      have h4 : δ s (t * h) = δ (t⁻¹ * s) h := by
        have : t * h = s ↔ h = t⁻¹ * s := by
          constructor
          · rintro rfl; simp
          · rintro rfl; simp
        simp [δ, this]
      rw [Pi.smul_apply, h4, h2, smul_eq_mul, map_mul, map_mul, _root_.mul_assoc]
    rw [h3]
    exact h1
  refine ⟨∏ x, e x, Finset.prod_ne_zero_iff.2 fun x _ => he x, fun f => ?_⟩
  have hf : (∏ x, e x) • f = ∑ s, f s • ((∏ x, e x) • δ s) := by
    funext h
    simp [δ, Finset.sum_apply, _root_.mul_comm]
  rw [hf]
  exact Subalgebra.sum_mem _ fun s _ => Subalgebra.smul_mem _ (hmem s) _
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinitePointExtendsSectionStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_point_extends_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → ∀ t, ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U → ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, (∀ z, σ.left z ∈ U) ∧ toUnit (genPt R) ≫ σ = Γ.pt t := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.exists_section_of_generic_point
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankAdjoinVarsFieldStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_adjoin_vars_field :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (I : Type) (d : ℕ),
      0 < d →
      (letI : Algebra Ω₀ Ω := fn.toAlgebra
       Module.finrank Ω₀ Ω = d) →
      letI : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
        ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra
      Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
        algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q)))
        (FractionRing (MvPolynomial I Ω)) = d := by
  intro Ω₀ Ω _ _ fn I d hd hfin
  let : Algebra Ω₀ Ω := fn.toAlgebra
  have : FiniteDimensional Ω₀ Ω := Module.finite_of_finrank_pos (hfin ▸ hd)
  let : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
    ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra
  have hdegree :=
    GlobalTheory.CompanionTheory.FieldDeg.finrank_fraction_over_adjoin_X_eq Ω₀ Ω I rfl
  exact hdegree.trans hfin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOfFlatSpecialFibre
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.FinAlgFlat

theorem isPushout_cancel (R k A B T U : Type*) [CommRing R] [CommRing k] [CommRing A] [CommRing B]
    [CommRing T] [CommRing U]
    [Algebra R k] [Algebra R A] [Algebra R B] [Algebra R T] [Algebra R U]
    [Algebra A B] [Algebra A T] [Algebra A U] [Algebra B U] [Algebra k T] [Algebra k U]
    [Algebra T U]
    [IsScalarTower R A B] [IsScalarTower R A T] [IsScalarTower R A U] [IsScalarTower R B U]
    [IsScalarTower R k T] [IsScalarTower R k U] [IsScalarTower k T U] [IsScalarTower A T U]
    [IsScalarTower A B U]
    (h₁ : Algebra.IsPushout R A k T) (h₂ : Algebra.IsPushout R B k U) :
    Algebra.IsPushout A B T U := by
  rw [Algebra.isPushout_iff] at h₁ h₂ ⊢
  refine IsBaseChange.of_comp (R := R) (S := A) (T := B)
    (f := (IsScalarTower.toAlgHom R k T).toLinearMap)
    (h := (IsScalarTower.toAlgHom A T U).toLinearMap) h₁ ?_
  convert h₂ using 1
  ext x
  simp [IsScalarTower.algebraMap_apply k T U]

noncomputable abbrev fibreMap (R k A B : Type*) [CommRing R] [CommRing k] [CommRing A] [CommRing B]
    [Algebra R k] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    k ⊗[R] A →+* k ⊗[R] B :=
  (Algebra.TensorProduct.map (AlgHom.id R k) (IsScalarTower.toAlgHom R A B)).toRingHom

theorem fibreMap_isLocalization (R k A B : Type*) [CommRing R] [CommRing k] [CommRing A]
    [CommRing B] [Algebra R k] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (M : Submonoid A) [IsLocalization M B] :
    letI := (fibreMap R k A B).toAlgebra
    IsLocalization (M.map (Algebra.TensorProduct.includeRight : A →ₐ[R] k ⊗[R] A))
      (k ⊗[R] B) := by
  letI iTU : Algebra (k ⊗[R] A) (k ⊗[R] B) := (fibreMap R k A B).toAlgebra
  letI iAT : Algebra A (k ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  letI iBU : Algebra B (k ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  letI iAU : Algebra A (k ⊗[R] B) := ((algebraMap B (k ⊗[R] B)).comp (algebraMap A B)).toAlgebra
  haveI t1 : IsScalarTower A B (k ⊗[R] B) := .of_algebraMap_eq' rfl
  haveI t2 : IsScalarTower A (k ⊗[R] A) (k ⊗[R] B) := .of_algebraMap_eq fun a => by
    change (1 : k) ⊗ₜ[R] (algebraMap A B a) = fibreMap R k A B ((1 : k) ⊗ₜ[R] a)
    simp
  haveI t3 : IsScalarTower R A (k ⊗[R] B) := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B (k ⊗[R] B) r, IsScalarTower.algebraMap_apply R A B r]
    rfl
  haveI t4 : IsScalarTower k (k ⊗[R] A) (k ⊗[R] B) := .of_algebraMap_eq fun a => by
    change a ⊗ₜ[R] (1 : B) = fibreMap R k A B (a ⊗ₜ[R] (1 : A))
    simp
  have h := isPushout_cancel R k A B (k ⊗[R] A) (k ⊗[R] B)
    TensorProduct.isPushout' TensorProduct.isPushout'
  exact (Algebra.isLocalization_iff_isPushout M B).mpr h.symm

end GlobalTheory.CompanionTheory.FinAlgFlat

namespace GlobalTheory.CompanionTheory.FinAlgFlat

theorem fibreMap_flat_localize (R k P Q Bp An : Type*) [CommRing R] [CommRing k] [CommRing P]
    [CommRing Q] [CommRing Bp] [CommRing An] [Algebra R k] [Algebra R P] [Algebra R Q]
    [Algebra R Bp] [Algebra R An] [Algebra P Q] [Algebra P Bp] [Algebra P An] [Algebra Q An]
    [Algebra Bp An] [IsScalarTower R P Q] [IsScalarTower R P Bp] [IsScalarTower R Q An]
    [IsScalarTower R Bp An] [IsScalarTower P Q An] [IsScalarTower P Bp An]
    (M : Submonoid P) [IsLocalization M Bp] (N : Submonoid Q) [IsLocalization N An]
    (h : (fibreMap R k P Q).Flat) : (fibreMap R k Bp An).Flat := by
  have hQA : (fibreMap R k Q An).Flat := by
    have hl := fibreMap_isLocalization R k Q An N
    letI := (fibreMap R k Q An).toAlgebra
    exact IsLocalization.flat (k ⊗[R] An)
      (N.map (Algebra.TensorProduct.includeRight : Q →ₐ[R] k ⊗[R] Q))
  have e : (fibreMap R k Bp An).comp (fibreMap R k P Bp) =
      (fibreMap R k Q An).comp (fibreMap R k P Q) := by
    refine RingHom.ext fun x => ?_
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b =>
      simp [← IsScalarTower.algebraMap_apply]
  have hPA : ((fibreMap R k Bp An).comp (fibreMap R k P Bp)).Flat := by
    rw [e]; exact h.comp hQA
  have hl := fibreMap_isLocalization R k P Bp M
  letI i1 := (fibreMap R k P Bp).toAlgebra
  letI i2 := (fibreMap R k Bp An).toAlgebra
  letI i3 := ((fibreMap R k Bp An).comp (fibreMap R k P Bp)).toAlgebra
  haveI : IsScalarTower (k ⊗[R] P) (k ⊗[R] Bp) (k ⊗[R] An) := .of_algebraMap_eq' rfl
  exact (Module.flat_iff_of_isLocalization (k ⊗[R] Bp)
    (M.map (Algebra.TensorProduct.includeRight : P →ₐ[R] k ⊗[R] P)) (k ⊗[R] An)).mpr hPA

theorem flat_localization_of_fibre (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Algebra P Q] [IsScalarTower R P Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q]
    (h : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat) (n : Ideal Q) [n.IsMaximal] :
    Module.Flat P (Localization.AtPrime n) := by
  haveI : Module.Finite P Q := .of_restrictScalars_finite R P Q
  haveI : Algebra.IsIntegral P Q := inferInstance
  haveI : Algebra.IsIntegral R P := inferInstance
  haveI : IsNoetherianRing P := IsNoetherianRing.of_finite R P
  haveI : IsNoetherianRing Q := IsNoetherianRing.of_finite R Q
  let p : Ideal P := n.comap (algebraMap P Q)
  haveI hp : p.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := P) n
  have hmR : p.comap (algebraMap R P) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) p)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime n) :=
    (Localization.localRingHom p n (algebraMap P Q) rfl).toAlgebra
  haveI tP : IsScalarTower P (Localization.AtPrime p) (Localization.AtPrime n) :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply P Q (Localization.AtPrime n) x]
      exact (Localization.localRingHom_to_map p n (algebraMap P Q) rfl x).symm
  haveI tR : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime n) :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R P (Localization.AtPrime p) x,
        ← IsScalarTower.algebraMap_apply P (Localization.AtPrime p) (Localization.AtPrime n),
        IsScalarTower.algebraMap_apply P Q (Localization.AtPrime n),
        ← IsScalarTower.algebraMap_apply R P Q,
        ← IsScalarTower.algebraMap_apply R Q (Localization.AtPrime n)]
  haveI : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime n) :=
    IsLocalization.isNoetherianRing n.primeCompl _ inferInstance
  haveI : IsLocalHom (algebraMap R (Localization.AtPrime p)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hnu
    have ham : a ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).mpr hnu
    rw [← hmR, Ideal.mem_comap] at ham
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p
      (algebraMap R P a)).mpr ham
    rw [← IsScalarTower.algebraMap_apply R P (Localization.AtPrime p)] at hm
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime n)) :=
    Localization.isLocalHom_localRingHom p n (algebraMap P Q) rfl
  have hfl : Module.Flat R (Localization.AtPrime n) := inferInstance
  have hfib := fibreMap_flat_localize R (IsLocalRing.ResidueField R) P Q (Localization.AtPrime p)
    (Localization.AtPrime n) p.primeCompl n.primeCompl h
  have hBA : Module.Flat (Localization.AtPrime p) (Localization.AtPrime n) :=
    _root_.PositivityTheory.HtPt.Pfib.fibre_crit_ring R (Localization.AtPrime p) (Localization.AtPrime n) hfl hfib
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
    (Localization.AtPrime n)).mp hBA

theorem flat_of_fibreMap_flat (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Algebra P Q] [IsScalarTower R P Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q]
    (h : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat) : Module.Flat P Q :=
  Module.flat_of_isLocalized_maximal Q Q (fun n _ => Localization.AtPrime n)
    (fun n _ => Algebra.linearMap Q _) (fun n _ => flat_localization_of_fibre R P Q h n)

theorem ringHom_flat_of_fibre_flat : ∀ (R P Q : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q] (φ : P →ₐ[R] Q),
    (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom.Flat →
      φ.toRingHom.Flat := by
  intro R P Q _ _ _ _ _ _ _ _ _ _ φ h
  letI : Algebra P Q := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R P Q := .of_algebraMap_eq fun x => (φ.commutes x).symm
  have e : IsScalarTower.toAlgHom R P Q = φ := by ext; rfl
  have h' : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat := by
    rw [fibreMap, e]; exact h
  exact flat_of_fibreMap_flat R P Q h'

end GlobalTheory.CompanionTheory.FinAlgFlat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegAtDom

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']

theorem spec_genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : X) (hq : genPt ξ ⤳ q) :
    Spec.map (CommRingCat.ofHom (genMap ξ ⟨q, hq⟩) : X.presheaf.stalk q ⟶ _) ≫ X.fromSpecStalk q = ξ := by
  show Spec.map (X.presheaf.stalkSpecializes (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ X.fromSpecStalk q = ξ
  have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) ξ
  refine Eq.trans ?_ h2
  refine Eq.trans ?_ (congrArg (fun g => Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ g) h1)
  exact (congrArg (fun g => g ≫ X.fromSpecStalk q) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)

theorem map_genPt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X}
    {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) : f (genPt ξ') = genPt ξ := by
  have h1 : (ξ' ≫ f) (IsLocalRing.closedPoint Ω') =
      (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω') := by rw [show ξ' ≫ f = _ from h]
  have h2 : Spec.map (CommRingCat.ofHom i) (IsLocalRing.closedPoint Ω') = IsLocalRing.closedPoint Ω :=
    Subsingleton.elim (α := PrimeSpectrum Ω) _ _
  exact h1.trans (congrArg ξ h2)

theorem genMap_stalkMap {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X}
    {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) (q : X') (hq : genPt ξ' ⤳ q) (hp : genPt ξ ⤳ f q)
    (s : X.presheaf.stalk (f q)) :
    genMap ξ' ⟨q, hq⟩ ((f.stalkMap q).hom s) = i (genMap ξ ⟨f q, hp⟩ s) := by
  have e : f.stalkMap q ≫ (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) =
      (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) ≫ CommRingCat.ofHom i := by
    apply Spec.map_injective
    have h1 := spec_genMap ξ' q hq
    have h2 := spec_genMap ξ (f q) hp
    generalize (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) = u at h1 ⊢
    generalize (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) = v at h2 ⊢
    have h3 := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := q)
    refine (cancel_mono (X.fromSpecStalk (f q))).1 ?_
    have l : Spec.map (f.stalkMap q ≫ u) ≫ X.fromSpecStalk (f q) = ξ' ≫ f :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        ((congrArg (fun g => Spec.map u ≫ g) h3).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ f) h1)))
    have r : Spec.map (v ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (f q) = Spec.map (CommRingCat.ofHom i) ≫ ξ :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        (congrArg (fun g => Spec.map (CommRingCat.ofHom i) ≫ g) h2)
    exact l.trans (Eq.trans h r.symm)
  exact congrArg (fun g => g.hom s) e

theorem regAt_dominates :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type)
      [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), Dominates ξ' ξ f i →
      ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, (∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧
        (IsCptGen ξ' → ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) := by
  intro X Ω _ ξ X' Ω' _ ξ' f i hd p'
  obtain ⟨q, hq⟩ := p'
  have hp : genPt ξ ⤳ f q := map_genPt hd ▸ hq.map f.continuous
  refine ⟨hp, ?_, fun hg => ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(f.stalkMap q).hom s, genMap_stalkMap hd q hq hp s⟩
  · rintro _ ⟨s, rfl⟩ ⟨h0, -, t, ht⟩
    have hv := genMap_stalkMap hd q hq hp s
    have hone : (f.stalkMap q).hom s * t = 1 := by
      apply hg.inj ⟨q, hq⟩
      rw [map_mul, map_one, hv, ht]
      exact mul_inv_cancel₀ h0
    have hu : IsUnit ((f.stalkMap q).hom s) := IsUnit.of_mul_eq_one _ hone
    exact RegAtMono.unitAt_of_isUnit ξ ⟨f q, hp⟩ (isUnit_of_map_unit (f.stalkMap q).hom s hu)

end GlobalTheory.CompanionTheory.Ar.RegAtDom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomAddMulOfUnitSection
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

variable {S : Scheme.{0}} {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S)
  {P V : Type} [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]
  [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

theorem ext_pair_mod {Z : Over S} (f g : ob x (P × P) ⟶ Z)
    (h₁ : hom x (LinearMap.fst R P P) ≫ f = hom x (LinearMap.fst R P P) ≫ g)
    (h₂ : hom x (LinearMap.snd R P P) ≫ f = hom x (LinearMap.snd R P P) ≫ g) : f = g := by
  ext1
  refine joint_epi (TrivSqZeroExt.map (LinearMap.fst R P P)).toRingHom
    (TrivSqZeroExt.map (LinearMap.snd R P P)).toRingHom ?_ ?_ f.left g.left
    (congrArg CommaMorphism.left h₁) (congrArg CommaMorphism.left h₂)
  · intro a b hab
    have e₁ : TrivSqZeroExt.map (LinearMap.fst R P P) a = TrivSqZeroExt.map (LinearMap.fst R P P) b :=
      congrArg Prod.fst hab
    have e₂ : TrivSqZeroExt.map (LinearMap.snd R P P) a = TrivSqZeroExt.map (LinearMap.snd R P P) b :=
      congrArg Prod.snd hab
    ext
    · simpa using congrArg TrivSqZeroExt.fst e₁
    · simpa using congrArg TrivSqZeroExt.snd e₁
    · simpa using congrArg TrivSqZeroExt.snd e₂
  · intro p
    let q : PrimeSpectrum (TrivSqZeroExt R P) :=
      PrimeSpectrum.comap (TrivSqZeroExt.map (LinearMap.inl R P P)).toRingHom p
    refine ⟨q, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
    change TrivSqZeroExt.map (LinearMap.inl R P P) (TrivSqZeroExt.map (LinearMap.fst R P P) a) ∈ p.asIdeal ↔
      a ∈ p.asIdeal
    set b := TrivSqZeroExt.map (LinearMap.inl R P P) (TrivSqZeroExt.map (LinearMap.fst R P P) a) with hb
    have h0 : (b - a).fst = 0 := by simp [hb]
    have hm : b - a ∈ p.asIdeal := by
      refine p.isPrime.mem_of_pow_mem 2 ?_
      have : (b - a) ^ 2 = 0 := by
        rw [pow_two]
        ext1 <;> simp [h0]
      rw [this]; exact zero_mem _
    constructor
    · intro h; simpa using p.asIdeal.sub_mem h hm
    · intro h; simpa using p.asIdeal.add_mem hm h

theorem hom_add_mod (G : Over S) [GrpObj G] (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1) (f g : P →ₗ[R] V) :
    hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) := by
  have h0 : hom x (0 : P →ₗ[R] P) ≫ u = 1 := by
    rw [hom_zero, Category.assoc, hu, MonObj.comp_one]
  have key : hom x (LinearMap.inl R P P + LinearMap.inr R P P) ≫ u =
      (hom x (LinearMap.inl R P P) ≫ u) * (hom x (LinearMap.inr R P P) ≫ u) := by
    apply ext_pair_mod
    · simp only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.fst_comp_inl,
        LinearMap.fst_comp_inr, add_zero, h0, _root_.mul_one]
    · simp only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.snd_comp_inl,
        LinearMap.snd_comp_inr, zero_add, h0, _root_.one_mul]
  have := congrArg (fun k => hom x (f.coprod g) ≫ k) key
  simpa only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.coprod_inl,
    LinearMap.coprod_inr] using this

theorem hom_add_mod_closed : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G] (P V : Type) [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P] [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (u : ob x P ⟶ G), zsec x ≫ u = 1 → ∀ f g : P →ₗ[R] V, hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) :=
  fun _ _ _ x G _ _ _ _ _ _ _ _ _ _ _ u hu f g => hom_add_mod x G u hu f g

end GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankTranscendenceDegreeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_rank_transcendence_degree : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (I : Type) [Fintype I] (u : I → L),
    AlgebraicIndependent K u → IntermediateField.adjoin K (Set.range u) = ⊤ →
    Module.finrank L (KaehlerDifferential K L) = Fintype.card I := by
  first | exact @GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top | exact GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top | (intros; apply GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regAt_noetherian_model_noetherian : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω), CoordTie o ξ x → (∀ p : Cpt ξ, IsNoetherianRing (regAt ξ p)) ∧ ((∀ q : X, genPt ξ ⤳ q) → IsNoetherian X ∧ IsIntegral X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie | exact GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie <;> assumption)
end

