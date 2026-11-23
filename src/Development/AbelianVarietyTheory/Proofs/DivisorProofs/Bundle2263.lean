module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2161
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLocalGeneratorNearFiniteSet
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch.Semiloc

theorem exists_basicOpen_cover : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∃ (J : Type) (_ : Fintype J) (f : J → Γ(X, W)) (k : J → L.ι), (∀ j, X.basicOpen (f j) ≤ L.U (k j)) ∧ ∀ x ∈ W, ∃ j, x ∈ X.basicOpen (f j) := by
  intro X L hL W hW
  classical
  have h : ∀ x : W, ∃ (f : Γ(X, W)) (i : L.ι), X.basicOpen f ≤ L.U i ∧ (x : X) ∈ X.basicOpen f := by
    intro x
    obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (x : X)
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le (V := L.U i) ⟨x, hi⟩ x.2
    exact ⟨f, i, hf, hxf⟩
  choose f i hf hx using h
  obtain ⟨s, hs⟩ := hW.isCompact.elim_finite_subcover (fun x : W => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).isOpen) (fun x hxW => Set.mem_iUnion.2 ⟨⟨x, hxW⟩, hx ⟨x, hxW⟩⟩)
  refine ⟨s, inferInstance, fun j => f j, fun j => i j, fun j => hf j, fun x hx => ?_⟩
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 (hs hx)
  exact ⟨⟨j, hj⟩, hxj⟩

theorem exists_separating : ∀ (X : Scheme.{0}) (W : X.Opens), IsAffineOpen W → ∀ (F : Set X), F.Finite → F ⊆ W → (∀ x ∈ F, ∀ y ∈ F, y ⤳ x → y = x) → ∃ a : X → Γ(X, W), (∀ x ∈ F, x ∈ X.basicOpen (a x)) ∧ ∀ x ∈ F, ∀ y ∈ F, y ≠ x → y ∉ X.basicOpen (a x) := by
  intro X W hW F hF hFW hsp
  classical
  have hb : ∀ x ∈ F, ∀ y ∈ F, y ≠ x → ∃ b : Γ(X, W), x ∈ X.basicOpen b ∧ y ∉ X.basicOpen b := by
    intro x hx y hy hne
    have hn : ¬ y ⤳ x := fun h => hne (hsp x hx y hy h)
    rw [specializes_iff_forall_open] at hn
    push Not at hn
    obtain ⟨O, hO, hxO, hyO⟩ := hn
    obtain ⟨b, hbO, hxb⟩ := hW.exists_basicOpen_le (V := ⟨O, hO⟩) ⟨x, hxO⟩ (hFW hx)
    exact ⟨b, hxb, fun h => hyO (hbO h)⟩
  choose! b hb1 hb2 using hb
  refine ⟨fun x => ∏ y ∈ hF.toFinset.erase x, b x y, fun x hx => ?_, fun x hx y hy hne h => ?_⟩
  · refine Finset.prod_induction _ (fun c => x ∈ X.basicOpen c) (fun c d hc hd => ?_) ?_ (fun y hy => ?_)
    · rw [Scheme.basicOpen_mul]; exact ⟨hc, hd⟩
    · rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; exact hFW hx
    · obtain ⟨hyx, hyF⟩ := Finset.mem_erase.1 hy
      exact hb1 x hx y (hF.mem_toFinset.1 hyF) hyx
  · have hmem : y ∈ hF.toFinset.erase x := Finset.mem_erase.2 ⟨hne, hF.mem_toFinset.2 hy⟩
    dsimp only at h
    rw [← Finset.mul_prod_erase _ _ hmem, Scheme.basicOpen_mul] at h
    exact hb2 x hx y hy hne h.1

theorem exists_locGen_near_finite : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a := by
  intro X L hL W hW F hF hFW
  classical
  obtain ⟨J, _, f, k, hk, hcov⟩ := exists_basicOpen_cover X L hL W hW
  set F' : Set X := {x | x ∈ F ∧ ∀ y ∈ F, x ⤳ y → y = x} with hF'
  have hF'F : F' ⊆ F := fun x hx => hx.1
  have hF'fin : F'.Finite := hF.subset hF'F
  have hup : ∀ x ∈ F, ∃ x' ∈ F', x ⤳ x' := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.Finite.exists_minimalFor (fun y : X => closure ({y} : Set X)) {y | y ∈ F ∧ x ⤳ y}
      (hF.subset fun y hy => hy.1) ⟨x, hx, specializes_rfl⟩
    refine ⟨i, ⟨hi.1.1, fun y hy hiy => ?_⟩, hi.1.2⟩
    have h1 : closure ({y} : Set X) ⊆ closure {i} := specializes_iff_closure_subset.1 hiy
    have h2 := hi.2 ⟨hy, hi.1.2.trans hiy⟩ h1
    exact ((specializes_iff_closure_subset.2 h2).antisymm hiy).eq
  obtain ⟨a, ha, ha'⟩ := exists_separating X W hW F' hF'fin (hF'F.trans hFW)
    (fun x hx y hy hyx => (hy.2 x hx.1 hyx).symm)
  have hE : ∀ x : X, ∃ e : ∀ j, Γ(X, X.basicOpen (f j)), x ∈ W →
      GlobalTheory.Pinch.IsSecFam L (fun j => X.basicOpen (f j)) k hk e ∧
        ∀ j (h : x ∈ X.basicOpen (f j)), IsUnit ((X.presheaf.germ (X.basicOpen (f j)) x h).hom (e j)) := by
    intro x
    by_cases hx : x ∈ W
    · obtain ⟨e, he⟩ := _root_.GlobalTheory.Pinch.SemiLoc.exists_secFam_isUnit_germ X L hL W hW J f k hk x hx
      exact ⟨e, fun _ => he⟩
    · exact ⟨fun _ => 0, fun h => absurd h hx⟩
  choose E hE using hE
  obtain ⟨e, he, heu⟩ := _root_.GlobalTheory.Pinch.secFam_unit_at_finite X L W J (fun j => X.basicOpen (f j)) (fun j => X.basicOpen_le (f j)) k hk F'
    hF'fin a ha ha' E (fun x hx => (hE x (hFW (hF'F hx))).1) (fun x hx => (hE x (hFW (hF'F hx))).2)
  obtain ⟨V, u, hV, hgen⟩ := _root_.GlobalTheory.Pinch.exists_locGen_of_secFam X L hL J (fun j => X.basicOpen (f j)) k hk e he
  refine ⟨V, u, fun x hx => ?_, hgen⟩
  obtain ⟨x', hx', hxx'⟩ := hup x hx
  obtain ⟨j, hj⟩ := hcov x' (hFW (hF'F hx'))
  exact hxx'.mem_open V.isOpen (hV j x' hj (heu x' hx' j hj))

end GlobalTheory.Pinch.Semiloc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalNormalDomainFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open scoped Pointwise

namespace GlobalTheory.LocalNormalExt

theorem exists_eq_of_mul_mem_integralClosure
    (R K K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Algebra R K'] [IsScalarTower R K K']
    (P : Ideal (integralClosure R K')) [P.IsMaximal]
    (x : K) (s : integralClosure R K') (hs : s ∉ P)
    (hx : algebraMap K K' x * (s : K') ∈ integralClosure R K') :
    ∃ r : R, algebraMap R K r = x := by
  classical
  let L := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R K' L := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R K K', ← IsScalarTower.algebraMap_apply K K' L]; rfl)
  haveI : FiniteDimensional K L := inferInstance
  haveI : IsGalois K L := inferInstance
  haveI : IsScalarTower R R L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let S := integralClosure R L
  let C := integralClosure R K'
  haveI : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
  let f : C →ₐ[R] S := ((IsScalarTower.toAlgHom R K' L).comp C.val).codRestrict S
    (fun c => (c.2 : IsIntegral R (c : K')).map (IsScalarTower.toAlgHom R K' L))
  have hfv : ∀ c : C, ((f c : S) : L) = algebraMap K' L (c : K') := fun _ => rfl
  have hfinj : Function.Injective f := by
    intro c d h
    have := congrArg (fun u : S => (u : L)) h
    simp only [hfv] at this
    exact Subtype.ext ((algebraMap K' L).injective this)
  letI : Algebra C S := f.toRingHom.toAlgebra
  haveI : IsScalarTower R C S := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : Algebra.IsIntegral C S := ⟨fun u => (Algebra.IsIntegral.isIntegral (R := R) u).tower_top⟩
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) P
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap C S)).mp hfinj]; exact bot_le)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  let J : Ideal S :=
    { carrier := {u | ∃ v : S, u * algebraMap R S a = algebraMap R S b * v}
      add_mem' := by
        rintro u₁ u₂ ⟨v₁, h₁⟩ ⟨v₂, h₂⟩
        exact ⟨v₁ + v₂, by rw [add_mul, h₁, h₂, mul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c u ⟨v, h⟩
        exact ⟨c * v, by rw [smul_eq_mul, _root_.mul_assoc, h, mul_left_comm]⟩ }
  have hJg : ∀ (g : S ≃ₐ[R] S) (u : S), u ∈ J → g u ∈ J := by
    rintro g u ⟨v, h⟩
    exact ⟨g v, by rw [← g.commutes a, ← g.commutes b, ← map_mul, h, map_mul]⟩

  have e1 : ∀ r : R, ((algebraMap R S r : S) : L) = algebraMap K L (algebraMap R K r) :=
    fun _ => rfl
  have hbL : algebraMap K L (algebraMap R K b) ≠ 0 := (map_ne_zero _).mpr hb0
  have htJ : f s ∈ J := by
    refine ⟨f ⟨_, hx⟩, ?_⟩
    apply Subtype.ext
    show (f s : L) * ((algebraMap R S a : S) : L) = ((algebraMap R S b : S) : L) * (f ⟨_, hx⟩ : L)
    rw [hfv, hfv, e1, e1]
    simp only [map_mul]
    rw [← IsScalarTower.algebraMap_apply K K' L, ← hab, map_div₀]
    field_simp
  have hmax : ∀ (I : Ideal S) [I.IsMaximal], I.under R = IsLocalRing.maximalIdeal R :=
    fun I _ => IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) I)
  have hJtop : J = ⊤ := by
    by_contra hne
    obtain ⟨N, hNmax, hJN⟩ := Ideal.exists_le_maximal J hne
    haveI : Finite (S ≃ₐ[R] S) := Finite.of_equiv _ (galRestrict R K L S).toEquiv
    haveI : Algebra.IsInvariant R S (S ≃ₐ[R] S) := Algebra.isInvariant_of_isGalois' R K L S
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := R) (B := S) (G := S ≃ₐ[R] S) Q N
      ((hmax Q).trans (hmax N).symm)
    set_option synthInstance.maxHeartbeats 200000 in
    have h1 : g • f s ∈ g • Q := by
      rw [← hg]; exact hJN (hJg g _ htJ)
    have h2 : f s ∈ Q := (Ideal.smul_mem_pointwise_smul_iff).mp h1
    exact hs (by rw [← hQ]; exact h2)
  obtain ⟨v, hv⟩ : (1 : S) ∈ J := hJtop ▸ Submodule.mem_top
  have hvL : (v : L) = algebraMap K L x := by
    have := congrArg (fun u : S => (u : L)) hv
    simp only [_root_.one_mul, Subalgebra.coe_mul, e1] at this
    rw [← hab, map_div₀, this]
    field_simp
  have hint : IsIntegral R (algebraMap K L x) := hvL ▸ v.2
  have hxint : IsIntegral R x :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).mp hint
  exact IsIntegrallyClosed.isIntegral_iff.mp hxint

theorem exists_local_normal_domain_of_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (K' : Type) [Field K'] [Algebra (FractionRing R) K'] [FiniteDimensional (FractionRing R) K'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (ρ : R →+* R') (e : FractionRing R' ≃+* K'), IsLocalHom ρ ∧ Function.Injective ρ ∧ (∀ r, e (algebraMap R' _ (ρ r)) = algebraMap (FractionRing R) K' (algebraMap R _ r)) ∧ ∀ (x : FractionRing R) (w : R'), e (algebraMap R' _ w) = algebraMap (FractionRing R) K' x → ∃ r : R, algebraMap R _ r = x := by
  intro R _ _ _ _ _ _ K' _ _ _
  classical
  let K := FractionRing R
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  letI : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let C := integralClosure R K'
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension K K'
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  haveI : IsNoetherianRing C := IsIntegralClosure.isNoetherianRing R K K' C
  haveI : IsDomain C := inferInstance
  obtain ⟨m', hm'⟩ := Ideal.exists_maximal C
  obtain ⟨R', _, _, _⟩ : ∃ (R' : Type) (_ : CommRing R') (_ : Algebra C R'),
      IsLocalization.AtPrime R' m' :=
    ⟨Localization.AtPrime m', inferInstance, inferInstance, inferInstance⟩
  haveI : IsLocalRing R' := IsLocalization.AtPrime.isLocalRing R' m'
  haveI : IsDomain R' :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := m'.primeCompl) (S := R') m'.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing R' := IsLocalization.isNoetherianRing m'.primeCompl R' inferInstance
  haveI : IsIntegrallyClosed R' :=
    isIntegrallyClosed_of_isLocalization R' m'.primeCompl m'.primeCompl_le_nonZeroDivisors
  letI : Algebra R' K' := (IsLocalization.lift (M := m'.primeCompl) (S := R') (g := algebraMap C K')
    (fun y => IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C K')).mpr
      (fun h => y.2 (h ▸ m'.zero_mem))))).toAlgebra
  haveI : IsScalarTower C R' K' :=
    IsScalarTower.of_algebraMap_eq (fun c => (IsLocalization.lift_eq _ c).symm)
  haveI : IsFractionRing R' K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m'.primeCompl R' K'
  let e : FractionRing R' ≃+* K' :=
    (FractionRing.algEquiv R' K').toRingEquiv
  have he : ∀ w : R', e (algebraMap R' _ w) = algebraMap R' K' w := fun w =>
    (FractionRing.algEquiv R' K').commutes w
  have hRC : ∀ r : R, algebraMap C K' (algebraMap R C r) = algebraMap K K' (algebraMap R K r) :=
    fun _ => rfl
  have hinjRC : Function.Injective (algebraMap R C) := by
    intro a b h
    have := congrArg (algebraMap C K') h
    rw [hRC, hRC] at this
    exact IsFractionRing.injective R K ((algebraMap K K').injective this)
  have hinjCR' : Function.Injective (algebraMap C R') :=
    IsLocalization.injective R' m'.primeCompl_le_nonZeroDivisors
  have hcomap : m'.comap (algebraMap R C) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) m')
  refine ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap C R').comp (algebraMap R C), e, ?_, hinjCR'.comp hinjRC, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    by_contra hnu
    have h1 : algebraMap R C r ∈ m' := by
      rw [← Ideal.mem_comap, hcomap]; exact hnu
    have h2 : algebraMap C R' (algebraMap R C r) ∈ IsLocalRing.maximalIdeal R' := by
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff R' m']; exact h1
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 hr
  · intro r
    rw [he]
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply C R' K', hRC]
  · intro x w hw
    rw [he] at hw
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective m'.primeCompl w
    have hmul : algebraMap K K' x * (s : C) = (c : K') := by
      rw [← hw]
      have := congrArg (algebraMap R' K') (IsLocalization.mk'_spec R' c s)
      rw [map_mul, ← IsScalarTower.algebraMap_apply C R' K', ← IsScalarTower.algebraMap_apply C R' K'] at this
      exact this
    exact exists_eq_of_mul_mem_integralClosure R K K' m' x (s : C) s.2 (hmul ▸ c.2)

end GlobalTheory.LocalNormalExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFibreOfGeometricLifting
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_mem_fibre_of_geometric_lifting :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (S P' X : Scheme.{0}) (π : S ⟶ Sp R) (h : P' ⟶ Sp R) (a : X ⟶ P') (q : X ⟶ S), Surjective π → ∀ x : P', h x = closedPoint R → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ h = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ q = s) → ∃ z : X, a z = x := by
  intro R _ _ S P' X π h a q hπ x hx H
  obtain ⟨s₀, hs₀⟩ := π.surjective (h x)
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := h) (g := π) x s₀ hs₀.symm
  let Ω : Type := AlgebraicClosure ((pullback h π).residueField w)
  let t : Sp Ω ⟶ pullback h π :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback h π).residueField w) Ω)) ≫
      (pullback h π).fromSpecResidueField w
  have ht : ∀ y, t y = w := by
    intro y
    simp only [t, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hξ : ∀ y, (t ≫ pullback.fst h π) y = x := by
    intro y
    rw [Scheme.Hom.comp_apply, ht, hw]
  obtain ⟨p, hp, -⟩ := H Ω (t ≫ pullback.fst h π) (t ≫ pullback.snd h π)
    (by
      ext y
      constructor
      · rintro ⟨u, rfl⟩
        exact hξ u
      · rintro rfl
        exact ⟨closedPoint Ω, hξ _⟩)
    (by simp [pullback.condition])
  refine ⟨p (closedPoint Ω), ?_⟩
  have h₀ := hξ (closedPoint Ω)
  rw [← hp] at h₀
  exact (Scheme.Hom.comp_apply p a _).symm.trans h₀

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationClosureOfGraph
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_modif_graph : ∀ (R : Type) [CommRing R] [IsDomain R] (o : Type) [CommRing o] (b : o →+* R) (Z : Scheme.{0}) (s : Z ⟶ Sp o), IsProper s → ∀ y : Sp (FractionRing R) ⟶ Z, y ≫ s = jK R ≫ spMap b → ∃ (M : Modif R) (h : M.S ⟶ Z), M.gp ≫ h = y ∧ h ≫ s = M.π ≫ spMap b := by
  intro R _ _ o _ b Z s hs y hy
  let ℓ : Sp (FractionRing R) ⟶ pullback s (spMap b) := pullback.lift y (jK R) hy
  have : QuasiCompact ℓ := inferInstance
  have : IsProper (pullback.snd s (spMap b)) := inferInstance
  refine ⟨{ S := ℓ.image
            π := ℓ.imageι ≫ pullback.snd s (spMap b)
            proper := inferInstance
            integral := isIntegral_image_of_field ℓ
            gp := ℓ.toImage
            gp_π := by rw [ℓ.toImage_imageι_assoc, pullback.lift_snd]
            dominant := inferInstance }, ℓ.imageι ≫ pullback.fst s (spMap b), ?_, ?_⟩
  · show ℓ.toImage ≫ ℓ.imageι ≫ pullback.fst s (spMap b) = y
    rw [ℓ.toImage_imageι_assoc, pullback.lift_fst]
  · show (ℓ.imageι ≫ pullback.fst s (spMap b)) ≫ s = (ℓ.imageι ≫ pullback.snd s (spMap b)) ≫ spMap b
    rw [Category.assoc, Category.assoc, pullback.condition]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsNonzeroOfIsClosedMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_nhds_nonzero_of_isClosedMap :
    ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), IsClosedMap p.base → ∀ (L : LB Z) (V : Y.Opens) (u : LB.Sec (L.pull (p ⁻¹ᵁ V).ι)) (y : Y), y ∈ V → (∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) = y → z ∈ nonzeroLocus u) → ∃ V₁ : Y.Opens, y ∈ V₁ ∧ V₁ ≤ V ∧ ∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) ∈ V₁ → z ∈ nonzeroLocus u := by
  intro Z Y p hp L V u y hy h
  have hO : IsOpen ((p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme)) :=
    (p ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap _ (nonzeroLocus u).isOpen
  have hC : IsClosed (p.base '' ((p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme))ᶜ) :=
    hp _ hO.isClosed_compl
  refine ⟨V ⊓ ⟨_, hC.isOpen_compl⟩, ⟨hy, ?_⟩, inf_le_left, ?_⟩
  · rintro ⟨c, hc, hcy⟩
    have hcV : c ∈ p ⁻¹ᵁ V := by
      change p c ∈ V
      have : p c = y := hcy
      rw [this]; exact hy
    exact hc ⟨⟨c, hcV⟩, h ⟨c, hcV⟩ hcy, rfl⟩
  · intro z hz
    have h2 : (p ⁻¹ᵁ V).ι z ∈ (p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme) := by
      by_contra hn
      exact hz.2 ⟨_, hn, rfl⟩
    obtain ⟨w, hw, hwz⟩ := h2
    have : w = z := (p ⁻¹ᵁ V).ι.isOpenEmbedding.injective hwz
    subst this
    exact hw

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddPrimeIsUnitOfCompleteNormalCharZeroBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem exists_odd_prime_isUnit_of_base :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : R) := by
  intro R _ _ _ _
  by_cases h3 : IsUnit ((3 : ℕ) : R)
  · exact ⟨3, Nat.prime_three, ⟨1, rfl⟩, h3⟩
  by_cases h5 : IsUnit ((5 : ℕ) : R)
  · exact ⟨5, by norm_num, ⟨2, rfl⟩, h5⟩
  exfalso
  have m3 : ((3 : ℕ) : R) ∈ maximalIdeal R := (mem_maximalIdeal _).2 h3
  have m5 : ((5 : ℕ) : R) ∈ maximalIdeal R := (mem_maximalIdeal _).2 h5
  have m2 : ((5 : ℕ) : R) - ((3 : ℕ) : R) ∈ maximalIdeal R := Ideal.sub_mem _ m5 m3
  have m1 : ((3 : ℕ) : R) - (((5 : ℕ) : R) - ((3 : ℕ) : R)) ∈ maximalIdeal R := Ideal.sub_mem _ m3 m2
  have e : ((3 : ℕ) : R) - (((5 : ℕ) : R) - ((3 : ℕ) : R)) = 1 := by push_cast; ring
  rw [e] at m1
  exact (mem_maximalIdeal _).1 m1 isUnit_one

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleRestrictOfUniversallyClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem exists_open_etale_restrict_of_universallyClosed : ∀ (X P' T : Scheme.{0}) (a : X ⟶ P') (W1 : P'.Opens) (c : (a ⁻¹ᵁ W1).toScheme ⟶ T) (x : P'), UniversallyClosed a → x ∈ W1 → (∀ z : (a ⁻¹ᵁ W1).toScheme, ((a ⁻¹ᵁ W1).ι ≫ a) z = x → ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c)) → ∃ W : P'.Opens, W ≤ W1 ∧ x ∈ W ∧ ∀ hle : a ⁻¹ᵁ W ≤ a ⁻¹ᵁ W1, Etale (X.homOfLE hle ≫ c) := by
  intro X P' T a W1 c x ha hx hloc
  have hEt : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  let S : Set (a ⁻¹ᵁ W1).toScheme := {z | ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c)}
  have hS : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨U, hz, hU⟩
    exact ⟨U, fun y hy => ⟨U, hy, hU⟩, U.isOpen, hz⟩
  let Z : Set X := ((a ⁻¹ᵁ W1).ι '' S)ᶜ
  have hZ : IsClosed Z := ((a ⁻¹ᵁ W1).ι.isOpenEmbedding.isOpenMap _ hS).isClosed_compl
  have haZ : IsClosed (a '' Z) := a.isClosedMap _ hZ
  refine ⟨W1 ⊓ ⟨(a '' Z)ᶜ, haZ.isOpen_compl⟩, inf_le_left, ⟨hx, ?_⟩, ?_⟩
  · rintro ⟨z, hzZ, hzx⟩
    apply hzZ
    have hz1 : z ∈ a ⁻¹ᵁ W1 := by
      show a z ∈ W1
      rw [hzx]; exact hx
    have hι : (a ⁻¹ᵁ W1).ι ⟨z, hz1⟩ = z := Scheme.Opens.ι_apply _ _
    refine ⟨⟨z, hz1⟩, hloc ⟨z, hz1⟩ ?_, hι⟩
    exact (Scheme.Hom.comp_apply _ _ _).trans (by rw [hι]; exact hzx)
  · intro hle
    have hcov : ∀ w : (a ⁻¹ᵁ (W1 ⊓ ⟨(a '' Z)ᶜ, haZ.isOpen_compl⟩)).toScheme,
        ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, X.homOfLE hle w ∈ U ∧ Etale (U.ι ≫ c) := by
      intro w
      have hw : a w.1 ∉ a '' Z := w.2.2
      have hw' : w.1 ∉ Z := fun h => hw ⟨w.1, h, rfl⟩
      simp only [Z, Set.mem_compl_iff, not_not] at hw'
      obtain ⟨s, ⟨U, hsU, hU⟩, hs⟩ := hw'
      refine ⟨U, ?_, hU⟩
      have : X.homOfLE hle w = s :=
        Subtype.ext ((Scheme.homOfLE_apply hle w).trans (hs.symm.trans (Scheme.Opens.ι_apply _ s)))
      rw [this]; exact hsU
    choose U hwU hU using hcov
    refine IsZariskiLocalAtSource.of_iSup_eq_top (fun w => (X.homOfLE hle) ⁻¹ᵁ (U w)) ?_ fun w => ?_
    · rw [eq_top_iff]
      intro w _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨w, hwU w⟩
    · rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι (X.homOfLE hle) (le_refl ((X.homOfLE hle) ⁻¹ᵁ U w)), Category.assoc]
      haveI : IsOpenImmersion ((X.homOfLE hle).resLE (U w) ((X.homOfLE hle) ⁻¹ᵁ U w) le_rfl) := by
        have h2 : IsOpenImmersion ((X.homOfLE hle).resLE (U w) ((X.homOfLE hle) ⁻¹ᵁ U w) le_rfl ≫ (U w).ι) := by
          rw [Scheme.Hom.resLE_comp_ι]; infer_instance
        exact IsOpenImmersion.of_comp _ (U w).ι
      exact IsZariskiLocalAtSource.comp (hU w) _

end GlobalTheory
end

