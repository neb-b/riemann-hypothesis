module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0120
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0121
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0108
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NegOneSmulCancel

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.WedgeOf

section Defs

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev QC : Type := C1 F ⧸ LinearMap.range (d0 F)

def iotaQ : H1 F →ₗ[R] QC F :=
  Submodule.mapQ _ _ (Z1 F).subtype (by
    rintro _ ⟨g, rfl⟩
    exact ⟨g, rfl⟩)

theorem iotaQ_mk (f : Z1 F) : iotaQ F (H1.mk F f) = Submodule.Quotient.mk f.1 := rfl

theorem iotaQ_injective : Function.Injective (iotaQ F) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [iotaQ_mk, Submodule.Quotient.mk_eq_zero] at hc
  obtain ⟨g, hg⟩ := hc
  exact H1.mk_eq_zero.2 ⟨g, hg⟩

def crossB : H1 F →ₗ[R] H1 F →ₗ[R] H2 (box F) :=
  (cup (box F)).compl₁₂ (boxL F).pull1 (boxR F).pull1

theorem crossB_apply (a b : H1 F) : crossB F a b = cup (box F) ((boxL F).pull1 a) ((boxR F).pull1 b) := rfl

end Defs

section Wedge

variable {R : Type} [CommRing R] (V : Type) [AddCommGroup V] [Module R V]

private theorem upd0 {X : Type} (a b c : X) : Function.update ![a, b] 0 c = ![c, b] := by
  funext i; fin_cases i <;> simp

private theorem upd1 {X : Type} (a b c : X) : Function.update ![a, b] 1 c = ![a, c] := by
  funext i; fin_cases i <;> simp

def wedgeT : V ⊗[R] V →ₗ[R] ⋀[R]^2 V :=
  TensorProduct.lift (LinearMap.mk₂ R (fun a b ↦ exteriorPower.ιMulti R 2 ![a, b])
    (fun a a' b ↦ by
      have := (exteriorPower.ιMulti R (M := V) 2).map_update_add ![a, b] 0 a a'
      simpa only [upd0, upd1] using this)
    (fun r a b ↦ by
      have := (exteriorPower.ιMulti R (M := V) 2).map_update_smul ![a, b] 0 r a
      simpa only [upd0, upd1] using this)
    (fun a b b' ↦ by
      have := (exteriorPower.ιMulti R (M := V) 2).map_update_add ![a, b] 1 b b'
      simpa only [upd0, upd1] using this)
    (fun r a b ↦ by
      have := (exteriorPower.ιMulti R (M := V) 2).map_update_smul ![a, b] 1 r b
      simpa only [upd0, upd1] using this))

theorem wedgeT_tmul (a b : V) : wedgeT (R := R) V (a ⊗ₜ b) = exteriorPower.ιMulti R 2 ![a, b] := rfl

end Wedge

end GlobalTheory.CompanionTheory.WedgeOf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KaehlerFreeConeRing
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem free_of_formallyEtale (K A B : Type) [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Algebra A B] [IsScalarTower K A B] [Algebra.FormallyEtale A B] [Module.Free A Ω[A⁄K]] :
    Module.Free B Ω[B⁄K] :=
  (KaehlerDifferential.isBaseChange_of_formallyEtale K A B).free

theorem free_of_bijective {K A B : Type} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (φ : A →ₐ[K] B) (hφ : Function.Bijective φ) [Module.Free A Ω[A⁄K]] : Module.Free B Ω[B⁄K] := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  haveI : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId A B) hφ)
  exact free_of_formallyEtale K A B

variable {K : Type} [Field K] {n d : ℕ}

theorem free_Bp : Module.Free (Bp K n d) Ω[Bp K n d⁄K] :=
  Module.Free.of_basis (KaehlerDifferential.mvPolynomialBasis K (E n d))

def cS (k : Fin d) (S : Finset (Fin d)) : Gam n d := ∑ j ∈ S, ratE k j

theorem ratE_inl (k j : Fin d) (l : Fin n) : (ratE k j : Gam n d) (Sum.inl l) = 0 := by
  simp [ratE, oneE]

theorem ratE_inr (k j j' : Fin d) :
    (ratE k j : Gam n d) (Sum.inr j') = (if j' = j then 1 else 0) - (if j' = k then 1 else 0) := by
  simp [ratE, oneE, Pi.single_apply]

theorem cS_inl (k : Fin d) (S : Finset (Fin d)) (l : Fin n) : (cS k S : Gam n d) (Sum.inl l) = 0 := by
  simp [cS, Finset.sum_apply, ratE_inl]

theorem cS_inr (k : Fin d) (S : Finset (Fin d)) {j : Fin d} (hj : j ≠ k) :
    (cS k S : Gam n d) (Sum.inr j) = if j ∈ S then 1 else 0 := by
  simp [cS, Finset.sum_apply, ratE_inr, hj]

theorem tdeg_cS (k : Fin d) (S : Finset (Fin d)) : tdeg (cS k S : Gam n d) = 0 := by
  unfold cS tdeg
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact ChartBij.tdeg_ratE k j

theorem cS_mem (k : Fin d) (S : Finset (Fin d)) : (cS k S : Gam n d) ∈ (cone {k} : AddSubmonoid (Gam n d)) :=
  AddSubmonoid.sum_mem _ fun j _ => ratE_mem (Finset.mem_singleton_self k) j

theorem neg_cS_mem {k : Fin d} {S : Finset (Fin d)} (hk : k ∈ S) :
    -(cS k S : Gam n d) ∈ (cone S : AddSubmonoid (Gam n d)) := by
  refine ⟨fun l => by simp [cS_inl], fun j hj => ?_, ?_⟩
  · have hne : j ≠ k := fun h => hj (h ▸ hk)
    simp [cS_inr k S hne, hj]
  · have h := tdeg_add (cS k S : Gam n d) (-cS k S)
    rw [add_neg_cancel, tdeg_cS] at h
    have h0 : tdeg (0 : Gam n d) = 0 := by simp [tdeg]
    rw [h0] at h
    linarith

theorem exists_add_nsmul_mem {k : Fin d} {S : Finset (Fin d)} (hk : k ∈ S) (g : Gam n d)
    (hg : g ∈ (cone S : AddSubmonoid (Gam n d))) :
    ∃ N : ℕ, g + N • (cS k S : Gam n d) ∈ (cone {k} : AddSubmonoid (Gam n d)) := by
  refine ⟨∑ j, (g (Sum.inr j)).natAbs, fun l => ?_, fun j hj => ?_, ?_⟩
  · simpa [cS_inl] using hg.1 l
  · have hne : j ≠ k := by simpa using hj
    have hle : (g (Sum.inr j)).natAbs ≤ ∑ j, (g (Sum.inr j)).natAbs :=
      Finset.single_le_sum (f := fun j => (g (Sum.inr j)).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [Pi.add_apply, Pi.smul_apply, cS_inr k S hne]
    by_cases hS : j ∈ S
    · simp only [hS, if_true, nsmul_eq_mul, mul_one]
      omega
    · simpa [hS] using hg.2.1 j hS
  · rw [tdeg_add]
    have h : tdeg ((∑ j, (g (Sum.inr j)).natAbs) • (cS k S : Gam n d)) = 0 := by
      have hs : ∀ N : ℕ, tdeg (N • (cS k S : Gam n d)) = 0 := fun N => by
        induction N with
        | zero => simp [tdeg]
        | succ N ih => rw [succ_nsmul, tdeg_add, ih, tdeg_cS, add_zero]
      exact hs _
    rw [h, add_zero]
    exact hg.2.2

theorem free_singleton (k : Fin d) : Module.Free (R0 K n d {k}) Ω[R0 K n d {k}⁄K] := by
  haveI : Module.Free (Bp K n d) Ω[Bp K n d⁄K] := free_Bp
  exact free_of_bijective _ (ChartBij.chart_bijective (K := K) (n := n) k)

theorem free_of_mem {k : Fin d} {S : Finset (Fin d)} (hk : k ∈ S) :
    Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := by
  have hle : (cone {k} : AddSubmonoid (Gam n d)) ≤ cone S :=
    cone_mono (Finset.singleton_subset_iff.2 hk)
  letI : Algebra (R0 K n d {k}) (R0 K n d S) := (incl (K := K) hle).toRingHom.toAlgebra
  haveI : IsScalarTower K (R0 K n d {k}) (R0 K n d S) := IsScalarTower.of_algHom (incl (K := K) hle)
  haveI : IsLocalization.Away (mon K (cS k S) (cS_mem k S)) (R0 K n d S) :=
    Away.isLocalization_away hle (cS k S) (cS_mem k S) (neg_cS_mem hk) fun g hg => exists_add_nsmul_mem hk g hg
  haveI : Algebra.FormallyEtale (R0 K n d {k}) (R0 K n d S) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (mon K (cS k S) (cS_mem k S)))
  haveI : Module.Free (R0 K n d {k}) Ω[R0 K n d {k}⁄K] := free_singleton k
  exact free_of_formallyEtale K (R0 K n d {k}) (R0 K n d S)

theorem free_om : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)),
    Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := by
  intro K _ n d S
  rcases S.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
  · haveI : Module.Free (Bp K n d) Ω[Bp K n d⁄K] := free_Bp
    exact free_of_bijective _ (PolyBij.poly_bijective (K := K) (n := n) (d := d))
  · exact free_of_mem hk

end GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEquivCohomologyOfQuasiIsomorphism
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfKerCoh

theorem ker_equiv_cohomology : ∀ (S P₀ P₁ P₂ T B₀ B₁ B₂ : Type) [CommRing S] [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂] [AddCommGroup T] [Module S T] [AddCommGroup B₀] [Module S B₀] [AddCommGroup B₁] [Module S B₁] [AddCommGroup B₂] [Module S B₂] (a₀ : P₀ →ₗ[S] P₁) (a₁ : P₁ →ₗ[S] P₂) (π : P₁ →ₗ[S] T) (dT : T →ₗ[S] P₂) (Z : Submodule S B₁) (dB : B₀ →ₗ[S] Z) (b₁ : B₁ →ₗ[S] B₂) (f : P₁ →ₗ[S] B₁) (ψ₀ : P₀ →ₗ[S] B₀), Function.Surjective π → Function.Exact a₀ π → dT ∘ₗ π = a₁ → (∀ z, z ∈ Z ↔ b₁ z = 0) → (∀ x, a₁ x = 0 → b₁ (f x) = 0) → (∀ y, f (a₀ y) = (dB (ψ₀ y) : B₁)) → QIsoAt a₀ a₁ (Z.subtype ∘ₗ dB) b₁ f → Nonempty (LinearMap.ker dT ≃ₗ[S] Z ⧸ LinearMap.range dB) := by
  intro S P₀ P₁ P₂ T B₀ B₁ B₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ a₁ π dT Z dB b₁ f ψ₀ hπ hex hdT hZ hf hψ hq
  have hdTπ : ∀ x, dT (π x) = a₁ x := fun x => LinearMap.congr_fun hdT x
  let H : LinearMap.ker a₁ →ₗ[S] LinearMap.ker dT :=
    (π.comp (LinearMap.ker a₁).subtype).codRestrict (LinearMap.ker dT) fun x => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, hdTπ]
      exact x.2
  let G : LinearMap.ker a₁ →ₗ[S] Z ⧸ LinearMap.range dB :=
    (LinearMap.range dB).mkQ.comp ((f.comp (LinearMap.ker a₁).subtype).codRestrict Z fun x =>
      (hZ _).2 (hf _ x.2))
  have hH : Function.Surjective H := by
    rintro ⟨t, ht⟩
    obtain ⟨x, rfl⟩ := hπ t
    have hx : a₁ x = 0 := by
      rw [← hdTπ]
      exact ht
    exact ⟨⟨x, hx⟩, rfl⟩
  have hG : Function.Surjective G := by
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, y, hx, hxy⟩ := hq.2 z ((hZ z).1 z.2)
    refine ⟨⟨x, hx⟩, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    exact ⟨y, Subtype.ext hxy.symm⟩
  have hker : LinearMap.ker H = LinearMap.ker G := by
    ext ⟨x, hx⟩
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro h
      have h' : π x = 0 := congrArg Subtype.val h
      obtain ⟨y, rfl⟩ := (hex x).1 h'
      show Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨ψ₀ y, Subtype.ext (hψ y).symm⟩
    · intro h
      have h' : (⟨f x, (hZ _).2 (hf _ hx)⟩ : Z) ∈ LinearMap.range dB :=
        (Submodule.Quotient.mk_eq_zero _).1 h
      obtain ⟨y, hy⟩ := h'
      obtain ⟨y', rfl⟩ := hq.1 x hx ⟨y, congrArg Subtype.val hy⟩
      exact Subtype.ext ((hex _).2 ⟨y', rfl⟩)
  exact ⟨(LinearMap.quotKerEquivOfSurjective H hH).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective G hG))⟩

end GlobalTheory.CompanionTheory.PerfKerCoh
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHomogeneousIdealOfEvalZero
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoVan

theorem evV_awayMap {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    {x y z : MvPolynomial (Fin (N + 1)) K} {b : ℕ} (hy : y ∈ grK K N b) (hz : z = x * y)
    (V : X.Opens) (h : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) z)
    (h' : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x) (u : HomogeneousLocalization.Away (grK K N) x) :
    evV i z V h (HomogeneousLocalization.awayMap (grK K N) hy hz u) = evV i x V h' u := by
  have e := congrArg (fun φ => φ.hom u) (Proj.awayMap_awayToSection (grK K N) hy hz)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [evV, RingHom.coe_comp, Function.comp_apply]
  rw [e, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem evV_res {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    {g : MvPolynomial (Fin (N + 1)) K} {V W : X.Opens} (hVW : V ≤ W)
    (hW : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g)
    (u : HomogeneousLocalization.Away (grK K N) g) :
    evV i g V hV u = resO hVW (evV i g W hW u) := by
  have e := congrArg (fun φ => φ.hom ((Proj.awayToSection (grK K N) g).hom u))
    (Scheme.Hom.appLE_map i hW (homOfLE hVW).op)
  exact e.symm

theorem away_factor {K : Type} [Field K] {N : ℕ} {x g f : MvPolynomial (Fin (N + 1)) K} {e s : ℕ}
    (hx : x ∈ grK K N 1) (hg : g ∈ grK K N e) (hf : f ∈ grK K N (s • e))
    (hf' : f ∈ grK K N ((s • e) • 1)) (hc : g ^ s ∈ grK K N ((s • e) • 1)) :
    HomogeneousLocalization.awayMap (grK K N) hg (rfl : x * g = x * g)
        (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) f hf') =
      HomogeneousLocalization.awayMap (grK K N) hx (mul_comm x g)
          (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) *
        HomogeneousLocalization.awayMap (grK K N) hg (rfl : x * g = x * g)
          (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) (g ^ s) hc) := by
  ext
  simp only [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr ?_
  rw [Localization.r_iff_exists]
  use 1
  simp
  ring

theorem mem_homIdeal_of_vanish {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    (hX : IsIntegral X) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e)
    (hg : g ∈ grK K N e) {s : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (s • e))
    (V : X.Opens) (hVne : (V : Set X).Nonempty)
    (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g)
    (h0 : evV i g V hV (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0) :
    f ∈ homIdeal i := by
  have hf' : f ∈ grK K N ((s • e) • 1) := by simpa using hf
  have hc : g ^ s ∈ grK K N ((s • e) • 1) := by
    have := SetLike.pow_mem_graded s hg
    simpa using this
  refine Ideal.subset_span ⟨s • e, hf', fun j => ?_⟩
  by_cases hU : ((i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) : Set X).Nonempty
  · have hW : ((V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter V.isOpen (TopologicalSpace.Opens.isOpen _) hVne hU
    haveI : Nonempty (V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) := hW.to_subtype
    have hx := xv_mem K N j
    have hWU : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤
        i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) := inf_le_right
    have hWV : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤ V := inf_le_left
    have hWg := hWV.trans hV
    have hWx : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤
        i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j * g) := by
      rw [Proj.basicOpen_mul]
      exact fun y hy => ⟨hWU hy, hWg hy⟩
    apply map_injective_of_isIntegral X (homOfLE hWU)
    rw [map_zero]
    refine (evV_res i hWU le_rfl hWU _).symm.trans ?_
    rw [← evV_awayMap i hg rfl _ hWx hWU, away_factor hx hg hf hf' hc, map_mul,
      evV_awayMap i hx (mul_comm _ g) _ hWx hWg, evV_res i hWV hV hWg, h0, map_zero, zero_mul]
  · refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 ?_)
    refine (X.basicOpen_le _).trans ?_
    intro y hy
    exact (hU ⟨y, hy⟩).elim

end GlobalTheory.CompanionTheory.GeoVan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Mk2EqZeroIffMemS
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

section SQ

variable {R : Type} [CommRing R] {D : Type 1} [Category.{0} D] {A : D ⥤ CommAlgCat.{0} R} (a b : IdF A)

def vl (T : D) : (sq a b).obj T →+ A.obj T ⧸ b.S T := (sqM a b T).subtype.toAddMonoidHom

def mk2 (T : D) : (CH.modF A).obj T →+ A.obj T ⧸ b.S T := (Ideal.Quotient.mk (b.S T)).toAddMonoidHom

def gC {q : ℕ} (x : CH.Cn (CH.modF A) q) (hx : ∀ s, x s ∈ a.S _) : CH.Cn (sq a b) q := fun s => sqMk a b (x s) (hx s)

variable {a b}

theorem mk2_eq_zero_iff_mem_S {T : D} (x : (CH.modF A).obj T) : mk2 b T x = 0 ↔ x ∈ b.S T := Ideal.Quotient.eq_zero_iff_mem

theorem map_val {T T' : D} (φ : T ⟶ T') (y : (sq a b).obj T) (x : (CH.modF A).obj T) (h : vl a b T y = mk2 b T x) :
    vl a b T' (((sq a b).map φ).hom y) = mk2 b T' (((CH.modF A).map φ).hom x) := by
  obtain ⟨y, hy⟩ := y
  have h' : y = mk2 b T x := h
  subst h'
  rfl

theorem d_val {q : ℕ} (f : CH.Cn (sq a b) q) (x : CH.Cn (CH.modF A) q)
    (h : ∀ s, vl a b _ (f s) = mk2 b _ (x s)) (s : ComposableArrows D (q + 1)) :
    vl a b _ (CH.d _ q f s) = mk2 b _ (CH.d _ q x s) := by
  change vl a b _ (∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • ((sq a b).map (GlobalTheory.CatH.toLast i s)).hom (f (GlobalTheory.CatH.face i s))) =
    mk2 b _ (∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • ((CH.modF A).map (GlobalTheory.CatH.toLast i s)).hom (x (GlobalTheory.CatH.face i s)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, map_val _ _ _ (h _)]

theorem lift_C {q : ℕ} (f : CH.Cn (sq a b) q) : ∃ x : CH.Cn (CH.modF A) q, (∀ s, x s ∈ a.S _) ∧
    ∀ s, vl a b _ (f s) = mk2 b _ (x s) := by
  have h : ∀ s, ∃ y : (CH.modF A).obj (s.obj (Fin.last q)), y ∈ a.S _ ∧ vl a b _ (f s) = mk2 b _ y := by
    intro s
    obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (show sqM a b _ from f s).2
    exact ⟨y, hy, e.symm⟩
  choose x hx hx' using h
  exact ⟨x, hx, hx'⟩

theorem vl_inj {T : D} {y y' : (sq a b).obj T} (h : vl a b T y = vl a b T y') : y = y' := Subtype.ext h

theorem gC_d {q : ℕ} (x : CH.Cn (CH.modF A) q) (hx : ∀ s, x s ∈ a.S _) (hd : ∀ s, CH.d _ q x s ∈ b.S _) :
    CH.d _ q (gC a b x hx) = 0 := by
  funext s
  refine vl_inj ?_
  rw [d_val _ x (fun _ => rfl) s, (mk2_eq_zero_iff_mem_S _).2 (hd s)]
  exact (map_zero (vl a b _)).symm

theorem ex_zero (hH : Subsingleton (CH.H (sq a b) 0)) (x : CH.Cn (CH.modF A) 0) (hx : ∀ s, x s ∈ a.S _)
    (hd : ∀ s, CH.d _ 0 x s ∈ b.S _) (s) : x s ∈ b.S _ := by
  have h0 := gC_d x hx hd
  have h1 : (CH.cx (sq a b)).cls (gC a b x hx) h0 = 0 := Subsingleton.elim _ _
  have h2 : gC a b x hx = 0 := ((CrystallineSemistableComparison.P.cls_surj (CH.cx (sq a b)) 0).2.1 _ h0).1 h1
  have h3 : vl a b _ (gC a b x hx s) = 0 := by rw [h2]; exact map_zero (vl a b _)
  exact (mk2_eq_zero_iff_mem_S _).1 h3

theorem ex_succ {q : ℕ} (hH : Subsingleton (CH.H (sq a b) (q + 1))) (x : CH.Cn (CH.modF A) (q + 1))
    (hx : ∀ s, x s ∈ a.S _) (hd : ∀ s, CH.d _ (q + 1) x s ∈ b.S _) :
    ∃ v : CH.Cn (CH.modF A) q, (∀ s, v s ∈ a.S _) ∧ ∀ s, (x - CH.d _ q v) s ∈ b.S _ := by
  have h0 := gC_d x hx hd
  have h1 : (CH.cx (sq a b)).cls (gC a b x hx) h0 = 0 := Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := ((CrystallineSemistableComparison.P.cls_surj (CH.cx (sq a b)) (q + 1)).2.1 _ h0).1 h1
  obtain ⟨v, hv, hv'⟩ := lift_C u
  refine ⟨v, hv, fun s => ?_⟩
  have h3 := d_val u v hv' s
  have h4 : vl a b _ (CH.d _ q u s) = mk2 b _ (x s) :=
    congrArg (fun y : CH.Cn (sq a b) (q + 1) => vl a b _ (y s)) hu
  rw [h4] at h3
  refine (mk2_eq_zero_iff_mem_S _).1 ?_
  change mk2 b _ (x s - CH.d _ q v s) = 0
  rw [map_sub, h3, sub_self]

theorem cls_sub_sum {K : Cx.{1} R} {m : ℕ} {ι : Type} [Fintype ι] (g : K.X m) (hg : K.d m g = 0) (Y : ι → K.X m)
    (hY : ∀ k, K.d m (Y k) = 0) (h : K.d m (g - ∑ k, Y k) = 0) :
    K.cls g hg - ∑ k, K.cls (Y k) (hY k) = K.cls (g - ∑ k, Y k) h := by
  have e : (⟨g - ∑ k, Y k, h⟩ : K.Z m) = ⟨g, hg⟩ - ∑ k, (⟨Y k, hY k⟩ : K.Z m) := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sub, Submodule.coe_sum]
  change _ = Submodule.mkQ _ (⟨g - ∑ k, Y k, h⟩ : K.Z m)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sub, map_sum]
  rfl

theorem rep_fin {m : ℕ} {ι : Type} [Fintype ι] {Cl E : CH.Cn (CH.modF A) m} {c : CH.H (sq a b) m} (hc : Rep a b Cl c)
    (Y : ι → CH.Cn (sq a b) m) (y : ι → CH.Cn (CH.modF A) m) (hY : ∀ k, CH.d _ m (Y k) = 0)
    (hy : ∀ k s, vl a b _ (Y k s) = mk2 b _ (y k s)) (hE : Cl - ∑ k, y k = E) :
    Rep a b E (c - ∑ k, (CH.cx (sq a b)).cls (Y k) (hY k)) := by
  obtain ⟨g, hg, rfl, hgs⟩ := hc
  have h : CH.d _ m (g - ∑ k, Y k) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, hg]
    simp [hY]
  refine ⟨g - ∑ k, Y k, h, cls_sub_sum (K := CH.cx (sq a b)) g hg Y hY h, fun s => ?_⟩
  subst hE
  change vl a b _ (g s - (∑ k, Y k) s) = mk2 b _ (Cl s - (∑ k, y k) s)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_apply, Finset.sum_apply, map_sub, map_sub, map_sum, map_sum]
  exact congrArg₂ (· - ·) (hgs s) (Finset.sum_congr rfl fun k _ => hy k s)

end SQ

end GlobalTheory.CompanionTheory.ConeZig
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.USt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh

namespace GlobalTheory.CompanionTheory.Axis

def USt {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module R M] (z : ∀ T : C, M ⊗[R] F.obj T),
    (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
    ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T)

def evZ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {T T' : C} (φ : T ⟶ T') :
    Z1 F →ₗ[R] F.obj T' where
  toFun f := f.1 T T' φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.CompanionTheory.Axis
end
end

