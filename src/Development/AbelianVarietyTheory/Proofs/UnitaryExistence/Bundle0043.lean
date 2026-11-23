module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCompleteNormalSubringJoin
section
open IsLocalRing

namespace GlobalTheory

namespace CompleteJoin

variable {C : Type} [NormedField C] [IsUltrametricDist C]


omit [IsUltrametricDist C] in
theorem not_isUnit_of_norm_lt_one {R : Type*} [CommRing R] (f : R →+* C) (hf : ∀ a, ‖f a‖ ≤ 1)
    {a : R} (ha : ‖f a‖ < 1) : ¬ IsUnit a := by
  rintro ⟨u, rfl⟩
  have h1 : ‖f u‖ * ‖f (↑u⁻¹ : R)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ha (hf (↑u⁻¹ : R))
  exact this.ne h1

theorem padicInt_ringHom_ext {p : ℕ} [Fact p.Prime] (hp : ‖(p : C)‖ < 1) (a b : ℤ_[p] →+* C)
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ x, ‖b x‖ ≤ 1) : a = b := by
  refine RingHom.ext fun x => ?_
  have key : ∀ k : ℕ, ‖a x - b x‖ ≤ ‖(p : C)‖ ^ k := fun k => by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k x)
    have hx : x = y * (p : ℤ_[p]) ^ k + (x.appr k : ℤ_[p]) := by rw [hy]; ring
    have : a x - b x = (a y - b y) * (p : C) ^ k := by
      conv_lhs => rw [hx]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      ring
    rw [this, norm_mul, norm_pow]
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha y) (by simpa using hb y))
  have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp) key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem subring_of_finite {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Subring C) (φ : R →+* S) (hφ : φ.Finite)
    (h1 : ∀ a, ‖(φ a : C)‖ ≤ 1) (h2 : ∀ a ∈ maximalIdeal R, ‖(φ a : C)‖ < 1) :
    ∃ _ : IsLocalRing S, IsNoetherianRing S ∧ IsAdicComplete (maximalIdeal S) S ∧
      (∀ z : S, ‖(z : C)‖ ≤ 1) ∧ ∀ z : S, z ∈ maximalIdeal S ↔ ‖(z : C)‖ < 1 := by
  letI := φ.toAlgebra
  haveI : Module.Finite R S := hφ
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  have hle : ∀ z : S, ‖(z : C)‖ ≤ 1 := fun z => by
    let v := NormedField.valuation (K := C)
    let ψ : R →+* v.integer := (S.subtype.comp φ).codRestrict _ fun a => h1 a
    have hz : IsIntegral R z := Algebra.IsIntegral.isIntegral z
    have hz' : IsIntegral v.integer (z : C) := hz.map_of_comp_eq ψ S.subtype rfl
    exact (Valuation.integer.integers v).isIntegral_iff_v_le_one.mp hz'
  refine ⟨inferInstance, IsNoetherianRing.of_finite R S,
    CompleteFiniteExtension.isAdicComplete_of_finite_local R S, hle, fun z => ⟨fun hz => ?_,
      fun hz => not_isUnit_of_norm_lt_one S.subtype hle hz⟩⟩
  let P : Ideal S :=
    { carrier := {z | ‖(z : C)‖ < 1}
      add_mem' := fun {a b} ha hb =>
        (IsUltrametricDist.norm_add_le_max (a : C) b).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        change ‖(c : C) * x‖ < 1
        rw [norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) hx }
  have hP : ∀ z : S, z ∈ P ↔ ‖(z : C)‖ < 1 := fun _ => Iff.rfl
  have hP1 : P ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, hP]
    simp
  haveI : P.IsPrime := ⟨hP1, fun {x y} hxy => by
    by_contra h
    rw [not_or, hP, hP, not_lt, not_lt] at h
    rw [hP, Subring.coe_mul, norm_mul] at hxy
    exact hxy.not_ge (one_le_mul_of_one_le_of_one_le h.1 h.2)⟩
  have hc : maximalIdeal R = P.comap (algebraMap R S) :=
    (maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ hP1) fun a ha => h2 a ha
  have hm : P.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) P
    change (P.comap (algebraMap R S)).IsMaximal
    rw [← hc]
    exact maximalIdeal.isMaximal R
  rw [← eq_maximalIdeal hm] at hz
  exact hz


omit [IsUltrametricDist C] in
theorem exists_subring_finite {R V : Type} [CommRing R] [CommRing V] {p : ℕ} [Fact p.Prime]
    [Algebra ℤ_[p] V] [Module.Finite ℤ_[p] V] (f : R →+* C) (g : V →+* C) (φ : ℤ_[p] →+* R)
    (h : f.comp φ = g.comp (algebraMap ℤ_[p] V)) :
    ∃ (S : Subring C) (ψ : R →+* S), ψ.Finite ∧ (∀ a, (ψ a : C) = f a) ∧ ∀ a, g a ∈ S := by
  letI := f.toAlgebra
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := V)
  have hint : ∀ x : V, IsIntegral R (g x) := fun x =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[p]) x).map_of_comp_eq φ g h
  have hfin : Module.Finite R (Algebra.adjoin R (g '' s)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (s.finite_toSet.image g)
      (by rintro _ ⟨x, -, rfl⟩; exact hint x)
  refine ⟨(Algebra.adjoin R (g '' s)).toSubring, algebraMap R (Algebra.adjoin R (g '' s)),
    (RingHom.finite_algebraMap (B := Algebra.adjoin R (g '' s))).2 hfin, fun _ => rfl, fun a => ?_⟩
  have ha : a ∈ Submodule.span ℤ_[p] (s : Set V) := hs ▸ Submodule.mem_top
  change g a ∈ Algebra.adjoin R (g '' s)
  induction ha using Submodule.span_induction with
  | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [Algebra.smul_def, map_mul]
    refine mul_mem ?_ hx
    have : g (algebraMap ℤ_[p] V c) = algebraMap R C (φ c) := (RingHom.congr_fun h c).symm
    rw [this]
    exact Subalgebra.algebraMap_mem _ _


omit [IsUltrametricDist C] in
theorem exists_normal_subring (S : Subring C)
    (h : Module.Finite S (integralClosure S (FractionRing S))) :
    ∃ (S' : Subring C) (ψ : S →+* S'), ψ.Finite ∧ (∀ a, (ψ a : C) = a) ∧ IsIntegrallyClosed S' := by
  let j : FractionRing S →ₐ[S] C :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId S C) Subtype.val_injective
  let e := (integralClosure S (FractionRing S)).equivMapOfInjective j j.injective
  haveI : IsFractionRing (integralClosure S (FractionRing S)) (FractionRing S) :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing S) (FractionRing S)
  haveI : IsIntegrallyClosed (integralClosure S (FractionRing S)) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (FractionRing S)).2 inferInstance
  exact ⟨((integralClosure S (FractionRing S)).map j).toSubring,
    algebraMap S ((integralClosure S (FractionRing S)).map j),
    (RingHom.finite_algebraMap (B := (integralClosure S (FractionRing S)).map j)).2
      (Module.Finite.equiv e.toLinearEquiv), fun _ => rfl,
    IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

end CompleteJoin


open CompleteJoin in
theorem exists_complete_normal_subring_join : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (T : Formalism.L2.Pj.CDVR) (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (f : R →+* C) (g : T.V →+* C) (p : ℕ), p.Prime → ‖(p : C)‖ < 1 → T.FinRes → IsNoetherianRing R → IsAdicComplete (maximalIdeal R) R → (∀ a, ‖f a‖ ≤ 1) → (∀ a ∈ maximalIdeal R, ‖f a‖ < 1) → (∀ a, ‖g a‖ ≤ 1) → (∀ a ∈ maximalIdeal T.V, ‖g a‖ < 1) → ∃ (S : Subring C) (_ : IsLocalRing S), IsNoetherianRing S ∧ IsIntegrallyClosed S ∧ IsAdicComplete (maximalIdeal S) S ∧ (∀ a, f a ∈ S) ∧ (∀ a, g a ∈ S) ∧ (∀ z : S, ‖(z : C)‖ ≤ 1) ∧ ∀ z : S, z ∈ maximalIdeal S ↔ ‖(z : C)‖ < 1 := by
  intro R _ _ _ _ T C _ _ _ _ f g _ _ _ hT hN hR hf1 hf2 hg1 hg2
  haveI : Finite (ResidueField T.V) := hT
  obtain ⟨q, hq, _, hfin⟩ := exists_padicInt_algebra_finite T.V
  have hqV : (q : T.V) ∈ maximalIdeal T.V := by
    have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := ℤ_[q]) T.V _ (maximalIdeal.isMaximal _)
      (Ideal.mem_map_of_mem _ (show (q : ℤ_[q]) ∈ maximalIdeal _ from
        PadicInt.irreducible_p.not_isUnit))
    rwa [map_natCast] at this
  have hqC : ‖(q : C)‖ < 1 := by simpa using hg2 _ hqV
  have hqR : (q : R) ∈ maximalIdeal R := not_isUnit_of_norm_lt_one f hf1 (by simpa using hqC)
  obtain ⟨φ⟩ := nonempty_padicInt_ringHom_of_isAdicComplete (maximalIdeal R) q hqR
  obtain ⟨S₀, ψ₀, hψ₀, h₀, hg₀⟩ := exists_subring_finite f g φ
    (GlobalTheory.CompleteJoin.padicInt_ringHom_ext hqC _ _ (fun x => hf1 _) fun x => hg1 _)
  obtain ⟨_, hN₀, hc₀, -, hm₀⟩ := subring_of_finite S₀ ψ₀ hψ₀ (fun a => h₀ a ▸ hf1 a)
    fun a ha => h₀ a ▸ hf2 a ha
  obtain ⟨S, ψ, hψ, h, hS⟩ := exists_normal_subring S₀
    (_root_.GlobalTheory.normalisation_finite_local_complete_of_mixedChar S₀ q hq.out ((hm₀ _).2 (by simpa using hqC)) hN₀ hc₀).1
  have h' : ∀ a, ((ψ.comp ψ₀ a : S) : C) = f a := fun a => (h _).trans (h₀ a)
  obtain ⟨_, hN₁, hc₁, hle, hm₁⟩ := subring_of_finite S (ψ.comp ψ₀) (hψ.comp hψ₀)
    (fun a => h' a ▸ hf1 a) fun a ha => h' a ▸ hf2 a ha
  exact ⟨S, inferInstance, hN₁, hS, hc₁, fun a => h' a ▸ (ψ.comp ψ₀ a).2,
    fun a => (show ((ψ ⟨g a, hg₀ a⟩ : S) : C) = g a from h _) ▸ (ψ ⟨g a, hg₀ a⟩).2, hle, hm₁⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexLinearOfPureTypes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice {A V W : Type} [AddCommGroup A] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] (P : A →+ V) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) (Q : A →+ W) :
    ∃ r : V →ₗ[ℝ] W, ∀ a, r (P a) = Q a := by
  set L : Submodule ℤ V := P.range.toIntSubmodule with hL
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by simpa [hL] using hs⟩
  let b := Module.Free.chooseBasis ℤ L
  let e : A ≃+ P.range := AddMonoidHom.ofInjective hi
  let r : V →ₗ[ℝ] W := (b.ofZLatticeBasis ℝ L).constr ℝ (fun i => Q (e.symm (b i)))
  refine ⟨r, fun a => ?_⟩
  let f₁ : L →+ W := r.toAddMonoidHom.comp L.subtype.toAddMonoidHom
  let f₂ : L →+ W := Q.comp e.symm.toAddMonoidHom
  have hf : f₁.toIntLinearMap = f₂.toIntLinearMap := by
    refine b.ext fun i => ?_
    show r (b i : V) = Q (e.symm (b i))
    rw [← Module.Basis.ofZLatticeBasis_apply ℝ L b i]
    exact (b.ofZLatticeBasis ℝ L).constr_basis ℝ (fun i => Q (e.symm (b i))) i
  have h : r (P a) = Q (e.symm ⟨P a, a, rfl⟩) := LinearMap.congr_fun hf ⟨P a, a, rfl⟩
  have he : e.symm ⟨P a, a, rfl⟩ = a := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  rw [h, he]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.CompRat.exists_complex_linear_of_pure_types : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) (hP' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D' ty P') (Φ : D.La ≃ₗ[𝓞 E] D'.La), _root_.GlobalTheory.CompRat.IsSplit hP → (∀ a ∈ _root_.GlobalTheory.PureType.lat hP H.rt0, Φ a ∈ _root_.GlobalTheory.PureType.lat hP' H.rt0) → (∀ a ∈ _root_.GlobalTheory.PureType.lat hP (-H.rt0), Φ a ∈ _root_.GlobalTheory.PureType.lat hP' (-H.rt0)) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' (Φ a) = L (P a) := by
  intro E _ _ _ H D D' g ty P P' hP hP' Φ hsplit h₁ h₂
  have hP₀ := hP
  have hP'₀ := hP'
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod at hP₀ hP'₀
  obtain ⟨-, hi, hd, hs, -⟩ := hP₀
  obtain ⟨-, hi', hd', hs', -⟩ := hP'₀
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice P hi hd hs
    (P'.comp Φ.toLinearMap.toAddMonoidHom)
  obtain ⟨r', hr'⟩ := _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice P' hi' hd' hs'
    (P.comp Φ.symm.toLinearMap.toAddMonoidHom)
  have hr₁ : ∀ a, r (P a) = P' (Φ a) := hr
  have hr'₁ : ∀ b, r' (P' b) = P (Φ.symm b) := hr'
  have him : H.rt0.im ≠ 0 := by
    intro h0
    have hsq : (H.rt0 ^ 2).re = H.rt0.re ^ 2 := by simp [pow_two, Complex.mul_re, h0]
    rw [H.sqrt_neg_disc_sq] at hsq
    have h2 : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    simp at hsq
    nlinarith [sq_nonneg H.rt0.re]
  have hsplit' : _root_.GlobalTheory.PureType.lat hP H.rt0 ⊔ _root_.GlobalTheory.PureType.lat hP (-H.rt0) = ⊤ :=
    hsplit
  have hkey : ∀ a, r (H.rt0 • P a) = H.rt0 • r (P a) := by
    intro a
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hsplit' ▸ Submodule.mem_top : a ∈ _)
    have ry : r (H.rt0 • P y) = H.rt0 • r (P y) := by
      rw [← _root_.GlobalTheory.PureType.period_rt_smul hP hy, hr₁, hr₁, map_smul,
        _root_.GlobalTheory.PureType.period_rt_smul hP' (h₁ y hy)]
    have rz : r (-H.rt0 • P z) = -H.rt0 • r (P z) := by
      rw [← _root_.GlobalTheory.PureType.period_rt_smul hP hz, hr₁, hr₁, map_smul,
        _root_.GlobalTheory.PureType.period_rt_smul hP' (h₂ z hz)]
    have rz' : r (H.rt0 • P z) = H.rt0 • r (P z) := by
      rw [neg_smul, map_neg, neg_smul, neg_inj] at rz
      exact rz
    simp only [map_add (f := _), smul_add, ry, rz']
  have hrot : ∀ v, r (H.rt0 • v) = H.rt0 • r v := by
    have hext : r.comp (H.rt0 • LinearMap.id) = (H.rt0 • LinearMap.id).comp r :=
      LinearMap.ext_on_range hs fun a => by simpa using hkey a
    intro v
    simpa using LinearMap.congr_fun hext v
  have hlin : ∀ (c : ℂ) v, r (c • v) = c • r v := by
    intro c v
    have hc : c = ((c.re - c.im / H.rt0.im * H.rt0.re : ℝ) : ℂ) +
        ((c.im / H.rt0.im : ℝ) : ℂ) * H.rt0 := by
      apply Complex.ext <;> simp <;> field_simp <;> ring
    rw [hc, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_add (f := _), map_smul, map_smul,
      hrot, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  have hl : ∀ v, r' (r v) = v := by
    have hext : r'.comp r = LinearMap.id :=
      LinearMap.ext_on_range hs fun a => by simp [hr₁, hr'₁]
    exact fun v => LinearMap.congr_fun hext v
  have hrr : ∀ w, r (r' w) = w := by
    have hext : r.comp r' = LinearMap.id :=
      LinearMap.ext_on_range hs' fun b => by simp [hr₁, hr'₁]
    exact fun w => LinearMap.congr_fun hext w
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := r, map_add' := r.map_add, map_smul' := hlin }
  exact ⟨LinearEquiv.ofBijective L ⟨Function.LeftInverse.injective (g := r') hl,
    fun w => ⟨r' w, hrr w⟩⟩, fun a => (hr₁ a).symm⟩

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDiscreteArithGroupImageRealUnitary
section
set_option autoImplicit false

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.ArithImage

open GlobalTheory.PeterssonCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem frameOf_one : frameOf X 1 = baseFr X := by
  funext τ
  show mat (frameOf X 1) τ = mat (baseFr X) τ
  rw [mat_frameOf]
  simp

theorem lact_one_fr (y : Frame X.Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = mat y τ
  simp

theorem lact_mul_fr (a b : GL (Fin r) E) (y : Frame X.Ψ r) : lact (a * b) y = lact a (lact b y) := by
  funext τ
  show ((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ =
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

def image : Subgroup (RealGrp X) where
  carrier := {s | ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s}
  one_mem' := ⟨1, X.Γ.one_mem, by rw [lact_one_fr, frameOf_one]⟩
  mul_mem' := by
    rintro s t ⟨γ, hγ, e⟩ ⟨δ, hδ, f⟩
    exact ⟨γ * δ, X.Γ.mul_mem hγ hδ, by rw [lact_mul_fr, f, lact_frameOf X e]⟩
  inv_mem' := by
    rintro s ⟨γ, hγ, e⟩
    refine ⟨γ⁻¹, X.Γ.inv_mem hγ, ?_⟩
    have h := lact_frameOf X e s⁻¹
    rw [mul_inv_cancel, frameOf_one] at h
    rw [← h, ← lact_mul_fr, inv_mul_cancel, lact_one_fr]

def smallSet : Set (RealGrp X) :=
  {s | ∀ (τ : X.Ψ) (a b : Fin r), ‖(mat (frameOf X s) τ * (mat (baseFr X) τ)⁻¹) a b‖ < 2}

theorem isOpen_smallSet : IsOpen (smallSet X) := by
  unfold smallSet
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
  refine isOpen_lt (Continuous.norm ?_) continuous_const
  have h : Continuous fun s : RealGrp X =>
      mat (baseFr X) τ * ((s τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat (baseFr X) τ)⁻¹ :=
    (continuous_const.matrix_mul (Units.continuous_val.comp
      (continuous_subtype_val.comp (continuous_apply τ)))).matrix_mul continuous_const
  exact h.matrix_elem a b

theorem one_mem_smallSet : (1 : RealGrp X) ∈ smallSet X := by
  intro τ a b
  rw [frameOf_one, Matrix.mul_nonsing_inv _ (det_baseFr X τ).isUnit, Matrix.one_apply]
  split_ifs <;> simp

theorem finite_image_inter : ((image X : Set (RealGrp X)) ∩ smallSet X).Finite := by
  refine Set.Finite.of_finite_image (f := frameOf X) ?_ (frameOf_injective X).injOn
  refine (((GlobalTheory.LatFin.latFin (E := E)).2 r X 2).image fun γ => lact γ (baseFr X)).subset ?_
  rintro _ ⟨s, ⟨⟨γ, hγ, e⟩, hs⟩, rfl⟩
  refine ⟨γ, ⟨X.Γ_stab γ hγ, fun τ a b => ?_⟩, e⟩
  have h1 : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (baseFr X) τ = mat (frameOf X s) τ := congrFun e τ
  have h2 := hs τ a b
  rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ (det_baseFr X τ).isUnit] at h2
  exact h2.le

theorem exists_discrete_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∃ Λ : Subgroup (RealGrp X), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) ∧ ∃ W ∈ 𝓝 (1 : RealGrp X), ∀ w ∈ Λ, w ∈ W → w = 1 := by
  intro E _ _ _ r X
  refine ⟨image X, fun _ => Iff.rfl, smallSet X \ (((image X : Set (RealGrp X)) ∩ smallSet X) \ {1}), ?_, ?_⟩
  · exact ((isOpen_smallSet X).sdiff ((finite_image_inter X).subset Set.diff_subset).isClosed).mem_nhds
      ⟨one_mem_smallSet X, fun h => h.2 rfl⟩
  · intro w hw hW
    by_contra hne
    exact hW.2 ⟨⟨hw, hW.1⟩, hne⟩

end GlobalTheory.ArithImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsTangentVectorBasisAtPointBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open scoped CategoryTheory.Obj

namespace GlobalTheory.Frames

theorem tanBasis_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)), TanBasis x v → TanBasis (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) := by
  intro E _ _ _ H Dw l Xo S T _ _ φ x n v hv
  have := Xo.univ.t.semi.comm
  have := Xo.univ.t.semi.smooth
  have h₁ := isGrpPullback_pullback Xo.univ.t.G x
  have h₂ := isGrpPullback_pullback ((Over.pullback x).obj Xo.univ.t.G) (spMap φ)
  have h₃ := h₂.comp h₁
  have : IsCommMonObj ((Over.pullback x).obj Xo.univ.t.G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj Xo.univ.t.G)) :=
    Functor.isCommMonObj_obj
  obtain ⟨a₁, b₁⟩ := _root_.GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo S x _ _ h₁
  obtain ⟨-, b₃⟩ := _root_.GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo T _ _ _ h₃
  choose u hu using fun i => a₁ (v i) (hv.1 i)
  have hb : IsLieBasis u := (b₁ n u).2 (by rw [funext hu]; exact hv)
  have hs : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom :=
    inferInstanceAs (Smooth (pullback.snd Xo.univ.t.G.hom x))
  obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange S T φ _ _ _ h₂ hs n u hb
  have e : Chart.dualMapR φ = dualMap φ := by
    ext a <;> rfl
  have key := (b₃ n u').1 hb'
  convert key using 2 with i
  rw [← Category.assoc, hu', e, Category.assoc, hu]

end GlobalTheory.Frames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesAnyLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem valAt_eq_of_finite_values_anyLevel :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (c : Coeff l) (j : c.F →+* ℂ) (f : Γ(Xo.XF c, ⊤)) (S : Set ℂ), S.Finite → (∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f ∈ S) → ∀ i P P', IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → ∀ x x' : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i P → x ≫ pullback.snd _ _ = spMap j → x' ≫ pullback.fst _ _ = F.u i P' → x' ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f = valAt' x' ⊤ f := by
  intro E _ _ _ H D l Xo σ g ty F _ _ hty c j f S hS hval i P P' hP hP' x x' hx1 hx2 hx1' hx2'
  classical
  have hty' : IsTypeFn H (F.Di i).p (F.Di i).q ty := by
    rw [(F.sig i).1, (F.sig i).2]
    exact hty
  obtain ⟨B, Q, hBo, hBc, hQ, huniq⟩ := GlobalTheory.exists_period_domain_param E H (F.Di i) g ty hty'
  have hcond : spMap σ = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [← F.over_σ i P hP, ← hx1, ← hx2, Category.assoc, Category.assoc, pullback.condition]
  let y : (Fin (F.Di i).dim → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ B then pullback.lift (F.u i (Q b)) (spMap j) ((F.over_σ i _ (hQ.1 b hb)).trans hcond) else x
  have hy1 : ∀ b ∈ B, y b ≫ pullback.fst _ _ = F.u i (Q b) := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_fst]
  have hy2 : ∀ b ∈ B, y b ≫ pullback.snd _ _ = spMap j := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_snd]
  have hhol : IsHolTo B y :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (GlobalTheory.LocLift.isHolTo_congr (F.hol i _ B Q hBo hQ).1 hy1)
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hBo (spMap j)) hy2)
  have hcont : ContinuousOn (fun b => valAt' (y b) ⊤ f) B :=
    ((hhol ⊤ f).2.mono fun b hb => ⟨hb, le_of_eq rfl⟩).continuousOn
  have hfind : ∀ R, IsPeriod (F.Di i) ty R → ∀ z : Sp ℂ ⟶ Xo.XF c, z ≫ pullback.fst _ _ = F.u i R →
      z ≫ pullback.snd _ _ = spMap j → ∃ b ∈ B, y b = z := by
    intro R hR z hz1 hz2
    obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := huniq R hR
    refine ⟨b, hb, pullback.hom_ext ?_ ?_⟩
    · rw [hy1 b hb, hz1]
      exact (F.fibre i _ _ (hQ.1 b hb) hR).2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩
    · rw [hy2 b hb, hz2]
  obtain ⟨b, hb, e⟩ := hfind P hP x hx1 hx2
  obtain ⟨b', hb', e'⟩ := hfind P' hP' x' hx1' hx2'
  rw [← e, ← e']
  exact hBc.isPreconnected.constant_of_mapsTo hS.isDiscrete hcont (fun a ha => hval _ (hy2 a ha)) hb hb'

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValuationExtension
section
noncomputable section

namespace GlobalTheory.ValuativeExtension

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem valuation_extension :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (oV : O →+* V) (fK : c.F →+* K) (y : Sp K ⟶ Xo.XF c), (algebraMap V K).comp oV = fK.comp β → y ≫ pullback.snd _ _ = spMap fK → (∃! yt : Sp V ⟶ Y.X, yt ≫ Y.s = spMap oV ∧ spMap (algebraMap V K) ≫ yt = y ≫ Y.j) ∧ ∀ yt : Sp V ⟶ Y.X, ∃ G : SAB H (Sp V), Nonempty (SABMap G Y.t yt) := by
  intro E _ _ _ H D l Xo c O _ β Y V K _ _ _ _ _ _ oV fK y ho hy
  obtain ⟨h1, h2, -⟩ := GlobalTheory.ModelPoints.model_points_charts E H D l Xo c O β Y
  exact ⟨h1 V K oV fK y ho hy, fun yt => h2 _ yt⟩

end GlobalTheory.ValuativeExtension
end
end

