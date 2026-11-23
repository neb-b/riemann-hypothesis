module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0023
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0116
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsHolomorphicDiscAvoidingPole
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MfCoords
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0051
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HTChartExistsHolds
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.ChartEx

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField

def powChar {R : Type} [CommRing R] (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) :
    Multiplicative (ZMod m) →* Rˣ where
  toFun k := ζ ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hζ).symm

theorem powChar_apply {R : Type} [CommRing R] (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) (k : ZMod m) :
    powChar m ζ hζ (Multiplicative.ofAdd k) = ζ ^ k.val := rfl

def liftSurj {G T H : Type} [Group G] [Group T] [Group H] (π : G →* T) (hπ : Function.Surjective π)
    (f : G →* H) (hf : ∀ z, π z = 1 → f z = 1) : T →* H :=
  π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
    ⟨f, fun z hz => (MonoidHom.mem_ker).2 (hf z ((MonoidHom.mem_ker).1 hz))⟩

theorem liftSurj_apply {G T H : Type} [Group G] [Group T] [Group H] (π : G →* T)
    (hπ : Function.Surjective π) (f : G →* H) (hf : ∀ z, π z = 1 → f z = 1) (z : G) :
    liftSurj π hπ f hf (π z) = f z :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z

theorem hom_ext_of_surj {G T H : Type} [Group G] [Group T] [Group H] (π : G →* T)
    (hπ : Function.Surjective π) (χ χ' : T →* H) (h : ∀ z, χ (π z) = χ' (π z)) : χ = χ' :=
  MonoidHom.ext fun t => by
    obtain ⟨z, rfl⟩ := hπ t
    exact h z

variable {R : Type} [CommRing R] {E : Type} [Field E] [NumberField E] {N : ℕ} {T : Type} [CommGroup T]

def charOf (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) (π : Multiplicative (Fin N → 𝓞 E) →* T)
    (hπ : Function.Surjective π) (hker : ∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = m • y')
    (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod m) (y : Fin N → 𝓞 E) : T →* Rˣ :=
  liftSurj π hπ ((powChar m ζ hζ).comp (e y).toMultiplicative) (fun z hz => by
    obtain ⟨z', hz'⟩ := (hker (Multiplicative.toAdd z)).1 hz
    have h0 : e y (Multiplicative.toAdd z) = 0 := by
      rw [hz', map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    show powChar m ζ hζ (Multiplicative.ofAdd (e y (Multiplicative.toAdd z))) = 1
    rw [h0, ofAdd_zero, map_one])

theorem charOf_apply (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) (π : Multiplicative (Fin N → 𝓞 E) →* T)
    (hπ : Function.Surjective π) (hker : ∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = m • y')
    (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod m) (y z : Fin N → 𝓞 E) :
    charOf m ζ hζ π hπ hker e y (π (Multiplicative.ofAdd z)) = ζ ^ (e y z).val :=
  liftSurj_apply _ _ _ _ _

end GlobalTheory.CompanionTheory.Ar.BT.ChartEx

namespace GlobalTheory.CompanionTheory.Ar.BT.ChartEx

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField

variable {R : Type} [CommRing R] {E : Type} [Field E] [NumberField E] {N : ℕ} {T : Type} [CommGroup T]

section chars
variable (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) (π : Multiplicative (Fin N → 𝓞 E) →* T)
    (hπ : Function.Surjective π) (hker : ∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = m • y')
    (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod m)

omit [NeZero m] in
theorem charOf_eq_iff (π : Multiplicative (Fin N → 𝓞 E) →* T)
    (hπ : Function.Surjective π) (χ χ' : T →* Rˣ) (h : ∀ z, χ (π (Multiplicative.ofAdd z)) = χ' (π (Multiplicative.ofAdd z))) :
    χ = χ' :=
  hom_ext_of_surj π hπ χ χ' fun z => h (Multiplicative.toAdd z)

theorem charOf_add (y y' : Fin N → 𝓞 E) :
    charOf m ζ hζ π hπ hker e (y + y') = charOf m ζ hζ π hπ hker e y * charOf m ζ hζ π hπ hker e y' :=
  charOf_eq_iff π hπ _ _ fun z => by
    rw [MonoidHom.mul_apply, charOf_apply, charOf_apply, charOf_apply, ← powChar_apply m ζ hζ,
      ← powChar_apply m ζ hζ, ← powChar_apply m ζ hζ, map_add, AddMonoidHom.add_apply, ofAdd_add, map_mul]

theorem charOf_zero : charOf m ζ hζ π hπ hker e 0 = 1 :=
  charOf_eq_iff π hπ _ _ fun z => by
    rw [MonoidHom.one_apply, charOf_apply, ← powChar_apply m ζ hζ, map_zero, AddMonoidHom.zero_apply,
      ofAdd_zero, map_one]

theorem charOf_neg (y : Fin N → 𝓞 E) :
    charOf m ζ hζ π hπ hker e (-y) = (charOf m ζ hζ π hπ hker e y)⁻¹ :=
  charOf_eq_iff π hπ _ _ fun z => by
    rw [MonoidHom.inv_apply, charOf_apply, charOf_apply, ← powChar_apply m ζ hζ,
      ← powChar_apply m ζ hζ, map_neg, AddMonoidHom.neg_apply, ofAdd_neg, map_inv]

def mulMap (b : 𝓞 E) : T →* T :=
  liftSurj π hπ (π.comp (DistribSMul.toAddMonoidHom (Fin N → 𝓞 E) b).toMultiplicative) (fun z hz => by
    obtain ⟨z', hz'⟩ := (hker (Multiplicative.toAdd z)).1 hz
    show π (Multiplicative.ofAdd (b • Multiplicative.toAdd z)) = 1
    rw [hker, hz', smul_comm]
    exact ⟨_, rfl⟩)

theorem mulMap_apply (b : 𝓞 E) (z : Fin N → 𝓞 E) :
    mulMap m π hπ hker b (π (Multiplicative.ofAdd z)) = π (Multiplicative.ofAdd (b • z)) :=
  liftSurj_apply _ _ _ _ _

end chars

def dualAct {L : Type} [AddCommGroup L] [Module R L] (ρ : 𝓞 E →+* Module.End R L) (σ : 𝓞 E ≃+* 𝓞 E) :
    𝓞 E →+* Module.End R (Module.Dual R L) where
  toFun a := (ρ (σ a)).dualMap
  map_one' := by ext w l; simp
  map_mul' a b := by
    rw [mul_comm a b]
    ext w l
    simp [Module.End.mul_apply]
  map_zero' := by ext w l; simp
  map_add' a b := by ext w l; simp

theorem dualAct_apply {L : Type} [AddCommGroup L] [Module R L] (ρ : 𝓞 E →+* Module.End R L) (σ : 𝓞 E ≃+* 𝓞 E)
    (a : 𝓞 E) (w : Module.Dual R L) : dualAct ρ σ a w = w ∘ₗ ρ (σ a) := rfl

end GlobalTheory.CompanionTheory.Ar.BT.ChartEx

namespace GlobalTheory.CompanionTheory.Ar.BT.ChartEx

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField

theorem htChartExists : HTChartExists := by
  intro R K _ _ _ _ _ _ _ _ E _ _ c p n N _ T _ _ Γ S G _ _ x i hTor hSm act hmon L _ _ M ρ hρ Ω _ _ _ _ j hj
    π hπ hker hact ζ hζ e halt hadj hsurj hinj
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hpn : ((p ^ n : ℕ) : R) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  haveI : Smooth G.hom := hSm
  obtain ⟨hfin, hproj, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange S G R x L M

  have hex : ∀ χ : T →* Rˣ, ∃ w, Γ.IsHT i M (p ^ n) χ w := fun χ =>
    _root_.PositivityTheory.UnitarySelfGeneration.ht_exists R T Γ S G x (p ^ n) i hTor hSm L M χ
  have hadd : ∀ (χ χ' : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M (p ^ n) χ w → Γ.IsHT i M (p ^ n) χ' w' →
      Γ.IsHT i M (p ^ n) (χ * χ') (w + w') := fun χ χ' w w' =>
    _root_.GlobalTheory.CompanionTheory.Ar.BT.isHT_mul_add R T Γ S G x (p ^ n) i hTor L M χ χ' w w'
  have huniq : ∀ (χ : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M (p ^ n) χ w →
      (Γ.IsHT i M (p ^ n) χ w' ↔ ∃ u : Module.Dual R L, w' = w + (p ^ n) • u) := fun χ w w' =>
    _root_.GlobalTheory.CompanionTheory.Ar.BT.HT.isHT_iff R T Γ S G x (p ^ n) i hTor hSm hpn L M χ w w'
  have hzero : Γ.IsHT i M (p ^ n) 1 0 := by
    obtain ⟨w, hw⟩ := hex 1
    have h2 := hadd 1 1 w w hw hw
    rw [_root_.mul_one] at h2
    obtain ⟨u, hu⟩ := (huniq 1 w (w + w) hw).1 h2
    refine (huniq 1 w 0 hw).2 ⟨-u, ?_⟩
    have : w = (p ^ n) • u := add_left_cancel hu
    rw [smul_neg, this, add_neg_cancel]
  have hneg : ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M (p ^ n) χ w → Γ.IsHT i M (p ^ n) χ⁻¹ (-w) := by
    intro χ w hw
    obtain ⟨w', hw'⟩ := hex χ⁻¹
    have h2 := hadd χ χ⁻¹ w w' hw hw'
    rw [_root_.mul_inv_cancel] at h2
    obtain ⟨u, hu⟩ := (huniq 1 0 (w + w') hzero).1 h2
    refine (huniq χ⁻¹ w' (-w) hw').2 ⟨-u, ?_⟩
    rw [zero_add] at hu
    rw [smul_neg, ← hu]
    abel

  let χ := charOf (p ^ n) ζ hζ π hπ hker e
  obtain ⟨b⟩ : Nonempty (Module.Basis (Module.Free.ChooseBasisIndex ℤ (Fin N → 𝓞 E)) ℤ (Fin N → 𝓞 E)) :=
    ⟨Module.Free.chooseBasis ℤ (Fin N → 𝓞 E)⟩
  choose wb hwb using fun k => hex (χ (b k))
  let h : (Fin N → 𝓞 E) →+ Module.Dual R L := (b.constr ℤ wb).toAddMonoidHom
  have hh : ∀ y, Γ.IsHT i M (p ^ n) (χ y) (h y) := by
    intro y
    have hy : y ∈ (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
      rw [Submodule.mem_toAddSubgroup, b.span_eq]; exact Submodule.mem_top
    rw [Submodule.span_int_eq_addSubgroupClosure] at hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      have : h (b k) = wb k := by simp [h, Module.Basis.constr_basis]
      rw [this]; exact hwb k
    | zero => rw [map_zero, show χ 0 = 1 from charOf_zero _ _ _ _ _ _ _]; exact hzero
    | add y y' _ _ h1 h2 =>
      rw [map_add (f := _), show χ (y + y') = χ y * χ y' from charOf_add _ _ _ _ _ _ _ y y']; exact hadd _ _ _ _ h1 h2
    | neg y _ h1 => rw [map_neg, show χ (-y) = (χ y)⁻¹ from charOf_neg _ _ _ _ _ _ _ y]; exact hneg _ _ h1

  have hlin : ∀ (a : 𝓞 E) y, ∃ u, h (a • y) = dualAct ρ (RingOfIntegers.mapRingEquiv c) a (h y) + (p ^ n) • u := by
    intro a y
    have hαc : χ (a • y) = (χ y).comp (mulMap (p ^ n) π hπ hker (RingOfIntegers.mapRingEquiv c a)) :=
      charOf_eq_iff π hπ _ _ fun z => by
        rw [MonoidHom.comp_apply, mulMap_apply, charOf_apply, charOf_apply, hadj]
    have hαpt : ∀ t, (Γ.pt (mulMap (p ^ n) π hπ hker (RingOfIntegers.mapRingEquiv c a) t)).left ≫ i =
        (Γ.pt t).left ≫ i ≫ (act (RingOfIntegers.mapRingEquiv c a)).left := by
      intro t
      obtain ⟨z, rfl⟩ := hπ t
      have := mulMap_apply (p ^ n) π hπ hker (RingOfIntegers.mapRingEquiv c a) (Multiplicative.toAdd z)
      rw [ofAdd_toAdd] at this
      rw [this]
      exact hact _ _
    haveI := hmon (RingOfIntegers.mapRingEquiv c a)
    have h1 : Γ.IsHT i M (p ^ n) (χ (a • y)) (dualAct ρ (RingOfIntegers.mapRingEquiv c) a (h y)) := by
      rw [hαc, dualAct_apply]
      exact _root_.GlobalTheory.CompanionTheory.Ar.BT.hodgeTate_endo R T Γ S G x (p ^ n) i hTor L M (act (RingOfIntegers.mapRingEquiv c a)) _
        (ρ (RingOfIntegers.mapRingEquiv c a)) hαpt (hρ _) (χ y) (h y) (hh y)
    obtain ⟨u, hu⟩ := (huniq _ _ _ (hh (a • y))).1 h1
    refine ⟨-u, ?_⟩
    rw [hu, smul_neg, add_neg_cancel_right]
  obtain ⟨D, hDom, hDe, hDh, hDρ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.htChart_of_projective_module R K E c p n N (Module.Dual R L) Ω j hj
    (dualAct ρ (RingOfIntegers.mapRingEquiv c)) e h halt hadj hsurj hinj hlin
  refine ⟨D, hDe, hDom, fun a w => ?_, fun y => ⟨χ y, h y, fun z => ?_, hDh y, hh y⟩⟩
  · rw [hDρ]; rfl
  · rw [hDe]; exact charOf_apply _ _ _ _ _ _ _ _ _

end GlobalTheory.CompanionTheory.Ar.BT.ChartEx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscRatioGrowth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc

open GlobalTheory.CompanionTheory.Ar.CptModel

theorem val_mul_eq {R K : Type} [CommRing R] [Field K] {φ₀ : R →+* K} (hξ : IsCptGen (pt φ₀)) (φ : R →+* ℂ)
    {g h : R} (h0 : φ₀ h ≠ 0) {r : ℂ} (hv : ValAt (pt φ₀) (pt φ) (φ₀ g / φ₀ h) r) : r * φ h = φ g := by
  obtain ⟨hsp, s, hs, rfl⟩ := hv
  let c : Cpt (pt φ₀) := ⟨centre (pt φ), hsp⟩
  have e : s * tS c.1 h = tS c.1 g := by
    apply hξ.inj c
    rw [map_mul, genMap_toStalk, genMap_toStalk]
    refine (congrArg (· * φ₀ h) hs).trans ?_
    exact div_mul_cancel₀ _ h0
  have k : ∀ a : R, (Scheme.stalkClosedPointTo (pt φ)).hom (tS c.1 a) = φ a := fun a => by
    have := genMap_toStalk φ (self (pt φ)) a
    rw [genMap_self] at this
    exact this
  rw [← k h, ← k g, ← e]
  exact (map_mul _ _ _).symm

theorem ne_zero_of_top_le {R K : Type} [CommRing R] [Field K] (φ : R →+* K) (f : R)
    (hW : ⊤ ≤ (pt φ) ⁻¹ᵁ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens)) : φ f ≠ 0 := by
  have h1 : genPt (pt φ) ∈ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) :=
    hW (show IsLocalRing.closedPoint K ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) from trivial)
  have h2 : f ∉ (genPt (pt φ)).asIdeal := h1
  rw [genPt_asIdeal] at h2
  exact h2

theorem isDVR_regAt {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    {φ : R →+* K} (hξ : IsCptGen (pt φ)) (x : Cpt (pt φ)) (h1 : x.1.asIdeal.height = 1) :
    IsDiscreteValuationRing (regAt (pt φ) x) := by
  haveI : (x.1 : PrimeSpectrum R).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have hd := _root_.GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one R x.1.asIdeal h1
  have key : ∀ (q : PrimeSpectrum R), Nonempty (Localization.AtPrime q.asIdeal ≃+* (Spec.structureSheaf R).presheaf.stalk q) :=
    fun q => ⟨(IsLocalization.algEquiv q.asIdeal.primeCompl _ _).toRingEquiv⟩
  obtain ⟨e⟩ := key x.1
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (e.trans (CPoint.regAtEquivStalk hξ x))

end GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc

namespace GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc

open GlobalTheory.CompanionTheory.Ar.CptModel

theorem exists_pole_prime {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] (t : K) (ht : ∀ a : R, algebraMap R K a ≠ t) :
    ∃ p : Ideal R, p.IsPrime ∧ p.height = 1 ∧ ∀ a c : R, c ∉ p → t * algebraMap R K c ≠ algebraMap R K a := by
  by_contra hcon
  push Not at hcon
  let e : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.integral_of_forall_height_one R (e.symm t) fun q hq h1 => by
    obtain ⟨a, c, hc, hac⟩ := hcon q hq h1
    refine ⟨a, c, hc, e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply, e.commutes, e.commutes]
    exact hac
  have h2 : e (algebraMap R (FractionRing R) a) = t := by rw [ha, e.apply_symm_apply]
  rw [e.commutes] at h2
  exact ht a h2

theorem exists_cpt {R K : Type} [CommRing R] [Field K] (φ : R →+* K) (hφ : Function.Injective φ) (p : Ideal R)
    (hp : p.IsPrime) : ∃ x : Cpt (pt φ), x.1.asIdeal = p := by
  have hsp : genPt (pt φ) ⤳ ((⟨p, hp⟩ : PrimeSpectrum R) : Spec (CommRingCat.of R)) := by
    refine (PrimeSpectrum.le_iff_specializes (genPt (pt φ) : PrimeSpectrum R) ⟨p, hp⟩).1 ?_
    show (genPt (pt φ)).asIdeal ≤ p
    rw [genPt_asIdeal, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact ⟨⟨_, hsp⟩, rfl⟩

theorem exists_ringHom {R S : Type} [CommRing R] [CommRing S]
    (f : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) : ∃ c : R →+* S, spMap c = f :=
  ⟨(Spec.preimage f).hom, Spec.map_preimage f⟩

theorem exists_disc {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    [Algebra ℚ R] [Algebra.FiniteType ℚ R] [Algebra R K] [IsFractionRing R K] (f : R) (hf : algebraMap R K f ≠ 0)
    (t : K) (x : Cpt (pt (algebraMap R K))) (hxf : f ∈ x.1.asIdeal) (hx1 : x.1.asIdeal.height = 1)
    (hxt : t ∉ regAt (pt (algebraMap R K)) x) :
    ∃ (φ : (Fin 1 → ℂ) → (R →+* ℂ)) (r : (Fin 1 → ℂ) → ℂ) (C : ℝ), IsHolPts (Metric.ball 0 1) φ ∧
      ∀ z ∈ punct 1 1 1, ⊤ ≤ (pt (φ z)) ⁻¹ᵁ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) ∧
        ValAt (pt (algebraMap R K)) (pt (φ z)) t (r z) ∧ r z ≠ 0 ∧ ‖(r z)⁻¹‖ ≤ C * ‖z 0‖ := by
  have hξ : IsCptGen (pt (algebraMap R K)) := isCptGen_fractionRing
  have hgW : genPt (pt (algebraMap R K)) ∈
      (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) := by
    show f ∉ (genPt (pt (algebraMap R K))).asIdeal
    rw [genPt_asIdeal]
    exact hf
  have hxW : x.1 ∉ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) := fun hm => (show f ∉ x.1.asIdeal from hm) hxf
  have hlft : LocallyOfFiniteType (spMap (algebraMap ℚ R)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  obtain ⟨V, hV, ψ, r, C, -, hhol, -, hz⟩ := _root_.PositivityTheory.Xgn.exists_holomorphic_disc_avoiding_pole ℚ (algebraMap ℚ ℂ) (Spec (CommRingCat.of R))
    (spMap (algebraMap ℚ R)) K (pt (algebraMap R K)) (PrimeSpectrum.basicOpen f) x ⊤ t hlft hξ hgW hxW trivial
    (isDVR_regAt hξ x hx1) hxt
  obtain ⟨c, hc⟩ := exists_ringHom (S := Γ(Spec (CommRingCat.of R), V)) hV.fromSpec
  have hy : ∀ w, spMap (ψ w) ≫ hV.fromSpec = pt ((ψ w).comp c) := fun w => by
    rw [← hc]
    exact (Spec.map_comp _ _).symm
  refine ⟨fun z => (ψ z).comp c, r, C, ⟨hhol.1, fun a => hhol.2 (c a)⟩, fun z hzp => ?_⟩
  have := hz z hzp
  rwa [hy] at this

theorem disc_of_pole {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    [Algebra ℚ R] [Algebra.FiniteType ℚ R] [Algebra R K] [IsFractionRing R K] (g h b : R)
    (hh : algebraMap R K h ≠ 0) (hb : algebraMap R K b ≠ 0)
    (ht : ∀ a : R, algebraMap R K a ≠ algebraMap R K g / algebraMap R K h) :
    ∃ (ψ : ℂ → (R →+* ℂ)) (C : ℝ), (∀ a : R, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖ := by
  have hξ : IsCptGen (pt (algebraMap R K)) := isCptGen_fractionRing
  obtain ⟨p, hp, hp1, hpole⟩ := exists_pole_prime _ ht
  have hhp : h ∈ p := by
    by_contra hn
    exact hpole g h hn (div_mul_cancel₀ _ hh)
  obtain ⟨x, rfl⟩ := exists_cpt (algebraMap R K) (IsFractionRing.injective R K) p hp
  have hnt : algebraMap R K g / algebraMap R K h ∉ regAt (pt (algebraMap R K)) x := by
    intro hm
    obtain ⟨a, c, hc, -, e⟩ := (mem_regAt_iff _ x _).1 hm
    exact hpole a c hc e
  obtain ⟨φ, r, C, hhol, hz⟩ := exists_disc (K := K) (b * h) (by rw [map_mul]; exact mul_ne_zero hb hh) _ x
    (Ideal.mul_mem_left _ b hhp) hp1 hnt
  have hd : ∀ z : ℂ, ‖(fun _ => z : Fin 1 → ℂ)‖ = ‖z‖ := fun z => pi_norm_const z
  refine ⟨fun z => φ fun _ => z, C, fun a => ?_, fun z hz1 hz0 => ?_⟩
  · have h1 : DifferentiableOn ℂ (fun (z : ℂ) (_ : Fin 1) => z) (Metric.ball 0 1) :=
      (differentiable_pi.2 fun _ => differentiable_id).differentiableOn
    refine (hhol.2 a).comp h1 fun z hz1 => ?_
    rw [mem_ball_zero_iff] at hz1 ⊢
    rwa [hd]
  · have hmem : (fun _ => z : Fin 1 → ℂ) ∈ punct 1 1 1 := by
      refine ⟨?_, fun _ _ => hz0⟩
      rw [mem_ball_zero_iff] at hz1 ⊢
      rwa [hd]
    obtain ⟨hW, hval, hr0, hbd⟩ := hz _ hmem
    have hbh := ne_zero_of_top_le _ _ hW
    rw [map_mul] at hbh
    have e := val_mul_eq hξ _ hh hval
    have hz0' := right_ne_zero_of_mul hbh
    refine ⟨left_ne_zero_of_mul hbh, hz0', ?_⟩
    have e2 : φ (fun _ => z) h = (r fun _ => z)⁻¹ * φ (fun _ => z) g := by
      rw [← e]
      field_simp
    show ‖φ (fun _ => z) h‖ ≤ C * ‖z‖ * ‖φ (fun _ => z) g‖
    rw [e2, norm_mul]
    exact mul_le_mul_of_nonneg_right hbd (norm_nonneg _)

theorem pole_disc : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω), A.FG → Algebra.Smooth ℚ A → (∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a) → ∀ g h b : A, (h : Ω) ≠ 0 → (b : Ω) ≠ 0 → (g : Ω) / h ∉ A → ∃ (ψ : ℂ → (A →+* ℂ)) (C : ℝ), (∀ a : A, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖ := by
  intro Ω _ _ A hFG hSm hfrac g h b hh hb ht
  haveI : Algebra.FiniteType ℚ A := (Subalgebra.fg_iff_finiteType A).1 hFG
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℚ A
  haveI : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth ℚ A
  haveI : IsFractionRing A Ω := IsFractionRing.of_field A Ω fun z => by
    obtain ⟨a, ha, c, hc, hc0, e⟩ := hfrac z
    have hc0' : algebraMap A Ω ⟨c, hc⟩ ≠ 0 := hc0
    exact ⟨⟨a, ha⟩, ⟨c, hc⟩, eq_div_of_mul_eq hc0' e⟩
  refine disc_of_pole (K := Ω) g h b hh hb fun a e => ht ?_
  have e' : (a : Ω) = (g : Ω) / h := e
  rw [← e']
  exact a.2

end GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverCoordsExist
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
private theorem isLocallyNoetherian_of_closedImmersion_pSpace (o : Type) [CommRing o] [IsNoetherianRing o] (X : Scheme.{0}) (N : ℕ)
    (i : X ⟶ PSpace o N) [IsClosedImmersion i] : IsLocallyNoetherian X := by
  refine isLocallyNoetherian_of_affine_cover
    (S := fun j : Fin (N + 1) => ⟨i ⁻¹ᵁ GlobalTheory.ProjSpace.chart o N j,
      (GlobalTheory.ProjSpace.isAffineOpen_chart o N j).preimage i⟩) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    have hx : i x ∈ (⨆ j, GlobalTheory.ProjSpace.chart o N j) := by
      rw [GlobalTheory.ProjSpace.iSup_chart]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hj⟩
  · intro j
    letI := GlobalTheory.ProjSpace.algebraSections o N (GlobalTheory.ProjSpace.chart o N j)
    haveI : IsNoetherianRing Γ(PSpace o N, GlobalTheory.ProjSpace.chart o N j) :=
      isNoetherianRing_of_ringEquiv _ (GlobalTheory.ProjSpace.chartAlgEquiv o N j).toRingEquiv
    exact isNoetherianRing_of_surjective _ _ (i.app (GlobalTheory.ProjSpace.chart o N j)).hom
      (Scheme.Hom.app_surjective i _ (GlobalTheory.ProjSpace.isAffineOpen_chart o N j))

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.projective_over_coords_exist : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (X : Scheme.{0}) (s : X ⟶ Sp o), IsProjOver s → ∀ (Ω : Type) [Field Ω] [Algebra o Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ξ ≫ s = spMap (algebraMap o Ω) → ∃ (n : ℕ) (x : Fin n → Ω), CoordTie o ξ x := by
  intro o _ _ X s hs Ω _ _ ξ hξ hcomp
  obtain ⟨N, i, hi, rfl⟩ := hs
  haveI := isLocallyNoetherian_of_closedImmersion_pSpace o X N i
  have hZ := GlobalTheory.CompanionTheory.Ar.isClopen_setOf_genPt_specializes X Ω ξ hξ
  let U : X.Opens := ⟨{q | genPt ξ ⤳ q}, hZ.isOpen⟩
  have hr : Set.range ξ ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : y = closedPoint Ω := Subsingleton.elim _ _
    subst this
    exact specializes_rfl
  let ξ' : Sp Ω ⟶ U := IsOpenImmersion.lift U.ι ξ hr
  have hfac : ξ' ≫ U.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _
    (by rw [Scheme.Opens.range_ι]; exact hZ.isClosed)
  have hξ2 : IsCptGen (ξ' ≫ U.ι) := by rw [hfac]; exact hξ
  have hgen' : IsCptGen ξ' := PositivityTheory.HtPt.Mf.isCptGen_of_comp ξ' U.ι hξ2
  have h1 : U.ι (genPt ξ') = genPt ξ := by
    change (ξ' ≫ U.ι) (closedPoint Ω) = ξ (closedPoint Ω)
    rw [hfac]
  have hall : ∀ q, genPt ξ' ⤳ q := by
    intro q
    rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff, h1]
    exact q.2
  obtain ⟨t, ht, heq⟩ := PositivityTheory.HtPt.Mf.exists_point (ξ' ≫ U.ι ≫ i)
    (by simpa [Category.assoc, reassoc_of% hfac] using hcomp)
  have hct : CoordTie o ξ' t := PositivityTheory.HtPt.Mf.coordTie_of_all (i := U.ι ≫ i) hgen' hall heq
  have h2 : genPt (ξ' ≫ U.ι) = genPt ξ := by rw [hfac]
  have hsurj : ∀ q : Cpt (ξ' ≫ U.ι), ∃ p : Cpt ξ', PositivityTheory.HtPt.Mf.push ξ' U.ι p = q := by
    intro q
    have hq : genPt ξ ⤳ q.1 := by
      rw [← h2]
      exact q.2
    exact ⟨⟨⟨q.1, hq⟩, hall _⟩, Subtype.ext rfl⟩
  have hfin := PositivityTheory.HtPt.Mf.coordTie_comp (o := o) U.ι hξ2 hsurj hct
  rw [hfac] at hfin
  exact ⟨N + 1, t, hfin⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SandwichPointOverFieldExt
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hodge_tate_model_point_sandwich : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (κ : Ω), HTFree 𝔐 p → Sandwich 𝔐 p κ → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra O' C], v.Integers O' → v (p : C) < 1 → ∀ (z : Sp O' ⟶ 𝔐.X) (EC : Type) [AddCommGroup EC] [Module C EC] [Module O' EC] [IsScalarTower O' C EC] (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) EC) (ρC : 𝓞 E →+* Module.End C EC) (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* O') (κz : O'), MC.IsActOf 𝔐.t.act.act ρC → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) → GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z κ κz → 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O' ≤ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC ∧ (∀ w ∈ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC, κz • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O') ∧ (𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC).FG :=
  PositivityTheory.HtPt.Gh.hodge_tate_free_sandwich

end GlobalTheory.CompanionTheory.Ar.HT
end

