module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0016
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0014
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeCartierDivisor
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.PrimeDivCartier

theorem exists_local_generator (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S] (p P : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime S p] [UniqueFactorizationMonoid S] (hP : P.IsPrime) (hPp : P ≤ p)
    (hP0 : P ≠ ⊥) (hmin : ∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → Q ≤ P → Q = P) :
    ∃ a ∈ P, a ≠ 0 ∧ ∃ t ∉ p, ∀ g ∈ P, ∃ r, t * g = a * r :=
  GlobalTheory.T.height_one_prime_principal_local R S p P hP hPp hP0 hmin

theorem primeIdealOf_minimal (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U)
    (z : X) (hz : z ∈ U) (h1 : Order.coheight z = 1) :
    (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≠ ⊥ ∧ ∀ Q : Ideal Γ(X, U), Q.IsPrime → Q ≠ ⊥ →
      Q ≤ (hU.primeIdealOf ⟨z, hz⟩).asIdeal → Q = (hU.primeIdealOf ⟨z, hz⟩).asIdeal :=
  GlobalTheory.T.codim_one_point_minimal_prime X U hU z hz h1

theorem ord_eq_one (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)) (h1 : Order.coheight z = 1)
    (ha0 : a ≠ 0) (ha : a ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (ht : t ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (hg : ∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) :
    Scheme.ord (fnOf U (gen_mem hz) a) z = 1 :=
  GlobalTheory.T.order_at_codim_one_eq_one X U hU z hz a t h1 ha0 ha ht hg

theorem ord_eq_zero (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)) (h1 : Order.coheight z = 1)
    (hg : ∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r)
    (v : X) (hv : v ∈ U) (hvt : v ∈ X.basicOpen t) (hvz : v ≠ z) :
    Scheme.ord (fnOf U (gen_mem hv) a) v = 0 :=
  GlobalTheory.T.order_off_codim_one_eq_zero X U hU z hz a t h1 hg v hv hvt hvz


open Classical in
theorem exists_local_eqn (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (hu : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (z : X)
    (h1 : Order.coheight z = 1) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ π : X.functionFieldˣ, ∀ v ∈ U,
      Scheme.ord (π : X.functionField) v = if v = z then 1 else 0 := by
  classical
  by_cases hzx : z ⤳ x
  · obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
    have hzU : z ∈ U := hzx.mem_open U.isOpen hxU
    haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
    haveI := hU.isLocalization_stalk ⟨x, hxU⟩
    haveI := hu x
    have hPp : (hU.primeIdealOf ⟨z, hzU⟩).asIdeal ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
      have h' : (⟨z, hzU⟩ : U) ⤳ ⟨x, hxU⟩ := Topology.IsInducing.subtypeVal.specializes_iff.1 hzx
      exact (PrimeSpectrum.le_iff_specializes _ _).2 (h'.map hU.isoSpec.hom.continuous)
    obtain ⟨hP0, hmin⟩ := primeIdealOf_minimal X U hU z hzU h1
    obtain ⟨a, haP, ha0, t, htp, hg⟩ := exists_local_generator Γ(X, U) (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal (hU.primeIdealOf ⟨z, hzU⟩).asIdeal
      (hU.primeIdealOf ⟨z, hzU⟩).2 hPp hP0 hmin
    have hf0 : fnOf U (gen_mem hxU) a ≠ 0 := fun h =>
      ha0 (fnOf_injective U (gen_mem hxU) (h.trans (map_zero _).symm))
    refine ⟨U ⊓ X.basicOpen t, ⟨hxU, ?_⟩, Units.mk0 _ hf0, fun v hv => ?_⟩
    · exact (Scheme.mem_basicOpen X t x hxU).2 ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ t).2 htp)
    · simp only [Units.val_mk0]
      split_ifs with hvz
      · subst hvz
        exact ord_eq_one X U hU v hzU a t h1 ha0 haP (fun h => htp (hPp h)) hg
      · exact ord_eq_zero X U hU z hzU a t h1 hg v hv.1 hv.2 hvz
  · refine ⟨⟨(closure {z})ᶜ, isClosed_closure.isOpen_compl⟩, ?_, 1, fun v hv => ?_⟩
    · exact fun h => hzx (specializes_iff_mem_closure.2 h)
    · have hvz : v ≠ z := fun e => hv (e ▸ subset_closure rfl)
      rw [if_neg hvz, Units.val_one]
      exact (unitAt_one v).ord_eq_zero

end GlobalTheory.PrimeDivCartier


open GlobalTheory.PrimeDivCartier in
theorem GlobalTheory.primeDivisor_isCartier : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
    (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ z : X, Order.coheight z = 1 →
      ∃ D : CartierDiv X, D.mult z = 1 ∧ ∀ v, v ≠ z → D.mult v = 0 := by
  intro X _ _ hu z h1
  classical
  haveI : GlobalTheory.IsNormalScheme X := ⟨fun x => inferInstance, fun x => by
    haveI := hu x; exact UniqueFactorizationMonoid.instIsIntegrallyClosed⟩
  choose U hxU π hπ using exists_local_eqn X hu z h1
  have hunit : ∀ x y, y ∈ U x → UnitAt y ((π x : X.functionField) / π y) := by
    intro x y hy
    have h := (GlobalTheory.T.cartier_divisor_mult_characterize X (0 : CartierDiv X)).2.2.2 y (π x / π y) (fun v hv => by
      have hvx : v ∈ U x := hv.mem_open (U x).isOpen hy
      have hvy : v ∈ U y := hv.mem_open (U y).isOpen (hxU y)
      have e := Scheme.ord_mul (X := X) (x := v) (Units.ne_zero (π x / π y)) (Units.ne_zero (π y))
      rw [← Units.val_mul, div_mul_cancel, hπ x v hvx, hπ y v hvy] at e
      rw [(CartierDiv.isEqn_zero v).mult_eq, Units.val_one, (unitAt_one v).ord_eq_zero]
      split_ifs at e <;> omega)
    simpa using (CartierDiv.isEqn_zero y).iff_unitAt.1 h
  let D : CartierDiv X := show cartierGroup X from
    ⟨fun y => germOf y (π y), fun x => ⟨U x, hxU x, π x, fun y hy => germOf_eq_iff.2 (hunit x y hy)⟩⟩
  have hD : ∀ y, D.IsEqn y (π y) := fun y => rfl
  refine ⟨D, ?_, fun v hv => ?_⟩
  · rw [(hD z).mult_eq, hπ z z (hxU z), if_pos rfl]
  · rw [(hD v).mult_eq, hπ v v (hxU v), if_neg hv]
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.PushforwardCohomologyAffineStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.pushforward_cohomology_affine : ∀ (X Y : Scheme.{0}) [CompactSpace X] [X.IsSeparated] [CompactSpace Y] [Y.IsSeparated] (s : Y ⟶ X) (F : Y.Modules) [F.IsQuasicoherent] (H : LB X), IsAmpleLB H → (∀ j, 0 < j → ∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow (H.pull s) c)) j)) → (∀ i, Nonempty (coh ((Scheme.Modules.pushforward s).obj F) i ≃+ coh F i)) ∧ ∀ U : X.Opens, IsAffineOpen U → ∀ j, 0 < j → Subsingleton (cohOn F (s ⁻¹ᵁ U) j) := by
  first | exact @_root_.GlobalTheory.passage_down_of_twist_vanishing | exact _root_.GlobalTheory.passage_down_of_twist_vanishing | (intros; apply _root_.GlobalTheory.passage_down_of_twist_vanishing <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDivisorEquation
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.MonoEqn

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

def ordU (v : Y) : Y.functionFieldˣ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (Scheme.ord (g : Y.functionField) v)
  map_one' := by
    have h := Scheme.ord_mul (x := v) (one_ne_zero (α := Y.functionField))
      (one_ne_zero (α := Y.functionField))
    rw [mul_one] at h
    have h0 : Scheme.ord (1 : Y.functionField) v = 0 := by omega
    simp [h0]
  map_mul' f g := by
    simp [Units.val_mul, Scheme.ord_mul f.ne_zero g.ne_zero, ofAdd_add]

theorem ord_prod_zpow {ι : Type} (J : Finset ι) (u : ι → Y.functionFieldˣ) (m : ι → ℤ) (v : Y) :
    Scheme.ord ((∏ j ∈ J, u j ^ m j : Y.functionFieldˣ) : Y.functionField) v =
      ∑ j ∈ J, m j * Scheme.ord (u j : Y.functionField) v := by
  have h := congrArg Multiplicative.toAdd (map_prod (ordU (Y := Y) v) (fun j => u j ^ m j) J)
  rw [toAdd_prod] at h
  calc Scheme.ord ((∏ j ∈ J, u j ^ m j : Y.functionFieldˣ) : Y.functionField) v
      = Multiplicative.toAdd (ordU v (∏ j ∈ J, u j ^ m j)) := rfl
    _ = ∑ j ∈ J, Multiplicative.toAdd (ordU v (u j ^ m j)) := h
    _ = ∑ j ∈ J, m j * Scheme.ord (u j : Y.functionField) v := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_zpow, toAdd_zpow, smul_eq_mul]
      rfl

end GlobalTheory.Discrepancy.MonoEqn

private theorem unitAt_of_ord_eq_zero_coheight_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {v : X}
    (hv : Order.coheight v = 1) {h : X.functionField} (h0 : h ≠ 0)
    (hord : Scheme.ord h v = 0) : UnitAt v h := by
  haveI := hufd v
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk v) := krullDimLE_of_coheight_le hv.le
  by_cases hF : IsField (X.presheaf.stalk v)
  · obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk v) h
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨b', hbb'⟩ := hF.mul_inv_cancel hb0
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply h0
      rw [← hab, map_zero, zero_div]
    obtain ⟨a', haa'⟩ := hF.mul_inv_cancel ha0
    refine ⟨a * b', ?_, ?_⟩
    · refine isUnit_iff_exists_inv.mpr ⟨a' * b, ?_⟩
      calc a * b' * (a' * b) = (a * a') * (b * b') := by ring
        _ = 1 := by rw [haa', hbb', one_mul]
    · rw [← hab, map_mul]
      have : algebraMap (X.presheaf.stalk v) X.functionField b *
          algebraMap (X.presheaf.stalk v) X.functionField b' = 1 := by
        rw [← map_mul, hbb', map_one]
      rw [eq_div_iff (fun h' => hb0 (IsFractionRing.injective (X.presheaf.stalk v) X.functionField
        (by rw [h', map_zero]))), mul_assoc, mul_comm _ (algebraMap _ _ b), this, mul_one]
  · haveI : IsDiscreteValuationRing (X.presheaf.stalk v) := by
      have hmax : ∀ I : Ideal (X.presheaf.stalk v), I ≠ ⊥ → I.IsPrime → I.IsMaximal :=
        Ring.krullDimLE_one_iff_of_isPrime_bot.mp inferInstance
      have hne : IsLocalRing.maximalIdeal (X.presheaf.stalk v) ≠ ⊥ :=
        IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hF
      have key := (IsDiscreteValuationRing.TFAE (X.presheaf.stalk v) hF).out 4 1
      exact key.mp ⟨inferInstance, ⟨IsLocalRing.maximalIdeal _, ⟨hne, inferInstance⟩,
        fun P hP => IsLocalRing.eq_maximalIdeal (hmax P hP.1 hP.2)⟩⟩
    have h1 : Scheme.ordHom v hv h = 1 := by
      have := (Scheme.ord_eq_iff hv h0 (n := 0)).mp hord
      simpa using this
    have hmem : h ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk v) (K := X.functionField)) :=
      MonoidHom.mem_mker.mpr h1
    rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hmem
    obtain ⟨a, ha, rfl⟩ := hmem
    exact ⟨a, ha, rfl⟩

private theorem Scheme_ord_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (v : X) :
    Scheme.ord (1 : X.functionField) v = 0 := by
  have h := Scheme.ord_mul (x := v) (one_ne_zero : (1 : X.functionField) ≠ 0) one_ne_zero
  rw [mul_one] at h
  omega

private theorem Scheme_ord_units_inv {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : (X.functionField)ˣ) (v : X) :
    Scheme.ord ((g⁻¹ : (X.functionField)ˣ) : X.functionField) v =
      - Scheme.ord (g : X.functionField) v := by
  have h := Scheme.ord_mul (x := v) g.ne_zero (g⁻¹).ne_zero
  rw [Units.mul_inv, Scheme_ord_one] at h
  omega

private theorem unitAt_of_ord_eq_zero_on_generizations {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {y : X}
    (h : (X.functionField)ˣ)
    (hord : ∀ v, v ⤳ y → Order.coheight v = 1 → Scheme.ord (h : X.functionField) v = 0) :
    UnitAt y (h : X.functionField) := by
  haveI : GlobalTheory.IsNormalScheme X :=
    ⟨fun x => inferInstance, fun x => by haveI := hufd x; infer_instance⟩
  have key : ∀ g : (X.functionField)ˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → Scheme.ord (g : X.functionField) v = 0) →
      RegAt y (g : X.functionField) := by
    intro g hg
    apply regAt_of_forall_coheight_eq_one
    intro z hz hz1
    exact (unitAt_of_ord_eq_zero_coheight_one hufd hz1 g.ne_zero (hg z hz hz1)).regAt
  obtain ⟨a, ha⟩ := key h hord
  obtain ⟨b, hb⟩ := key h⁻¹ (fun v hv hv1 => by rw [Scheme_ord_units_inv, hord v hv hv1, neg_zero])
  refine ⟨a, ?_, ha⟩
  have hab : algebraMap (X.presheaf.stalk y) X.functionField (a * b) =
      algebraMap (X.presheaf.stalk y) X.functionField 1 := by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact isUnit_iff_exists_inv.mpr ⟨b, IsFractionRing.injective _ _ hab⟩


open GlobalTheory.Discrepancy.MonoEqn in
theorem GlobalTheory.Discrepancy.IsSncChart.isEqn_monomial : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ D : CartierDiv Y, D.supp ≤ B → D.IsEqn y (∏ j ∈ J, u j ^ D.mult (w j)) := by
  intro k _ _ Y _ _ q n _ B y U hy z J w u hc D hD
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have hufd : ∀ x : Y, UniqueFactorizationMonoid (Y.presheaf.stalk x) :=
    fun x => AbelianProjective.ufd_stalk (K := k) q x
  obtain ⟨h, hh⟩ := D.exists_isEqn y
  obtain ⟨W, hyW, hW⟩ := hh.exists_nhds
  have key : ∀ v, v ⤳ y → Order.coheight v = 1 →
      Scheme.ord (((∏ j ∈ J, u j ^ D.mult (w j)) : Y.functionFieldˣ) : Y.functionField) v =
        D.mult v := by
    intro v hv hv1
    rw [ord_prod_zpow]
    by_cases hex : ∃ j ∈ J, v = w j
    · obtain ⟨j0, hj0, rfl⟩ := hex
      rw [Finset.sum_eq_single j0]
      · rw [hc.ord_self j0 hj0, mul_one]
      · intro j hj hne
        rw [hc.ord_other j hj (w j0) hv (fun heq => hne (hc.inj hj hj0 heq.symm)), mul_zero]
      · intro h'
        exact absurd hj0 h'
    · have h0 : D.mult v = 0 := by
        by_contra hne
        exact hex ((hc.mem v hv hv1).mp (hD (CartierDiv.mem_supp_of_mult_ne_zero hne)))
      rw [h0]
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [hc.ord_other j hj v hv (fun heq => hex ⟨j, hj, heq⟩), mul_zero]
  show D.germ y = germOf y _
  rw [show D.germ y = germOf y h from hh, germOf_eq_iff]
  have hu := unitAt_of_ord_eq_zero_on_generizations hufd ((∏ j ∈ J, u j ^ D.mult (w j)) * h⁻¹)
    (fun v hv hv1 => by
      rw [Units.val_mul, Scheme.ord_mul (Units.ne_zero _) (Units.ne_zero _), Scheme_ord_units_inv,
        key v hv hv1, ← (hW v (hv.mem_open W.isOpen hyW)).mult_eq, add_neg_cancel])
  simpa [div_eq_mul_inv] using hu
end
end

