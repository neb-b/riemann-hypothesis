module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeBasisPullbackDominant
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem Lat.pull_isFrameAt_comp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (E E' : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω' E'] (j : E →+ E'), Dominates ξ' ξ f i → (∀ (a : Ω) (e : E), j (a • e) = i a • j e) → ∀ (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1), LinearIndependent Ω' (fun k => j (b k)) → L.IsFrameAt b ⟨f p'.1, h⟩ → (L.pull ξ' f j).IsFrameAt (fun k => j (b k)) p' := by
  intro X Ω _ ξ X' Ω' _ ξ' f i E E' _ _ _ _ j hD hj L r b p' h hli hb
  obtain ⟨h', hreg, -⟩ := pull_reg_and_gen X Ω ξ X' Ω' ξ' f i hD p'
  refine ⟨hli, ?_⟩
  rw [Lat.pull_apply L hD]
  have hL : L ⟨f p'.1, hD.specializes p'⟩ = Submodule.span (regAt ξ ⟨f p'.1, h⟩) (Set.range b) := hb.2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ Submodule.span (regAt ξ ⟨f p'.1, h⟩) (Set.range b) := by
      rw [← hL]; exact he
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun k => ⟨i (c k), hreg _ (c k).2⟩, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => (hj (c k) (b k)).symm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨b k, ?_, rfl⟩
    show b k ∈ (L ⟨f p'.1, hD.specializes p'⟩ : Set E)
    rw [hL]
    exact Submodule.subset_span ⟨k, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEqOfCodimOneEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem lat_agree_of_height_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → ∀ (T : Set (Cpt ξ)), (∀ p ∈ T, ∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p ∈ T, IsIntegrallyClosed (X.presheaf.stalk p.1)) → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (L L' : Lat ξ E) (r : ℕ) (V : Submodule Ω E), L.IsVBOn T r V → L'.IsVBOn T r V → (∀ p ∈ T, ringKrullDim (X.presheaf.stalk p.1) = 1 → L p = L' p) → ∀ p ∈ T, L p = L' p :=
  @PositivityTheory.UnitarySelfGeneration.lattices_agree_of_height_one

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeRangeOfStalk
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

theorem lat_eq_range : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (h : IsCptGen ξ) (G : Over X) [GrpObj G] (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (Ep : Type) [AddCommGroup Ep] [Module (regAt ξ p) Ep] (Mp : LieModel G (regPt h p) Ep) (j : Ep →ₗ[regAt ξ p] E), (∀ e, (M.pt (j e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left) → (M.lat p : Set E) = Set.range j :=
  @PositivityTheory.Xgn.normal_lattice_range

end GlobalTheory.CompanionTheory.Ar.LieStalk
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MapDomainRelationLiftCommutingSquare
section
namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem HostAut.s_symm_s (g : HostAut H) (a : 𝓞 E) : g.s (g.symm.s a) = a :=
  RingOfIntegers.ext (g.σ.apply_symm_apply (a : E))

theorem HostAut.hostAut_symm_s_s (g : HostAut H) (a : 𝓞 E) : g.symm.s (g.s a) = a :=
  RingOfIntegers.ext (g.σ.symm_apply_apply (a : E))

theorem HostAut.hostAut_refl_s (a : 𝓞 E) : (HostAut.refl H).s a = a :=
  RingOfIntegers.ext rfl

theorem oAct_eq {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] {u v : OAct O G}
    (h : ∀ a, u.act a = v.act a) : u = v := by
  cases u
  cases v
  have : ∀ a, _ = _ := h
  obtain rfl : _ = _ := funext this
  rfl

theorem twistSAB_eq_of_act {S : Scheme.{0}} (t : SAB H S) (g : HostAut H)
    (h : ∀ a, t.act.act (g.s a) = t.act.act a) : twistSAB t g = t := by
  cases t with
  | mk G semi act PP cub sym adj prim =>
    have hact : twistAct act g.s = act := oAct_eq h
    have key : ∀ (act' : OAct (𝓞 E) G) (_ : act' = act) (adj' prim'),
        (SAB.mk G semi act' PP cub sym adj' prim' : SAB H S) = SAB.mk G semi act PP cub sym adj prim := by
      intro act' e adj' prim'
      subst e
      rfl
    exact key _ hact _ _

theorem twistSAB_twistSAB {S : Scheme.{0}} (t : SAB H S) (g g' : HostAut H)
    (h : ∀ a, g.s (g'.s a) = a) : twistSAB (twistSAB t g) g' = t := by
  cases t with
  | mk G semi act PP cub sym adj prim =>
    have hact : twistAct (twistAct act g.s) g'.s = act := oAct_eq fun a => congrArg act.act (h a)
    have key : ∀ (act' : OAct (𝓞 E) G) (_ : act' = act) (adj' prim'),
        (SAB.mk G semi act' PP cub sym adj' prim' : SAB H S) = SAB.mk G semi act PP cub sym adj prim := by
      intro act' e adj' prim'
      subst e
      rfl
    exact key _ hact _ _

theorem twistSAB_symm_refl (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0})
    (t : SAB H S) (g : HostAut H) :
    twistSAB (twistSAB t g) g.symm = t ∧ twistSAB (twistSAB t g.symm) g = t ∧
      twistSAB t (HostAut.refl H) = t :=
  ⟨twistSAB_twistSAB t g g.symm g.s_symm_s, twistSAB_twistSAB t g.symm g g.hostAut_symm_s_s,
    twistSAB_eq_of_act t _ fun a => congrArg t.act.act (HostAut.hostAut_refl_s a)⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSet
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem mem_btOrder_iff_mem_btSet : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → R), f ∈ Γ.btOrder U ↔ f ∈ Γ.btSet U :=
  PositivityTheory.HtPt.Twhopf.mem_order

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MinorRatioRegularOfInvertibleStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_ratio_regular_of_invertible : ∀ (K : Type) [Field K] (R : Subring K) (n r : ℕ) (A : Matrix (Fin n) (Fin r) K) (B : Matrix (Fin r) (Fin n) K) (G : Matrix (Fin r) (Fin r) K) (a : K) (k : Fin r) (J : Fin ((k : ℕ) + 1) → Fin n), (∀ j l, A j l ∈ R) → (∀ l j, B l j ∈ R) → B * A = 1 → a ≠ 0 → ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ≠ 0 → (∀ l j, ((a • (A * G)).submatrix (Function.update J l j) (Fin.castLE k.2)).det / ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ∈ R) → ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧ (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧ ∀ l, D l ∈ flagStep K (fun c i => G i c) ((k : ℕ) + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios | exact GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NotInFibreOfIsUnit
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem regAt_isLocalRing (q : Cpt ξ) : IsLocalRing (regAt ξ q) :=
  IsLocalRing.of_surjective' (genMap ξ q).rangeRestrict (genMap ξ q).rangeRestrict_surjective

theorem not_inFibre_of_isUnit {q : Cpt ξ} {p : ℕ} (h : IsUnit (p : regAt ξ q)) : ¬ InFibre ξ p q := by
  obtain ⟨v, hv⟩ := h.exists_right_inv
  have e : (p : Ω) * (v : Ω) = 1 := by
    have := congrArg (Subtype.val) hv
    simpa using this
  have hp : (p : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one e
  have hreg : (p : Ω) ∈ regAt ξ q := natCast_mem (regAt ξ q) p
  have hinv : (p : Ω)⁻¹ ∈ regAt ξ q := by
    rw [eq_comm.1 (eq_inv_of_mul_eq_one_right e)]
    exact v.2
  exact not_not.2 ⟨hp, hreg, hinv⟩

theorem inFibre_unique {q : Cpt ξ} {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (h : InFibre ξ p q)
    (h' : InFibre ξ p' q) : p' = p := by
  by_contra hne
  haveI := regAt_isLocalRing (ξ := ξ) q
  have hc : IsCoprime (p : ℤ) (p' : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hp').2 (Ne.symm hne))
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (regAt ξ q))
  simp only [eq_intCast, Int.cast_natCast] at hab
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with hu | hu
  · exact not_inFibre_of_isUnit (isUnit_of_mul_isUnit_right hu) h
  · exact not_inFibre_of_isUnit (isUnit_of_mul_isUnit_right hu) h'

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrderValuationCompare
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem z_value_of_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (L : Lat ξ Ω) (σ ϖ : Ω) (M : ℕ) (a : ℤ) (V C : Type) [CommRing V] [IsLocalRing V] [Field C] [Algebra V C] (z : Spec (CommRingCat.of V) ⟶ X) (h : genPt ξ ⤳ centre z) (e : Ω) (γ π : C), IsCptGen ξ → OrderAt L σ ϖ M a ⟨centre z, h⟩ → L.IsGenAt ⟨centre z, h⟩ e → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) (σ / e) γ → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) ϖ π → π ≠ 0 → ∃ u : Vˣ, γ ^ M = π ^ a * algebraMap V C u :=
  @PositivityTheory.Xgn.valuation_at_centre_order

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PieceLocalizationAtElement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem exists_basicOpen_piece (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (U : X.Opens) (R : Subring Ω) (a : Ω) (hc : IsCptGen ξ) (hP : IsPiece ξ U R) (haR : a ∈ R)
    (ha0 : a ≠ 0) :
    ∃ U' : X.Opens, IsPiece ξ U' (locSub R a) ∧ ∀ q : Cpt ξ, q.1 ∈ U' ↔ q.1 ∈ U ∧ unitAt ξ q a := by
  by_cases hη : genPt ξ ∈ U
  swap
  · have hno : ∀ q : Cpt ξ, q.1 ∉ U := fun q hq => hη (q.2.mem_open U.isOpen hq)
    refine ⟨U, ⟨hP.affine, hP.spec, fun b => ?_⟩, fun q => ?_⟩
    · refine ⟨fun _ q hq => absurd hq (hno q), fun _ => le_locSub R a ?_⟩
      exact (hP.ring b).2 fun q hq => absurd hq (hno q)
    · exact ⟨fun h => absurd h (hno q), fun h => h.1⟩
  obtain ⟨-, hrng⟩ := _root_.GlobalTheory.CompanionTheory.Ar.regAt_sections X Ω ξ hc U hη hP.spec
  obtain ⟨s, hs⟩ := (hrng a).2 ((hP.ring a).1 haR)
  have hga : ∀ (q : Cpt ξ) (hq : q.1 ∈ U), genMap ξ q (X.presheaf.germ U q.1 hq s) = a :=
    fun q hq => (genMap_germ_eq_stalk_closed ξ q U hq hη s).trans hs
  have hmem : ∀ q : Cpt ξ, q.1 ∈ X.basicOpen s ↔ q.1 ∈ U ∧ unitAt ξ q a := by
    intro q
    constructor
    · intro hq
      have hqU : q.1 ∈ U := X.basicOpen_le s hq
      have hu := (Scheme.mem_basicOpen X s q.1 hqU).1 hq
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have h1 : a * genMap ξ q v = 1 := by
        rw [← hga q hqU, ← map_mul, hv, map_one]
      exact ⟨hqU, ha0, ⟨_, hga q hqU⟩, ⟨v, (inv_eq_of_mul_eq_one_right h1).symm⟩⟩
    · rintro ⟨hqU, -, -, ⟨t, ht⟩⟩
      refine (Scheme.mem_basicOpen X s q.1 hqU).2 (isUnit_iff_exists_inv.2 ⟨t, hc.inj q ?_⟩)
      rw [map_mul, map_one, hga q hqU, ht, mul_inv_cancel₀ ha0]
  have hreg : ∀ c : Ω, c ∈ regAt ξ (Subtype.mk (genPt ξ) specializes_rfl : Cpt ξ) := by
    intro c
    obtain ⟨y, hy⟩ := hc.bij.2 c
    refine ⟨y, ?_⟩
    have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
      TopCat.Presheaf.stalkSpecializes_refl _ _
    change (X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
      Scheme.stalkClosedPointTo ξ).hom y = c
    rw [e]
    exact hy
  have hη' : genPt ξ ∈ X.basicOpen s :=
    (hmem (Subtype.mk (genPt ξ) specializes_rfl : Cpt ξ)).2 ⟨hη, ha0, hreg a, hreg a⁻¹⟩
  refine ⟨X.basicOpen s, ⟨hP.affine.basicOpen s, fun q hq => hP.spec q (X.basicOpen_le s hq),
    fun b => ?_⟩, hmem⟩
  constructor
  · intro hb q hq
    obtain ⟨k, hk⟩ := (mem_locSub_iff haR ha0 b).1 hb
    obtain ⟨hqU, -, -, hinv⟩ := (hmem q).1 hq
    have h1 := (hP.ring _).1 hk q hqU
    have e : b = a⁻¹ ^ k * (a ^ k * b) := by
      rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ha0), _root_.one_mul]
    rw [e]
    exact (regAt ξ q).mul_mem ((regAt ξ q).pow_mem hinv _) h1
  · intro hb
    obtain ⟨-, hrng'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.regAt_sections X Ω ξ hc (X.basicOpen s) hη'
      (fun q hq => hP.spec q (X.basicOpen_le s hq))
    obtain ⟨t, ht⟩ := (hrng' b).2 hb
    have hloc := hP.affine.isLocalization_basicOpen s
    obtain ⟨n, c, hcn⟩ := IsLocalization.Away.surj s t
    have hres : ∀ x : Γ(X, U),
        (X.presheaf.germ (X.basicOpen s) (genPt ξ) hη' ≫ Scheme.stalkClosedPointTo ξ).hom
          (algebraMap Γ(X, U) Γ(X, X.basicOpen s) x) =
        (X.presheaf.germ U (genPt ξ) hη ≫ Scheme.stalkClosedPointTo ξ).hom x := by
      intro x
      have := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le s)) (genPt ξ) hη' x
      exact congrArg (Scheme.stalkClosedPointTo ξ).hom this
    have key : a ^ n * b = (X.presheaf.germ U (genPt ξ) hη ≫ Scheme.stalkClosedPointTo ξ).hom c := by
      have := congrArg (X.presheaf.germ (X.basicOpen s) (genPt ξ) hη' ≫
        Scheme.stalkClosedPointTo ξ).hom hcn
      rw [map_mul, map_pow, hres, hres, hs, ht] at this
      rw [← this, _root_.mul_comm]
    refine (mem_locSub_iff haR ha0 b).2 ⟨n, (hP.ring _).2 fun q hq => ?_⟩
    rw [key]
    exact (hrng _).1 ⟨c, rfl⟩ q hq

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperDominatingSurjectiveStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_dominating_surjective : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (s' : X' ⟶ Spec (CommRingCat.of ℤ)) (f : X' ⟶ X) (i : Ω →+* Ω'), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → IsProper s' → Dominates ξ' ξ f i → Function.Surjective f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.surjective_of_dominates | exact GlobalTheory.CompanionTheory.Ar.FlagBun.surjective_of_dominates | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.surjective_of_dominates <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalization
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem chart_regAt_localisation : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ), InChart M.ξ x c p → (∀ a ∈ chRing o x c, a ∈ regAt M.ξ p) ∧ ∀ a : Ω, a ∈ regAt M.ξ p ↔ ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, unitAt M.ξ p v ∧ a = u / v :=
  PositivityTheory.HtPt.Ma.regat_loc

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLeIffSpecializes
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_le_regAt_iff_specializes : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (p q : Cpt M.ξ), regAt M.ξ p ≤ regAt M.ξ q ↔ q.1 ⤳ p.1 :=
  @PositivityTheory.HtPt.Ma.reg_le_spec

end GlobalTheory.CompanionTheory.Ar
end

