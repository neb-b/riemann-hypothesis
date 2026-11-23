module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0052
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0058
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0054
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0056
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0043
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.WeilBound.CoreStatements.HodgeTatePoints.IsPullbackWhisker
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0158
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0059
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CdAffine

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cf

theorem fib_inj_of (htan : type_of% @_root_.PositivityTheory.HtPt.Ce.geompf_tan) (hbc : type_of% @_root_.PositivityTheory.HtPt.Ce.germ_bc)
    (hinj : type_of% @_root_.PositivityTheory.HtPt.Cocp.tanpf_inj) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), FibPF t (x (IsLocalRing.closedPoint k)) → ConjInj g.B p := by
  intro E _ _ _ H _ hs X0 t hP k _ p _ _ x d g ⟨k', _, _, x', hx, h⟩
  obtain ⟨Ω, _, _, y, a, -, e⟩ := exists_common x (IsLocalRing.closedPoint k) x' hx
  obtain ⟨b, rfl⟩ : ∃ b : k →+* Ω, y = spMap b := ⟨(Spec.preimage y).hom, (Spec.map_preimage y).symm⟩
  have : CharP Ω p := charP_of_injective_ringHom b.injective p
  have h' : GeomPF t (spMap b ≫ x) := e ▸ (geompf_bc E H X0 t).1 k' Ω a x' h
  obtain ⟨g₂, hg, -⟩ := hbc E H hs X0 t k Ω b x d g
  exact (PositivityTheory.HtPt.Cc.conjInj_map hg p).1 (hinj E H hs X0 t Ω p _ d g₂ (htan E H hs X0 t hP Ω p _ h'))

theorem isMapOf_cancel {R R₂ R₃ O : Type} [CommRing R] [CommRing R₂] [CommRing R₃] [CommRing O] [StarRing O] {d : ℕ}
    {f : R →+* R₂} {g : R₂ →+* R₃} {B : Germ.FB R d O} {B₂ : Germ.FB R₂ d O} {B₃ : Germ.FB R₃ d O}
    (h : IsMapOf f B B₂) (h' : IsMapOf (g.comp f) B B₃) : IsMapOf g B₂ B₃ := by
  exact
    { F := fun i => by simp only [h'.F i, h.F i, MvPowerSeries.map_comp, RingHom.comp_apply]
      act := fun a i => by simp only [h'.act a i, h.act a i, MvPowerSeries.map_comp, RingHom.comp_apply]
      ph1 := by simp only [h'.ph1, h.ph1, MvPowerSeries.map_comp, RingHom.comp_apply]
      ph2 := by simp only [h'.ph2, h.ph2, MvPowerSeries.map_comp, RingHom.comp_apply]
      sy := by simp only [h'.sy, h.sy, MvPowerSeries.map_comp, RingHom.comp_apply]
      ad := fun a => by simp only [h'.ad a, h.ad a, MvPowerSeries.map_comp, RingHom.comp_apply] }

theorem spMap_comp' {R R₂ R₃ : Type} [CommRing R] [CommRing R₂] [CommRing R₃] (f : R →+* R₂) (g : R₂ →+* R₃) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem dualMap_comp' {R R₂ R₃ : Type} [CommRing R] [CommRing R₂] [CommRing R₃] (f : R →+* R₂) (g : R₂ →+* R₃) :
    (GlobalTheory.CompanionTheory.Ar.dualMap g).comp (GlobalTheory.CompanionTheory.Ar.dualMap f) = GlobalTheory.CompanionTheory.Ar.dualMap (g.comp f) := by
  ext r <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem exists_factor {R A : Type} [CommRing R] [IsLocalRing R] [CommRing A] {X : Scheme.{0}} (x : Sp R ⟶ X)
    (j : Sp A ⟶ X) [IsOpenImmersion j] (h : GlobalTheory.CompanionTheory.Ar.centre x ∈ Set.range j) : ∃ a : A →+* R, x = spMap a ≫ j := by
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint q).map x.continuous).mem_open j.isOpenEmbedding.isOpen_range h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j x hr)).hom, ?_⟩
  show x = Spec.map (Spec.preimage (IsOpenImmersion.lift j x hr)) ≫ j
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem finite_nonint {K : Type} [Field K] (C : ACurve K) (x : K) : {i | ¬ C.v i x ≤ 1}.Finite := by
  by_cases h : x = 0
  · simp [h]
  · exact (C.fin x h).subset fun i hi e => hi e.le

theorem family_ex_of' (hfib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), FibPF t (x (IsLocalRing.closedPoint k)) → ConjInj g.B p)
    (hbc : type_of% @_root_.PositivityTheory.HtPt.Ce.germ_bc) (huniv : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.GermUniv.germ_chart_universal) (hiso : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.Conj.germ_iso_main)
    (haff : type_of% @_root_.PositivityTheory.HtPt.Cd.germ_affine) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∃ (d : ℕ) (F : Family C p d (𝓞 E)) (g : GermAt t z d), g.B = F.B ∧ ∀ i, ∃ gi : GermAt t (Y.x i) d, ∀ l, IsCombAtG t z g.tg (fun j => lin (F.φ i) 1 j l) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) := by
  intro E _ _ _ H _ hs X0 t hP K _ p _ _ C z Y hY
  have bc : ∀ {S S₂ : Type} [CommRing S] [CommRing S₂] (f : S →+* S₂) {x : Sp S ⟶ X0} {x₂ : Sp S₂ ⟶ X0}
      (_ : x₂ = spMap f ≫ x) {d : ℕ} (g : GermAt t x d), ∃ g₂ : GermAt t x₂ d, IsMapOf f g.B g₂.B ∧
        ∀ l, g₂.tg l = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l := by
    intro S S₂ _ _ f x x₂ e d g
    subst e
    exact hbc E H hs X0 t S S₂ f x d g
  obtain ⟨A, _, j, d, _, hj, ⟨gA⟩⟩ := haff E H hs X0 t hP (GlobalTheory.CompanionTheory.Ar.centre z)
  obtain ⟨a, ha⟩ := exists_factor z j hj
  obtain ⟨g, hg, hgt⟩ := bc a ha gA
  obtain ⟨φ₀, ψ₀, lam₀, h₀, h₀t⟩ := hiso E H hs X0 t hP K z d g g
  have loc : ∀ i : C.I, ∃ (gi : GermAt t (Y.x i) d) (BK : Germ.FB K d (𝓞 E)) (φ ψ : Germ.Pt K 1 d)
      (lam : Germ.PS K 2 d), IsMapOf (C.v i).valuationSubring.subtype gi.B BK ∧ GlobalTheory.CompanionTheory.Ar.Conj.IsIso g.B BK φ ψ lam ∧
      (GlobalTheory.CompanionTheory.Ar.centre (Y.x i) ∈ Set.range j → φ = φ₀ ∧ ψ = ψ₀ ∧ lam = lam₀) ∧
      ∀ l, IsCombAtG t z g.tg (fun j => lin φ 1 j l)
        (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) := by
    intro i
    by_cases hi : GlobalTheory.CompanionTheory.Ar.centre (Y.x i) ∈ Set.range j
    · obtain ⟨b, hb⟩ := exists_factor (Y.x i) j hi
      obtain ⟨gi, hgi, hgit⟩ := bc b hb gA
      have e : spMap ((C.v i).valuationSubring.subtype.comp b) = spMap a := by
        rw [← cancel_mono j, ← ha, ← spMap_comp', Category.assoc, ← hb]
        exact Y.gen i
      obtain rfl : (C.v i).valuationSubring.subtype.comp b = a :=
        congrArg CommRingCat.Hom.hom (Spec.map_injective e)
      refine ⟨gi, g.B, φ₀, ψ₀, lam₀, isMapOf_cancel hgi hg, h₀, fun _ => ⟨rfl, rfl, rfl⟩, fun l => ?_⟩
      rw [hgit, ← Category.assoc, spMap_comp', dualMap_comp', ← hgt]
      exact h₀t l
    · obtain ⟨d', ⟨gi⟩⟩ := PositivityTheory.HtPt.Cd.germ_local E H hs X0 t hP _ (Y.x i)
      obtain ⟨g₂, hg₂, hg₂t⟩ := bc (C.v i).valuationSubring.subtype (Y.gen i).symm gi
      obtain rfl := (huniv E H hs X0 t K z d g).1 d' g₂
      obtain ⟨φ, ψ, lam, h, ht⟩ := hiso E H hs X0 t hP K z d g g₂
      exact ⟨gi, g₂.B, φ, ψ, lam, hg₂, h, fun h' => absurd h' hi, fun l => hg₂t l ▸ ht l⟩
  choose gi BK φ ψ lam hK hI hgood ht using loc
  have red : ∀ i : C.I, ∃ Bk : Germ.FB (IsLocalRing.ResidueField (C.v i).valuationSubring) d (𝓞 E),
      IsMapOf (IsLocalRing.residue _) (gi i).B Bk ∧ ConjInj Bk p := by
    intro i
    obtain ⟨gk, hk, -⟩ := bc (IsLocalRing.residue _) rfl (gi i)
    have h0 : (p : (C.v i).valuationSubring) = 0 := Subtype.ext (by simp)
    have : CharP (IsLocalRing.ResidueField (C.v i).valuationSubring) p :=
      (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
        rw [← map_natCast (IsLocalRing.residue (C.v i).valuationSubring), h0, map_zero])
    refine ⟨gk.B, hk, hfib E H hs X0 t hP _ p _ d gk ?_⟩
    have e : (spMap (IsLocalRing.residue (C.v i).valuationSubring) ≫ Y.x i) (IsLocalRing.closedPoint _) =
        GlobalTheory.CompanionTheory.Ar.centre (Y.x i) :=
      (Scheme.Hom.comp_apply _ _ _).trans (congrArg (Y.x i) (IsLocalRing.comap_closedPoint (IsLocalRing.residue _)))
    exact e ▸ hY i
  choose Bk hk hinj using red
  refine ⟨d, ⟨g.B, fun i => (gi i).B, BK, Bk, hK, hk, hinj, φ, ψ, lam, hI, ?_⟩, g, rfl, fun i => ⟨gi i, ht i⟩⟩
  refine ((Y.ae j.opensRange hj).union (Set.finite_iUnion fun a : Fin d => Set.finite_iUnion fun b : Fin d =>
    (finite_nonint C (lin φ₀ 1 a b)).union ((finite_nonint C (lin ψ₀ 1 a b)).union
      (finite_nonint C (bil lam₀ 1 1 a b))))).subset fun i hi => ?_
  by_cases hc : GlobalTheory.CompanionTheory.Ar.centre (Y.x i) ∈ Set.range j
  · obtain ⟨e₁, e₂, e₃⟩ := hgood i hc
    rw [Set.mem_ofPred_eq, e₁, e₂, e₃] at hi
    simp only [not_forall, not_and_or] at hi
    obtain ⟨a, b, h⟩ := hi
    exact Or.inr (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨b, h⟩⟩)
  · exact Or.inl hc

theorem family_ex_of (htan : type_of% @_root_.PositivityTheory.HtPt.Ce.geompf_tan)
    (hbc : type_of% @_root_.PositivityTheory.HtPt.Ce.germ_bc) (hinj : type_of% @_root_.PositivityTheory.HtPt.Cocp.tanpf_inj)
    (haff : type_of% @_root_.PositivityTheory.HtPt.Cd.germ_affine) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∃ (d : ℕ) (F : Family C p d (𝓞 E)) (g : GermAt t z d), g.B = F.B ∧ ∀ i, ∃ gi : GermAt t (Y.x i) d, ∀ l, IsCombAtG t z g.tg (fun j => lin (F.φ i) 1 j l) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) :=
  family_ex_of' (fib_inj_of htan hbc hinj) hbc PositivityTheory.HtPt.Cd.germ_univ PositivityTheory.HtPt.Cd.germ_iso haff

end PositivityTheory.HtPt.Cf
