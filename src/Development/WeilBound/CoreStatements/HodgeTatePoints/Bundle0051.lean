module

public import Mathlib
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0006
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0050
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0003
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtExistsBc
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNefF
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0044

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GhModel
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

set_option backward.isDefEq.respectTransparency false

namespace PositivityTheory.HtPt.Gh

open GlobalTheory.CompanionTheory.Ar.LieTangent

section Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem htDual_le_lat {p : ℕ} (hpS : p ∈ S) (s : CMType H ⊕ CMType H) (q q' : Cpt 𝔐.ξ) (hqq : q'.1 ⤳ q.1)
    (hq : InFibre 𝔐.ξ p q) (hu : ∀ p' ∈ S, InFibre 𝔐.ξ p' q → p' = p) (hq' : ∀ p' ∈ S, ¬ InFibre 𝔐.ξ p' q')
    (hreg : ∀ a, 𝔐.emb s a ∈ regAt 𝔐.ξ q) (e : 𝔐.Li)
    (he : e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q) : e ∈ 𝔐.M.lat q' := by
  obtain ⟨U, hU, b, -, hb⟩ := 𝔐.vb s q trivial
  have h1 := (hb q trivial hU).2
  have h2 := (hb q' trivial (hqq.mem_open U.isOpen hU)).2
  rw [Lat.patch_of_unique _ _ _ hpS hq hu] at h1
  rw [Lat.patch_of_not _ _ _ hq'] at h2
  have h3 : e ∈ Submodule.span (regAt 𝔐.ξ q) (Set.range b) := by
    rw [← h1]
    cases s with
    | inr τ => exact he
    | inl τ =>
      exact Submodule.subset_span ⟨𝔐.M.mem_eigSp_of_mem_htDual _ _ _ _ he, fun d _ =>
        Submodule.smul_mem _ (⟨_, hreg d⟩ : regAt 𝔐.ξ q) he⟩
  clear he
  induction h3 using Submodule.span_induction with
  | mem x hx =>
    have : x ∈ Submodule.span (regAt 𝔐.ξ q') (Set.range b) := Submodule.subset_span hx
    rw [← h2] at this
    exact this.1
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨_, t, rfl⟩ := a
    exact Submodule.smul_mem _ (⟨genMap 𝔐.ξ q t, _, genMap_specializes q q'.2 hqq t⟩ : regAt 𝔐.ξ q') hx

end Reg

set_option maxHeartbeats 1000000 in
theorem hodge_tate_free_sandwich : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (κ : Ω), HTFree 𝔐 p → Sandwich 𝔐 p κ → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra O' C], v.Integers O' → v (p : C) < 1 → ∀ (z : Sp O' ⟶ 𝔐.X) (EC : Type) [AddCommGroup EC] [Module C EC] [Module O' EC] [IsScalarTower O' C EC] (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) EC) (ρC : 𝓞 E →+* Module.End C EC) (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* O') (κz : O'), MC.IsActOf 𝔐.t.act.act ρC → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) → GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z κ κz → 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O' ≤ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC ∧ (∀ w ∈ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC, κz • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O') ∧ (𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC).FG := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p hp hpS κ hfree hsand C _ _ v O' _ _ _ hv hvp z EC _ _ _ _ MC
    ρC s σ κz hact hσ hκ
  have hξ := 𝔐.tie.gen
  haveI := 𝔐.t.semi.smooth
  have h : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have h' : genPt 𝔐.ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) := 𝔐.all _
  have hsp := centre_specializes (algebraMap O' C) z
  have hpu : ¬ IsUnit (p : O') := fun hu => by
    have := hv.one_of_isUnit hu
    rw [map_natCast] at this
    exact hvp.ne this
  have hq : InFibre 𝔐.ξ p ⟨centre z, h⟩ := fun hu => hpu ((unitAt_centre_iff hξ z h p).1 hu)
  have hu : ∀ p' ∈ S, InFibre 𝔐.ξ p' ⟨centre z, h⟩ → p' = p := by
    intro p' hp' hf
    by_contra hne
    have hc : IsCoprime (p' : O') (p : O') :=
      Nat.Coprime.cast ((Nat.coprime_primes (𝔐.S_prime p' hp') hp.out).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h1 | h1
    · exact hf ((unitAt_centre_iff hξ z h p').2 (isUnit_of_mul_isUnit_right h1))
    · exact hpu (isUnit_of_mul_isUnit_right h1)
  have hq' : ∀ p' ∈ S, ¬ InFibre 𝔐.ξ p' ⟨_, h'⟩ := fun p' hp' hf =>
    hf ((unitAt_centre_iff hξ _ h' p').2 (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (𝔐.S_prime p' hp').ne_zero)))
  have hreg : ∀ a, 𝔐.emb s a ∈ regAt 𝔐.ξ ⟨centre z, h⟩ := fun a => by
    obtain ⟨_, t, ht, -⟩ := hσ a
    exact ⟨t, ht⟩
  obtain ⟨n, βb, gm, hβ, hVal⟩ := exists_frame 𝔐.M z MC h h'
  haveI : FiniteDimensional Ω 𝔐.Li := Module.Finite.of_basis βb
  obtain ⟨U, hU, b, hbs, hb⟩ := hfree.2 s ⟨centre z, h⟩ hq
  obtain ⟨hli, hbq⟩ := hb _ hq hU
  obtain ⟨f, hf1, hf2⟩ := exists_predual b hli hbs
  have hw : ∀ j, ∃ w ∈ omP 𝔐 p ⟨centre z, h⟩, (𝔐.Vgen s).dualRestrict w = b j := fun j => by
    have : b j ∈ ((omP 𝔐 p).map (𝔐.Vgen s).dualRestrict) ⟨centre z, h⟩ := by
      rw [hbq]; exact Submodule.subset_span ⟨j, rfl⟩
    exact this
  choose w hw1 hw2 using hw
  have hw3 : ∀ j (e : 𝔐.Vgen s), w j e = b j e := fun j e => by rw [← hw2]; rfl
  have hgk : ∀ a, genMap 𝔐.ξ ⟨_, h'⟩ ((𝔐.X.presheaf.stalkSpecializes hsp).hom a) = genMap 𝔐.ξ ⟨centre z, h⟩ a :=
    fun a => genMap_specializes ⟨centre z, h⟩ h' hsp a
  have hfW : ∀ j, (f j : 𝔐.Li) ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) ⟨centre z, h⟩ := fun j => by
    refine (𝔐.M.mem_htDual _ _ _ _ _ (f j)).2 fun u hu => ?_
    have hu' : u ∈ Submodule.span (regAt 𝔐.ξ ⟨centre z, h⟩) (Set.range b) := hbq ▸ hu
    clear hu
    induction hu' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine (hf1 i j).symm ▸ (?_ : (if i = j then (1 : Ω) else 0) ∈ regAt 𝔐.ξ ⟨centre z, h⟩)
      by_cases hij : i = j
      · rw [ite_eq_left hij]
        exact one_mem _
      · rw [ite_eq_right hij]
        exact zero_mem _
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact mul_mem a.2 hx
  have hfib : ∀ L : Lat 𝔐.ξ 𝔐.Li, 𝔐.M.fibAt L z MC = Submodule.span O'
      {x | ∃ e ∈ (L ⟨centre z, h⟩ : Set 𝔐.Li),
        𝔐.M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) e (MC.pt x)} := fun L => by
    unfold LieModel.fibAt
    congr 1
    ext x
    exact ⟨fun ⟨_, e, h1, h2⟩ => ⟨e, h1, h2⟩, fun ⟨e, h1, h2⟩ => ⟨h, e, h1, h2⟩⟩
  rw [hfib, hfib]
  refine alg_main (A := 𝔐.X.presheaf.stalk (centre z)) (𝔐.X.presheaf.stalkSpecializes hsp).hom
    (genMap 𝔐.ξ ⟨_, h'⟩) (hξ.inj _) (Scheme.stalkClosedPointTo _).hom (Scheme.stalkClosedPointTo z).hom
    (fun a => congrArg (fun g => g.hom a) (stalk_base (algebraMap O' C) z)) βb gm _ hVal 𝔐.ρ ρC (𝔐.emb s) σ
    ?_ ?_ _ _ w (fun j => f j) hβ ?_ hfW ?_ ?_ ?_ κ κz ?_ ?_
  · intro a
    obtain ⟨_, t, h1, h2⟩ := hσ a
    exact ⟨t, (hgk t).trans h1, h2⟩
  · intro a e x hx
    haveI := 𝔐.t.act.hom a
    exact valAt_act 𝔐.M MC _ _ _ (𝔐.act a) (hact a) hx
  · intro j e he
    obtain ⟨t, ht⟩ := 𝔐.M.htOm_le _ _ _ (hw1 j) e he
    exact ⟨t, (hgk t).trans ht⟩
  · intro e he
    obtain ⟨h1, h2⟩ := (𝔐.M.mem_htDual_iff _ _ _ _ _ e).1 he
    refine ⟨h1, fun j => ?_⟩
    obtain ⟨t, ht⟩ := h2 _ (hw1 j)
    exact ⟨t, (hgk t).trans ht⟩
  · intro e he
    have := congrArg Subtype.val (hf2 ⟨e, he⟩)
    simpa [← hw3] using this
  · intro j
    obtain ⟨u, hu'⟩ := (𝔐.M.exists_valAt_iff _ _).2
      ⟨h', htDual_le_lat 𝔐 hpS s ⟨centre z, h⟩ ⟨_, h'⟩ hsp hq hu hq' hreg _ (hfW j)⟩
    obtain ⟨x, rfl⟩ := MC.onto u hu'.isTanAt
    exact ⟨x, hu'⟩
  · obtain ⟨_, t, h1, h2⟩ := hκ
    exact ⟨t, (hgk t).trans h1, h2⟩
  · intro e he
    exact (((hsand _ hq).2.2.2 s).2 e he).1

end PositivityTheory.HtPt.Gh
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfFin
section
namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct in
open GlobalTheory.CompanionTheory.Ar.BT in
theorem bt_sub_eq_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ :=
  @bt_sub_eq_top_of @hens_normal @PositivityTheory.UnitarySelfGeneration.bt_exists_bc @reg_pull

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct in
open GlobalTheory.CompanionTheory.Ar.BT in
theorem bt_hopf : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) :=
  @bt_hopf_of @hens_normal @PositivityTheory.UnitarySelfGeneration.bt_exists_bc @reg_pull

end PositivityTheory.HtPt.Htat
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.JetOfMono
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cg

open IsLocalRing

theorem spMap_comp' {k A B C : Type} [CommRing k] [CommRing A] [CommRing B] [CommRing C] [Algebra k A] [Algebra k B]
    [Algebra k C] (f : A →ₐ[k] B) (g : B →ₐ[k] C) :
    spMap (g : B →+* C) ≫ spMap (f : A →+* B) = spMap (g.comp f : A →+* C) := by
  rw [← Spec.map_comp]; rfl

section
variable {k : Type} [Field k] {Z : Scheme.{0}} {π : Z ⟶ Sp k} {κ : Type}

def UnivJet (π : Z ⟶ Sp k) (e : Sp k ⟶ Z) {m : ℕ} (x : Sp (Jet k κ m) ⟶ Z) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra k B] (aug : B →ₐ[k] k), RingHom.ker aug ^ (m + 1) = ⊥ →
    ∀ y : Sp B ⟶ Z, y ≫ π = spMap (algebraMap k B) → spMap (aug : B →+* k) ≫ y = e →
      ∃! χ : Jet k κ m →ₐ[k] B, aug.comp χ = jetAug ∧ y = spMap (χ : Jet k κ m →+* B) ≫ x

theorem jet_of_mono {e : Sp k ⟶ Z} {m : ℕ} {x : Sp (Jet k κ m) ⟶ Z} (hu : UnivJet π e x)
    (hxa : spMap ((jetAug : Jet k κ m →ₐ[k] k) : Jet k κ m →+* k) ≫ x = e)
    {O : Type} [CommRing O] [Algebra k O] (s : Sp O ⟶ Z) [Mono s] (hs : s ≫ π = spMap (algebraMap k O))
    (ε : O →ₐ[k] k) (hε : spMap (ε : O →+* k) ≫ s = e) (τ : O →ₐ[k] Jet k κ m)
    (hτ : spMap (τ : O →+* Jet k κ m) ≫ s = x) :
    Function.Surjective τ ∧ ∀ a, τ a = 0 ↔ a ∈ RingHom.ker ε ^ (m + 1) := by
  have canc : ∀ {A : Type} [CommRing A] [Algebra k A] (f f' : O →ₐ[k] A),
      spMap (f : O →+* A) ≫ s = spMap (f' : O →+* A) ≫ s → f = f' := by
    intro A _ _ f f' h
    have h3 := Spec.map_injective ((cancel_mono s).1 h)
    ext a
    exact congrArg (fun q => q.hom a) h3
  let aJ : Jet k κ m →ₐ[k] k := jetAug
  have hJ : RingHom.ker aJ ^ (m + 1) = ⊥ := Chart.ker_jetAug_pow (R := k) κ m
  have haug : aJ.comp τ = ε := canc _ _ (by rw [← spMap_comp', Category.assoc, hτ, hxa, hε])
  set I : Ideal O := RingHom.ker ε ^ (m + 1) with hI
  have hkill : ∀ a ∈ I, τ a = 0 := by
    intro a ha
    have hle : RingHom.ker ε ≤ (RingHom.ker aJ).comap τ := fun c hc => by
      show aJ (τ c) = 0
      rw [← AlgHom.comp_apply, haug]; exact hc
    have h2 := Ideal.le_comap_pow τ (m + 1) (Ideal.pow_right_mono hle (m + 1) ha)
    rw [hJ] at h2
    simpa using h2
  have hε0 : ∀ a ∈ I, ε a = 0 := fun a ha => Ideal.pow_le_self (Nat.succ_ne_zero m) ha
  let aA : (O ⧸ I) →ₐ[k] k := Ideal.Quotient.liftₐ I ε hε0
  have haA : aA.comp (Ideal.Quotient.mkₐ k I) = ε := by ext a; rfl
  have hA : RingHom.ker aA ^ (m + 1) = ⊥ := by
    have hle : RingHom.ker aA ≤ (RingHom.ker ε).map (Ideal.Quotient.mk I) := by
      intro c hc
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact Ideal.mem_map_of_mem _ hc
    rw [← le_bot_iff]
    refine (Ideal.pow_right_mono hle _).trans ?_
    rw [← Ideal.map_pow, ← hI, Ideal.map_quotient_self]
  obtain ⟨ψ, ⟨h1, h2⟩, -⟩ := hu (O ⧸ I) aA hA (spMap (Ideal.Quotient.mkₐ k I : O →+* O ⧸ I) ≫ s)
    (by rw [Category.assoc, hs, spMap_comp_alg]) (by rw [← Category.assoc, spMap_comp', haA, hε])
  have hψτ : ψ.comp τ = Ideal.Quotient.mkₐ k I :=
    canc _ _ (by rw [← spMap_comp', Category.assoc, hτ, h2])
  let τ' : (O ⧸ I) →ₐ[k] Jet k κ m := Ideal.Quotient.liftₐ I τ hkill
  have hτ' : τ'.comp (Ideal.Quotient.mkₐ k I) = τ := by ext a; rfl
  have haτ' : aJ.comp τ' = aA := by
    refine Ideal.Quotient.algHom_ext k ?_
    rw [AlgHom.comp_assoc, hτ', haug, haA]
  have hid : τ'.comp ψ = AlgHom.id k _ := by
    refine (hu (Jet k κ m) aJ hJ x (by rw [← hτ, Category.assoc, hs, spMap_comp_alg]) hxa).unique
      ⟨?_, ?_⟩ ⟨rfl, ?_⟩
    · rw [← AlgHom.comp_assoc, haτ', h1]
    · rw [← spMap_comp', Category.assoc, ← h2, ← Category.assoc, spMap_comp', hτ', hτ]
    · exact (Category.id_comp x).symm.trans (congrArg (· ≫ x) (Spec.map_id _).symm)
  refine ⟨fun c => ?_, fun a => ⟨fun ha => ?_, hkill a⟩⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ c)
    refine ⟨a, ?_⟩
    have := AlgHom.congr_fun hid c
    rw [AlgHom.comp_apply, ← ha] at this
    exact this
  · have := AlgHom.congr_fun hψτ a
    rw [AlgHom.comp_apply, ha, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm

theorem stalk_jet {e : Sp k ⟶ Z} (he : e ≫ π = 𝟙 _) {m : ℕ} {x : Sp (Jet k κ m) ⟶ Z} (hu : UnivJet π e x)
    (hx : x ≫ π = spMap (algebraMap k _))
    (hxa : spMap ((jetAug : Jet k κ m →ₐ[k] k) : Jet k κ m →+* k) ≫ x = e)
    (b : Z) (hb : e (closedPoint k) = b) [alg : Algebra k (Z.presheaf.stalk b)]
    (hs : Z.fromSpecStalk b ≫ π = spMap (algebraMap k (Z.presheaf.stalk b))) :
    ∃ τ : Z.presheaf.stalk b →ₐ[k] Jet k κ m,
      spMap (τ : Z.presheaf.stalk b →+* Jet k κ m) ≫ Z.fromSpecStalk b = x ∧ Function.Surjective τ ∧
        ∀ a, τ a = 0 ↔ a ∈ maximalIdeal (Z.presheaf.stalk b) ^ (m + 1) := by
  let aJ : Jet k κ m →ₐ[k] k := jetAug
  have hJ : RingHom.ker aJ ^ (m + 1) = ⊥ := Chart.ker_jetAug_pow (R := k) κ m
  have := GlobalTheory.StalkJet.isLocalRing_of_aug aJ hJ
  have hxb : x (closedPoint _) = b := by
    have : IsLocalHom (aJ : Jet k κ m →+* k) :=
      IsLocalHom.of_surjective _ (fun c => ⟨algebraMap _ _ c, aJ.commutes c⟩)
    rw [← hb, ← hxa, ← IsLocalRing.comap_closedPoint (aJ : Jet k κ m →+* k)]
    rfl
  let s : Sp (Z.presheaf.stalk b) ⟶ Z := Z.fromSpecStalk b
  have : Mono s := inferInstanceAs (Mono (Z.fromSpecStalk b))
  have hs' : s ≫ π = spMap (algebraMap k (Z.presheaf.stalk b)) := hs
  obtain ⟨ε, hε⟩ : ∃ ε : Z.presheaf.stalk b →ₐ[k] k, spMap (ε : Z.presheaf.stalk b →+* k) ≫ s = e := by
    obtain ⟨ε, -, hε⟩ := @GlobalTheory.StalkJet.exists_factor k _ (Over.mk π) b alg hs k _ _ _
      (Over.homMk e (he.trans (Spec.map_id _).symm)) hb
    exact ⟨ε, hε⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Z.presheaf.stalk b →ₐ[k] Jet k κ m,
      spMap (τ : Z.presheaf.stalk b →+* Jet k κ m) ≫ s = x := by
    obtain ⟨τ, -, hτ⟩ := @GlobalTheory.StalkJet.exists_factor k _ (Over.mk π) b alg hs
      (Jet k κ m) _ _ _ (Over.homMk x hx) hxb
    exact ⟨τ, hτ⟩
  have hker : RingHom.ker ε = maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ε (fun c => ⟨algebraMap _ _ c, ε.commutes c⟩))
  have := jet_of_mono hu hxa s hs' ε hε τ hτ
  rw [hker] at this
  exact ⟨τ, hτ, this⟩

theorem tj_eq [Fintype κ] [DecidableEq κ] (m : ℕ) (F : MvPowerSeries κ k) :
    GlobalTheory.JetExpansion.tj m F = psJet m F := by
  rw [psJet, FBIdJet.psTrunc_eq]; rfl

theorem taylor [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] [IsIntegral Z] [LocallyOfFiniteType π]
    [Fintype κ] [DecidableEq κ] {e : Sp k ⟶ Z} (he : e ≫ π = 𝟙 _) (x : ∀ m, Sp (Jet k κ m) ⟶ Z)
    (hu : ∀ m, UnivJet π e (x m)) (hx : ∀ m, x m ≫ π = spMap (algebraMap k _))
    (hxa : ∀ m, spMap ((jetAug : Jet k κ m →ₐ[k] k) : Jet k κ m →+* k) ≫ x m = e)
    (ht : ∀ m, spMap ((jetTrunc : Jet k κ (m + 1) →ₐ[k] Jet k κ m) : Jet k κ (m + 1) →+* Jet k κ m) ≫ x (m + 1) = x m)
    (U : Z.Opens) (hU : ∀ m, ⊤ ≤ x m ⁻¹ᵁ U) [Nonempty U] (f : Γ(Z, U)) :
    ∃ F : MvPowerSeries κ k, (∀ m, ((x m).appLE U ⊤ (hU m)).hom f = toΓ _ (psJet m F)) ∧ (F = 0 → f = 0) ∧
      ((∀ q, MvPowerSeries.pderiv (R := k) q F = 0) → ∃ r : Z.functionField, r ^ p = (Z.germToFunctionField U).hom f) := by
  obtain ⟨b, hbdef⟩ : ∃ b, e (closedPoint k) = b := ⟨_, rfl⟩
  have hb : b ∈ U := by
    rw [← hbdef, ← hxa 0]
    exact hU 0 (x := _) trivial
  let φ : CommRingCat.of k ⟶ Z.presheaf.stalk b := StructureSheaf.toStalk k (π b) ≫ π.stalkMap b
  let _ : Algebra k (Z.presheaf.stalk b) := φ.hom.toAlgebra
  have hφ : Z.fromSpecStalk b ≫ π = spMap (algebraMap k (Z.presheaf.stalk b)) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]
    erw [Spec.fromSpecStalk_eq']
    exact (Spec.map_comp _ _).symm
  have : Algebra.EssFiniteType k (Z.presheaf.stalk b) := by
    have e0 : ∀ p : PrimeSpectrum k, (StructureSheaf.toStalk k p).hom.EssFiniteType := fun p =>
      Algebra.EssFiniteType.of_isLocalization (R := k) ((Spec.structureSheaf k).presheaf.stalk p) p.asIdeal.primeCompl
    exact RingHom.EssFiniteType.comp (e0 (π b)) (LocallyOfFiniteType.stalkMap π b)
  have : IsNoetherianRing (Z.presheaf.stalk b) := Algebra.EssFiniteType.isNoetherianRing k _
  choose τ h1 h2 h3 using fun m => stalk_jet he (hu m) (hx m) (hxa m) b hbdef hφ
  have hc : ∀ m a, jetTrunc (τ (m + 1) a) = τ m a := by
    intro m a
    have e : spMap (((jetTrunc : Jet k κ (m + 1) →ₐ[k] Jet k κ m).comp (τ (m + 1)) :
        Z.presheaf.stalk b →ₐ[k] Jet k κ m) : Z.presheaf.stalk b →+* Jet k κ m) =
        spMap (τ m : Z.presheaf.stalk b →+* Jet k κ m) := by
      rw [← cancel_mono (Z.fromSpecStalk b), h1, ← ht m, ← h1, ← spMap_comp', Category.assoc]
    exact congrArg (fun q => q.hom a) (Spec.map_injective e)
  choose F hF using fun a : Z.presheaf.stalk b =>
    GlobalTheory.JetExpansion.exists_tj (k := k) (κ := κ) (fun m => τ m a) (fun m => hc m a)
  let σ : ∀ m, Z.presheaf.stalk b →ₐ[k] JetR k κ m := τ
  have hF' : ∀ a m, GlobalTheory.JetExpansion.tj m (F a) = σ m a := hF
  let j : Z.presheaf.stalk b →ₐ[k] MvPowerSeries κ k :=
    { toFun := F
      map_one' := GlobalTheory.JetExpansion.tj_ext fun m => by rw [hF', map_one, map_one]
      map_mul' := fun a b => GlobalTheory.JetExpansion.tj_ext fun m => by rw [map_mul, hF', hF', hF', map_mul]
      map_zero' := GlobalTheory.JetExpansion.tj_ext fun m => by rw [hF', map_zero, map_zero]
      map_add' := fun a b => GlobalTheory.JetExpansion.tj_ext fun m => by rw [map_add (f := _), hF', hF', hF', map_add (f := _)]
      commutes' := fun r => GlobalTheory.JetExpansion.tj_ext fun m => by rw [hF', AlgHom.commutes, AlgHom.commutes] }
  have hj : ∀ m a, GlobalTheory.JetExpansion.tj m (j a) = σ m a := fun m a => hF a m
  have j1 : ∀ (m : ℕ) a, j a ∈ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ k)) ^ m ↔
      a ∈ maximalIdeal (Z.presheaf.stalk b) ^ m := fun m a => by
    rcases m with _ | m
    · simp
    · rw [← GlobalTheory.JetExpansion.tj_eq_zero_iff, hj]; exact h3 m a
  have j2 : ∀ (m : ℕ) (s : MvPowerSeries κ k), ∃ a, j a - s ∈
      Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ k)) ^ m := fun m s => by
    obtain ⟨a, ha⟩ := h2 m (GlobalTheory.JetExpansion.tj m s)
    refine ⟨a, Ideal.pow_le_pow_right (Nat.le_succ m) ?_⟩
    rw [← GlobalTheory.JetExpansion.tj_eq_zero_iff, map_sub, hj]
    exact sub_eq_zero.2 ha
  have htop : ⊤ ≤ Z.fromSpecStalk b ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem _ (by rw [Scheme.fromSpecStalk_closedPoint]; exact hb)).ge
  have hv : valR (A := Z.presheaf.stalk b) (Z.fromSpecStalk b) U f = (Z.presheaf.germ U b hb).hom f := by
    refine (dif_pos htop).trans ?_
    have : (Z.fromSpecStalk b).appLE U ⊤ htop ≫ (Scheme.ΓSpecIso (Z.presheaf.stalk b)).hom =
        Z.presheaf.germ U b hb := by
      rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hb]
      simp only [Category.assoc]
      have e : (Spec (Z.presheaf.stalk b)).presheaf.map (homOfLE (le_top : Z.fromSpecStalk b ⁻¹ᵁ U ≤ ⊤)).op ≫
          (Spec (Z.presheaf.stalk b)).presheaf.map (homOfLE htop).op = 𝟙 _ := by
        rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
      rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
    exact congrArg (fun q => q.hom f) this
  refine ⟨j ((Z.presheaf.germ U b hb).hom f), fun m => ?_, fun h0 => ?_, fun hd => ?_⟩
  · have e1 : valR (x m) U f = psJet m (j ((Z.presheaf.germ U b hb).hom f)) := by
      rw [← tj_eq, hj, ← hv, ← h1]
      exact (GlobalTheory.ZH.CrdCalc.valR_spMap (τ m : Z.presheaf.stalk b →+* Jet k κ m) _ U htop).2 f
    rw [← e1, valR, dif_pos (hU m)]
    exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (Jet k κ m))) _).symm
  · apply germ_injective_of_isIntegral Z b hb
    rw [map_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top,
      Ideal.mem_iInf]
    intro m
    rw [← j1, h0]
    exact zero_mem _
  · obtain ⟨r, hr⟩ := GlobalTheory.CubeFib.exists_pow_eq_fractionRing_of_pderiv_eq_zero k p _ κ j j1 j2 _ hd
    refine ⟨FractionRing.algEquiv (Z.presheaf.stalk b) Z.functionField r, ?_⟩
    rw [← map_pow, hr, AlgEquiv.commutes]
    exact Scheme.algebraMap_germ_eq_germToFunctionField Z hb f

end

end PositivityTheory.HtPt.Cg
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.KTwins
section
namespace PositivityTheory.HtPt.Ktw

theorem a64 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.NefProductNonneg.Statement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.NefProductNonneg.unfolding_matrix_of_form a28 (a63 hR)

theorem a73 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.VeryAmpleNefPlusAmple.Statement :=
  (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.VeryAmpleNefPlusAmple.equiv
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BundleOfDeg.full a65 a71
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelDimEq.full).mp (a72 hR)

theorem a77 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.SectionCount.Statement := (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SectionCount.equiv
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.GraphModel.full
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BundleOfDeg.full
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelDim.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BaseRealises.proof a66
    (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.VeryAmpleModel.proof
      PositivityTheory.HtPt.KtwS.SectionsOverLocalization.VeryAmpleEq.full a69) a18).mp
    (GroundTheory.Heights₂.Heights.Kleiman.SectionCount.assembled a39 a43 a48 a51 hR)

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 in
theorem k_twins : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0} → NefProductNonneg.Statement ∧ VeryAmpleNefPlusAmple.Statement ∧ SectionCount.Statement :=
  fun hR => ⟨a64 hR, a73 hR, a77 hR⟩

end PositivityTheory.HtPt.Ktw
end

