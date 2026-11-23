module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2271
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0109
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2255
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelLevelAfterFiniteExtensionDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelAfterExt

theorem exists_siegPre_divPoints : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (s : SiegPre PB.g n (zetaAway n) (spMap (f₁.comp b))) (β₁ : s.A.left ⟶ PB.A.left) (β₁₂ : (G2 s.A).left ⟶ (G2 PB.A).left) (d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ s.Principal ∧ IsGrpPullback s.A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso s.P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ i, (d i ^ n).left ≫ β₁ = spMap f₁ ≫ (c (Pi.single i 1)).left := by
  intro n hn3 _ V _ _ _ hV _ b PB r c
  have hn0 : n ≠ 0 := by omega
  haveI := hV.2.2.1
  haveI := hV.2.2.2
  haveI : CharZero (FractionRing V) := charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))
  let ze : (cycAway n)ˣ := (GlobalTheory.LowChart.isUnit_zetaAway n hn3).unit
  let ζ : (FractionRing V)ˣ := Units.map ((algebraMap V (FractionRing V)).comp b).toMonoidHom ze
  have hζ : IsPrimitiveRoot ζ n :=
    IsPrimitiveRoot.coe_units_iff.1 (isPrimitiveRoot_map hn0 ((algebraMap V (FractionRing V)).comp b))
  obtain ⟨L, _, _, _, lev, d, hadd, htor, hweil, hd⟩ :=
    _root_.GlobalTheory.FieldLevel.exists_level_and_roots V PB (FractionRing V) (algebraMap V (FractionRing V)) n (by omega) ζ hζ r (fun i => c (Pi.single i 1))
  obtain ⟨W, _, _, _, hcW, _, _, _, hcomp, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  generalize hT : (algebraMap (FractionRing V) L).comp (algebraMap V (FractionRing V)) = T at lev d hadd htor hweil hd
  have hT' : (algebraMap W L).comp (algebraMap V W) = T := hcomp.trans hT
  subst hT'
  let f₁ : V →+* W := algebraMap V W
  let e : Over.mk (spMap ((algebraMap W L).comp f₁)) ⟶ Over.mk (spMap f₁) :=
    Over.homMk (spMap (algebraMap W L)) (by show Spec.map _ ≫ Spec.map _ = Spec.map _; rw [← Spec.map_comp]; rfl)
  have hel : e.left = spMap (algebraMap W L) := rfl
  have uniq : ∀ y y' : Over.mk (spMap f₁) ⟶ PB.A, e ≫ y = e ≫ y' → y = y' := fun y y' h =>
    (_root_.GlobalTheory.DVRExt.exists_unique_extend V PB W L f₁ (e ≫ y)).unique (rfl : spMap (algebraMap W L) ≫ y.left = (e ≫ y).left)
      (show spMap (algebraMap W L) ≫ y'.left = (e ≫ y).left by rw [h]; rfl)
  have lift : ∀ x : Over.mk (spMap ((algebraMap W L).comp f₁)) ⟶ PB.A, ∃ y, e ≫ y = x := fun x => by
    obtain ⟨y, hy, -⟩ := _root_.GlobalTheory.DVRExt.exists_unique_extend V PB W L f₁ x
    exact ⟨y, Over.OverMorphism.ext hy⟩
  choose lev₁ hlev₁ using fun a => lift (lev a)
  choose d₁ hd₁ using fun i => lift (d i)
  have add₁ : ∀ x y, lev₁ (x + y) = lev₁ x * lev₁ y := fun x y =>
    uniq _ _ (by rw [MonObj.comp_mul, hlev₁, hlev₁, hlev₁, hadd])
  have tor₁ : ∀ x, lev₁ x ^ n = 1 := fun x =>
    uniq _ _ (by rw [MonObj.comp_pow, hlev₁, htor, MonObj.comp_one])
  have div₁ : ∀ i, d₁ i ^ n = toUnit _ ≫ c (Pi.single i 1) := fun i =>
    uniq _ _ (by rw [MonObj.comp_pow, hd₁, hd, ← Category.assoc, toUnit_unique (e ≫ toUnit _) (toUnit _)])
  have weil₁ : ∀ x y, Out.WeilIs PB.A PB.L n (lev₁ x) (lev₁ y)
      (unitOn (Units.map (f₁.comp b).toMonoidHom ze ^ omegaStd x y)) := fun x y => by
    refine _root_.GlobalTheory.WeilDomain.weilIs_of_fractionField V PB W L f₁ e hel n _ _ (tor₁ x) (tor₁ y) _ ?_
    rw [hlev₁, hlev₁, map_zpow]
    have hz : Units.map (algebraMap W L).toMonoidHom (Units.map (f₁.comp b).toMonoidHom ze) =
        Units.map (algebraMap (FractionRing V) L).toMonoidHom ζ := Units.ext (by
      show (algebraMap W L) (f₁ (b (zetaAway n))) = (algebraMap (FractionRing V) L) ((algebraMap V (FractionRing V)) (b (zetaAway n)))
      exact congrArg (fun q : V →+* L => q (b (zetaAway n))) hcomp)
    rw [hz]
    exact hweil x y
  obtain ⟨s, β₁, β₁₂, d', hP, hpb, hsq, hlb, hdd⟩ :=
    _root_.GlobalTheory.SiegelLevelPull.exists_siegPre_of_points n hn3 V W f₁ b PB lev₁ r d₁ (fun i => c (Pi.single i 1)) add₁ tor₁ weil₁ div₁
  refine ⟨W, inferInstance, inferInstance, inferInstance, f₁, s, β₁, β₁₂, d',
    ⟨inferInstance, inferInstance, hcW, charZero_of_injective_ringHom hinj⟩, inferInstance, hinj,
    RingHom.finite_algebraMap.2 hfin, hloc, hP, hpb, hsq, hlb, hdd⟩

end GlobalTheory.LevelAfterExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallSectionAddMultipleAmpleAfterShift
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.TwistSmall

theorem mem_regular_sections_second_bundle_indep_first {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (P : Pair p) (L' : HermLB p) (r : L'.B.ι → X.functionFieldˣ) (hr : IsRatSec L'.B r)
    {s : X.functionField} (hs : s ∈ P.H 0 1) :
    s ∈ (⟨L', P.A, r, P.r', hr, P.hr'⟩ : Pair p).H 0 1 := by
  intro x i j _ hj
  have hx : x ∈ (⨆ i, P.L.B.U i) := by rw [P.L.isLB.cover]; trivial
  obtain ⟨i', hi'⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  simpa [Pair.loc] using hs x i' j hi' hj

theorem le_dual_pow_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (N : HermLB p) (s : X.functionField), IsAmpleLB P.A.B → s ∈ P.H 0 1 → s ≠ 0 →
    ∃ c₁ : ℕ, ∀ c, c₁ ≤ c → 0 < c → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → Le (((shiftA P u).A.pow c).dual) N := by
  intro k _ X _ p D hX P N s hA hs hs0
  obtain ⟨rN, hrN⟩ := exists_isRatSec N.isLB
  let Q : Pair p := ⟨N, P.A, rN, P.r', hrN, P.hr'⟩
  obtain ⟨c₁, g, _, hg0, hg, -⟩ := _root_.GlobalTheory.HSNef.Den.exists_clear_denominators k X p D hX Q hA 1 Empty (fun e => e.elim)
  refine ⟨c₁, fun c hc hc0 => ?_⟩
  have hsQ : s ∈ Q.H 0 1 := mem_regular_sections_second_bundle_indep_first P N rN hrN hs
  obtain ⟨hpow, -⟩ := NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 s hsQ (c - c₁)
  obtain ⟨hf, -⟩ := NuMul.mul_mem_H_and_nu_mul k X p Q 1 c₁ _ _ g (s ^ (c - c₁)) hg hpow
  have e1 : (1 : ℤ) + ((c - c₁ : ℕ) : ℤ) * 0 = 1 := by ring
  have e2 : (c₁ : ℤ) + ((c - c₁ : ℕ) : ℤ) * 1 = c := by push_cast [Nat.cast_sub hc]; ring
  rw [e1, e2] at hf
  obtain ⟨w, _, hw⟩ := _root_.GlobalTheory.HSNef.bounded_norm k X p D hX Q 1 c _ hf
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc0
  refine ⟨w / c, fun u hu => ?_⟩
  obtain ⟨-, hBl, -⟩ := _root_.GlobalTheory.HSNef.shiftA_props k X p Q u
  have hwu : w ≤ (c : ℤ) * u := by
    have := (div_le_iff₀ hcpos).1 hu
    push_cast; linarith
  have hmem : g * s ^ (c - c₁) ∈ (shiftA Q u).Bl 1 c 1 := by
    rw [hBl, one_mul]
    exact ⟨hw.1, fun σ y => (hw.2 σ y).trans (Real.exp_le_exp.2 hwu)⟩
  have hne : g * s ^ (c - c₁) ≠ 0 := mul_ne_zero hg0 (pow_ne_zero _ hs0)
  have hrepN := (Pair.rep_base k X p (shiftA Q u)).1
  have hrepA := (Pair.rep_base k X p (shiftA Q u)).2.1
  have hpowA := Pair.rep_pow k X p (shiftA Q u) 0 1 _ c hrepA
  have hdual := Pair.rep_dual k X p (shiftA Q u) _ _ _ hpowA
  have e3 : (1 : ℤ) - -((c : ℤ) * 0) = 1 := by ring
  have e4 : (0 : ℤ) - -((c : ℤ) * 1) = c := by ring
  have hmem' : g * s ^ (c - c₁) ∈ (shiftA Q u).Bl (1 - -((c : ℤ) * 0)) (0 - -((c : ℤ) * 1)) 1 := by
    rw [e3, e4]; exact hmem
  exact _root_.GlobalTheory.HSNef.le_of_rep k X p (shiftA Q u) 1 0 _ _ N _ _ hrepN hdual hne hmem'

end GlobalTheory.HSNef.TwistSmall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftOfRetractSquareZero
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Obs

theorem retractLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.Smooth R B'] (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀] (i : B₀ →ₐ[R₀] B₀') (r : B₀' →ₐ[R₀] B₀), (∀ x, r (i x) = x) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B' B₀' _ _ _ _ p' hs' hp' hker' _ B₀ _ _ i r hri
  obtain ⟨e, he, hpe⟩ := _root_.GlobalTheory.Obs.idemLift R R₀ I hI π hπ hk B' B₀' p' hs' hp' hker' (i.comp r) (fun x ↦ by simp [hri])
  have hmem : ∀ x ∈ I.map (algebraMap R B'), e.rangeRestrict x ∈ I.map (algebraMap R e.range) := by
    intro x hx
    have hle : I.map (algebraMap R B') ≤ (I.map (algebraMap R e.range)).comap (e.rangeRestrict : B' →+* e.range) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      intro y hy
      simp only [Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
      rw [AlgHom.commutes]
      exact Ideal.mem_map_of_mem _ hy
    exact hle hx
  refine ⟨e.range, inferInstance, inferInstance,
    ((r : B₀' →+* B₀).comp p').comp (e.range.val : e.range →+* B'), ?_, ?_, ?_, _root_.GlobalTheory.smooth_range_of_idempotent R B' e he⟩
  · intro c b
    show r (p' ((c • b : e.range) : B')) = π c • r (p' (b : B'))
    rw [Subalgebra.coe_smul, hs' c (b : B'), map_smul]
  · intro y
    obtain ⟨b, hb⟩ := hp' (i y)
    refine ⟨⟨e b, e.mem_range_self b⟩, ?_⟩
    show r (p' (e b)) = y
    rw [hpe, hb]
    simp [hri]
  · intro b
    constructor
    · intro h
      change r (p' (b : B')) = 0 at h
      obtain ⟨c, hc⟩ := b.2
      change e c = (b : B') at hc
      have hfix : e (b : B') = b := by rw [← hc, he]
      have h0 : p' (b : B') = 0 := by
        rw [← hfix, hpe]
        simp [h]
      have hb : e.rangeRestrict (b : B') = b := Subtype.ext hfix
      rw [← hb]
      exact hmem _ ((hker' _).mp h0)
    · intro h
      have hle : I.map (algebraMap R e.range) ≤ RingHom.ker (((r : B₀' →+* B₀).comp p').comp (e.range.val : e.range →+* B')) := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
        have hx0 : π x = 0 := by rw [← RingHom.mem_ker, hk]; exact hx
        show r (p' (algebraMap R B' x)) = 0
        rw [hs'.map_algebraMap, hx0, map_zero, map_zero]
      exact hle h

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtLatticeHomFiniteExtensionComplete
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootHom

theorem exists_sqrt_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h : X → (FractionRing R)ˣ) (m : ℕ) (t : Fin m → R), IsCN R → (∀ a b, h (a + b) = h a * h b) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (gam : FractionRing R →+* FractionRing R') (r : Fin m → R') (eta : X → (FractionRing R')ˣ), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x)) ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ (∀ a b, eta (a + b) = eta a * eta b) ∧ ∀ a, eta a ^ 2 = Units.map gam.toMonoidHom (h a) := by
  intro R _ _ _ X _ _ _ h m t hR hh
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hpq : ∀ k, ∃ p q : R, q ∈ nonZeroDivisors R ∧
      algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q = (h (b k) : FractionRing R) :=
    fun k => IsFractionRing.div_surjective R _
  choose p q hq hpq using hpq
  obtain ⟨R', _, _, _, ρ, r, hR', hinj, hfin, hloc, hr⟩ :=
    _root_.GlobalTheory.sqrt_of_finite_family R (Fin m ⊕ Module.Free.ChooseBasisIndex ℤ X) (Sum.elim t (fun k => p k * q k)) hR
  have hι : Function.Injective (algebraMap R' (FractionRing R')) := IsFractionRing.injective R' (FractionRing R')
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) := hι.comp hinj
  let gam : FractionRing R →+* FractionRing R' := IsFractionRing.lift hinj'
  have hgam : ∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x) := fun x => IsFractionRing.lift_algebraMap hinj' x
  have hq0 : ∀ k, algebraMap R' (FractionRing R') (ρ (q k)) ≠ 0 := by
    intro k h0
    have : ρ (q k) = 0 := hι (by simpa using h0)
    exact nonZeroDivisors.ne_zero (hq k) (hinj (by simpa using this))
  have hp0 : ∀ k, p k ≠ 0 := by
    intro k h0
    have := hpq k
    rw [h0, map_zero, zero_div] at this
    exact (h (b k)).ne_zero this.symm
  have hs : ∀ k, (r (Sum.inr k)) ^ 2 = ρ (p k * q k) := fun k => by simpa using hr (Sum.inr k)
  have hs0 : ∀ k, algebraMap R' (FractionRing R') (r (Sum.inr k)) ≠ 0 := by
    intro k h0
    have h1 : r (Sum.inr k) = 0 := hι (by simpa using h0)
    have h2 := hs k
    rw [h1, zero_pow two_ne_zero] at h2
    exact mul_ne_zero (hp0 k) (nonZeroDivisors.ne_zero (hq k)) (hinj (by simpa using h2.symm))
  let e : Module.Free.ChooseBasisIndex ℤ X → (FractionRing R')ˣ := fun k =>
    Units.mk0 (algebraMap R' _ (r (Sum.inr k)) / algebraMap R' _ (ρ (q k))) (div_ne_zero (hs0 k) (hq0 k))
  let L : X →ₗ[ℤ] Additive (FractionRing R')ˣ := b.constr ℤ (fun k => Additive.ofMul (e k))
  let H : X →+ Additive (FractionRing R)ˣ := AddMonoidHom.mk' (fun a => Additive.ofMul (h a)) (fun a c => by
    simp [hh a c])
  let G : X →+ Additive (FractionRing R')ˣ := (MonoidHom.toAdditive (Units.map gam.toMonoidHom)).comp H
  have hLG : L + L = G.toIntLinearMap := by
    refine b.ext fun k => ?_
    simp only [LinearMap.add_apply, L, Module.Basis.constr_basis, AddMonoidHom.coe_toIntLinearMap, G, H,
      AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.mk'_apply, MonoidHom.toAdditive_apply_apply]
    rw [← ofMul_mul]
    congr 1
    ext
    simp only [Units.val_mul, e, Units.val_mk0, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, toMul_ofMul]
    rw [← hpq k, map_div₀, hgam, hgam, div_mul_div_comm, div_eq_div_iff (mul_ne_zero (hq0 k) (hq0 k)) (hq0 k)]
    have := congrArg (algebraMap R' (FractionRing R')) (hs k)
    rw [map_pow, map_mul, map_mul] at this
    rw [← sq, this]
    ring
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, gam, fun i => r (Sum.inl i), fun a => Additive.toMul (L a),
    hR', hinj, hfin, hloc, hgam, fun i => by simpa using hr (Sum.inl i), fun a c => by simp [map_add (f := _)], fun a => ?_⟩
  have h2 : Additive.toMul (L a + L a) = Units.map gam.toMonoidHom (h a) := by
    rw [← LinearMap.add_apply, LinearMap.congr_fun hLG a]
    rfl
  rw [sq, ← toMul_add]
  exact h2

end GlobalTheory.RootHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquare
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.Descent

variable {R : Type} [CommRing R]

theorem descend {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (ψ : D →ₐ[R] D')
    (hψ : (ψ : D →+* D').FaithfullyFlat) (s : D')
    (hs : ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D' →ₐ[R] E), α.comp ψ = β.comp ψ → α s = β s) :
    ∃ k, ψ k = s := by
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  haveI : IsScalarTower R D D' := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  refine (Algebra.IsEffective.of_faithfullyFlat D D' s).1 ?_
  have h := hs (D' ⊗[D] D') ((Algebra.TensorProduct.includeLeft : D' →ₐ[D] D' ⊗[D] D').restrictScalars R)
    ((Algebra.TensorProduct.includeRight : D' →ₐ[D] D' ⊗[D] D').restrictScalars R) (by
      ext d
      exact ((Algebra.TensorProduct.includeLeft : D' →ₐ[D] D' ⊗[D] D').commutes d).trans
        ((Algebra.TensorProduct.includeRight : D' →ₐ[D] D' ⊗[D] D').commutes d).symm)
  simpa [sub_eq_zero] using h

theorem exists_square {D D' D₂ : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing D₂]
    [Algebra R D₂] (ψ : D →ₐ[R] D') (hψ : (ψ : D →+* D').FaithfullyFlat) (ψ₂ : D →ₐ[R] D₂) :
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra R E) (α : D' →ₐ[R] E) (β : D₂ →ₐ[R] E),
      α.comp ψ = β.comp ψ₂ ∧ Function.Injective β := by
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  haveI : IsScalarTower R D D' := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  letI : Algebra D D₂ := (ψ₂ : D →+* D₂).toAlgebra
  haveI : IsScalarTower R D D₂ := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ₂.commutes r).symm
  refine ⟨D₂ ⊗[D] D', inferInstance, inferInstance,
    (Algebra.TensorProduct.includeRight : D' →ₐ[D] D₂ ⊗[D] D').restrictScalars R,
    (Algebra.TensorProduct.includeLeft : D₂ →ₐ[D] D₂ ⊗[D] D').restrictScalars R, ?_, ?_⟩
  · ext d
    exact ((Algebra.TensorProduct.includeRight : D' →ₐ[D] D₂ ⊗[D] D').commutes d).trans
        ((Algebra.TensorProduct.includeLeft : D₂ →ₐ[D] D₂ ⊗[D] D').commutes d).symm
  · exact FaithfulSMul.algebraMap_injective D₂ (D₂ ⊗[D] D')

variable {A : Over (Sp R)} [GrpObj A]

def sig (p : ℕ) (f : Fn1 A) (g : Fn2 A) {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (ψ : D →ₐ[R] D') (x : Pt A D) (z : Pt A D') : D' :=
  PtExt.chi p g D' z + f R D' (Algebra.ofId R D') (1 : Pt A R) - f D D' ψ x

theorem sig_nat {p : ℕ} (hp : (p : R) = 0) {f : Fn1 A} {g : Fn2 A} (hf : IsCoc (whole A) f) (hfg : IsAdd f g)
    {D D' D'' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing D''] [Algebra R D'']
    (ψ : D →ₐ[R] D') (θ : D' →ₐ[R] D'') (x : Pt A D) (z : Pt A D') (hz : (z ^ p : Pt A D') = spOver ψ ≫ x) :
    θ (sig p f g ψ x z) = sig p f g (θ.comp ψ) x (spOver θ ≫ z) := by
  have h1 := GlobalTheory.T.sumTwoPointFunction_multiples_natural_charP p R hp A f g hfg D' D'' θ z
  have h2 := hf D D' D'' ψ θ x (sm_whole _)
  have h3 := hf R D' D'' (Algebra.ofId R D') θ (1 : Pt A R) (sm_whole _)
  have e : θ.comp (Algebra.ofId R D') = Algebra.ofId R D'' := Subsingleton.elim _ _
  rw [e, MonObj.comp_one] at h3
  rw [hz] at h1
  simp only [sig, map_add θ, map_sub θ]
  linear_combination -h1 + h2 - h3

theorem chi_indep [IsCommMonObj A] {p : ℕ} (hp : (p : R) = 0) {g : Fn2 A} (hg : IsSymCoc g)
    (h0 : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ p = 1 → PtExt.chi p g D x = 0)
    {D : Type} [CommRing D] [Algebra R D] (z z' : Pt A D) (h : z ^ p = z' ^ p) :
    PtExt.chi p g D z = PtExt.chi p g D z' := by
  obtain ⟨t, rfl⟩ : ∃ t, z = z' * t := ⟨z'⁻¹ * z, by simp⟩
  have ht : t ^ p = 1 := by rwa [mul_pow, mul_eq_left] at h
  have h1 := GlobalTheory.T.symmetric_two_cocycle_sum_pow_mul (Pt A D) D (g D) (hg D).1 (hg D).2 p z' t
  have h2 := (hg D).2 (z' ^ p) 1 1
  have h3 := h0 D t ht
  have h4 : (p : D) = 0 := by rw [← map_natCast (algebraMap R D), hp, map_zero]
  rw [ht, nsmul_eq_mul, h4] at h1
  simp only [_root_.mul_one] at h2
  simp only [PtExt.chi] at h3 ⊢
  linear_combination h1 - h2 + h3

theorem pow_comp {p : ℕ} {D D' D'' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing D'']
    [Algebra R D''] (ψ : D →ₐ[R] D') (θ : D' →ₐ[R] D'') (x : Pt A D) (z : Pt A D')
    (hz : (z ^ p : Pt A D') = spOver ψ ≫ x) :
    ((spOver θ ≫ z) ^ p : Pt A D'') = spOver (θ.comp ψ) ≫ x := by
  rw [← MonObj.comp_pow, hz, ← Category.assoc, spOver_comp]

theorem exists_isCob (p : ℕ) (R : Type) [CommRing R] (hp : (p : R) = 0) (A : Over (Sp R)) [GrpObj A]
    [IsCommMonObj A] (f : Fn1 A) (g : Fn2 A) (hf : IsCoc (whole A) f) (hfg : IsAdd f g) (hg : IsSymCoc g)
    (h0 : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ p = 1 → PtExt.chi p g D x = 0)
    (hr : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D')
      (ψ : D →ₐ[R] D') (z : Pt A D'), (ψ : D →+* D').FaithfullyFlat ∧ (z ^ p : Pt A D') = spOver ψ ≫ x) :
    ∃ k : Fn0 A, IsCob (whole A) f k := by
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ k : D,
      ∀ (D₂ : Type) [CommRing D₂] [Algebra R D₂] (ψ₂ : D →ₐ[R] D₂) (z₂ : Pt A D₂),
        (z₂ ^ p : Pt A D₂) = spOver ψ₂ ≫ x → ψ₂ k = sig p f g ψ₂ x z₂ := by
    intro D _ _ x
    obtain ⟨D', _, _, ψ, z, hψ, hz⟩ := hr D x
    have cmp : ∀ (D₂ : Type) [CommRing D₂] [Algebra R D₂] (ψ₂ : D →ₐ[R] D₂) (z₂ : Pt A D₂),
        (z₂ ^ p : Pt A D₂) = spOver ψ₂ ≫ x →
        ∀ (E : Type) [CommRing E] [Algebra R E] (α : D' →ₐ[R] E) (β : D₂ →ₐ[R] E),
          α.comp ψ = β.comp ψ₂ → α (sig p f g ψ x z) = β (sig p f g ψ₂ x z₂) := by
      intro D₂ _ _ ψ₂ z₂ hz₂ E _ _ α β e
      rw [sig_nat hp hf hfg ψ α x z hz, sig_nat hp hf hfg ψ₂ β x z₂ hz₂, sig, sig, e,
        chi_indep hp hg h0 (spOver α ≫ z) (spOver β ≫ z₂)
          (by rw [pow_comp ψ α x z hz, pow_comp ψ₂ β x z₂ hz₂, e])]
    obtain ⟨k, hk⟩ := descend ψ hψ (sig p f g ψ x z) (fun E _ _ α β e ↦ cmp D' ψ z hz E α β e)
    refine ⟨k, fun D₂ _ _ ψ₂ z₂ hz₂ ↦ ?_⟩
    obtain ⟨E, _, _, α, β, e, hβ⟩ := exists_square ψ hψ ψ₂
    apply hβ
    rw [← cmp D₂ ψ₂ z₂ hz₂ E α β e, ← hk]
    exact (DFunLike.congr_fun e k).symm
  choose k hk using key
  refine ⟨k, fun D _ _ D₁ _ _ φ x _ ↦ ?_⟩
  obtain ⟨D', _, _, ψ, z, hψ, hz⟩ := hr D₁ (spOver φ ≫ x)
  have hi : Function.Injective ψ := hψ.injective
  apply hi
  have h1 := hk D₁ (spOver φ ≫ x) D' ψ z hz
  have h2 := hk D x D' (ψ.comp φ) z (by rw [hz, ← Category.assoc, spOver_comp])
  have h3 := hf D D₁ D' φ ψ x (sm_whole _)
  simp only [sig, AlgHom.comp_apply] at h1 h2
  rw [map_sub ψ]
  linear_combination h2 - h1 - h3

end GlobalTheory.PtExt.Descent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricDataComparePolarisedUpToFunctionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_data_compare_polarised_up_to_function : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] (Q : Data R) (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), Function.Injective ρ → IsGrpPullback P.A Q.B (spMap ρ) β → IsSquare β β₂ → (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) → ∃ (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ), Half Q ρ D e f := by
  first | exact @GlobalTheory.HalfEx.half_exists | exact GlobalTheory.HalfEx.half_exists | (intros; apply GlobalTheory.HalfEx.half_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelGeometricPointHarrisTaylorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplectic_level_geometric_point_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N M e : ℕ),
  3 ≤ M → Odd M → M.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
    ∃ (t₁ : Sp K ⟶ Sp (cycAway M))
      (lv : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (Over.mk x ⟶ o.A)),
      SympCond o (Module.finrank ℤ D.La / 2) M (Over.mk x) t₁ lv := by
  first | (exact @GlobalTheory.HTSympCover.exists_sympCond_geom) | (exact GlobalTheory.HTSympCover.exists_sympCond_geom) | (intros; apply GlobalTheory.HTSympCover.exists_sympCond_geom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemSpreadOfLevelFractionFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSystem_spread_of_level_fractionField : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [CharZero R₁] (A₁ : PolAV (Sp (FractionRing R₁))), (letI := A₁.isAb.comm; GlobalTheory.ZH.HypS A₁.A A₁.L) → ∀ (n k j : ℕ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : R₁) → ∀ (ζ : R₁ˣ), ReciprocityTheory.ChartRestriction.G.Out.Level A₁ ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ)) → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : GlobalTheory.ZH.ArithBase o Ω) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (b : o →+* R₁) (e : Ω →+* FractionRing R₁) (φ : A₁.A.left ⟶ ρS.P.A.left), S.g = A₁.g ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ (∀ x : o, e (algebraMap o Ω x) = algebraMap R₁ (FractionRing R₁) (b x)) ∧ IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ ∧ LBIso A₁.L (ρS.P.L.pull φ) := by
  first | exact @GlobalTheory.Mum.exists_thetaSys_spread | exact GlobalTheory.Mum.exists_thetaSys_spread | (intros; apply GlobalTheory.Mum.exists_thetaSys_spread <;> assumption)
end

