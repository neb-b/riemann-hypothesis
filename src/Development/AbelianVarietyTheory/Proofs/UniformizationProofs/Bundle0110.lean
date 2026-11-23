module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusTorsionToAbelianTorsionThetaAction
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProportionalField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProportionalRaw
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionComponentsProportionalShiftMultiple
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU.SchurComp


set_option maxHeartbeats 1000000 in
theorem components_proportional : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → ∀ (α mu : D.X) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (Kbar V) N α mu) (DegPre.deltaε N))), u.IsGen → U.Supp (Kbar V) N α → ∃ a : Kbar V, ∀ t s, U.ExpF (Kbar V) N t s → ∀ z J, Good D.P.L z J → sval (s (α + N • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) a ⊤) * (sval (s α) (DegPre.trF D (Kbar V) mu).left z J * (val u (𝟙 _) z J).val)) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U N hN α mu u hu hS
  have := hV.1
  have := hV.2.2
  have hN0 : N ≠ 0 := by omega
  have hNF : (N : Kbar V) ≠ 0 := Nat.cast_ne_zero.2 hN0
  obtain ⟨Φ, e, hfr, hθ, hmul, hcomm, hnd⟩ :=
    GlobalTheory.ThetaRep.exists_projective_rep hL hL2 _ A (Kbar V) (jFK (R := V) (Kbar V)) N hNF
  obtain ⟨m, hm, hact, -⟩ := GlobalTheory.UU.Eqv.main hL hL2 V hV D A G U N hN
  obtain ⟨hw1, hw2, hw3⟩ := _root_.GlobalTheory.UU.Weight.main hL hL2 V hV D A G U N hN
  have huniq := GlobalTheory.UU.ExpFUniq.main V hV D A G U (Kbar V) N
  choose xp hxp using GlobalTheory.UU.ExpTotal.expF_total hL hL2 V hV D A G U (Kbar V) N hN
  have hcA := (hL.mulN _ A N hN).2.2.2.2 (Kbar V) (jFK (R := V) (Kbar V)) hNF
  have hcH := (GlobalTheory.GtCount.card_gtTors hL hL2 V D (Kbar V) N hNF).1
  have hg : A.g = D.P.g + D.rank := GlobalTheory.UU.PreU.dim_eq V hV D A G U
  have hlinF := ExpLin.expF_linear V hV D A G U (Kbar V) N
  have hbas := exists_basis_twist_field hL hL2 V D (Kbar V) N hN
  clear * - hL hN0 hu hS Φ e hfr hθ hmul hcomm hnd m hm hact hw1 hw2 hw3 huniq xp hxp hcA hcH hg hlinF hbas
  have := A.isAb.comm
  let iso := (Scheme.ΓSpecIso (CommRingCat.of (Kbar V))).commRingCatIsoToRingEquiv
  let S : Subgroup (TFK (R := V) (Kbar V) ⟶ A.A) := (powMonoidHom N).ker
  have hcS : Nat.card S = N ^ (2 * A.g) := hcA
  have : Finite S := Nat.finite_of_card_ne_zero (hcS ▸ pow_ne_zero _ hN0)
  obtain ⟨x, hx⟩ : ∃ x : SecM A.A A.L N (TFK (R := V) (Kbar V)) → Raw D (Kbar V) N,
    ∀ v, U.ExpF (Kbar V) N (SecM.toSec A.A v) (x v) := ⟨_, fun v => hxp _⟩
  have hxe : ∀ t s, U.ExpF (Kbar V) N t s → x (SecM.ofSec A.A t) = s := fun t s h => (huniq _ _ _ _ (hx _) h).1 rfl
  have hsupp : ∀ β, U.Supp (Kbar V) N β ↔ ∃ v j, (x v β).f j ≠ 0 := fun β =>
    ⟨fun ⟨t, s, h, hj⟩ => ⟨SecM.ofSec A.A t, by rwa [hxe t s h]⟩, fun ⟨v, hv⟩ => ⟨_, _, hx v, hv⟩⟩
  refine (proportional_raw (D := D) (k := Γ((TFK (R := V) (Kbar V)).left, ⊤)) (A := S)
    (E := SecM A.A A.L N (TFK (R := V) (Kbar V))) hL.globalFns iso e Φ ?_ ?_ ?_ ?_ hN0 (fun g => ⟨m g, (hact g).1⟩)
    ?_ ?_ (n := N ^ D.P.g) ?_ x ?_ ?_ ?_ ?_ ?_ ?_ ?_ α mu u hu ((hsupp _).1 hS)).elim fun a ha => ?_
  · rw [hcS, mul_comm, pow_mul]; exact congrArg (· ^ 2) hfr
  · exact fun a b => hmul a b (a * b : S) rfl
  · exact fun a b => (hcomm a b).2
  · exact fun a h => Subtype.ext (hnd a h)
  · exact fun g g' h => hm (congrArg Subtype.val h)
  · rw [hcS, hcH, hg, ← pow_add]; exact le_of_eq (congrArg _ (by ring))
  · rw [← pow_add, add_comm, ← hg]; exact hfr.ge
  · intro c v v' β
    obtain ⟨c, rfl⟩ := iso.symm.surjective c
    choose s hs using fun β => exists_comb ((fst (TF (R := V) (Kbar V)) D.P.A).left.appTop.hom (iso.symm c))
      (x v β) (x v' β)
    have := hlinF _ _ (SecM.toSec A.A (iso.symm c • v + v' :)) _ _ s c (hx v) (hx v') (fun _ => rfl) hs
    rw [(huniq _ _ _ _ (hx _) this).1 rfl, iso.apply_symm_apply]
    exact hs β
  · exact fun v v' h => congrArg (SecM.ofSec A.A) ((huniq _ _ _ _ (hx v) (hx v')).2 h)
  · intro χ v
    obtain ⟨t', s', h, H⟩ := hw1 χ _ _ (hx v)
    exact ⟨SecM.ofSec A.A t', by rwa [hxe _ _ h]⟩
  · exact fun χ => (hw2 χ).imp fun ν h => (hsupp _).1 h
  · exact fun χ hχ v h h' => Subtype.ext (funext (hw3 χ ((hsupp _).2 hχ) _ _ (hx v) h h'))
  · exact fun β => (hbas β).imp fun b hb s => (hb s).exists
  · intro g
    obtain ⟨θ, hθ₁, hθ₂⟩ := hθ ⟨m g, (hact g).1⟩
    obtain ⟨w, hw, H⟩ := (hact g).2 θ hθ₁
    exact ⟨w, hw, fun v => H _ _ _ _ (hx _) (hx _) (hθ₂ v)⟩
  · refine ⟨a, fun t s h => ?_⟩
    rw [← hxe t s h]
    exact ha _

end GlobalTheory.UU.SchurComp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PairingNondegenerate
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU.SpecialPairing

theorem card_map {A₀ A A' : Type} [CommGroup A₀] [CommGroup A] [CommGroup A'] (r : A →* A₀) (j : A →* A') (N : ℕ)
    (ri : ∀ y y', y ^ N = 1 → y' ^ N = 1 → r y = r y' → y = y') (rs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ r y = x)
    (hj : Function.Injective j) (K : Subgroup A₀) :
    Nat.card (((powMonoidHom N).ker ⊓ K.comap r).map j) = Nat.card {x : A₀ // x ^ N = 1 ∧ x ∈ K} := by
  rw [Subgroup.card_map_of_injective hj]
  refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨r y.1, by rw [← map_pow, show y.1 ^ N = 1 from y.2.1, map_one],
    y.2.2⟩) ⟨fun y y' h => Subtype.ext (ri _ _ y.2.1 y'.2.1 (congrArg Subtype.val h)), fun x => ?_⟩)
  obtain ⟨y, hy, e⟩ := rs x.1 x.2.1
  exact ⟨⟨y, hy, show r y ∈ K from e ▸ x.2.2⟩, Subtype.ext e⟩

theorem core {A₀ A A' B : Type} [CommGroup A₀] [CommGroup A] [CommGroup A'] [CommGroup B] (r : A →* A₀)
    (j : A →* A') (q : A₀ →* B) (N M : ℕ) (P' : A' → A' → Prop) (P : B → B → Prop)
    (ri : ∀ y y', y ^ N = 1 → y' ^ N = 1 → r y = r y' → y = y') (rs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ r y = x)
    (hj : Function.Injective j) (qs : ∀ b, b ^ N = 1 → ∃ x, x ^ N = 1 ∧ q x = b)
    (hP : ∀ y y', y ^ N = 1 → y' ^ N = 1 → P (q (r y)) (q (r y')) → P' (j y) (j y'))
    (h1 : ∀ b, b ^ N = 1 → P 1 b)
    (hc : Nat.card {x : A₀ // x ^ N = 1 ∧ q x = 1} * Nat.card {x : A₀ // x ^ N = 1} = M)
    (rad : ∀ T H : Subgroup A', (∀ x ∈ T, x ^ N = 1) → (∀ x ∈ H, x ^ N = 1) → Nat.card T * Nat.card H = M →
      (∀ x ∈ T, ∀ y ∈ H, P' x y) → ∀ x, x ^ N = 1 → (∀ y ∈ H, P' x y) → x ∈ T)
    (b : B) (hb : b ^ N = 1) (h : ∀ b', b' ^ N = 1 → P b b') : b = 1 := by
  have tq : ∀ y : A, y ^ N = 1 → q (r y) ^ N = 1 := fun y hy => by rw [← map_pow, ← map_pow, hy, map_one, map_one]
  have tj : ∀ y : A, y ^ N = 1 → j y ^ N = 1 := fun y hy => by rw [← map_pow, hy, map_one]
  obtain ⟨x, hx, rfl⟩ := qs b hb
  obtain ⟨y, hy, rfl⟩ := rs x hx
  obtain ⟨y', hy', e⟩ := rad (((powMonoidHom N).ker ⊓ q.ker.comap r).map j)
    (((powMonoidHom N).ker ⊓ (⊤ : Subgroup A₀).comap r).map j)
    (by rintro _ ⟨z, hz, rfl⟩; exact tj z hz.1) (by rintro _ ⟨z, hz, rfl⟩; exact tj z hz.1)
    (by
      rw [card_map r j N ri rs hj, card_map r j N ri rs hj, ← hc]
      simp only [Subgroup.mem_top, and_true, MonoidHom.mem_ker])
    (by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
      refine hP z z' hz.1 hz'.1 ?_
      rw [show q (r z) = 1 from hz.2]
      exact h1 _ (tq _ hz'.1))
    (j y) (tj y hy) (by
      rintro _ ⟨z', hz', rfl⟩
      exact hP y z' hy hz'.1 (h _ (tq _ hz'.1)))
  obtain rfl := hj e
  exact hy'.2

theorem exists_embedding (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] [Algebra V W]
    [Module.Finite V W] (h : Function.Injective (algebraMap V W)) :
    ∃ φ : W →+* AlgebraicClosure (FractionRing V), Function.Injective φ ∧ φ.comp (algebraMap V W) =
      (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V)) := by
  have i : Function.Injective (algebraMap V (AlgebraicClosure (FractionRing V))) := by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V)]
    exact (algebraMap (FractionRing V) _).injective.comp (IsFractionRing.injective V (FractionRing V))
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 h
  have : FaithfulSMul V (AlgebraicClosure (FractionRing V)) := (faithfulSMul_iff_algebraMap_injective _ _).2 i
  let φ : W →ₐ[V] AlgebraicClosure (FractionRing V) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom, ?_, ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    change Ideal.comap (algebraMap V W) (RingHom.ker φ.toRingHom) = ⊥
    rw [RingHom.comap_ker, show φ.toRingHom.comp (algebraMap V W) = algebraMap V _ from φ.comp_algebraMap]
    exact (RingHom.injective_iff_ker_eq_bot _).1 i
  · rw [← IsScalarTower.algebraMap_eq]; exact φ.comp_algebraMap

theorem torsion_ext (W : Type) [CommRing W] [IsLocalRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (p : Spec (CommRingCat.of W) ⟶ S) (N : ℕ)
    (hN : IsUnit (N : W)) {Ω : Type} [Field Ω] (f : W →+* Ω) [IsLocalHom f] (y y' : Over.mk p ⟶ G) (hy : y ^ N = 1)
    (hy' : y' ^ N = 1) (e : Spec.map (CommRingCat.ofHom f) ≫ y.left = Spec.map (CommRingCat.ofHom f) ≫ y'.left) :
    y = y' := by
  have := GlobalTheory.TorsionSeparable.epi_specMap (IsLocalRing.ResidueField.lift f)
  rw [← IsLocalRing.ResidueField.lift_comp_residue f, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Category.assoc, cancel_epi] at e
  let ρ : Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)) ≫ p) ⟶ Over.mk p :=
    Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W))) rfl
  exact (GlobalTheory.existsUnique_torsion_lift W S G p N hN (ρ ≫ y)
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])).unique ⟨hy, rfl⟩ ⟨hy', e.symm⟩

theorem toBase_bijective {S S' : Scheme.{0}} (G : Over S) (f : S' ⟶ S) (T : Over S') :
    Function.Bijective (toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f)
      pullback.condition (T := T)) :=
  ⟨fun x y h => Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun z => z.left) h)
    ((Over.w x).trans (Over.w y).symm)), fun x =>
    ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩⟩


set_option maxHeartbeats 800000 in
theorem pairing_nondegenerate : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun {V} _ _ _ {_} {_} _ _ s => ∀ (t : Tower s) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)))) (N : ℕ), IsUnit (N : V) → ∀ x : Over.mk p ⟶ (t.l 0).Q.B, x ^ N = 1 → (∀ y : Over.mk p ⟶ (t.l 0).Q.B, y ^ N = 1 → CubWeil (t.l 0).D.M.c N x y 1) → x = 1 := by
  intro hAb hL V _ _ _ A G _ _ s t Ω _ _ p N hN
  obtain ⟨dvr, cpl, -⟩ := s.cdvr
  have := s.semi.smooth
  have := s.semi.separated
  have := (t.l 0).Q.q_hom
  obtain ⟨φ₀, rfl⟩ : ∃ φ₀ : (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) →+* Ω, p = Spec.map (CommRingCat.ofHom φ₀) :=
    ⟨(Spec.preimage p).hom, (Spec.map_preimage p).symm⟩
  let f : V →+* Ω := φ₀.comp (Ideal.Quotient.mk _)
  have hf : IsLocalHom f := ⟨fun a ha => by
    by_contra h
    have : Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact h)
    exact ha.ne_zero (by rw [RingHom.comp_apply, this, map_zero])⟩
  have hNΩ : (N : Ω) ≠ 0 := by simpa using (hN.map f).ne_zero
  have hN0 : N ≠ 0 := by rintro rfl; simp at hNΩ
  obtain ⟨g', hg'⟩ : ∃ g', SmoothOfRelativeDimension g' (t.l 0).Q.B.hom := by
    have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := φ₀.domain_nontrivial
    have : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    exact GlobalTheory.AbelianDim.exists_relDim _ _ (t.l 0).Q.isAb
  have hd := (GlobalTheory.UU.Tower.dim_eq_add_finrank V A G s t g').1 hg'
  obtain ⟨c₁, c₂⟩ := torusQuotient_card_torsion _ _ _ (t.l 0).Q Ω (Spec.map (CommRingCat.ofHom φ₀)) N hNΩ
  rw [GlobalTheory.card_torsion_geometricPoint_of_field hAb _ _ (t.l 0).Q.isAb g' hg' Ω _ N hNΩ] at c₂
  let T₀ : Over (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)))) :=
    Over.mk (Spec.map (CommRingCat.ofHom φ₀))
  have hpf : Spec.map (CommRingCat.ofHom f) = T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0 := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  let β : (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) ≃*
      (Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) ⟶ G) :=
    MulEquiv.ofBijective (toBaseHom (toBase_mul_pullback G _) T₀) (toBase_bijective G _ T₀)
  have hβ : ∀ x, (β x).left = x.left ≫ (fstG _ 0 G).left := fun _ => rfl
  let ι₀ : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hpf.symm)
  have fin : Finite {x : T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G // x ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  have fin' := (show Set.Finite {x : T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G | x ^ N = 1} from fin).image
    (fun x => ι₀ ≫ β x)
  obtain ⟨W, _, _, _, _, _, f', _, inj, _, _, hf', lifts⟩ := GlobalTheory.exists_finite_extension_torsion_lift hL.unramExt V G N
    hN Ω f hf fin'.toFinset (by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := fin'.mem_toFinset.1 hx
      show (ι₀ ≫ β u) ^ N = 1
      rw [← MonObj.comp_pow, ← map_pow, show u ^ N = 1 from hu, map_one, MonObj.comp_one])
  obtain ⟨φ, φi, hφ⟩ := exists_embedding V W inj
  let TW : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))
  let ρ : Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) ⟶ TW :=
    Over.homMk (Spec.map (CommRingCat.ofHom f')) (by
      refine Eq.trans ?_ hpf
      rw [← hf', CommRingCat.ofHom_comp, Spec.map_comp]; rfl)
  let σ : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ TW :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
      have e := congrArg (fun z => Spec.map (CommRingCat.ofHom z)) hφ
      simp only [CommRingCat.ofHom_comp, Spec.map_comp] at e
      exact e)
  let r : (TW ⟶ G) →* (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) := β.symm.toMonoidHom.comp (preHom ρ)
  have hr : ∀ y, (r y).left ≫ (fstG _ 0 G).left = Spec.map (CommRingCat.ofHom f') ≫ y.left := fun y =>
    (hβ _).symm.trans (congrArg (fun z => z.left) (β.apply_symm_apply (ρ ≫ y)))
  let q : (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) →* (T₀ ⟶ (t.l 0).Q.B) :=
    MonoidHom.mk' (· ≫ (t.l 0).Q.q) fun x y => MonObj.mul_comp x y _
  refine core r (preHom σ) q N (N ^ (2 * A.g)) (fun x y => CubWeil s.P.c N x y 1)
    (fun x y => CubWeil (t.l 0).D.M.c N x y 1) (fun y y' hy hy' e => ?_) (fun x hx => ?_) (fun y y' e => ?_)
    ?_ (fun y y' hy hy' h => ?_) (fun b hb => cubWeil_one_left _ hb) ?_
    (mem_of_cubWeil_orthogonal hL V A G s _ N (Nat.one_le_iff_ne_zero.2 hN0))
  · refine torsion_ext W G _ N (by simpa using hN.map (algebraMap V W)) f' y y' hy hy' ?_
    rw [← hr, ← hr, e]
  · obtain ⟨y, hy, e⟩ := lifts (ι₀ ≫ β x) (fin'.mem_toFinset.2 ⟨x, hx, rfl⟩)
    refine ⟨y, hy, β.injective (Over.OverMorphism.ext ?_)⟩
    have e' : (ι₀ ≫ β x).left = (β x).left := Category.id_comp _
    rw [hβ, hr y, e, e']
  · exact GlobalTheory.over_points_ext_of_injective _ G W _ φ φi _ y y' (congrArg (fun z => z.left) e)
  · refine (torusQuotient_points_lift _ _ _ (t.l 0).Q Ω _).2 N fun a => ?_
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a.val (Nat.pos_of_ne_zero hN0)
    have hz0 : z ≠ 0 := by rintro rfl; exact a.ne_zero (by rw [← hz, zero_pow hN0])
    exact ⟨Units.mk0 z hz0, Units.ext hz⟩
  · have := ((cubWeil_one_iff_closedFibre V A G s t W Ω f' inferInstance _ N hN y y' (r y) (r y') hy hy' (hr y) (hr y')).2 h).comp σ
    rwa [map_one] at this
  · have e : N ^ (2 * A.g) = N ^ Module.finrank ℤ s.X * (N ^ Module.finrank ℤ s.X * N ^ (2 * g')) := by
      rw [hd]; ring
    rw [e]
    exact congrArg₂ (· * ·) ((Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)).trans c₁) c₂

end GlobalTheory.UU.SpecialPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PolAVNonzeroLocusCoverAffine
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem polAV_nonzeroLocus_cover_affine (hA : AmpleSt) {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    (P : PolAV S) {N : ℕ} (hN : 4 ≤ N) :
    (∀ x : P.A.left, ∃ s : H0 P.L N, x ∈ nonzeroLocus s) ∧ ∀ s : H0 P.L N, IsAffineOpen (nonzeroLocus s) := by
  classical
  have := P.isAb.proper
  let := P.grp
  obtain ⟨M, s, hs⟩ := AmpleSpan.exists_embedsBy_of_isPullback P.A P.isLB (hA S P N hN).2 (isAffineOpen_top S)
    (φ := 𝟙 P.A.left) (f' := P.A.hom) (g := 𝟙 S ≫ S.topIso.inv)
    (by rw [AmpleSpan.comp_topIso_inv_ι]; exact IsPullback.of_id_fst) (K := Fin 1) (ε := fun _ => (N : ℤ)) (by simp)
  refine ⟨fun x => ?_, fun t => (hs.affine_and_surjective (t := s) (fun j => ⟨Pi.single j 1, fun k => ?_⟩) t).1⟩
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.1.ge (Set.mem_univ x))
    exact ⟨s i, hi⟩
  · rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, map_one, _root_.one_mul]
    · intro l _ hl
      rw [Pi.single_eq_of_ne hl, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h

theorem exists_iso_of_polAV_sectionRing : Laws → ∀ (K : Type) [Field K] (P P' : PolAV (Spec (CommRingCat.of K))), ∀ θ : ∀ n : ℕ, 1 ≤ n → (H0 P'.L n ≃ H0 P.L n), (∀ (n : ℕ) (hn : 1 ≤ n) (c : K) (a b d : H0 P'.L n), (∀ j, d.f j = a.f j + resTop _ (scal P'.A.hom c) * b.f j) → ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal P.A.hom c) * (θ n hn b).f j) → (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 P'.L n) (b : H0 P'.L m) (d : H0 P'.L (n + m)), (∀ j : Fin 1 → P'.L.ι, (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from d.f j) = (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from a.f j) * (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from b.f j)) → ∀ j : Fin 1 → P.L.ι, (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) = (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ n hn a).f j) * (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ m hm b).f j)) → ∃ Φ₀ : P'.A ≅ P.A, ∃ w : LB.Iso P'.L (P.L.pull Φ₀.hom.left), w.IsGen ∧ ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 P'.L n), (∀ (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (p : Fin 1 → P.L.ι) (q : Fin 1 → P'.L.ι), (∀ κ, (Φ₀.hom.left) ((fun _ : Fin 1 => 𝟙 P'.A.left) κ (r z)) ∈ P.L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 P'.A.left) κ (r z) ∈ P'.L.U (q κ)) → Geo.Tor.gs (r ≫ Φ₀.hom.left) z (LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) p) ((θ n hn a).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (fun _ : Fin 1 => 𝟙 P'.A.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (n : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) q) ((a).f q)) := by
  intro hL K _ P P' θ hlin hmul
  have := P.isAb.proper
  have := P'.isAb.proper
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : CompactSpace P'.A.left := QuasiCompact.compactSpace_of_compactSpace P'.A.hom
  have : QuasiSeparatedSpace P.A.left := quasiSeparatedSpace_of_quasiSeparated P.A.hom
  have : QuasiSeparatedSpace P'.A.left := quasiSeparatedSpace_of_quasiSeparated P'.A.hom
  obtain ⟨c, a⟩ := polAV_nonzeroLocus_cover_affine hL.ample P (le_refl 4)
  obtain ⟨c', a'⟩ := polAV_nonzeroLocus_cover_affine hL.ample P' (le_refl 4)
  obtain ⟨c₅, -⟩ := polAV_nonzeroLocus_cover_affine hL.ample P' (N := 4 + 1) (by norm_num)
  obtain ⟨Φ, hΦ⟩ := exists_iso_of_sectionRing_equiv K P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul
    ⟨4, by norm_num, H0 P'.L 4, id, top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (c' x),
      top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (by
        obtain ⟨s, hs⟩ := c x
        obtain ⟨t, rfl⟩ := (θ 4 (by norm_num)).surjective s
        exact ⟨t, hs⟩), fun i => ⟨a' _, a _⟩⟩
  refine ⟨Φ, exists_iso_of_sectionRing K P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul Φ.hom.left hΦ fun x => ?_⟩
  obtain ⟨s, hs⟩ := c' x
  obtain ⟨t, ht⟩ := c₅ x
  exact ⟨4, by norm_num, s, t, hs, ht⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleDescent

theorem isAmpleLB_of_pull {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') [Flat (specOf g)]
    [Surjective (specOf g)] {X X' : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X]
    {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')} [UniversallyClosed f']
    (H : IsPullback π f' f (specOf g)) {L : LB X} (hL : L.IsLB) (h : IsAmpleLB (L.pull π)) : IsAmpleLB L := by
  have hg : g.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 (inferInstance : Flat (specOf g))
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) H.flip inferInstance
  refine ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := π.surjective x
  obtain ⟨n, hn, s, hs, -⟩ := h.exists_affine z
  have hM := isLB_lbPow hL n
  obtain ⟨σ, hσ⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull hM π) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL π n).symm s
  obtain ⟨m, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H _ hM σ
  obtain ⟨k, hk⟩ := exists_chart hM (π z)
  have hz : IsUnit (gs (𝟙 X') z _ (σ.f fun _ => k)) :=
    (mem_nonzeroLocus_iff_isUnit σ (k := fun _ => k) (mem_pull.2 hk)).1 (hσ.ge hs)
  rw [hu z k hk] at hz
  obtain ⟨j, -, hj⟩ := IsLocalRing.exists_of_isUnit_sum hz
  refine ⟨n, hn, u j, (mem_nonzeroLocus_iff_pull (u j) π z hk).2 (isUnit_of_mul_isUnit_right hj), ?_⟩
  have ha := h.isAffineOpen_nonzeroLocus f' hn (secPowPull (u j) π)
  rw [nonzeroLocus_secPowPull] at ha
  have : IsAffine (π ⁻¹ᵁ nonzeroLocus (u j)) := ha
  exact isAffine_of_isPullback_of_flat_surjective
    ((isPullback_morphismRestrict π (nonzeroLocus (u j))).paste_vert H)

theorem kTriv_of_pull {S S' : Scheme.{0}} [IsAffine S] [IsAffine S'] {f : S' ⟶ S} [Flat f] [Surjective f]
    {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : KTriv A' L') :
    KTriv A L := by
  obtain ⟨w, hw⟩ := hw
  intro R _ t x hx
  obtain ⟨R', g, t', hg, sq⟩ : ∃ (R' : CommRingCat.{0}) (g : Spec R' ⟶ Spec (CommRingCat.of R)) (t' : Spec R' ⟶ S'),
      Epi g ∧ g ≫ t = t' ≫ f := by
    refine ⟨Γ(pullback t f, ⊤), (pullback t f).isoSpec.inv ≫ pullback.fst t f,
      (pullback t f).isoSpec.inv ≫ pullback.snd t f, Flat.epi_of_flat_of_surjective _, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition]
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have hxw : (g ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = g ≫ x.left := h.1.lift_fst _ _ _
  have key : x' = toUnit _ ≫ η[A'] := hK R' t' x' fun p => by
    obtain ⟨V, hV, c, hc⟩ := hx (g p)
    refine ⟨g ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ g)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ g := congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (lift a b).left ≫ (snd T A).left = (snd T' A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a b)
    have k₃ : (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left = ((fst T' A' ≫ x') * snd T' A').left ≫ φ := by
      have e : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      refine (congrArg (fun q => q.left) e).trans (h.2 (T' ⊗ A') _ _ _ _ ?_ rfl)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)
    have le : (fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V ≤ (lift a b).left ⁻¹ᵁ (fst T A).left ⁻¹ᵁ V := fun y hy =>
      (congrArg (fun q => q y ∈ V) k₁).mpr hy
    have hn := Scheme.Hom.resLE_comp_ι (lift a b).left le
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k : Fin 2 => (((fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V).ι ≫
      ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k) ≫ φ) _ _
      ((lift a b).left.resLE _ _ le) fun k => by
        rw [← Category.assoc, hn, Category.assoc, Category.assoc]
        fin_cases k
        exacts [congrArg (_ ≫ ·) k₃.symm, congrArg (_ ≫ ·) k₂.symm]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ _ fun _ => rfl) c₃ h₃
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g sq
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext hx'.symm
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  exact Over.OverMorphism.ext ((cancel_epi g).1 (congrArg (fun q => q.left) e₂))

theorem proper_relAmple_kTriv_of_fieldExtension : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [QuasiCompact G.hom] [IsSeparated G.hom] [Smooth G.hom] (G' : Over (Spec (CommRingCat.of K'))) [GrpObj G'] (Ψ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (specOf i) Ψ → ∀ (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (L.pull Ψ) → IsProper G'.hom → RelAmple G' L' → KTriv G' L' → IsProper G.hom ∧ RelAmple G L ∧ KTriv G L := by
  intro K K' _ _ i G _ _ _ _ G' _ Ψ h L L' hL hL' hw hP hA hK
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of K')) := inferInstanceAs (Nonempty (PrimeSpectrum K'))
  have : Flat (specOf i) := inferInstance
  have : Surjective (specOf i) := inferInstance
  have : UniversallyClosed G.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have hG : IsProper G.hom := ⟨⟩
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  refine ⟨hG, (relAmple_iff_isAmpleLB_of_isAffine G hL).2 (isAmpleLB_of_pull i h.1 hL ?_),
    kTriv_of_pull h hL hL' hw hK⟩
  exact (isAmpleLB_of_relAmple_of_isAffine G' hL' hA).of_lbIso (LB.isLB_pull hL Ψ) hw.symm

end GlobalTheory.AmpleDescent
end
end

