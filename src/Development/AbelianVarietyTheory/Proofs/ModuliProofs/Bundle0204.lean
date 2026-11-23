module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.HeckeKerZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointObjectExistsOfLaws
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0161
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardEqMapMulKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.HeckeDual

open GlobalTheory.HeckeKerModel

section Count

theorem card_eq_map_mul_ker {A B : Type} [Group A] [Group B] (f : A →* B) (X : Subgroup A) (h : f.ker ≤ X) :
    Nat.card X = Nat.card (X.map f) * Nat.card f.ker := by
  have h1 := (f.domRestrict X).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h1
  rw [← h1, Nat.mul_comm]

theorem card_dual_ker {Q Q' : Type} [CommGroup Q] [CommGroup Q'] (f : Q →* Q') (g : Q' →* Q) (p N : ℕ)
    (hf : Function.Surjective f) (hg : ∀ x, g (f x) = x ^ p ^ 2) (hN : N ≠ 0)
    (h1 : Nat.card (powMonoidHom p : Q →* Q).ker = N) (h2 : Nat.card (powMonoidHom (p ^ 2) : Q →* Q).ker = N ^ 2)
    (h3 : Nat.card f.ker = N) (hdiv : ∀ x : Q, x ^ p = 1 → ∃ y, y ^ p = x) :
    Nat.card g.ker = N ∧ Nat.card (g.ker ⊓ (powMonoidHom p : Q' →* Q').ker : Subgroup Q') =
      Nat.card (f.ker ⊓ (powMonoidHom p : Q →* Q).ker : Subgroup Q) := by
  have hle : ∀ x, f x = 1 → x ^ p ^ 2 = 1 := fun x hx => by rw [← hg, hx, map_one]
  constructor
  · have e := card_eq_map_mul_ker f (powMonoidHom (p ^ 2) : Q →* Q).ker hle
    have e' : (powMonoidHom (p ^ 2) : Q →* Q).ker.map f = g.ker := by
      ext y
      obtain ⟨x, rfl⟩ := hf y
      refine ⟨?_, fun h => ⟨x, (hg x).symm.trans h, rfl⟩⟩
      rintro ⟨z, hz, ez⟩
      rw [← ez]
      exact (hg z).trans hz
    rw [e', h2, h3, sq] at e
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hN) e).symm
  · let X : Subgroup Q := (f.ker ⊓ (powMonoidHom p : Q →* Q).ker).comap (powMonoidHom p)
    have hX : ∀ x, x ∈ X ↔ f x ^ p = 1 ∧ x ^ p ^ 2 = 1 := fun x => by
      rw [← map_pow, sq, pow_mul]
      rfl
    have e := card_eq_map_mul_ker f X fun x hx => (hX x).2 ⟨by rw [show f x = 1 from hx, one_pow], hle x hx⟩
    have e₂ := card_eq_map_mul_ker (powMonoidHom p) X fun x hx => (hX x).2 (by
      have hx' : x ^ p = 1 := hx
      rw [← map_pow, sq, pow_mul, hx', map_one, one_pow]
      exact ⟨rfl, rfl⟩)
    have e' : X.map f = g.ker ⊓ (powMonoidHom p : Q' →* Q').ker := by
      ext y
      obtain ⟨x, rfl⟩ := hf y
      refine ⟨?_, fun h => ⟨x, (hX x).2 ⟨h.2, (hg x).symm.trans h.1⟩, rfl⟩⟩
      rintro ⟨z, hz, ez⟩
      rw [← ez]
      exact ⟨(hg z).trans ((hX z).1 hz).2, ((hX z).1 hz).1⟩
    have e₂' : X.map (powMonoidHom p) = f.ker ⊓ (powMonoidHom p : Q →* Q).ker := by
      refine Subgroup.map_comap_eq_self fun x hx => hdiv x hx.2
    rw [e', h3] at e
    rw [e₂', h1] at e₂
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hN) (e.symm.trans e₂)

end Count

variable {S : Scheme.{0}}

theorem exists_lift {A B : Over S} (ψ : A ⟶ B) [LocallyOfFiniteType ψ.left] [Surjective ψ.left] {k : Type} [Field k]
    [IsAlgClosed k] (t : Sp k ⟶ S) (y : Over.mk t ⟶ B) : ∃ x : Over.mk t ⟶ A, x ≫ ψ = y := by
  let y' : Sp k ⟶ B.left := y.left
  obtain ⟨z, -⟩ := (pullback.snd ψ.left y').surjective (IsLocalRing.closedPoint k)
  have : JacobsonSpace ↥(pullback ψ.left y') := LocallyOfFiniteType.jacobsonSpace (pullback.snd ψ.left y')
  obtain ⟨z', -, hz'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback ψ.left y')))
    ⟨z, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {z'} := hz'
  have e : (pointOfClosedPoint (pullback.snd ψ.left y') z' hc ≫ pullback.fst ψ.left y') ≫ ψ.left = y' := by
    rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  exact ⟨Over.homMk (pointOfClosedPoint (pullback.snd ψ.left y') z' hc ≫ pullback.fst ψ.left y')
    (by rw [← Over.w ψ, ← Category.assoc, e]; exact Over.w y), Over.OverMorphism.ext e⟩

theorem kerSet_unit {G G' : Over S} [GrpObj G'] [IsSeparated G'.hom] (ψ : G ⟶ G') :
    KerSet ψ (ψ.left ⁻¹' Set.range (η[G'] : 𝟙_ (Over S) ⟶ G').left) := by
  intro k _ _ x z
  have hw : (η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom = 𝟙 _ := Over.w _
  have : IsClosedImmersion (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    have : IsClosedImmersion ((η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom) := by rw [hw]; infer_instance
    exact IsClosedImmersion.of_comp _ G'.hom
  have h1 : (1 : Over.mk x ⟶ G').left = x ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left := rfl
  have lift_closed : ∀ {N B : Scheme.{0}} (u : Sp k ⟶ B) (ν : N ⟶ B) [IsClosedImmersion ν],
      Set.range u ⊆ Set.range ν → ∃ l : Sp k ⟶ N, l ≫ ν = u := fun u ν _ h => by
    have hs : Surjective (pullback.snd ν u) := ⟨by
      rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
      exact Set.eq_univ_of_forall fun t => h ⟨t, rfl⟩⟩
    have : IsIso (pullback.snd ν u) := isIso_of_isClosedImmersion_of_surjective _
    exact ⟨inv (pullback.snd ν u) ≫ pullback.fst ν u, by
      rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩
  constructor
  · rintro h _ ⟨w, rfl⟩
    refine ⟨x w, ?_⟩
    have := congrArg (fun f : Over.mk x ⟶ G' => f.left w) h
    simp only [h1, Over.comp_left, Scheme.Hom.comp_apply] at this
    exact this.symm
  · intro h
    obtain ⟨t, ht⟩ := lift_closed (z.left ≫ ψ.left) (η[G'] : 𝟙_ (Over S) ⟶ G').left (by
      rintro _ ⟨w, rfl⟩
      exact h ⟨w, rfl⟩)
    have ht' : t = x := by
      have := Over.w (z ≫ ψ)
      rw [Over.comp_left, ← ht, Category.assoc, hw] at this
      exact (Category.comp_id _).symm.trans this
    exact Over.OverMorphism.ext (by rw [h1, Over.comp_left, ← ht, ht'])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem map_bar_map_bar (I : Ideal (𝓞 E)) :
    (I.map (H.bar : 𝓞 E →+* 𝓞 E)).map (H.bar : 𝓞 E →+* 𝓞 E) = I := by
  have : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ := by
    refine RingHom.ext fun a => RingOfIntegers.ext ?_
    change ((H.bar (H.bar a) : 𝓞 E) : E) = a
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  rw [Ideal.map_map, this, Ideal.map_id]

theorem absNorm_map_bar (I : Ideal (𝓞 E)) : Ideal.absNorm (I.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I _ H.bar rfl).toEquiv).symm

theorem mem_tors_mul (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (I J : Ideal (𝓞 E))
    (h : ∀ a ∈ I, x ≫ t.act.act a ∈ t.tors T J) : x ∈ t.tors T (I * J) := fun c hc =>
  Submodule.mul_induction_on hc
    (fun a ha b hb => by rw [t.act.mul, ← Category.assoc]; exact h a ha b hb)
    (fun a b ha hb => by rw [t.act.add, MonObj.comp_mul, ha, hb, _root_.one_mul])

theorem card_pow_ker {s : S ⟶ Sp (KA l)} (o : Ob D l s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
    {n : ℕ} (hn : 0 < n) : Nat.card (o.t.tors (Over.mk x) (Ideal.span {(n : 𝓞 E)})) =
      n ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) :=
  (heckeKer_zero o k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage (x ≫ s)).symm ⊤ n hn).2.2.2.2.1

end GlobalTheory.HeckeDual

namespace GlobalTheory

open HeckeDual HeckeKerModel

theorem isHecke_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o o' : Ob D l s) (ψ : o.t.G ⟶ o'.t.G) (ψ' : o'.t.G ⟶ o.t.G), admitted l 𝔓 p → IsHecke o o' 𝔓 p i ψ → IsIsog o' o p ψ' → ψ ≫ ψ' = 𝟙 o.t.G ^ p ^ 2 → IsHecke o' o (𝔓.map (H.bar : 𝓞 E →+* 𝓞 E)) p i ψ' := by
  rintro E _ _ _ H D l P p i S s o o' ψ ψ' ⟨-, -, hp, hpP, -⟩ ⟨⟨⟨hm, hfin, -, hsurj, hlin, hLB⟩, -⟩, K, hK, hH⟩ h' hψ
  have hpr := o.proper
  have hm' := h'.1.1
  have hlin' := h'.1.2.2.2.2.1
  refine ⟨h', _, kerSet_unit ψ', fun k _ _ x => ?_⟩
  obtain ⟨C, hC, c1, c2, c3, -, c5, c6⟩ := hH k x
  let f : (Over.mk x ⟶ o.t.G) →* (Over.mk x ⟶ o'.t.G) := MonoidHom.mk' (· ≫ ψ) fun a b => MonObj.mul_comp a b ψ
  let g : (Over.mk x ⟶ o'.t.G) →* (Over.mk x ⟶ o.t.G) := MonoidHom.mk' (· ≫ ψ') fun a b => MonObj.mul_comp a b ψ'
  have hCf : C = f.ker := Subgroup.ext fun z => (hC z).trans (hK k x z).symm
  subst hCf
  have hf : Function.Surjective f := fun y => exists_lift ψ x y
  have hg : ∀ z, g (f z) = z ^ p ^ 2 := fun z => by
    change (z ≫ ψ) ≫ ψ' = _
    rw [Category.assoc, hψ, MonObj.comp_pow, Category.comp_id]
  have hfa : ∀ z a, f (z ≫ o.t.act.act a) = f z ≫ o'.t.act.act a := fun z a => by
    change (z ≫ _) ≫ ψ = (z ≫ ψ) ≫ _
    rw [Category.assoc, hlin, Category.assoc]
  have hp0 := hp.pos
  have hq0 : 0 < p ^ 2 := pow_pos hp0 2
  have hsq : Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)} = Ideal.span {(p : 𝓞 E)} * Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.span_singleton_mul_span_singleton, Nat.cast_pow, sq]
  obtain ⟨-, I, -⟩ := o.geom k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage (x ≫ s)).symm
  obtain ⟨-, I', -⟩ := o'.geom k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage (x ≫ s)).symm
  have tk : ∀ (u : Ob D l s) (n : ℕ), u.t.tors (Over.mk x) (Ideal.span {(n : 𝓞 E)}) =
      ((powMonoidHom n : (Over.mk x ⟶ u.t.G) →* (Over.mk x ⟶ u.t.G)).ker : Set _) := fun u n =>
    Set.ext fun z => mem_tors_span u.t z n
  obtain ⟨d5, d6⟩ := card_dual_ker f g p (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) hf hg
    (pow_ne_zero _ hp0.ne') (by have := card_pow_ker o k x hp0; rw [tk] at this; exact this)
    (by have := card_pow_ker o k x hq0; rw [tk, ← pow_mul, Nat.mul_comm, pow_mul] at this; exact this) c5
    (fun z hz => by
      obtain ⟨a, rfl⟩ := (I.onto p hp0 z).1 hz
      exact ⟨_, I.tower p p hp0 hp0 a⟩)
  refine ⟨g.ker, fun z => kerSet_unit ψ' k x z, fun y hy a => ?_, fun J hJ y hy => ?_, fun y hy a ha => ?_,
    fun y hy y' hy' => ?_, d5, ?_⟩
  · have := o.t.act.hom a
    change (y ≫ _) ≫ ψ' = 1
    rw [Category.assoc, hlin', ← Category.assoc, show y ≫ ψ' = 1 from hy]
    simp
  · obtain ⟨z, rfl⟩ := hf y
    have h1 := mem_tors_mul o.t z J _ fun a ha => c3 (show f _ = 1 from (hfa z a).trans (hy a ha))
    rw [mul_left_comm, hJ, ← hsq, mem_tors_span] at h1
    exact (hg z).trans h1
  · obtain ⟨z, rfl⟩ := hf y
    have hz : z ∈ o.t.tors (Over.mk x) (Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)}) :=
      (mem_tors_span o.t z _).2 ((hg z).symm.trans hy)
    rw [map_bar_map_bar] at ha
    obtain ⟨J, hJ⟩ : P ∣ Ideal.span {(p : 𝓞 E)} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hpP)
    rw [← hfa]
    refine c2 J (by rw [hJ, _root_.mul_comm]) fun b hb => ?_
    rw [Category.assoc, ← o.t.act.mul]
    refine hz _ ?_
    have := Ideal.mul_mem_mul ha hb
    rwa [_root_.mul_assoc, ← hJ, ← hsq] at this
  · obtain ⟨z, rfl⟩ := hf y
    obtain ⟨z', rfl⟩ := hf y'
    have hz : z ^ p ^ 2 = 1 := (hg z).symm.trans hy
    have hz' : z' ^ p ^ 2 = 1 := (hg z').symm.trans hy'
    obtain ⟨a, ha⟩ := (I.onto _ hq0 z).1 hz
    obtain ⟨a', ha'⟩ := (I.onto _ hq0 z').1 hz'
    obtain ⟨b, hb⟩ := (I'.onto _ hq0 (f z)).1 (by rw [← map_pow, hz, map_one])
    obtain ⟨b', hb'⟩ := (I'.onto _ hq0 (f z')).1 (by rw [← map_pow, hz', map_one])
    have w := I.isom _ hq0 a a'
    have w' := I'.isom _ hq0 b b'
    rw [ha, ha'] at w
    rw [hb, hb'] at w'
    have e := (weilIs_along_hom firstFiveLaws.1.globalFns S _ _ ψ _ _ (p ^ 2) _ _ z z' _ _
      ⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩
      ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩ o.t.PP.isLB o'.t.PP.isLB hm hLB w').2 w
    have e1 : (unitOn (I.ζ (p ^ 2) ^ D.EF a a')) ^ p ^ 2 = 1 := by
      have h2 : (I.ζ (p ^ 2) ^ D.EF a a') ^ p ^ 2 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, _root_.mul_comm, zpow_mul, zpow_natCast, (I.ζ_prim _ hq0).pow_eq_one, one_zpow]
      exact (map_pow (Units.map _) _ _).symm.trans ((congrArg _ h2).trans (map_one _))
    have e2 : unitOn (I'.ζ (p ^ 2) ^ D.EF b b') = 1 := e.trans e1
    rw [e2] at w'
    exact_mod_cast w'
  · rw [absNorm_map_bar, card_pow_ker o' k x hp0, ← card_pow_ker o k x hp0, c6, tk, tk]
    exact congrArg (· * _) d6.symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmExistsClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

theorem cmExists_closed : CMExistsSt :=
  _root_.GlobalTheory.CM.ExObj.cmExists _root_.GlobalTheory.cmCurve_closed GlobalTheory.cmPoint_closed GlobalTheory.thetaUnifAV_closed
    GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    (GlobalTheory.CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional)
    GlobalTheory.kernelFiniteFlat_holds

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalWeilPairingEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors

theorem weilIs_of_cubWeil_of_proper {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (hpr : IsProper (pullback.snd G.hom f)) {L : RigLB G} (c : CubicalStr G L) (k : ℕ)
    (T : Over S') (x y : Over.mk (T.hom ≫ f) ⟶ G) (z : Γ(T.left, ⊤)ˣ) (h : GlobalTheory.UU.CubWeil c k x y z) :
    WeilIs G L.L (k : ℤ) x y z := by
  let G' : Over S' := (Over.pullback f).obj G
  have hp : IsGrpPullback G' G f (pullback.fst G.hom f) := isGrpPullback_pullback G f
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback f G hG
  have := hG'.comm
  have hA : IsAbelianScheme G' := ⟨hG'.comm, hG'.smooth, hpr, hG'.geomConnected⟩
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := CubePf.cubePull _ _ G G' (cubeMapOf hp) L c
  have hw : pullback.fst G.hom f ≫ G.hom = G'.hom ≫ f := pullback.condition
  let β := GlobalTheory.UU.toBaseHom (GlobalTheory.UU.toBase_mul_pullback G f) T
  have inj : Function.Injective β := fun a b e =>
    Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w a).trans (Over.w b).symm))
  have sur : Function.Surjective β := fun p =>
    ⟨Over.homMk (hp.1.lift p.left T.hom (Over.w p)) (hp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩
  obtain ⟨u, rfl⟩ := sur x
  obtain ⟨v, rfl⟩ := sur y
  have hu : u ^ k = 1 := inj (by rw [map_pow, map_one]; exact h.1)
  have hv : v ^ k = 1 := inj (by rw [map_pow, map_one]; exact h.2.1)
  obtain ⟨z', hz', -⟩ := GlobalTheory.UU.existsUnique_cubWeil c' hu hv
  have h₁ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f G G' (cubeMapOf hp) hw (GlobalTheory.UU.toBase_mul_pullback G f) L _ c c' hc'
    k T u v z' hz'
  obtain rfl : z = z' := h.unique h₁
  have h₂ := (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.SemiRigid.globalFns hA hu hv z).1 hz'
  exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ G G' f _ L.L _ L.isLB hL hp
    ⟨GlobalTheory.UU.pullIso _ _, GlobalTheory.UU.pullIso_isGen L.isLB _⟩ T k u v (β u) (β v) z rfl rfl).1 h₂

end GlobalTheory.FlatTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DescendToThetaConstantField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem descend_to_theta_field : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (K₀ K : Type) [Field K₀] [Field K] [IsAlgClosed K] (β : o →+* K₀) (e : K₀ →+* K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s) (v : Ix g ((n ^ j) ^ 2) → K₀), s = spMap e ≫ spMap β → t.Shape Mat κ → t.Prim w w' → t.HasTh (𝟙 _) (fun a => e (v a)) → ∃ t₀ : TObj g ((n ^ j) ^ 2) J b (spMap β), TMap t t₀ (spMap e) ∧ t₀.Shape Mat κ ∧ t₀.Prim w w' ∧ t₀.HasTh (𝟙 _) v := by
  intro hL hL2 g J _ Mat κ n w w' hn hodd
  obtain ⟨j₀, hj₀⟩ := _root_.GlobalTheory.ZM.exists_tObj_of_veryDense hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b K₀ K _ _ _ β e s t v hs hsh hpr hth => ?_⟩
  subst hs

  have hdense : VeryDense (objPrimes b Mat κ β v) := by
    intro q f hq hf
    have hq0 : q = ⊥ := (Ideal.eq_bot_or_top q).resolve_right hq.ne_top
    have hker : RingHom.ker e = q := by
      rw [hq0]; exact (RingHom.injective_iff_ker_eq_bot e).mp e.injective
    exact ⟨q, ⟨K, inferInstance, inferInstance, e, t, hker, hsh, hth⟩, hq, le_rfl, hf⟩
  obtain ⟨t₀, hth₀, hu⟩ := hj₀ j hj o b K₀ β v hdense

  have hmap : TMap t t₀ (spMap e) := hu K e t hsh hth
  obtain ⟨-, -, hdesc⟩ := GlobalTheory.shape_prim_pull_and_descend o g ((n ^ j) ^ 2) J b Mat κ w w' _ _ _ _ _ t₀ t hmap
  obtain ⟨hS, hP⟩ := hdesc K₀ rfl inferInstance inferInstance
  exact ⟨t₀, hmap, hS hsh, hP inferInstance hpr, hth₀⟩

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory

namespace SectionQuot

open PointQuot

variable {S : Scheme.{0}}

lemma exists_geomPt (Z : Over S) (z : Z.left) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (t : Sp k ⟶ S), Nonempty (Over.mk t ⟶ Z) := by
  let k := AlgebraicClosure (Z.left.residueField z)
  let p : Sp k ⟶ Z.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.left.residueField z) k)) ≫
      Z.left.fromSpecResidueField z
  exact ⟨k, inferInstance, inferInstance, p ≫ Z.hom, ⟨Over.homMk p rfl⟩⟩

lemma mono_constDesc_of_geom {I : Type} {A : Over S} (x : I → (𝟙_ (Over S) ⟶ A))
    (hx : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (c d : I),
      toUnit (Over.mk t) ≫ x c = toUnit (Over.mk t) ≫ x d → c = d) : Mono (constDesc x) := by
  refine ⟨fun {Z} f g h => hom_ext_local f g fun z => ?_⟩
  obtain ⟨V, hV, c, hc⟩ := locally_const f z
  obtain ⟨W, hW, d, hd⟩ := locally_const g z
  have hc' := const_of_le (inf_le_left : V ⊓ W ≤ V) hc
  have hd' := const_of_le (inf_le_right : V ⊓ W ≤ W) hd
  obtain ⟨k, _, _, t, ⟨p⟩⟩ :=
    exists_geomPt (openObj Z (V ⊓ W)) (⟨z, hV, hW⟩ : (V ⊓ W : Z.left.Opens))
  obtain rfl : c = d := by
    apply hx k t
    rw [toUnit_unique (toUnit _) (p ≫ toUnit _), Category.assoc, Category.assoc,
      ← constPt_desc x c, ← constPt_desc x d, ← reassoc_of% hc', ← reassoc_of% hd', h]
  exact ⟨V ⊓ W, ⟨hV, hW⟩, hc'.trans hd'.symm⟩

end SectionQuot


open PointQuot SectionQuot in
theorem exists_quotient_by_finite_group_of_sections :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over (Sp R)) ⟶ P.A)), (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (c : C), toUnit (Over.mk t) ≫ i c = 1 → c = 1) → ∃ (B : Over (Sp R)) (_ : GrpObj B) (ψ : P.A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ c, i c ≫ ψ = 1) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (x : Over.mk t ⟶ P.A), x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ i c := by
  open SectionQuot PointQuot in
    intro R _ _ P C _ _ i hi
    have L : Out.Laws := GlobalTheory.firstFiveLaws.1
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin C
    let x : Fin n → (𝟙_ (Over (Sp R)) ⟶ P.A) := fun c => i (e.symm c)
    have hr : Set.range x = i.range := by
      ext y
      exact ⟨by rintro ⟨c, rfl⟩; exact ⟨e.symm c, rfl⟩,
        by rintro ⟨c, rfl⟩; exact ⟨e c, by simp [x]⟩⟩
    have hmono : Mono (constDesc x) := mono_constDesc_of_geom x fun k _ _ t c d h => by
      apply e.symm.injective
      rw [← div_eq_one]
      apply hi k t
      rw [map_div, GrpObj.comp_div, div_eq_one]
      exact h
    obtain ⟨_, hhom⟩ := exists_grpObj_constObj x i.range hr
    have hs : FinEt.IsSplitOfRank (constObj (Sp R) (Fin n)).hom n :=
      (FinEt.isSplitOfRank_iff_exists_iso _ _).mpr ⟨Iso.refl _, Category.id_comp _⟩
    have het := hs.etale
    obtain ⟨B, _, hB, q, hq, hfin, hflat, hsurj, hker⟩ :=
      L.quotient R P (constObj (Sp R) (Fin n)) (constDesc x) hhom hmono hs.isFinite inferInstance
    have hw : constDesc x ≫ q = 1 := hker.w
    have hkill : ∀ c, i c ≫ q = 1 := fun c => by
      have : i c = x (e c) := by simp [x]
      rw [this, ← constPt_desc x (e c), Category.assoc, hw, MonObj.comp_one]
    refine ⟨B, inferInstance, q, hB, hq, hfin, ?_, hsurj, hkill,
      fun k _ _ t y => ⟨fun hy => ?_, ?_⟩⟩
    · refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
        ((H1.torsor_pullback (constDesc x) q hker).map (Over.forget _)).flip
        ⟨⟨hsurj, hflat⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
      exact MorphismProperty.of_isPullback (P := @Etale) (IsPullback.of_hasPullback _ _) het
    · obtain ⟨z⟩ : Nonempty (Over.mk t).left := inferInstanceAs (Nonempty (PrimeSpectrum k))
      have : Subsingleton (Over.mk t).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
      obtain ⟨V, hV, c, hc⟩ := locally_const_desc x (hker.lift y (toUnit _) hy) z
      rw [hker.lift_fst] at hc
      refine ⟨e.symm c, hom_ext_local _ _ fun z' => ⟨V, Subsingleton.elim z z' ▸ hV, ?_⟩⟩
      rw [hc, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    · rintro ⟨c, rfl⟩
      rw [Category.assoc, hkill, MonObj.comp_one]

end GlobalTheory
end
end

