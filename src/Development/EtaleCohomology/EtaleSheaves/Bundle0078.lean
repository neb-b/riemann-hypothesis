module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0075
public import Development.EtaleCohomology.EtaleSheaves.Bundle0073
public import Development.EtaleCohomology.EtaleSheaves.Bundle0063
public import Development.EtaleCohomology.EtaleSheaves.Bundle0074

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTw0TwFreeOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0TwFreePf

def aug (q : ℕ) (A : CommRingCat.{0}) : (twF q 0).obj A →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Submodule.liftQ (twRel q 0 A) (Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun _ => (1 : ULift.{1} (ZMod q)))) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, _, rfl⟩
    simp [SetLike.mem_coe, LinearMap.mem_ker, Finsupp.linearCombination_single]
    exact sub_self (1 : ULift.{1} (ZMod q)))

theorem aug_mk (q : ℕ) (A : CommRingCat.{0}) (ζ : Prim q A) :
    aug q A (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  show Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun _ => (1 : ULift.{1} (ZMod q))) (Finsupp.single ζ 1) = 1
  rw [Finsupp.linearCombination_single, one_smul]

theorem aug_map (q : ℕ) (A B : CommRingCat.{0}) (g : A ⟶ B) (ζ : Prim q A) :
    aug q B (((twF q 0).map g).hom (Submodule.Quotient.mk (Finsupp.single ζ 1))) = 1 := by
  show aug q B (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.hom) (Finsupp.single ζ 1))) = 1
  rw [Finsupp.mapDomain_single]
  exact aug_mk q B _

theorem LeafTw0TwFree_of : LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0TwFree := by
  intro q _ V ζ
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q 0
  let x : P.obj (op V) := (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q 0).obj Γ(V, ⊤))
  let φ := ((toSheafify Scheme.etaleTopology P).app (op V)).hom
  by_cases hS : ∃ (c : ULift.{1} (ZMod q)), c • twGen 0 ζ = 0 ∧ c ≠ 0
  · obtain ⟨c, hc, hc0⟩ := hS
    have heq : φ (c • x) = φ 0 := by
      rw [φ.map_smul, φ.map_zero]; exact hc
    have hmem := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c • x) 0 heq
    by_cases hne : ∃ (U : Scheme.{0}) (f : U ⟶ V), (Presheaf.equalizerSieve (F := P) (X := op V) (c • x) 0).arrows f
    · exfalso
      obtain ⟨U, f, hf⟩ := hne
      apply hc0
      have h1 : (P.map f.op).hom (c • x) = (P.map f.op).hom 0 := hf
      rw [(P.map f.op).hom.map_smul, (P.map f.op).hom.map_zero] at h1
      let y : (twF q 0).obj Γ(U, ⊤) := ((twF q 0).map (Scheme.Γ.map f.op)).hom (Submodule.Quotient.mk (Finsupp.single ζ 1))
      have h3 : aug q Γ(U, ⊤) y = 1 := aug_map q _ _ _ ζ
      have h4 : aug q Γ(U, ⊤) (c • y) = c • aug q Γ(U, ⊤) y := (aug q _).map_smul c y
      have h5 : c • y = 0 := h1
      rw [h5, h3, map_zero, smul_eq_mul, mul_one] at h4
      exact h4.symm
    · left
      push Not at hne
      exact (tw q 0).isSeparated V _ hmem _ _ (fun U f hf => absurd hf (hne U f))
  · right
    intro c hc
    by_contra h0
    exact hS ⟨c, hc, h0⟩

end LateralTheory.E.LeafTw0TwFreePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpecSubalgebraPullbackLiftIsClosedImmersion
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

theorem prod_surj {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
    (hA : A ≤ D) (hB : B ≤ D) (hD : D ≤ Algebra.adjoin Ω ((A : Set L) ∪ B)) :
    Function.Surjective (Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)) := by
  intro x
  have hx : (x : L) ∈ (Algebra.TensorProduct.productMap A.val B.val).range := by
    rw [Algebra.TensorProduct.productMap_range, A.range_val, B.range_val]
    have := hD x.2
    rwa [Algebra.adjoin_union, Algebra.adjoin_eq, Algebra.adjoin_eq] at this
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, Subtype.ext ?_⟩
  rw [← hy]
  have e : D.val.comp (Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)) =
      Algebra.TensorProduct.productMap A.val B.val := by
    ext <;> rfl
  exact congrArg (fun φ : _ →ₐ[Ω] L => φ y) e

theorem spec_subalgebra_pullback_lift_is_closed_immersion : LeafSpecGenClosed := by
  intro Ω L _ _ _ A B D hA hB hD
  let φ := Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)
  have e : pullback.lift _ _ (spec_w A B D hA hB) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullbackSpecIso Ω A B).inv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      congr 1
      ext a; simp [φ]
    · rw [pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1
      ext a; simp [φ]
  rw [e]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (prod_surj A B D hA hB hD)
  infer_instance

end LateralTheory.E.GluedCurveChartOverlaps
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpreadingOutQuasiFiniteness
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutQuasiFiniteness

def LeafSpreadSmooth1 : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → SmoothOfRelativeDimension 1 q'

def LeafSpreadLQFMap : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {CA CB A B : Scheme.{0}} (cB : CB ⟶ Sp Ω) (γ : CA ⟶ CB) (qB : B ⟶ Sp R) (g : A ⟶ B) (vA : CA ⟶ A)
    (vB : CB ⟶ B), (LocallyOfFinitePresentation qB ∧ QuasiCompact qB ∧ QuasiSeparated qB) →
    (LocallyOfFinitePresentation (g ≫ qB) ∧ QuasiCompact (g ≫ qB) ∧ QuasiSeparated (g ≫ qB)) →
    IsPullback vB cB qB (toR R) → IsPullback vA (γ ≫ cB) (g ≫ qB) (toR R) → γ ≫ vB = vA ≫ g →
    LocallyQuasiFinite γ →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (EA EB : Scheme.{0})
      (qB' : EB ⟶ Sp R') (h : EA ⟶ EB) (rA : EA ⟶ A) (rB : EB ⟶ B), IsPullback rB qB' qB (incl hR) →
      IsPullback rA (h ≫ qB') (g ≫ qB) (incl hR) → h ≫ rB = rA ≫ g → LocallyQuasiFinite h

def LeafSpreadLQFGraph : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R)
    (v0 : C0 ⟶ D0) (f : D0 ⟶ X) (e : C0 ⟶ X) (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → IsPullback v0 c0 q (toR R) → v0 ≫ f = e →
    LocallyQuasiFinite (pullback.lift c0 e he.symm) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E0 : Scheme.{0})
      (q' : E0 ⟶ Sp R') (r : E0 ⟶ D0), IsPullback r q' q (incl hR) →
      ∀ (hf' : (r ≫ f) ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))),
        LocallyQuasiFinite (pullback.lift q' (r ≫ f) hf'.symm)

def LeafBaseChangePreR : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R R' : Subalgebra k Ω)
    (hR : R ≤ R') {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
    LateralTheory.E.LeafDescendChainPf.PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 →
    ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1)
      (w2 : C2 ⟶ E2) (r0 : E0 ⟶ D0) (r1 : E1 ⟶ D1) (r2 : E2 ⟶ D2),
      (IsPullback w0 c0 q' (toR R') ∧ IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧
        IsPullback w2 (γ2 ≫ γ1 ≫ c0) (e2 ≫ e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1 ∧ γ2 ≫ w1 = w2 ≫ e2) ∧
      IsPullback r0 q' q (incl hR) ∧ IsPullback r1 (e1 ≫ q') (d1 ≫ q) (incl hR) ∧
      IsPullback r2 (e2 ≫ e1 ≫ q') (d2 ≫ d1 ≫ q) (incl hR) ∧
      w0 ≫ r0 = v0 ∧ e1 ≫ r0 = r1 ≫ d1 ∧ e2 ≫ r1 = r2 ≫ d2

theorem incl_toK {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    incl hR ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k R')) := by
  rw [← Spec.map_comp]; rfl

theorem LeafSpreadQF_of (hSep : LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated) (hSm : LeafSpreadSmooth1)
    (hG : LeafSpreadLQFGraph) (hM : LeafSpreadLQFMap) (hB : LeafBaseChangePreR) :
    LateralTheory.E.QuasiFiniteDescent.LeafSpreadQF := by
  intro k _ X p _ Ω _ _ R hR C0 C1 C2 c0 γ1 γ2 e he hc0 h1 h2 qf0 qf1 qf2 D0 D1 D2 q d1 d2 f v0 v1 v2 hf hpre hve
  obtain ⟨f0, f1, f2, p0, p1, p2, m1, m2⟩ := id hpre
  obtain ⟨S0, a0, g0, H0⟩ := hSep k Ω R hR c0 q v0 f0 hc0.2.1.toIsSeparated p0
  obtain ⟨S1, a1, g1, H1⟩ := hSep k Ω R hR (γ1 ≫ c0) (d1 ≫ q) v1 f1 h1.2.1.toIsSeparated p1
  obtain ⟨S2, a2, g2, H2⟩ := hSep k Ω R hR (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) v2 f2 h2.2.1.toIsSeparated p2
  obtain ⟨T0, b0, k0, K0⟩ := hSm k Ω R hR c0 q v0 f0 hc0.2.2 p0
  obtain ⟨T1, b1, k1, K1⟩ := hSm k Ω R hR (γ1 ≫ c0) (d1 ≫ q) v1 f1 h1.2.2 p1
  obtain ⟨T2, b2, k2, K2⟩ := hSm k Ω R hR (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) v2 f2 h2.2.2 p2
  obtain ⟨G, aG, gG, HG⟩ := hG k p Ω R hR c0 q v0 f e he hf f0 p0 hve qf0
  obtain ⟨M1, aM1, gM1, HM1⟩ := hM k Ω R hR c0 γ1 q d1 v1 v0 f0 f1 p0 p1 m1 qf1
  obtain ⟨M2, aM2, gM2, HM2⟩ := hM k Ω R hR (γ1 ≫ c0) γ2 (d1 ≫ q) d2 v2 v1 f1 f2 p1 p2 m2 qf2
  let T := S0 ⊔ S1 ⊔ S2 ⊔ T0 ⊔ T1 ⊔ T2 ⊔ G ⊔ M1 ⊔ M2
  have gT : T.FG := ((((((((g0.sup g1).sup g2).sup k0).sup k1).sup k2).sup gG).sup gM1).sup gM2)
  have lS0 : S0 ≤ T := (((((((le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have literatureStatementsS1 : S1 ≤ T := (((((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have logSupBoundLevelFree : S2 ≤ T := ((((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT0 : T0 ≤ T := (((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT1 : T1 ≤ T := ((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT2 : T2 ≤ T := (((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lG : G ≤ T := ((le_sup_right).trans le_sup_left).trans le_sup_left
  have familyMassFirstBound : M1 ≤ T := (le_sup_right).trans le_sup_left
  have familyMassSecondBound : M2 ≤ T := le_sup_right
  have hRT : R ≤ T := a0.trans lS0
  obtain ⟨E0, E1, E2, q', e1, e2, w0, w1, w2, r0, r1, r2, ⟨P0, P1, P2, c1, c2⟩, Q0, Q1, Q2, n0, n1, n2⟩ :=
    hB k Ω R T hRT c0 γ1 γ2 q d1 d2 v0 v1 v2 hpre
  have hf' : (r0 ≫ f) ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k T)) := by
    rw [Category.assoc, hf, ← Category.assoc, Q0.w, Category.assoc, incl_toK]
  haveI := f0.2.1; haveI := f1.2.1; haveI := f2.2.1
  refine ⟨T, gT, E0, E1, E2, q', e1, e2, r0 ≫ f, w0, w1, w2, hf', ?_⟩
  exact ⟨H0 T lS0 hRT E0 q' r0 Q0, MorphismProperty.of_isPullback (P := @QuasiCompact) Q0 inferInstance,
    K0 T lT0 hRT E0 q' r0 Q0,
    H1 T literatureStatementsS1 hRT E1 (e1 ≫ q') r1 Q1, MorphismProperty.of_isPullback (P := @QuasiCompact) Q1 inferInstance,
    K1 T lT1 hRT E1 (e1 ≫ q') r1 Q1,
    H2 T logSupBoundLevelFree hRT E2 (e2 ≫ e1 ≫ q') r2 Q2, MorphismProperty.of_isPullback (P := @QuasiCompact) Q2 inferInstance,
    K2 T lT2 hRT E2 (e2 ≫ e1 ≫ q') r2 Q2,
    HG T lG hRT E0 q' r0 Q0 hf', HM1 T familyMassFirstBound hRT E1 E0 q' e1 r1 r0 Q0 Q1 n1,
    HM2 T familyMassSecondBound hRT E2 E1 (e1 ≫ q') e2 r2 r1 Q1 Q2 n2, P0, P1, P2, c1, c2,
    by rw [← Category.assoc, n0, hve]⟩

end LateralTheory.E.SpreadingOutQuasiFiniteness

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StrictHenselianLocalization
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf LateralTheory.E.LeafSHPtPf

namespace LateralTheory.E.StrictHenselianLocalization
open LateralTheory.E.StrictHenselianNeighbourhood

lemma isUnit_of_forall_prime {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (y : R)
    (h : ∀ p : PrimeSpectrum S, ψ y ∉ p.asIdeal) : IsUnit (ψ y) := by
  by_contra hu
  obtain ⟨M, hM, hyM⟩ := exists_max_ideal_of_mem_nonunits hu
  exact h ⟨M, hM.isPrime⟩ hyM

theorem key {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
    (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
    (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left) (hP : IsPtNb U x Ω s D c V a l e t)
    (j : J) (y : D.obj j) (hy : (Spec.preimage (l j)).hom y ≠ 0) :
    ∃ (n : J) (f : j ⟶ n), IsUnit (D.map f y) := by
  obtain ⟨-, he, hl, hcomp, -, hlc, hcof, heq⟩ := hP
  have _ : ∀ j, IsIso (e j) := he
  let O : (Sp (D.obj j)).Opens := PrimeSpectrum.basicOpen y
  have hrange : Set.range (l j).base ⊆ Set.range O.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    have := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [← Spec.map_preimage (l j)]
    show y ∉ Ideal.comap (Spec.preimage (l j)).hom q.asIdeal
    rw [hq, Ideal.mem_comap, Ideal.mem_bot]
    exact hy
  have : Etale (V j).hom := (V j).prop
  let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ e j ≫ (V j).hom) (by
    show Etale (O.ι ≫ e j ≫ (V j).hom); infer_instance)
  let b : U' ⟶ U := MorphismProperty.Over.homMk (O.ι ≫ e j ≫ (a j).left) (by
    have hw : (a j).left ≫ U.hom = (V j).hom := MorphismProperty.Over.w (a j)
    show _ = O.ι ≫ e j ≫ (V j).hom
    exact (Category.assoc _ _ _).trans (congrArg (O.ι ≫ ·) ((Category.assoc _ _ _).trans (congrArg (e j ≫ ·) hw)))) trivial
  have hOI : IsOpenImmersion O.ι := inferInstance
  let l' := IsOpenImmersion.lift O.ι (l j) hrange
  have hl' : l' ≫ O.ι = l j := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨k, g, hg', hlg'⟩ : ∃ (k : J) (g : (V k).left ⟶ (O : Scheme)),
      g ≫ O.ι ≫ e j ≫ (a j).left = (a k).left ∧ l k ≫ e k ≫ g = l' := by
    obtain ⟨k, g, hg, hlg⟩ := hcof U' b l' (by
      show l' ≫ (O.ι ≫ e j ≫ (a j).left) = s
      rw [← Category.assoc, hl', hl j])
    exact ⟨k, g, hg, hlg⟩
  clear_value b U' l'
  let m := IsFiltered.max j k
  let f1 : j ⟶ m := IsFiltered.leftToMax j k
  let f2 : k ⟶ m := IsFiltered.rightToMax j k
  have h1 := hlc j m f1
  have h2 := hlc k m f2
  obtain ⟨n, f3, h3⟩ := heq (V j) (a j) m
    (inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map f1).hom) ≫ e j)
    (inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map f2).hom) ≫ e k ≫ g ≫ O.ι ≫ e j)
    (by simp only [Category.assoc]; rw [hcomp j m f1, IsIso.inv_hom_id_assoc])
    (by simp only [Category.assoc]; rw [hg', hcomp k m f2, IsIso.inv_hom_id_assoc])
    (by
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% hlg', reassoc_of% hl'])
  simp only [IsIso.hom_inv_id_assoc] at h3
  have hfac : Spec.map (CommRingCat.ofHom (D.map f3).hom) ≫ Spec.map (CommRingCat.ofHom (D.map f1).hom) =
      (Spec.map (CommRingCat.ofHom (D.map f3).hom) ≫ Spec.map (CommRingCat.ofHom (D.map f2).hom) ≫ e k ≫ g) ≫ O.ι := by
    rw [← cancel_mono (e j)]
    simpa only [Category.assoc] using h3
  refine ⟨n, f1 ≫ f3, ?_⟩
  rw [D.map_comp, CommRingCat.comp_apply]
  apply isUnit_of_forall_prime (D.map f3).hom
  intro p
  have hp : (Spec.map (CommRingCat.ofHom (D.map f3).hom) ≫ Spec.map (CommRingCat.ofHom (D.map f1).hom)).base p ∈
      Set.range O.ι.base := by
    rw [hfac]; exact ⟨_, rfl⟩
  rw [Scheme.Opens.range_ι] at hp
  exact hp

theorem LeafSHLoc_of : LeafSHLoc := by
  intro B U x Ω _ _ s J _ _ D c hc V a l e t hP
  have hunit : ∀ (j : J) (y : D.obj j), (Spec.preimage (l j)).hom y ≠ 0 → IsUnit (c.ι.app j y) := by
    intro j y hy
    obtain ⟨n, f, hf⟩ := key U x Ω s D c V a l e t hP j y hy
    have h : c.ι.app j y = c.ι.app n (D.map f y) := by
      rw [← c.w f]; rfl
    rw [h]; exact hf.map _
  have hrep : ∀ z : c.pt, ∃ (j : J) (y : D.obj j), c.ι.app j y = z := fun z =>
    Concrete.isColimit_exists_rep D hc z
  have : Nontrivial c.pt := by
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' : c.ι.app j 0 = c.ι.app j 1 := by rw [map_zero, map_one]; exact h
    obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc _ _ h'
    have := congrArg (Spec.preimage (l k)).hom hfg
    rw [map_zero, map_one, map_zero, map_one] at this
    exact zero_ne_one this
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨j, y, rfl⟩ := hrep z
  by_cases hy : (Spec.preimage (l j)).hom y = 0
  · right
    have h1 : (Spec.preimage (l j)).hom (1 - y) ≠ 0 := by
      rw [map_sub, map_one, hy, sub_zero]; exact one_ne_zero
    have := hunit j (1 - y) h1
    rwa [map_sub, map_one] at this
  · left; exact hunit j y hy

end LateralTheory.E.StrictHenselianLocalization
end

