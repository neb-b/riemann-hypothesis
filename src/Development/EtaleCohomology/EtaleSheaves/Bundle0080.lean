module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0076
public import Development.EtaleCohomology.EtaleSheaves.Bundle0078

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTw0LocGenOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPf
open LateralTheory.E.LeafTw0LocGenPfA LateralTheory.E.LeafTw0LocGenPfB

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => h V g⟩

theorem loc_finset {ι : Type*} [DecidableEq ι] {U : Scheme.{0}} (s : Finset ι)
    {P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ i ∈ s, Loc U (P i)) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  induction s using Finset.induction_on with
  | empty => exact loc_top fun _ _ i hi => by simp at hi
  | insert j s hj ih =>
    obtain ⟨S0, h0, hP0⟩ := h j (Finset.mem_insert_self j s)
    obtain ⟨S1, h1, hP1⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨S0 ⊓ S1, Scheme.etaleTopology.intersection_covering h0 h1, fun V g hg i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hP0 V g hg.1
    · exact hP1 V g hg.2 i hi

theorem res_sec {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {W V : Scheme.{0}}
    (g : W ⟶ V) (x : M.obj Γ(V, ⊤)) :
    Sec.res g (ofRings.sec M V x) = ofRings.sec M W ((M.map g.appTop).hom x) := by
  have := congrArg (fun f => f.hom x) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  exact this.symm

theorem relq {q : ℕ} {A : CommRingCat.{0}} (ζ ξ : Prim q A) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 A) =
      Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  rw [Submodule.Quotient.eq]
  refine Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩
  simp
  rfl

theorem mk_mapDomain {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (r : Prim q A →₀ ULift.{1} (ZMod q))
    (ζ0 : Prim q A)
    (hrel : ∀ ξ ∈ r.support, (Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ξ) 1) :
      (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 B) = Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ζ0) 1)) :
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) r) : (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 B) =
      (r.sum fun _ c => c) • Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ζ0) 1) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Submodule.mkQ_apply, Finsupp.mapDomain, Finsupp.sum, map_sum, Finsupp.sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun ξ hξ => ?_
  rw [← hrel ξ hξ, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Finsupp.smul_single_one]

theorem LeafTw0LocGen_of : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocGen := by
  classical
  intro q _ U n a
  have hA : ∀ k, Loc U fun V g => ∃ t : (twF q 0).obj Γ(V, ⊤), ofRings.sec (twF q 0) V t = Sec.res g (a k) := by
    intro k
    exact ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) (U := op U) (a k), fun V g hg => hg⟩
  have hA' := loc_finset (U := U) Finset.univ (fun k _ => hA k)
  refine LateralTheory.E.LeafTensMonoPf.loc_trans hA' fun V g hg => ?_
  choose t ht using fun k => hg k (Finset.mem_univ k)
  let r : Fin n → (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) := fun k =>
    (Submodule.Quotient.mk_surjective _ (t k : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤))).choose
  have hr : ∀ k, (Submodule.Quotient.mk (r k) : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤)) = t k :=
    fun k => (Submodule.Quotient.mk_surjective _ (t k : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤))).choose_spec
  rcases isEmpty_or_nonempty (Prim q Γ(V, ⊤)) with hE | ⟨⟨ζ0⟩⟩
  · refine loc_top fun W h => ⟨0, fun _ => 0, fun k => ?_, Or.inl rfl⟩
    rw [zero_smul, LateralTheory.E.LeafTensMonoPf.res_comp, ← ht k, ← hr k, Subsingleton.elim (r k) 0,
      Submodule.Quotient.mk_zero]
    unfold ofRings.sec
    have h0 := map_zero (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app (op V)).hom)
    first
      | exact (congrArg (Sec.res h) h0).trans (map_zero _)
      | (erw [h0]; exact map_zero _)
  · obtain ⟨S, hS, hP⟩ := loc_finset (U := V) (Finset.univ.biUnion fun k => (r k).support) (fun ξ _ => geo V ζ0 ξ)
    refine ⟨S, hS, fun W h hh => ?_⟩
    have hrel := hP W h hh
    refine ⟨twGen 0 (Prim.map h.appTop.hom ζ0), fun k => (r k).sum fun _ c => c, fun k => ?_, Or.inr ⟨_, rfl⟩⟩
    rw [LateralTheory.E.LeafTensMonoPf.res_comp, ← ht k, ← hr k]
    refine (res_sec (twF q 0) h _).trans ?_
    have e1 : ((twF q 0).map h.appTop).hom (Submodule.Quotient.mk (r k)) =
        Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map h.appTop.hom) (r k)) := rfl
    rw [e1, mk_mapDomain h.appTop (r k) ζ0 (fun ξ hξ => ?_)]
    · exact map_smul _ _ _
    · obtain ⟨b, hb⟩ := hrel ξ (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, hξ⟩)
      exact relq _ _ b hb

end LateralTheory.E.LeafTw0LocGenPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpreadingOutLocallyQuasiFinite
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutLocallyQuasiFinite

def LeafQFAtBaseChange : Prop := ∀ {EA EB A B : Scheme.{0}} (h : EA ⟶ EB) (g : A ⟶ B) (rA : EA ⟶ A) (rB : EB ⟶ B),
    IsPullback rA h g rB → LocallyOfFiniteType g → ∀ x : EA, g.QuasiFiniteAt (rA x) → h.QuasiFiniteAt x

def LeafQFAtDescend : Prop := ∀ {CA CB A B : Scheme.{0}} (γ : CA ⟶ CB) (g : A ⟶ B) (vA : CA ⟶ A) (vB : CB ⟶ B),
    IsPullback vA γ g vB → LocallyOfFiniteType g → ∀ x : CA, γ.QuasiFiniteAt x → g.QuasiFiniteAt (vA x)

def LeafOpenSpread : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C A : Scheme.{0}} (c : C ⟶ Sp Ω) (p : A ⟶ Sp R) (v : C ⟶ A) (U : A.Opens),
    (LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p) → IsPullback v c p (toR R) →
    (∀ x : C, v x ∈ U) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ A), IsPullback r q' p (incl hR) → ∀ z : E, r z ∈ U

theorem quasi_finite_at_base_change_of_finite_type : LeafQFAtBaseChange := by
  intro EA EB A B h g rA rB sq hg x hx
  let U := g.quasiFiniteLocus
  have sq2 : IsPullback (rA ∣_ U) ((rA ⁻¹ᵁ U).ι ≫ h) (U.ι ≫ g) rB :=
    (isPullback_morphismRestrict rA U).paste_vert sq
  have : LocallyQuasiFinite ((rA ⁻¹ᵁ U).ι ≫ h) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) sq2 inferInstance
  have hxV : x ∈ rA ⁻¹ᵁ U := hx
  have := ((rA ⁻¹ᵁ U).ι ≫ h).quasiFiniteAt ⟨x, hxV⟩
  have h2 := (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion (f := (rA ⁻¹ᵁ U).ι) (g := h)
    (x := ⟨x, hxV⟩)).mp this
  simpa using h2

theorem LeafSpreadLQFMap_of (hBC : LeafQFAtBaseChange) (hD : LeafQFAtDescend) (hO : LeafOpenSpread) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap := by
  intro k _ Ω _ _ R hR CA CB A B cB γ qB g vA vB hB hA pB pA hw hγ
  have : LocallyOfFinitePresentation (g ≫ qB) := hA.1
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g qB
  have sqC : IsPullback vA γ g vB := IsPullback.of_bot pA hw.symm pB
  have hU : ∀ x : CA, vA x ∈ g.quasiFiniteLocus := fun x =>
    hD γ g vA vB sqC inferInstance x (γ.quasiFiniteAt x)
  obtain ⟨S, hRS, hS, H⟩ := hO k Ω R hR (γ ≫ cB) (g ≫ qB) vA g.quasiFiniteLocus hA pA hU
  refine ⟨S, hRS, hS, ?_⟩
  intro R' hSR' hRR' EA EB qB' h rA rB QB QA hc
  have sqE : IsPullback rA h g rB := IsPullback.of_bot QA hc.symm QB
  have : LocallyOfFiniteType h :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sqE inferInstance
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  refine top_le_iff.mp fun z _ => ?_
  exact hBC h g rA rB sqE inferInstance z (H R' hSR' hRR' EA (h ≫ qB') rA QA z)

end LateralTheory.E.SpreadingOutLocallyQuasiFinite

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpreadingOutQuasiFinitenessBaseChange
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutQuasiFinitenessBaseChange

theorem toR_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    toR R' ≫ incl hR = toR R := by
  rw [← Spec.map_comp]; rfl

theorem sq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {c : C ⟶ Sp Ω} {q : D ⟶ Sp R} {v : C ⟶ D} (hv : IsPullback v c q (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hv.w)) c
      (pullback.snd q (incl hR)) (toR R') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl hR))
  rw [pullback.lift_fst, toR_incl]; exact hv

theorem spread_chain_base_change_to_larger_subalgebra : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafBaseChangePreR := by
  intro k _ Ω _ _ R R' hR C0 C1 C2 c0 γ1 γ2 D0 D1 D2 q d1 d2 v0 v1 v2 hpre
  obtain ⟨-, -, -, p0, p1, p2, m1, m2⟩ := hpre
  let e1 : pullback (d1 ≫ q) (incl hR) ⟶ pullback q (incl hR) :=
    pullback.lift (pullback.fst _ _ ≫ d1) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  let e2 : pullback (d2 ≫ d1 ≫ q) (incl hR) ⟶ pullback (d1 ≫ q) (incl hR) :=
    pullback.lift (pullback.fst _ _ ≫ d2) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  have t1 : e1 ≫ pullback.snd q (incl hR) = pullback.snd _ _ := pullback.lift_snd _ _ _
  have t2 : e2 ≫ pullback.snd (d1 ≫ q) (incl hR) = pullback.snd _ _ := pullback.lift_snd _ _ _
  have t12 : e2 ≫ e1 ≫ pullback.snd q (incl hR) = pullback.snd _ _ := by rw [t1, t2]
  have P0 := sq hR p0
  have P1 := sq hR p1
  have P2 := sq hR p2
  refine ⟨_, _, _, pullback.snd q (incl hR), e1, e2, _, pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (by rw [Category.assoc, toR_incl]; exact p1.w), pullback.lift v2 ((γ2 ≫ γ1 ≫ c0) ≫ toR R') (by rw [Category.assoc, toR_incl]; exact p2.w), pullback.fst _ _, pullback.fst _ _, pullback.fst _ _,
    ⟨P0, ?_, ?_, ?_, ?_⟩, IsPullback.of_hasPullback _ _, ?_, ?_, pullback.lift_fst _ _ _,
    pullback.lift_fst _ _ _, pullback.lift_fst _ _ _⟩
  · rw [t1]; exact P1
  · rw [t12]; exact P2
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, e1, pullback.lift_fst_assoc]; exact m1
    · simp only [Category.assoc, pullback.lift_snd, e1]
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, e2, pullback.lift_fst_assoc]; exact m2
    · simp only [Category.assoc, pullback.lift_snd, e2]
  · rw [t1]; exact IsPullback.of_hasPullback _ _
  · rw [t12]; exact IsPullback.of_hasPullback _ _

theorem LeafSpreadQF_of (hSep : LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated)
    (hSm : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadSmooth1) (hG : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFGraph)
    (hM : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap) : LateralTheory.E.QuasiFiniteDescent.LeafSpreadQF :=
  LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadQF_of hSep hSm hG hM spread_chain_base_change_to_larger_subalgebra

end LateralTheory.E.SpreadingOutQuasiFinitenessBaseChange

end
end

