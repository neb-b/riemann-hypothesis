module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0033
public import Development.EtaleCohomology.EtaleSheaves.FPColimPf
public import Development.EtaleCohomology.EtaleSheaves.Bundle0082
public import Development.EtaleCohomology.EtaleSheaves.Bundle0018
public import Development.EtaleCohomology.EtaleSheaves.Bundle0063
public import Development.EtaleCohomology.EtaleSheaves.LeafDescendMapPf
public import Development.EtaleCohomology.EtaleSheaves.Bundle0073
public import Development.EtaleCohomology.EtaleSheaves.Bundle0077
public import Development.EtaleCohomology.EtaleSheaves.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.EtaleCohomology.EtaleSheaves.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.ArchimedeanComparison
section
theorem LateralTheory.E.TruncationIsoComparison.IEComp_of : LateralTheory.E.t_E3Cut.IEComp :=
  LateralTheory.E.IECompPf.IEComp_of (LateralTheory.E.UnderFAPf.UnderFA_of LateralTheory.E.FPColimPf.FPColim_of)
    (LateralTheory.E.SpreadPf.Cut.EtSpreads_of LateralTheory.E.SpreadPf.FPProof.finite_presentation_ring_maps_pre_ind_spread LateralTheory.E.EtStagePf.EtStage_of)
theorem LateralTheory.E.TruncationIsoComparison.Comp_of : LateralTheory.E.SHExistsPf.Comp := @LateralTheory.E.TruncationIsoComparison.IEComp_of
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DiagramDescent
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.DiagramDescent

theorem descendFP_of (hA : LateralTheory.E.LeafObjFPPf.LeafObjAff) (hG : LateralTheory.E.LeafObjGluePf.LeafGlueTwo)
    (hQ : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct) (hI : LateralTheory.E.LeafInclDescendPf.LeafInclPiece)
    (hL : LateralTheory.E.LeafMapFPPf.LeafLimFP) (hF : LateralTheory.E.LeafPairRelPf.LeafFactorStage) : LeafDescendFP := by
  have hO : LeafObjFP := LateralTheory.E.LeafObjFPPf.objectDescent_of_affineDescent hA
    (LateralTheory.E.LeafObjGluePf.LeafObjGlue_of (LateralTheory.E.LeafInclDescendPf.LeafInclDescend_of hI) hG) hQ
  exact diagramDescent_of_objects_pairs_triples hO (LateralTheory.E.LeafPairFPPf.pairDescent_of_objects_morphisms hO (LateralTheory.E.LeafMapFPPf2.morphismDescent_of_isLimit hL))
    (LateralTheory.E.LeafTripleFPPf.tripleDescent_of_pairRelation (LateralTheory.E.LeafPairRelPf.LeafPairRel_of hO hF))

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem cond {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D} {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) :
    v ≫ g = (c ≫ toR R') ≫ incl hR := by
  rw [Category.assoc, LateralTheory.E.LeafDescendMapPf.toR_incl]; exact h.w

theorem sq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D} {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (cond hR h)) c (pullback.snd g (incl hR)) (toR R') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback g (incl hR))
  rw [pullback.lift_fst, LateralTheory.E.LeafDescendMapPf.toR_incl]; exact h

theorem LeafDescendPreMap_of (hA : LateralTheory.E.LeafObjFPPf.LeafObjAff) (hG : LateralTheory.E.LeafObjGluePf.LeafGlueTwo)
    (hQ : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct) (hI : LateralTheory.E.LeafInclDescendPf.LeafInclPiece)
    (hL : LateralTheory.E.LeafMapFPPf.LeafLimFP) (hF : LateralTheory.E.LeafPairRelPf.LeafFactorStage) :
    LateralTheory.E.QuasiFiniteDescent.LeafDescendPreMap := by
  intro k _ X p _ Ω _ _ C0 c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hRfg, D0, D1, D2, q, d1, d2, v0, v1, v2, hpre⟩ :=
    descendFP_of hA hG hQ hI hL hF k Ω c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨hq0, hq1, hq2, p0, p1, p2, m1, m2⟩ := hpre
  have : LocallyOfFinitePresentation p := LateralTheory.E.LeafDescendMapPf.lfp p
  let bk := Spec.map (CommRingCat.ofHom (algebraMap k R))
  have hlfp : LocallyOfFinitePresentation (pullback.snd p bk) := inferInstance
  have ha : e ≫ p = (c0 ≫ toR R) ≫ bk := by
    rw [he, Category.assoc, LateralTheory.E.LeafDescendMapPf.toR_base]
  obtain ⟨R', h, hR'fg, g, hg1, hg2⟩ := hF k Ω R hRfg c0 q v0 hq0 p0 (pullback.snd p bk) hlfp
    (pullback.lift e (c0 ≫ toR R) ha) (pullback.lift_snd _ _ _)
  let e1 : pullback (d1 ≫ q) (incl h) ⟶ pullback q (incl h) :=
    pullback.map _ _ _ _ d1 (𝟙 _) (𝟙 _) (by simp) (by simp)
  let e2 : pullback (d2 ≫ d1 ≫ q) (incl h) ⟶ pullback (d1 ≫ q) (incl h) :=
    pullback.map _ _ _ _ d2 (𝟙 _) (𝟙 _) (by simp) (by simp)
  have E1 : e1 ≫ pullback.snd q (incl h) = pullback.snd (d1 ≫ q) (incl h) := by
    simp only [e1, pullback.map, pullback.lift_snd, Category.comp_id]
  have E2 : e2 ≫ e1 ≫ pullback.snd q (incl h) = pullback.snd (d2 ≫ d1 ≫ q) (incl h) := by
    rw [E1]; simp only [e2, pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨R', hR'fg, _, _, _, pullback.snd q (incl h), e1, e2, g ≫ pullback.fst p bk,
    pullback.lift v0 (c0 ≫ toR R') (cond h p0), pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (cond h p1),
    pullback.lift v2 ((γ2 ≫ γ1 ≫ c0) ≫ toR R') (cond h p2), ?_, ⟨fp_snd _ _ hq0, ?_, ?_, sq h p0, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hg1, Category.assoc,
      LateralTheory.E.LeafDescendMapPf.incl_base]
  · rw [E1]; exact fp_snd _ _ hq1
  · rw [E2]; exact fp_snd _ _ hq2
  · rw [E1]; exact sq h p1
  · rw [E2]; exact sq h p2
  · apply pullback.hom_ext
    · simp only [e1, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact m1
    · simp only [e1, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  · apply pullback.hom_ext
    · simp only [e2, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact m2
    · simp only [e2, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  · rw [← Category.assoc, hg2, pullback.lift_fst]

end LateralTheory.E.DiagramDescent

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafClosedImmSpreadPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafSpreadSeparatedPf

namespace LateralTheory.E.LeafClosedImmSpreadPf

theorem bc_sq {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z) :
    IsPullback (pullback.fst (f ≫ g) t) (BC f g (f ≫ g) rfl t) f (pullback.fst g t) := by
  have e : BC f g (f ≫ g) rfl t ≫ pullback.snd g t = pullback.snd (f ≫ g) t := by
    simp only [BC, pullback.map, pullback.lift_snd, Category.comp_id]
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback g t)
  · rw [e]; exact IsPullback.of_hasPullback (f ≫ g) t
  · simp only [BC, pullback.map, pullback.lift_fst]

theorem toR_eq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) :
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap R.toSubring.subtype : Sp Ω ⟶ Sp R) = toR R := rfl

theorem incl_eq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S : Subalgebra k Ω} (h : R ≤ S)
    (h' : R.toSubring ≤ S.toSubring) :
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Subring.inclusion h') : Sp S ⟶ Sp R) = incl h := rfl

theorem LeafClosedImmSpread_of : LeafClosedImmSpread := by
  intro k _ Ω _ _ R hR X Y f g hg hfg hci
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hp1, hp2, hp3⟩ := hfg
  have := hg1; have := hg2; have := hg3; have := hp1; have := hp2; have := hp3
  have : QuasiSeparated f := QuasiSeparated.of_comp f g
  have : QuasiCompact f := QuasiCompact.of_comp f g
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f g
  have hY : IsPullback (pullback.fst g (toR R)) (pullback.snd g (toR R)) (g : Y ⟶ Sp R.toSubring)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap R.toSubring.subtype) := by
    rw [toR_eq]; exact IsPullback.of_hasPullback g (toR R)
  have : QuasiCompact (g : Y ⟶ Sp R.toSubring) := hg2
  obtain ⟨F, hF⟩ := GlobalTheory.isClosedImmersion_descends_to_subring Ω R.toSubring X Y _ _ f g
    (BC f g (f ≫ g) rfl (toR R)) (pullback.fst _ _) (pullback.fst _ _) (pullback.snd _ _) hY (bc_sq f g _) hci
  let S : Subalgebra k Ω := R ⊔ Algebra.adjoin k (F : Set Ω)
  have h : R ≤ S := le_sup_left
  have h' : R.toSubring ≤ S.toSubring := fun x hx => h hx
  have hsub : (F : Set Ω) ⊆ S.toSubring := fun x hx =>
    (le_sup_right : Algebra.adjoin k (F : Set Ω) ≤ S) (Algebra.subset_adjoin hx)
  refine ⟨S, h, hR.sup (Subalgebra.fg_adjoin_finset F), ?_⟩
  have hY1 : IsPullback (pullback.fst g (incl h)) (pullback.snd g (incl h)) (g : Y ⟶ Sp R.toSubring)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Subring.inclusion h')) := by
    rw [incl_eq h h']; exact IsPullback.of_hasPullback g (incl h)
  exact hF S.toSubring h' hsub _ _ (BC f g (f ≫ g) rfl (incl h)) (pullback.fst _ _) (pullback.fst _ _)
    (pullback.snd _ _) hY1 (bc_sq f g _)

end LateralTheory.E.LeafClosedImmSpreadPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StalkContPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.StalkGermPf GlobalTheory.StalkLimit

namespace LateralTheory.E.StalkContPf

set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme.{0}}

theorem diagram_map_eq (p : X ⟶ S) (s : S) {V W : AffNhd s} (i : V ⟶ W) :
    (diagram s p).map i = resO p i.le := by
  apply pullback.hom_ext <;> simp [diagram, resO]

theorem cone_app_eq (p : X ⟶ S) (s : S) (V : AffNhd s) :
    (cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V = toO p s V.1 V.2.1 := by
  apply pullback.hom_ext <;> simp [cone, toO]

theorem pull_cone {q : ℕ} {n i : ℤ} (p : X ⟶ S) (s : S) (V : AffNhd s) (y : Ht q (sch.obj (overO p V.1)) n i) :
    pull _ (sch.map ((cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V)) (tw q i) n y =
      pull _ (sch.map (toO p s V.1 V.2.1)) (tw q i) n y := by
  rw [cone_app_eq]; rfl

theorem pull_diag {q : ℕ} {n i : ℤ} (p : X ⟶ S) (s : S) {V W : AffNhd s} (f : V ⟶ W)
    (y : Ht q (sch.obj (overO p W.1)) n i) :
    pull _ (sch.map ((diagram s p).map f)) (tw q i) n y = pull _ (sch.map (resO p f.le)) (tw q i) n y := by
  rw [diagram_map_eq]; rfl

theorem exists_aff (s : S) (U : S.Opens) (hs : s ∈ U) : ∃ V : AffNhd s, V.1 ≤ U := by
  obtain ⟨W, h₁, h₂, h₃⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hs
  exact ⟨⟨W, h₂, h₁⟩, h₃⟩

theorem StalkCont_of : StalkCont := by
  intro hC hH q X S p _ _ _ _ hq i n s
  have hc := (nonempty_isLimit (IsPullback.of_hasPullback p (S.fromSpecStalk s))).some
  have hcpt : ∀ V : AffNhd s, CompactSpace ((diagram s p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V.1.ι)
  have hqs : ∀ V : AffNhd s, QuasiSeparatedSpace ((diagram s p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V.1.ι)
  have hu : ∀ V : AffNhd s, IsUnit (q : Γ((diagram s p).obj V, ⊤)) := fun V => by
    have := hq.map ((pullback.fst p V.1.ι ≫ p).appTop).hom
    simp only [map_natCast] at this
    exact this
  obtain ⟨hsurj, hkill⟩ := hC hH q (diagram s p) _ hc (fun f => inferInstance) hcpt hqs hu n i
  constructor
  · intro U hs x hx
    obtain ⟨V0, hV0⟩ := exists_aff s U hs
    have h0 : pull _ (sch.map ((cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V0)) _ _
        (pull _ (sch.map (resO p hV0)) _ _ x) = 0 := by
      rw [pull_cone, ← pull_mc, toO_res]; exact hx
    obtain ⟨k, f, hf⟩ := hkill V0 _ h0
    have hkV : k.1 ≤ V0.1 := f.le
    refine ⟨k.1, hkV.trans hV0, k.2.1, ?_⟩
    rw [pull_diag, ← pull_mc, res_res] at hf
    exact hf
  · intro z
    obtain ⟨j, y, hy⟩ := hsurj z
    exact ⟨j.1, j.2.1, y, (pull_cone p s j y).symm.trans hy⟩

end LateralTheory.E.StalkContPf
end
end

