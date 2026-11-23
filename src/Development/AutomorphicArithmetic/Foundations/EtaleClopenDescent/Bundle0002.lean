module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.EtaleCohomology.EtaleTrace.LocalSplitting.Cover2
public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CurveMayerVietorisOfDegreeZero
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

theorem UpperTheory.Cb.curve_mayer_vietoris_of_degree_zero :
    LateralTheory.E.E4.H0TwistOverClosedField → LateralTheory.E.E4.CurveCut.LeafMV := by
  intro _ _ R _ F X U V hUV n
  obtain ⟨d, hd, -⟩ := mayerVietoris R F
  have hc := LateralTheory.EtaleTrace.LSplitPf.Sch.cover2 R U V hUV
  haveI : PreservesLimitsOfShape WalkingCospan sch := by
    unfold sch; infer_instance
  have P := (isPullback_opens_inf U V).map sch
  refine ⟨(d _ _ hc n).comp (pull R P.isoPullback.inv F n), fun x => ?_⟩
  rw [(hd _ _ hc n).2.2 x]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨pull R P.isoPullback.hom F n c, ?_⟩
    rw [AddMonoidHom.comp_apply, ← pull_comp, Iso.inv_hom_id, pull_id]
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleExcisionHocolimOfLocalProperties
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut

namespace UpperTheory.Cb

private theorem dbl_map_id (P : Arrow Spc) : dbl.map (𝟙 P) = 𝟙 _ := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext <;> simp [dbl.map] <;> rfl

private theorem hs_pull_id (q : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs.pull q (𝟙 P) n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1
  rw [dbl_map_id, pull_id]

private theorem exc_iso (q : ℕ) {P' P : Arrow Spc} (e : P' ≅ P) : Exc q e.hom := fun n i =>
  Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv n i,
    fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id],
    fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id]⟩

private theorem pb_app {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (n : SimplexCategoryᵒᵖ) :
    IsPullback (P := disc.obj ((pullback π (sch.map U.ι)).obj n)) (X := disc.obj (E.obj n)) (Y := sch.obj U.toScheme) (Z := sch.obj X)
      (disc.map ((pullback.fst π (sch.map U.ι)).app n))
      (disc.map ((pullback.snd π (sch.map U.ι)).app n)) (disc.map (π.app n)) (sch.map U.ι) := by
  have h := (IsPullback.of_hasPullback π (sch.map U.ι)).map ((evaluation _ _).obj n)
  exact IsPullback.of_forall_isPullback_app fun _ => h

private def levIso {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (n : SimplexCategoryᵒᵖ) :
    (lev n).obj (abv U π) ≅ abv U (E := disc.obj (E.obj n)) (disc.map (π.app n)) :=
  Arrow.isoMk (pb_app U π n).isoPullback (Iso.refl _)
    ((pb_app U π n).isoPullback_hom_fst.trans (Category.comp_id _).symm)

private theorem pbRel_fst {B G E' E : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π') :
    pbRel g a π' π h ≫ pullback.fst π g = pullback.fst π' g ≫ a := pullback.lift_fst _ _ _

private theorem pbRel_snd {B G E' E : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π') :
    pbRel g a π' π h ≫ pullback.snd π g = pullback.snd π' g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

private theorem abvRel_square {X : Scheme.{0}} (U : X.Opens) {A B C D : Spc} (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (pA : A ⟶ sch.obj X) (pB : B ⟶ sch.obj X) (pC : C ⟶ sch.obj X) (pD : D ⟶ sch.obj X) (h1 : a ≫ pB = pA) (h2 : b ≫ pD = pB)
    (h3 : c ≫ pC = pA) (h4 : d ≫ pD = pC) (w : a ≫ b = c ≫ d) :
    abvRel U a pA pB h1 ≫ abvRel U b pB pD h2 = abvRel U c pA pC h3 ≫ abvRel U d pC pD h4 := by
  apply Arrow.hom_ext
  · change pbRel _ a _ _ h1 ≫ pbRel _ b _ _ h2 = pbRel _ c _ _ h3 ≫ pbRel _ d _ _ h4
    apply pullback.hom_ext
    · simp only [Category.assoc, pbRel_fst]
      rw [← Category.assoc, pbRel_fst, ← Category.assoc, pbRel_fst, Category.assoc, Category.assoc, w]
    · simp only [Category.assoc, pbRel_snd]
  · exact w

private theorem iso_gen {B G E' E P' P : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π')
    (f' : P' ⟶ E') (s' : P' ⟶ G) (f : P ⟶ E) (s : P ⟶ G) (hp' : IsPullback f' s' π' g) (hp : IsPullback f s π g)
    (t : P' ⟶ P) (h1 : t ≫ f = f' ≫ a) (h2 : t ≫ s = s') :
    t ≫ hp.isoPullback.hom = hp'.isoPullback.hom ≫ pbRel g a π' π h := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pbRel_fst, hp.isoPullback_hom_fst, ← Category.assoc _ (pullback.fst _ _),
      hp'.isoPullback_hom_fst, h1]
  · rw [Category.assoc, Category.assoc, pbRel_snd, hp.isoPullback_hom_snd, hp'.isoPullback_hom_snd, h2]

private theorem lev_abvRel {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (a : E' ⟶ E) (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X)
    (h : a ≫ π = π') (n : SimplexCategoryᵒᵖ) (hn) :
    (lev n).map (abvRel U a π' π h) ≫ (levIso U π n).hom =
      (levIso U π' n).hom ≫ abvRel U (E' := disc.obj (E'.obj n)) (E := disc.obj (E.obj n)) (disc.map (a.app n))
        (disc.map (π'.app n)) (disc.map (π.app n)) hn := by
  have f1 := pbRel_fst (sch.map U.ι) a π' π h
  have f2 := pbRel_snd (sch.map U.ι) a π' π h
  apply Arrow.hom_ext
  · exact iso_gen _ _ _ _ hn _ _ _ _ (pb_app U π' n) (pb_app U π n) (disc.map ((pbRel _ a _ _ h).app n))
      ((disc.map_comp _ _).symm.trans ((congrArg (fun t => disc.map (NatTrans.app t n)) f1).trans (disc.map_comp _ _)))
      ((disc.map_comp _ _).symm.trans (congrArg (fun t => disc.map (NatTrans.app t n)) f2))
  · rfl

section
variable {J : Type} [SmallCategory J]

private theorem inj_aug {D : J ⥤ PSh} {Y : PSh} (c : ∀ j, D.obj j ⟶ Y) (hc : Coc D c) (n : SimplexCategoryᵒᵖ)
    (σ : Fin (n.unop.len + 1) ⥤ J) : inj D n σ ≫ (aug c hc).app n = c (σ.obj 0) := by
  have e : σ.map (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))) = 𝟙 _ := σ.map_id _
  ext U x
  change (c (σ.obj 0)).app U ((D.map (σ.map (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))))).app U x) = _
  rw [e]
  simp

private theorem inj_nat {D' D : J ⥤ PSh} (α : D' ⟶ D) (n : SimplexCategoryᵒᵖ) (σ : Fin (n.unop.len + 1) ⥤ J) :
    inj D' n σ ≫ ((hocF J).map α).app n = α.app (σ.obj 0) ≫ inj D n σ := by
  ext U x
  have e : (fun i => (α.app (σ.obj i)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)) =
      fun i => (D.map (σ.map (homOfLE (Fin.zero_le i)))).app U ((α.app (σ.obj 0)).app U x) :=
    funext fun i => ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality (σ.map (homOfLE (Fin.zero_le i)))) U) x
  have hk : ∀ i k (g : i ⟶ k), (D.flip.obj U).map (σ.map g) ((α.app (σ.obj i)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)) =
      (α.app (σ.obj k)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le k)))).app U x) := fun i k g => by
    have a := congrFun e i
    have b := congrFun e k
    dsimp only at a b
    rw [a, b]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) _
  exact mkChn_congr (F := D.flip.obj U) σ e hk
    (fun i k g => ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) _)

end

private theorem sum_transfer (q : ℕ) {P' P : Arrow Spc} (f : P' ⟶ P) {A : Type} (Q' Q : A → Arrow Spc)
    (r' : ∀ a, Q' a ⟶ P') (r : ∀ a, Q a ⟶ P) (t : ∀ a, Q' a ⟶ Q a) (w : ∀ a, r' a ≫ f = t a ≫ r a) (ht : ∀ a, Exc q (t a))
    (B : ∀ n i : ℤ, Function.Bijective fun (x : Hs q P n i) a => Hs.pull q (r a) n i x)
    (B' : ∀ n i : ℤ, Function.Bijective fun (x : Hs q P' n i) a => Hs.pull q (r' a) n i x) : Exc q f := by
  intro n i
  refine (Function.Bijective.of_comp_iff' (B' n i) _).1 ?_
  have T : Function.Bijective (Pi.map fun a => Hs.pull q (t a) n i) := Function.Bijective.piMap fun a => ht a n i
  convert T.comp (B n i) using 1
  funext x a
  change Hs.pull q (r' a) n i (Hs.pull q f n i x) = Hs.pull q (t a) n i (Hs.pull q (r a) n i x)
  rw [← hs_pull_comp, ← hs_pull_comp, w]

private theorem exc_lvl (hL : LeafLevel) (hS : LeafHsSum) (q : ℕ) {J : Type} [SmallCategory J] {D' D : J ⥤ PSh} (α : D' ⟶ D)
    {X : Scheme.{0}} (U : X.Opens) (c' : ∀ j, D'.obj j ⟶ yoneda.obj X) (c : ∀ j, D.obj j ⟶ yoneda.obj X)
    (hc' : Coc D' c') (hc : Coc D c) (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j))
    (ht : ∀ j, Exc q (abvRel U (disc.map (α.app j)) (disc.map (c' j)) (disc.map (c j)) (h j)))
    (n : SimplexCategoryᵒᵖ) (π' : (hoc D').obj n ⟶ yoneda.obj X) (π : (hoc D).obj n ⟶ yoneda.obj X)
    (e' : π' = (aug c' hc').app n) (e : π = (aug c hc).app n) (hn) :
    Exc q (abvRel U (E' := disc.obj ((hoc D').obj n)) (E := disc.obj ((hoc D).obj n)) (disc.map (((hocF J).map α).app n))
      (disc.map π') (disc.map π) hn) := by
  obtain ⟨cD⟩ := hL J D n
  obtain ⟨cD'⟩ := hL J D' n
  have hp : ∀ σ : Fin (n.unop.len + 1) ⥤ J, disc.map (inj D n σ) ≫ disc.map π = disc.map (c (σ.obj 0)) :=
    fun σ => (disc.map_comp _ _).symm.trans (congrArg disc.map (e ▸ inj_aug c hc n σ))
  have hp' : ∀ σ : Fin (n.unop.len + 1) ⥤ J, disc.map (inj D' n σ) ≫ disc.map π' = disc.map (c' (σ.obj 0)) :=
    fun σ => (disc.map_comp _ _).symm.trans (congrArg disc.map (e' ▸ inj_aug c' hc' n σ))
  refine sum_transfer q _ (fun σ : Fin (n.unop.len + 1) ⥤ J => abv U (E := disc.obj (D'.obj (σ.obj 0))) (disc.map (c' (σ.obj 0))))
    (fun σ => abv U (E := disc.obj (D.obj (σ.obj 0))) (disc.map (c (σ.obj 0))))
    (fun σ => abvRel U (disc.map (inj D' n σ)) _ _ (hp' σ)) (fun σ => abvRel U (disc.map (inj D n σ)) _ _ (hp σ))
    (fun σ => abvRel U (disc.map (α.app (σ.obj 0))) _ _ (h _)) (fun σ => ?_) (fun σ => ht _) ?_ ?_
  · exact abvRel_square U _ _ _ _ _ _ _ _ _ _ _ _
      ((disc.map_comp _ _).symm.trans ((congrArg disc.map (inj_nat α n σ)).trans (disc.map_comp _ _)))
  · exact fun m i => hS q X U _ (fun σ : Fin (n.unop.len + 1) ⥤ J => D.obj (σ.obj 0)) (Cofan.mk _ (inj D n)) ⟨cD⟩
      π (fun σ => c (σ.obj 0)) hp m i
  · exact fun m i => hS q X U _ (fun σ : Fin (n.unop.len + 1) ⥤ J => D'.obj (σ.obj 0)) (Cofan.mk _ (inj D' n)) ⟨cD'⟩
      π' (fun σ => c' (σ.obj 0)) hp' m i

theorem etale_excision_hocolim_of_local_properties :
    LateralTheory.CohomologicalPurity.TubeCut.LeafExcLevel → LateralTheory.CohomologicalPurity.TubeCut.LeafLevel → LateralTheory.CohomologicalPurity.TubeCut.LeafHsSum → LateralTheory.CohomologicalPurity.LeafAW → LateralTheory.CohomologicalPurity.LeafBd → LateralTheory.CohomologicalPurity.LeafExc → LateralTheory.CohomologicalPurity.LeafHens → LateralTheory.CohomologicalPurity.LeafIndExc → LateralTheory.CohomologicalPurity.TubeCut.LeafExcHoc := by
  intro hE hL hS _ _ _ _ _ a3 q J _ D' D α X U c' c hc' hc h h' ht
  refine hE a3 q _ _ _ fun n => ?_
  have hn : disc.map (((hocF J).map α).app n) ≫ disc.map ((aug c hc).app n) = disc.map ((aug c' hc').app n) :=
    (disc.map_comp _ _).symm.trans (congrArg (fun t => disc.map (t.app n)) h')
  have e := lev_abvRel U ((hocF J).map α) (aug c' hc') (aug c hc) h' n hn
  have k := exc_lvl hL hS q α U c' c hc' hc h ht n _ _ rfl rfl hn
  have e' : (lev n).map (abvRel U ((hocF J).map α) (aug c' hc') (aug c hc) h') =
      (levIso U (aug c' hc') n).hom ≫ abvRel U (E' := disc.obj ((hoc D').obj n)) (E := disc.obj ((hoc D).obj n))
        (disc.map (((hocF J).map α).app n)) (disc.map ((aug c' hc').app n)) (disc.map ((aug c hc).app n)) hn ≫
        (levIso U (aug c hc) n).inv := by
    rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e']
  exact exc_comp q (exc_iso q _) (exc_comp q k (exc_iso q (levIso U (aug c hc) n).symm))

end UpperTheory.Cb
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TateTwistSectionsLocallyGenerated
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Cb.TwSec

private theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (y : Sec F U) : Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

private noncomputable def gsec {q : ℕ} (i : ℤ) (U : Scheme.{0}) :
    (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] Sec (tw q i) U :=
  ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom ∘ₗ (twRel q i Γ(U, ⊤)).mkQ

private theorem gsec_one {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    gsec i U (Finsupp.single ζ 1) = twGen i ζ := rfl

end UpperTheory.Cb.TwSec

private theorem twRel_mk_single_eq_zpow_smul_mk_single_of_eq_pow {q : ℕ} (i : ℤ) {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) =
      (ULift.up (((a ^ i : (ZMod q)ˣ) : ZMod q)) : ULift.{1} (ZMod q)) • Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single_one, Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩

private theorem ulift_zmod_smul_eq_val_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (s : ULift.{1} (ZMod q)) (x : M) : s • x = s.down.val • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  congr 1
  apply ULift.ext
  rw [ULift.down_natCast, ZMod.natCast_zmod_val]

private theorem exists_twRel_mk_eq_nsmul_mk_single_of_support_pow {q : ℕ} [NeZero q] (i : ℤ) {A : Type} [CommRing A] (ζ : Prim q A)
    (f : Prim q A →₀ ULift.{1} (ZMod q)) (hf : ∀ ξ ∈ f.support, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ∃ c : ℕ, (Submodule.Quotient.mk f : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) =
      c • Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  have key : ∀ ξ, ∃ c : ℕ, (Submodule.Quotient.mk (Finsupp.single ξ (f ξ)) :
      (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) = c • Submodule.Quotient.mk (Finsupp.single ζ 1) := by
    intro ξ
    by_cases hξ : f ξ = 0
    · refine ⟨0, ?_⟩
      rw [hξ, Finsupp.single_zero, zero_smul]
      exact Submodule.Quotient.mk_zero _
    · obtain ⟨a, ha⟩ := hf ξ (Finsupp.mem_support_iff.mpr hξ)
      refine ⟨(f ξ * ULift.up (((a ^ i : (ZMod q)ˣ) : ZMod q))).down.val, ?_⟩
      rw [← ulift_zmod_smul_eq_val_nsmul, mul_smul, ← twRel_mk_single_eq_zpow_smul_mk_single_of_eq_pow i ζ ξ a ha, ← Submodule.Quotient.mk_smul, Finsupp.smul_single_one]
  choose c hc using key
  refine ⟨∑ ξ ∈ f.support, c ξ, ?_⟩
  conv_lhs => rw [← Finsupp.sum_single f]
  rw [Finsupp.sum, Finset.sum_smul, ← Finset.sum_congr rfl (fun ξ _ => hc ξ)]
  exact map_sum (twRel q i A).mkQ _ _

private theorem sec_res_gsec_eq_gsec_mapDomain {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (f : Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) :
    Sec.res g (UpperTheory.Cb.TwSec.gsec i U f) = UpperTheory.Cb.TwSec.gsec i V (Finsupp.mapDomain (Prim.map g.appTop.hom) f) := by
  have h := congrArg (fun φ => φ.hom (Submodule.Quotient.mk f : (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(U, ⊤)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  exact h.symm

private theorem gsec_single_eq_zpow_smul_gsec_single_of_eq_pow {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    UpperTheory.Cb.TwSec.gsec i U (Finsupp.single ξ 1) =
      (ULift.up (((a ^ i : (ZMod q)ˣ) : ZMod q)) : ULift.{1} (ZMod q)) • UpperTheory.Cb.TwSec.gsec i U (Finsupp.single ζ 1) := by
  rw [← map_smul]
  have e : (twRel q i Γ(U, ⊤)).mkQ (Finsupp.single ξ 1) =
      (twRel q i Γ(U, ⊤)).mkQ ((ULift.up (((a ^ i : (ZMod q)ˣ) : ZMod q)) : ULift.{1} (ZMod q)) • Finsupp.single ζ 1) := by
    rw [map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply]
    exact twRel_mk_single_eq_zpow_smul_mk_single_of_eq_pow i ζ ξ a h
  exact congrArg (fun t => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom t) e

private theorem exists_gsec_eq_nsmul_twGen_of_support_pow {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤))
    (f : Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) (hf : ∀ ξ ∈ f.support, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ∃ c : ℕ, UpperTheory.Cb.TwSec.gsec i U f = c • twGen i ζ := by
  obtain ⟨c, hc⟩ := exists_twRel_mk_eq_nsmul_mk_single_of_support_pow i ζ f hf
  refine ⟨c, ?_⟩
  rw [← UpperTheory.Cb.TwSec.gsec_one, ← map_nsmul]
  have e : (twRel q i Γ(U, ⊤)).mkQ f = (twRel q i Γ(U, ⊤)).mkQ (c • Finsupp.single ζ 1) := by
    rw [map_nsmul]
    exact hc
  exact congrArg (fun t => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom t) e

theorem UpperTheory.Cb.tateTwist_sections_locally_generated :
    ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ := by
  intro q _ i
  have h4 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)),
      Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
    intro V U g ζ
    rw [← UpperTheory.Cb.TwSec.gsec_one, ← UpperTheory.Cb.TwSec.gsec_one, sec_res_gsec_eq_gsec_mapDomain, Finsupp.mapDomain_single]
  have h5 : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ := by
    intro U ζ ξ a h
    rw [← UpperTheory.Cb.TwSec.gsec_one, ← UpperTheory.Cb.TwSec.gsec_one, gsec_single_eq_zpow_smul_gsec_single_of_eq_pow i ζ ξ a h, ulift_zmod_smul_eq_val_nsmul]
  have L := GlobalTheory.T.etaleLocal_property_calculus_rules
  have S := GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod q) (Scheme.Γ ⋙ twF q i)
  have h2 : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U),
      Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom) := by
    classical
    intro U ζ y
    apply L.2.2.2.2.1
    refine L.2.1 U _ _ (S.1 U y) ?_
    rintro V g ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : Sec.res g y = UpperTheory.Cb.TwSec.gsec i V f := hx.symm
    have hl := L.2.2.2.2.2.1 V (↥f.support) _ (fun ξ => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 (ζ.map g.appTop.hom) ξ.1)
    refine L.2.1 V _ _ hl ?_
    intro W k hk
    obtain ⟨c, hc⟩ := exists_gsec_eq_nsmul_twGen_of_support_pow i ((ζ.map g.appTop.hom).map k.appTop.hom)
      (Finsupp.mapDomain (Prim.map k.appTop.hom) f) (by
        intro ξ' hξ'
        obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hξ')
        obtain ⟨a, ha⟩ := hk ⟨ξ, hξ⟩
        exact ⟨a, ha⟩)
    refine ⟨c, ?_⟩
    have e : twGen i ((ζ.map g.appTop.hom).map k.appTop.hom) = twGen i (ζ.map (k ≫ g).appTop.hom) := by
      calc twGen i ((ζ.map g.appTop.hom).map k.appTop.hom) = Sec.res k (Sec.res g (twGen i ζ)) := by
            rw [h4, h4]
        _ = twGen i (ζ.map (k ≫ g).appTop.hom) := by
            rw [← UpperTheory.Cb.TwSec.res_comp, h4]
    rw [e] at hc
    rw [UpperTheory.Cb.TwSec.res_comp, hx']
    exact (sec_res_gsec_eq_gsec_mapDomain i k f).trans hc
  have h1 : ∀ (U : Scheme.{0}) (y : Sec (tw q i) U),
      Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ := by
    intro U y
    apply L.2.2.2.2.1
    refine L.2.1 U _ _ (S.1 U y) ?_
    rintro V g ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : Sec.res g y = UpperTheory.Cb.TwSec.gsec i V f := hx.symm
    by_cases hP : Nonempty (Prim q Γ(V, ⊤))
    · obtain ⟨ζ⟩ := hP
      refine L.2.1 V _ _ (h2 V ζ (Sec.res g y)) ?_
      rintro W k ⟨c, hc⟩
      exact Or.inr ⟨_, c, by rw [UpperTheory.Cb.TwSec.res_comp]; exact hc⟩
    · apply L.1
      intro W k
      left
      have hf : f = 0 := by
        ext ξ
        exact (hP ⟨ξ⟩).elim
      rw [UpperTheory.Cb.TwSec.res_comp, hx', hf]
      exact (congrArg (Sec.res k) (map_zero (UpperTheory.Cb.TwSec.gsec i V))).trans (map_zero ((tw q i).obj.map k.op).hom)
  have h3 : ∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c := by
    intro U _ ζ c h
    have hz : UpperTheory.Cb.TwSec.gsec i U (c • Finsupp.single ζ 1) = 0 := by
      rw [map_nsmul, UpperTheory.Cb.TwSec.gsec_one]
      exact h
    have hl := S.2.1 U ((twRel q i Γ(U, ⊤)).mkQ (c • Finsupp.single ζ 1)) hz
    obtain ⟨u⟩ := ‹Nonempty U›
    have hmono : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
        ((Scheme.Γ ⋙ twF q i).map g.op).hom ((twRel q i Γ(U, ⊤)).mkQ (c • Finsupp.single ζ 1)) = 0 →
        ((Scheme.Γ ⋙ twF q i).map (k ≫ g).op).hom ((twRel q i Γ(U, ⊤)).mkQ (c • Finsupp.single ζ 1)) = 0 := by
      intro V W g k hg
      change ((Scheme.Γ ⋙ twF q i).map (g.op ≫ k.op)).hom _ = 0
      rw [Functor.map_comp, ModuleCat.hom_comp]
      exact (congrArg (ModuleCat.Hom.hom ((Scheme.Γ ⋙ twF q i).map k.op)) hg).trans (map_zero _)
    obtain ⟨V, g, -, -, ⟨v, -⟩, hV⟩ := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U _ hmono).mp hl u
    have hV' : (c • Submodule.Quotient.mk (Finsupp.single (ζ.map g.appTop.hom) 1) :
        (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(V, ⊤)) = 0 := by
      refine Eq.trans ?_ hV
      change _ = Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (c • Finsupp.single ζ 1))
      rw [Finsupp.smul_single, Finsupp.mapDomain_single, ← Finsupp.smul_single, Submodule.Quotient.mk_smul]
    haveI : Nonempty (⊤ : V.Opens) := ⟨⟨v, trivial⟩⟩
    haveI : Nontrivial Γ(V, ⊤) := Scheme.component_nontrivial V ⊤
    obtain ⟨φ, hφ⟩ := (GlobalTheory.T.tateTwistModule_free_and_generator_summand q i Γ(V, ⊤)).2 (ζ.map g.appTop.hom)
    have hc := congrArg φ hV'
    rw [map_nsmul, hφ, map_zero, nsmul_eq_mul, mul_one] at hc
    have hd := congrArg ULift.down hc
    rw [ULift.down_natCast] at hd
    exact (ZMod.natCast_eq_zero_iff c q).mp hd
  have h6 : ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U),
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) →
      (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
        e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) →
      ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ := by
    intro M e hnat hrel
    let lin : ∀ U : Scheme.{0}, (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] M.obj.obj (op U) :=
      fun U => Finsupp.linearCombination (ULift.{1} (ZMod q)) (e U)
    have lin_single : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), lin U (Finsupp.single ζ 1) = e U ζ := by
      intro U ζ
      simp only [lin, Finsupp.linearCombination_single, one_smul]
    have hker : ∀ U : Scheme.{0}, twRel q i Γ(U, ⊤) ≤ LinearMap.ker (lin U) := by
      intro U
      refine Submodule.span_le.mpr ?_
      rintro x ⟨ζ, ξ, a, h, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, lin_single, ← Finsupp.smul_single_one, map_smul, lin_single,
        hrel U ζ ξ a h, ulift_zmod_smul_eq_val_nsmul, sub_self]
    let φ0 : Scheme.Γ ⋙ twF q i ⟶ M.obj :=
      { app := fun X => ModuleCat.ofHom ((twRel q i Γ(X.unop, ⊤)).liftQ (lin X.unop) (hker X.unop))
        naturality := by
          intro X Y f
          apply ModuleCat.hom_ext
          apply Submodule.linearMap_qext
          apply Finsupp.lhom_ext'
          intro ξ
          apply LinearMap.ext_ring
          change lin Y.unop (Finsupp.mapDomain (Prim.map f.unop.appTop.hom) (Finsupp.single ξ 1)) =
            (M.obj.map f).hom (lin X.unop (Finsupp.single ξ 1))
          erw [Finsupp.mapDomain_single]
          rw [lin_single]
          exact ((congrArg (M.obj.map f).hom (lin_single X.unop ξ)).trans (hnat Y.unop X.unop f.unop ξ)).symm }
    obtain ⟨ψ, hψ, huniq⟩ := S.2.2 M φ0
    refine ⟨ψ, fun U ζ => ?_, fun φ' hφ' => huniq φ' ?_⟩
    · have := congrArg (fun t => (t.app (op U)).hom
        (Submodule.Quotient.mk (p := twRel q i Γ(U, ⊤)) (Finsupp.single ζ 1))) hψ
      exact this.trans (lin_single U ζ)
    · apply NatTrans.ext
      funext X
      apply ModuleCat.hom_ext
      apply Submodule.linearMap_qext
      apply Finsupp.lhom_ext'
      intro ξ
      apply LinearMap.ext_ring
      exact (hφ' X.unop ξ).trans (lin_single X.unop ξ).symm
  exact ⟨h1, h2, h3, h4, h5, h6⟩
end

