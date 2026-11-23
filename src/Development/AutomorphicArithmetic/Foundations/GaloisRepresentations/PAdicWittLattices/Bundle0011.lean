module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JCharVan
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.G3

private theorem prim_isEmpty {k : Type} [Field k] {q : ℕ} (hq : (q : k) = 0) {V : Scheme.{0}} (v : V) (f : V ⟶ sp k) :
    IsEmpty (Prim q Γ(V, ⊤)) := by
  constructor
  rintro ⟨ζ, hu, -⟩
  have h0 : ((q : ℕ) : Γ(sp k, ⊤)) = 0 := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom,
      show ((q : ℕ) : CommRingCat.of k) = 0 from hq, map_zero]
  have h1 : ((q : ℕ) : Γ(V, ⊤)) = 0 := by
    rw [← map_natCast f.appTop.hom, h0, map_zero]
  rw [h1] at hu
  haveI : Nonempty (⊤ : V.Opens) := ⟨⟨v, trivial⟩⟩
  exact not_isUnit_zero hu

private theorem sec_subsingleton {k : Type} [Field k] {q : ℕ} (hq : (q : k) = 0) (i : ℤ) {U : Scheme.{0}} (f : U ⟶ sp k) :
    Subsingleton (Sec (tw q i) U) := by
  suffices h : ∀ x : Sec (tw q i) U, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  let S : Sieve U :=
    { arrows := fun V j => Sec.res j x = 0
      downward_closed := by
        intro V W j hj g
        have hj' : ModuleCat.Hom.hom ((tw q i).obj.map j.op) x = 0 := hj
        show ModuleCat.Hom.hom ((tw q i).obj.map (g ≫ j).op) x = 0
        rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hj', map_zero] }
  have hS : S ∈ Scheme.etaleTopology U := by
    rw [GlobalTheory.etale_mem_iff_points]
    intro u
    obtain ⟨V, j, v, m, -, hj, hv, hm⟩ := (GlobalTheory.ofRings_loc (ZMod q) (twF q i) U).1 x u
    refine ⟨V, j, v, hj, hv, ?_⟩
    refine hm.symm.trans ?_
    haveI : IsEmpty (Prim q Γ(V, ⊤)) := prim_isEmpty hq v (j ≫ f)
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective (twRel q i Γ(V, ⊤)) m
    rw [Subsingleton.elim g 0, Submodule.Quotient.mk_zero]
    exact map_zero _
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget (J := Scheme.etaleTopology) (P' := (tw q i).obj)
      (forget (ModuleCat.{1} (ULift.{1, 0} (ZMod q))))).mp (tw q i).property)
  exact (hsh S hS).isSeparatedFor (fun _ _ _ => 0) x 0 (fun V j hj => hj)
    (fun V j hj => show ModuleCat.Hom.hom ((tw q i).obj.map j.op) 0 = 0 from map_zero _)

private theorem ht_subsingleton {k : Type} [Field k] {q : ℕ} (hq : (q : k) = 0) {X : Scheme.{0}} (p : X ⟶ sp k) (n i : ℤ) :
    Subsingleton (Ht q (sch.obj X) n i) := by
  have hbij := GlobalTheory.T.etaleCohomology_bijective_of_support_bijective (ZMod q) (sch.obj X) (0 : tw q i ⟶ tw q i) (fun U hU => by
    obtain ⟨g⟩ := hU
    have g' : U ⟶ X := g
    haveI := sec_subsingleton hq i (g' ≫ p)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨b, Subsingleton.elim _ _⟩⟩) n
  have hz : HK.post (ZMod q) ((chains (ZMod q)).obj (sch.obj X)) (0 : tw q i ⟶ tw q i) n = 0 := by
    have h := PostFun.post_add ((chains (ZMod q)).obj (sch.obj X)) (0 : tw q i ⟶ tw q i) 0 n
    rw [add_zero] at h
    exact left_eq_add.1 h
  refine ⟨fun a b => hbij.1 ?_⟩
  rw [hz]; rfl

theorem jCharVan : CharVan := by
  intro l _ k _ hl X x n i
  have hs : ∀ m : ℕ, Subsingleton (Ht (l ^ (m + 1)) (sch.obj X) n i) := fun m =>
    ht_subsingleton (k := k) (by push_cast; rw [hl, zero_pow (Nat.succ_ne_zero m)]) x n i
  constructor
  intro a b
  apply Subtype.ext
  funext m
  cases m with
  | zero =>
    rw [← a.2 0, ← b.2 0]
    congr 1
    exact (hs 0).elim _ _
  | succ m => exact (hs m).elim _ _

end UpperTheory.Gal.G3

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JCorrUniq
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem htot_subsingleton (l : ℕ) [Fact l.Prime] (E : Spc)
    (h : ∀ n : ℤ, Subsingleton (Hl l E n 0)) : Subsingleton (Htot l E) := by
  have hq : ∀ n : ℤ, Subsingleton (HQ l E n 0) := fun n => by
    have := h n
    refine ⟨fun a b => ?_⟩
    have z : ∀ c : HQ l E n 0, c = 0 := fun c => by
      induction c using TensorProduct.induction_on with
      | zero => rfl
      | tmul q y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
      | add c d hc hd => rw [hc, hd, add_zero]
    rw [z a, z b]
  exact ⟨fun a b => DFinsupp.ext fun n => (hq n).elim _ _⟩

private theorem op_eq (l : ℕ) [Fact l.Prime] (k : Type) [Field k] {Z Y Z' : Scheme.{0}} (p : Z ⟶ sp k)
    (s : Y ⟶ Z) (t : Y ⟶ Z') (hT : (et l (sp k)).Good)
    (tr : (et l (sp k)).H (s ≫ p) →ₗ[ℚ_[l]] (et l (sp k)).H p) (htr : (et l (sp k)).IsTr p (s ≫ p) s tr)
    (A : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)) (hA : IsCorrOp l s t A)
    (x : Htot l (sch.obj Z')) : A x = tr (pullTot l (sch.map t) x) := by
  obtain ⟨W, c, G, _, _, a, J, _, σ, hgal, hsp, hx⟩ := hA
  have hσ : ∀ j, σ j ≫ s ≫ p = c ≫ p := fun j => by
    rw [← Category.assoc, hsp.choose j]
  have hinj := hT.inj p (c ≫ p) c rfl G a hgal
  apply hinj
  have e := htr W (c ≫ p) c rfl J σ hσ hsp (pullTot l (sch.map t) x)
  refine Eq.trans ?_ e.symm
  refine (hx x).trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Functor.map_comp, pullTot_comp]
  rfl

theorem UpperTheory.Gal.G3.jCorrUniq :
    EtGood → SplitDesc → CharVan → CorrUniq := by
  intro hG hD hV l _ k _ Z Y Z' p s t A A' hA hA'
  by_cases hl : (l : k) = 0
  · have := htot_subsingleton l (sch.obj Z) fun n => hV l k hl p n 0
    exact LinearMap.ext fun x => Subsingleton.elim _ _
  · have hu : IsUnit (l : Γ(sp k, ⊤)) := by
      have h : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (l : k)) := (IsUnit.mk0 _ hl).map _
      rwa [map_natCast] at h
    have hT := hG l (sp k) hu
    obtain ⟨W, c, G, _, _, a, J, _, σ, hgal, hsp, -⟩ := id hA
    obtain ⟨hf, he, hs, -, -, -⟩ := hgal
    obtain ⟨_, _⟩ := @hD Z Y W s c hf he hs J _ σ hsp
    obtain ⟨tr, htr⟩ := hT.tr p (s ≫ p) s rfl
    exact LinearMap.ext fun x => (op_eq l k p s t hT tr htr A hA x).trans (op_eq l k p s t hT tr htr A' hA' x).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JSplitDesc
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3 MorphismProperty
universe u v

set_option backward.isDefEq.respectTransparency.types false in
private theorem isProper_desc {A G U Z : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Flat j] [Surjective j] [QuasiCompact j] (h : IsPullback φ f g j) [IsProper f] : IsProper g := by
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hUC : UniversallyClosed g :=
    of_isPullback_of_descendsAlong h.flip hQ (inferInstanceAs (UniversallyClosed f))
  have hLFT : LocallyOfFiniteType g :=
    of_isPullback_of_descendsAlong h.flip hQ (inferInstanceAs (LocallyOfFiniteType f))
  have hD : MorphismProperty.diagonal @UniversallyClosed g := by
    refine of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed) h.flip hQ ?_
    rw [MorphismProperty.diagonal_iff]
    infer_instance
  rw [MorphismProperty.diagonal_iff] at hD
  have hP : IsProper (pullback.diagonal g) := IsProper.mk
  have hC : IsClosedImmersion (pullback.diagonal g) :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨hP, inferInstance⟩
  haveI : IsSeparated g := ⟨hC⟩
  exact IsProper.mk

set_option backward.isDefEq.respectTransparency.types false in
private theorem isFinite_desc_fin (W : Scheme.{0}) (n : ℕ) :
    IsFinite (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
  induction n with
  | zero =>
    haveI := Function.isEmpty (sigmaMk (fun _ : Fin 0 => W)).symm
    infer_instance
  | succ n ih =>
    let t := extendCofanIsColimit (fun _ : Fin (n + 1) => W) (coproductIsCoproduct fun _ : Fin n => W)
      (coprodIsCoprod W (∐ fun _ : Fin n => W))
    let e : (∐ fun _ : Fin (n + 1) => W) ≅ W ⨿ (∐ fun _ : Fin n => W) :=
      (coproductIsCoproduct fun _ : Fin (n + 1) => W).coconePointUniqueUpToIso t
    have key : (Sigma.desc (f := fun _ : Fin (n + 1) => W) fun _ => 𝟙 W) =
        e.hom ≫ coprod.desc (𝟙 W) (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
      refine Sigma.hom_ext _ _ fun j => ?_
      have hj := IsColimit.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct (fun _ : Fin (n + 1) => W)) t ⟨j⟩
      rw [Sigma.ι_desc, ← Category.assoc]
      erw [hj]
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [extendCofan, Cofan.mk_ι_app, Fin.cases_zero]
        exact (coprod.inl_desc _ _).symm
      · simp only [extendCofan, Cofan.mk_ι_app, Fin.cases_succ]
        show 𝟙 W = (Sigma.ι (fun _ : Fin n => W) i ≫ coprod.inr) ≫
          coprod.desc (𝟙 W) (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W)
        rw [Category.assoc, coprod.inr_desc, Sigma.ι_desc]
    rw [key]
    infer_instance

set_option backward.isDefEq.respectTransparency.types false in
private theorem isFinite_desc (W : Scheme.{0}) (J : Type) [Finite J] :
    IsFinite (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have key : (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) =
      (Sigma.reindex e.symm (fun _ : J => W)).inv ≫ (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc, ← Category.assoc]
    have h := Sigma.ι_reindex_inv e.symm (fun _ : J => W) (e j)
    simp only [Equiv.symm_apply_apply] at h
    rw [h]
    exact (Sigma.ι_desc (f := fun _ : Fin n => W) (fun _ => 𝟙 W) (e j)).symm
  rw [key]
  haveI := isFinite_desc_fin W n
  infer_instance

private theorem locallyQuasiFinite_of_etale {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] : LocallyQuasiFinite f := by
  have hf : affineLocally RingHom.Etale f := by
    rw [← HasRingHomProperty.eq_affineLocally @Etale]
    exact ‹Etale f›
  rw [HasRingHomProperty.eq_affineLocally @LocallyQuasiFinite]
  refine affineLocally_le (fun {R S} _ _ {g} hg => ?_) f hf
  letI : Algebra R S := RingHom.toAlgebra g
  have : Algebra.Etale R S := hg
  show Algebra.QuasiFinite R S
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
theorem UpperTheory.Gal.G3.jSplitDesc :
    SplitDesc := by
  intro Z Y W s c _ _ _ J _ σ hs
  obtain ⟨hσ, hiso⟩ := hs
  haveI : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have key : pullback.snd s c =
      inv (Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hσ j, Category.id_comp])) ≫
        Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W := by
    rw [IsIso.eq_inv_comp]
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc_assoc, pullback.lift_snd, Sigma.ι_desc]
  haveI : IsFinite (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) := isFinite_desc W J
  haveI : Etale (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) :=
    IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  haveI : IsFinite (pullback.snd s c) := by rw [key]; infer_instance
  haveI : Etale (pullback.snd s c) := by rw [key]; infer_instance
  have hpb := IsPullback.of_hasPullback s c
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) c :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  haveI : IsProper s := isProper_desc hpb
  have hE : Etale s := of_isPullback_of_descendsAlong hpb.flip hQ (inferInstanceAs (Etale (pullback.snd s c)))
  haveI := hE
  haveI := locallyQuasiFinite_of_etale s
  exact ⟨(IsFinite.iff_isProper_and_locallyQuasiFinite s).mpr ⟨inferInstance, inferInstance⟩, hE⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasicHolds
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct

universe u v

namespace UpperTheory.Gal.G3

theorem isoPts_holds : IsoPts := @pIsoPts

theorem ptsOfSplits_holds : PtsOfSplits := @pPtsOfSplits

theorem splitsPts_holds : SplitsPts := pSplitsPts isoPts_holds

theorem extPts_holds : ExtPts := @pExtPts

theorem fEtBasic_holds : FEtBasic := pFEtBasic ptsOfSplits_holds

theorem splitsBasic_holds : SplitsBasic := pSplitsBasic splitsPts_holds ptsOfSplits_holds

theorem splitsComp_holds : SplitsComp := pSplitsComp splitsPts_holds ptsOfSplits_holds

theorem bcSplits_holds : BcSplits := @pBcSplits @splitsBasic_holds

theorem bcGal_holds : BcGal := pBcGal bcSplits_holds

theorem ordStep_holds : OrdStep := @pOrdStep

theorem ordEx_holds : OrdEx := pOrdEx ordStep_holds

theorem galClosD_holds : GalClosD := pGalClosD splitsPts_holds ordEx_holds

theorem galClos_holds : GalClos := pGalClos galClosD_holds

theorem multiSplit_holds : MultiSplit := pMultiSplit fEtBasic_holds splitsBasic_holds galClosD_holds

theorem algIsoPts_holds : AlgIsoPts := pAlgIsoPts isoPts_holds

theorem algSplit_holds : AlgSplit := @pAlgSplit @algIsoPts_holds

theorem algTr_holds : AlgTr := @pAlgTr

theorem hodgeFun_holds : ∀ (k : Type) [Field k] {Z Y W : Scheme.{0}} (p : Z ⟶ sp k) (q : Y ⟶ sp k) (r : W ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c), Splits s c σ → ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)), GlobalTheory.HodgeCoh.appSec p r c U (secTrace p q hU b) = ∑ j, GlobalTheory.CechDR.Sec.res r (GlobalTheory.GalTrace.preimage_le (hσ j) U) (GlobalTheory.HodgeCoh.appSec q r (σ j) (s ⁻¹ᵁ U) b) := pHodgeFun ptsOfSplits_holds algSplit_holds algTr_holds

theorem hodgeTr_holds : HodgeTr := @pHodgeTr @hodgeFun_holds

theorem hodgeInj_holds : HodgeInj := @pHodgeInj

theorem hodgeGood_holds : HodgeGood := @pHodgeGood @hodgeTr_holds @hodgeInj_holds

theorem etTr_holds : EtTr := @pEtTr

theorem etnGood_holds : EtnGood := @pEtnGood @fEtBasic_holds @etTr_holds

theorem etGood_holds : EtGood := @pEtGood @etnGood_holds

theorem bcGood_holds : BcGood.{u} := pBcGood bcSplits_holds bcGal_holds

theorem extTr_holds : ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L) :=
  @pExtTr.{u}

theorem extGood_holds : ExtGood.{u} := pExtGood extTr_holds

theorem opTr_holds : OpTr.{u} := @pOpTr.{u}

theorem opEx_holds : OpEx.{u} := pOpEx opTr_holds

theorem galInv_holds : GalInv.{u} := @pGalInv.{u}

theorem opEt_holds : OpEt := @pOpEt

theorem opBc_holds : OpBc.{u} := pOpBc bcSplits_holds bcGal_holds

theorem fEtInj_holds : FEtInj.{u} := pFEtInj galClosD_holds

theorem trBase_holds : TrBase.{u} := pTrBase fEtBasic_holds splitsBasic_holds galClosD_holds

theorem trPushM_holds : TrPushM.{u} := pTrPushM fEtBasic_holds splitsBasic_holds splitsComp_holds multiSplit_holds fEtInj_holds

theorem liesAbs_holds : LiesAbs.{u} := pLiesAbs fEtBasic_holds trBase_holds trPushM_holds

theorem hopSpec_holds : HopSpec := pHopSpec etGood_holds bcGood_holds galClos_holds opEx_holds opTr_holds opEt_holds opBc_holds bcSplits_holds

theorem liesGen_holds : LiesGen := @pLiesGen

theorem liesOp_holds : LiesOp.{u} := pLiesOp liesGen_holds liesAbs_holds

theorem coverInv_holds : CoverInv.{u} := pCoverInv galInv_holds splitsPts_holds

theorem pieceLe_holds : PieceLe := pPieceLe etGood_holds bcGood_holds extGood_holds extTr_holds hopSpec_holds coverInv_holds

theorem twSplit_holds : TwSplit := pTwSplit splitsPts_holds

theorem twGal_holds : TwGal := pTwGal twSplit_holds

end UpperTheory.Gal.G3
end

