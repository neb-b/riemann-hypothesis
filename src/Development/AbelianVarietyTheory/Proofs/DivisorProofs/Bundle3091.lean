module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2876
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionIdentityOfHodgeSummand
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTLieCrys

theorem isLieImage_sum {C : Type} [CommRing C] {A : Over (Sp C)} [GrpObj A] :
    ∀ (n : ℕ) (H : Fin n → HdR A) (u : Fin n → (epsR C ⟶ A)), (∀ i, IsLieImage (H i) (u i)) →
      IsLieImage (∑ i, H i) (List.ofFn u).prod
  | 0, H, u, _ => by
      simpa using (isLieImage_one_iff (A := A)).2 (zero_mem _)
  | n + 1, H, u, hu => by
      rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
      exact (hu 0).add (isLieImage_sum n _ _ fun i => hu i.succ)

theorem comp_listProd {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] {M X Y : 𝒞} [MonObj M]
    (f : X ⟶ Y) : ∀ (n : ℕ) (u : Fin n → (Y ⟶ M)),
      f ≫ (List.ofFn u).prod = (List.ofFn fun i => f ≫ u i).prod
  | 0, u => by simp
  | n + 1, u => by
      rw [List.ofFn_succ, List.prod_cons, MonObj.comp_mul, comp_listProd f n, List.ofFn_succ,
        List.prod_cons]

theorem one_left_eq {C : Type} [CommRing C] (A : Over (Sp C)) [GrpObj A] (x : Sp C ⟶ Sp C) (hx : x = 𝟙 (Sp C)) :
    (1 : Over.mk x ⟶ A).left = η[A].left := by
  have w := Over.w (toUnit (Over.mk x))
  rw [Hom.one_def, Over.comp_left]
  have e1 : (toUnit (Over.mk x)).left = x := by
    simpa using w
  rw [e1, hx]
  exact Category.id_comp _

def overId {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) : Over.mk q ⟶ Over.mk q' :=
  Over.homMk (𝟙 P) ((Category.id_comp q').trans h)

theorem overId_rfl {P S : Scheme.{0}} (q : P ⟶ S) : overId q q rfl = 𝟙 _ :=
  Over.OverMorphism.ext rfl

theorem overId_comp {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) (h' : q = q') :
    overId q' q h' ≫ overId q q' h = 𝟙 _ := by
  subst h
  rw [overId_rfl, Category.id_comp]

theorem overId_comp_left {T P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) {A : Over S}
    (f : Over.mk q' ⟶ A) (a : T ⟶ P) (b : T ⟶ A.left) (e : a ≫ f.left = b) :
    a ≫ (overId q q' h ≫ f).left = b := by
  subst h
  rw [overId_rfl, Category.id_comp]
  exact e

theorem overId_scal {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) {A : Over S}
    (f : Over.mk q' ⟶ A) (g : A ⟶ A) (a : P ⟶ P) (e : Over.mk q ⟶ Over.mk q) (he : e.left = a)
    (hf : (f ≫ g).left = a ≫ f.left) : (overId q q' h ≫ f) ≫ g = e ≫ overId q q' h ≫ f := by
  subst h
  subst he
  rw [overId_rfl, Category.id_comp]
  exact Over.OverMorphism.ext hf

theorem overId_scal_left {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) {A : Over S}
    (f : Over.mk q' ⟶ A) (g : A ⟶ A) (a : P ⟶ P) (e : Over.mk q' ⟶ Over.mk q') (he : e.left = a)
    (hf : f ≫ g = e ≫ f) : ((overId q q' h ≫ f) ≫ g).left = a ≫ (overId q q' h ≫ f).left := by
  subst h
  subst he
  rw [overId_rfl, Category.id_comp, hf]
  rfl

theorem epsPt_hq (C : Type) [CommRing C] :
    spMap (algebraMap C (DualNumber C)) ≫ spMap (RingHom.id C) = spMap (algebraMap C (DualNumber C)) := by
  rw [show spMap (RingHom.id C) = 𝟙 (Sp C) from Spec.map_id _, Category.comp_id]

theorem lieAt_id_of_liftFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) h → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) h) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) h) → GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h hA act hact hyp
  obtain ⟨g, hg⟩ := GlobalTheory.SemiAbelianDim.exists_relDim_of_isSemiAbelian C A
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA)
  have ADR := _root_.GlobalTheory.abelianDeRham
  obtain ⟨LE1, LE2⟩ : LieExact A := (ADR.2.1 C A g hA hg).1
  have bij : Function.Bijective (crysToDR (divided₂ hsq) h) :=
    GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective ADR.2.2.2.1 hA hg (isDPNilpotent_squareZero hsq) hπ rfl h
  have eqv : ∀ (c : D.O) (d : Crys (divided₂ hsq) (spMap π) o₀.A),
      (haveI := o₀.act.hom c; crysToDR (divided₂ hsq) h (push (divided₂ hsq) (spMap π) (o₀.act.act c) d)) =
      (haveI := act.hom c; push (dp0 C) (𝟙 _) (act.act c) (crysToDR (divided₂ hsq) h d)) := by
    intro c d
    haveI := o₀.act.hom c
    haveI := act.hom c
    exact crysToDR_push (divided₂ hsq) h h (o₀.act.act c) (act.act c) (hact c).symm d
  have hq := epsPt_hq C
  have one_left := one_left_eq A (spMap (RingHom.id C)) (Spec.map_id _)
  intro v hv
  obtain ⟨hv1, hv2⟩ := hv
  let v' : epsR C ⟶ A := overId _ _ hq ≫ v
  have tan' : IsTangent v' := overId_comp_left _ _ hq v _ _ (hv1.trans one_left)
  obtain ⟨H0, hH0⟩ := LE2 v' tan'
  obtain ⟨d, rfl⟩ := bij.2 H0
  have scal : v' ≫ act.act (algebraMap (𝓞 D.F) D.O D.ω) = GlobalTheory.GrpTangent.epsScale (tR b.ρ) ≫ v' :=
    overId_scal _ _ hq v _ _ _ (GlobalTheory.GrpTangent.epsScale_left _) hv2
  have hmem : (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
      push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) d) - tR b.ρ • d ∈
      liftFil (divided₂ hsq) h := by
    haveI := act.hom (algebraMap (𝓞 D.F) D.O D.ω)
    rw [liftFil, Submodule.mem_comap, map_sub, map_smul, eqv]
    have h1 := hH0.push (act.act (algebraMap (𝓞 D.F) D.O D.ω))
    rw [scal] at h1
    exact h1.sub_mem (hH0.smul (tR b.ρ))
  obtain ⟨w, hw, hsum⟩ := hyp d hmem
  have ex : ∀ j, ∃ u : epsR C ⟶ A, IsLieImage (crysToDR (divided₂ hsq) h (w j)) u :=
    fun j => (LE1 _).exists
  choose u hu using ex
  have hu_scal : ∀ j (c : 𝓞 D.F), u j ≫ act.act (algebraMap (𝓞 D.F) D.O c) =
      GlobalTheory.GrpTangent.epsScale (tR (b.t j c)) ≫ u j := by
    intro j c
    haveI := act.hom (algebraMap (𝓞 D.F) D.O c)
    have m := hw j c
    rw [liftFil, Submodule.mem_comap, map_sub, map_smul, eqv] at m
    have k2 := ((hu j).smul (tR (b.t j c))).add (isLieImage_one_iff.2 m)
    rw [_root_.mul_one, add_sub_cancel] at k2
    exact (LE1 _).unique ((hu j).push _) k2
  have hprod : v' = (List.ofFn u).prod := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [liftFil, Submodule.mem_comap, map_sub, map_sum] at hsum
    have k2 := (isLieImage_sum _ _ _ hu).add (isLieImage_one_iff.2 hsum)
    rw [_root_.mul_one, add_sub_cancel] at k2
    exact (LE1 _).unique hH0 k2
  refine ⟨fun j => overId _ _ hq.symm ≫ u j, fun j c => ⟨?_, ?_⟩, ?_⟩
  · exact overId_comp_left _ _ hq.symm (u j) _ _ (Eq.trans (hu j).1 one_left.symm)
  · exact overId_scal_left _ _ hq.symm (u j) _ _ _ (GlobalTheory.GrpTangent.epsScale_left _) (hu_scal j c)
  · have e1 : v = overId _ _ hq.symm ≫ v' := by
      show v = overId _ _ hq.symm ≫ (overId _ _ hq ≫ v)
      rw [← Category.assoc, overId_comp, Category.id_comp]
    rw [e1, hprod, comp_listProd]
end GlobalTheory.HTLieCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HTSummand.LieMod

variable {R : Type} [CommRing R]

def epsIso : epsR R ≅ GlobalTheory.UPel.HT.epsPtR (𝟙 (Sp R)) := Over.isoMk (Iso.refl _) (by simp)

@[simp] lemma epsIso_hom_left : (epsIso (R := R)).hom.left = 𝟙 _ := rfl
@[simp] lemma epsIso_inv_left : (epsIso (R := R)).inv.left = 𝟙 _ := rfl

lemma one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Scheme.{0}} (x : X ⟶ S) :
    (1 : Over.mk x ⟶ G).left = x ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

lemma comp_prod {S : Scheme.{0}} {G Y Z : Over S} [GrpObj G] (f : Z ⟶ Y) (l : List (Y ⟶ G)) :
    f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [MonObj.comp_mul, ih]

lemma isLieImage_sum {A : Over (Sp R)} [GrpObj A] : ∀ (n : ℕ) (u : Fin n → HdR A) (w : Fin n → (epsR R ⟶ A)),
    (∀ i, IsLieImage (u i) (w i)) → IsLieImage (∑ i, u i) (List.ofFn w).prod
  | 0, u, w, _ => by simpa using (isLieImage_one_iff (A := A)).2 (zero_mem _)
  | n + 1, u, w, h => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
    exact (h 0).add (isLieImage_sum n _ _ fun i => h i.succ)

lemma isLieImage_eq {A : Over (Sp R)} [GrpObj A] (H : LieExact A) {h h' : HdR A} {v v' : epsR R ⟶ A}
    (e : IsLieImage h v) (e' : IsLieImage h' v') (hd : h - h' ∈ Fil A) : v = v' := by
  have k : IsLieImage (h' + (h - h')) (v' * 1) := e'.add (isLieImage_one_iff.2 hd)
  rw [add_sub_cancel, _root_.mul_one] at k
  exact (H.1 h).unique e k

lemma tan_of {A : Over (Sp R)} [GrpObj A] {v : epsR R ⟶ A} (hv : IsTangent v) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (epsIso.inv ≫ v).left =
      (1 : Over.mk (𝟙 (Sp R)) ⟶ A).left := by
  rw [one_left, Category.id_comp, Over.comp_left, epsIso_inv_left, Category.id_comp]
  exact hv

lemma tan_to {A : Over (Sp R)} [GrpObj A] {w : GlobalTheory.UPel.HT.epsPtR (𝟙 (Sp R)) ⟶ A}
    (hw : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp R)) ⟶ A).left) :
    IsTangent (epsIso.hom ≫ w) := by
  rw [one_left, Category.id_comp] at hw
  show _ ≫ (epsIso.hom ≫ w).left = _
  rw [Over.comp_left, epsIso_hom_left, Category.id_comp]
  exact hw

end GlobalTheory.HTSummand.LieMod

namespace GlobalTheory.HTSummand


open LieMod in
theorem lie_mod_fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (β : R →+* C₀) (s : Sp C₀ ⟶ Sp R), s = spMap β → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N s) (y : HdR o₀.A), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) y - β b.ρ • y ∈ Fil o₀.A → ∃ w : Fin D.a → HdR o₀.A, (∀ i (c : 𝓞 D.F), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - β (b.t i c) • w i ∈ Fil o₀.A) ∧ y - ∑ i, w i ∈ Fil o₀.A := by
  intro p _ D R _ b N C₀ _ _ β s hs o₀ y hy
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A o₀.ab
  have H : LieExact o₀.A := (GlobalTheory.abelianDeRham.2.1 C₀ o₀.A g o₀.ab hg).1
  obtain ⟨v, hv, -⟩ := H.1 y
  set ωO := algebraMap (𝓞 D.F) D.O D.ω
  haveI := o₀.act.hom ωO
  have hω : v ≫ o₀.act.act ωO = GlobalTheory.GrpTangent.epsScale (β b.ρ) ≫ v :=
    isLieImage_eq H (hv.push (o₀.act.act ωO)) (hv.smul (β b.ρ)) hy
  have hx : 𝟙 (Sp C₀) ≫ s = spMap β := by rw [Category.id_comp, hs]
  have hvT : GlobalTheory.UPel.HT.IsTanScal o₀.act (𝟙 (Sp C₀)) ωO (β b.ρ) (epsIso.inv ≫ v) := by
    refine ⟨tan_of hv.1, ?_⟩
    rw [Category.assoc, Over.comp_left, hω, Over.comp_left, Over.comp_left, epsIso_inv_left, Category.id_comp,
      Category.id_comp, GlobalTheory.GrpTangent.epsScale_left]
  obtain ⟨w, hw, hprod⟩ := o₀.lie C₀ β (𝟙 (Sp C₀)) hx (epsIso.inv ≫ v) hvT
  have hwT : ∀ i, IsTangent (epsIso.hom ≫ w i) := fun i => tan_to (hw i 0).1
  choose u hu using fun i => H.2 _ (hwT i)
  refine ⟨u, fun i c => ?_, ?_⟩
  · haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c)
    have e : (epsIso.hom ≫ w i) ≫ o₀.act.act (algebraMap (𝓞 D.F) D.O c) =
        GlobalTheory.GrpTangent.epsScale (β (b.t i c)) ≫ epsIso.hom ≫ w i := by
      ext1
      simp only [Over.comp_left, epsIso_hom_left, Category.id_comp, GlobalTheory.GrpTangent.epsScale_left]
      rw [← Over.comp_left]
      exact (hw i c).2
    have k₁ := (hu i).push (o₀.act.act (algebraMap (𝓞 D.F) D.O c))
    rw [e] at k₁
    exact k₁.sub_mem ((hu i).smul (β (b.t i c)))
  · have k := isLieImage_sum D.a u _ hu
    have e : (List.ofFn fun i => epsIso.hom ≫ w i).prod = v := by
      rw [show (List.ofFn fun i => epsIso.hom ≫ w i) = (List.ofFn w).map (epsIso.hom ≫ ·) from
        List.map_ofFn.symm, ← comp_prod, ← hprod, Iso.hom_inv_id_assoc]
    rw [e] at k
    exact hv.sub_mem k

end GlobalTheory.HTSummand
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationPairingNondegenerate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTPolPair
open GlobalTheory.AbDual

theorem nondeg : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ x, (∀ y, φ x y = 0) → x = 0 := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β ht φ hφ x hx
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  let A' : GlobalTheory.AV.AbVar k := ⟨o₀.A, o₀.ab, g, hg⟩
  obtain ⟨B, P₀, ⟨h1, h2⟩, hdim⟩ := GlobalTheory.AV.exists_dualPair k A'
  have hgB : SmoothOfRelativeDimension g B.X.hom := by
    have := B.smooth; rw [hdim] at this; exact this
  obtain ⟨l, hl, hlP⟩ := _root_.GlobalTheory.BirigidHom.exists_hom_of_triv k o₀.A B.X o₀.ab B.ab P₀ h1 o₀.P o₀.isLB o₀.rig₁ o₀.rig₂
  obtain ⟨iso, hker⟩ := GlobalTheory.T.poincareBundleIso_swap_trivial_of_kernelPoint k o₀.A B.X P₀ h1 o₀.P o₀.isLB o₀.symm l hlP
  obtain ⟨e, he, hkP⟩ := o₀.kerP
  have hu : IsUnit (e : k) := by
    have := (b.unit e he).map β
    simpa using this
  obtain ⟨m, hm, hlm⟩ := _root_.GlobalTheory.AV.exists_comp_eq_pow_of_ker_killed k o₀.A B.X g o₀.ab B.ab hg hgB l hl e hu fun T y hy => hkP T y (hker T y hy)
  have hPf : IsPerfect B.X o₀.A (swap P₀) := (IsDual.isPerfect h1 h2).swap
  have CAA := cupSquare_of_free GlobalTheory.abelianDeRham.1 (AbelianSchemeGerms.isAbelianScheme_tensor o₀.A o₀.A o₀.ab o₀.ab)
    (smooth_prod hg hg)
  have CBA := cupSquare_of_free GlobalTheory.abelianDeRham.1 (AbelianSchemeGerms.isAbelianScheme_tensor B.X o₀.A B.ab o₀.ab)
    (smooth_prod hgB hg)
  obtain ⟨φ', hφ'⟩ := exists_isCorrForm CBA hPf.isLB hPf.zero_left hPf.zero_right
  have hadj := IsCorrForm.adjoint CAA o₀.isLB hPf.isLB hφ hφ' l (𝟙 o₀.A) iso
  have perf := (IsCorrForm.perfect GlobalTheory.abelianDeRham B.ab hgB o₀.ab hg hPf hφ').1
  have h0 : push (dp0 k) (𝟙 _) l x = 0 := by
    refine (injective_iff_map_eq_zero _).1 perf.bijective_left.1 _ (LinearMap.ext fun y => ?_)
    rw [← hadj x y, push_id]
    exact hx y

  have hpowM : ∀ j : ℕ, IsMonHom (𝟙 o₀.A ^ j) := by
    intro j
    induction j with
    | zero => rw [pow_zero]; exact isMonHom_one o₀.A o₀.A
    | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift (𝟙 o₀.A ^ n) (𝟙 o₀.A) ≫ μ[o₀.A]))
  have hpush : ∀ j : ℕ, push (dp0 k) (𝟙 _) (𝟙 o₀.A ^ j) = (j : k) • LinearMap.id := by
    intro j
    induction j with
    | zero =>
      rw [push_congr (dp0 k) (𝟙 _) (pow_zero (𝟙 o₀.A)), push_one]
      simp
    | succ n ih =>
      haveI := hpowM n
      haveI : IsMonHom (𝟙 o₀.A ^ n * 𝟙 o₀.A) := by rw [← pow_succ]; exact hpowM (n + 1)
      rw [push_congr (dp0 k) (𝟙 _) (pow_succ (𝟙 o₀.A) n), push_mul, ih, push_id]
      push_cast
      rw [add_smul, one_smul]
  haveI := hpowM e
  have key : push (dp0 k) (𝟙 _) m (push (dp0 k) (𝟙 _) l x) = (e : k) • x := by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr (dp0 k) (𝟙 _) hlm, hpush]
    rfl
  rw [h0, map_zero] at key
  exact (hu.smul_eq_zero.1 key.symm)

end GlobalTheory.HTPolPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem has_of_hasFin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)), HasFin D → Has D := by
  intro R _ _ _ hR D ⟨R', _, _, _, ρ, D', hρ, ⟨p⟩, hH⟩
  obtain ⟨R'', _, _, _, σ, hσ, hσl, hc, hg⟩ := _root_.GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom R R' ρ hR hρ
  obtain ⟨D'', ⟨q⟩⟩ := _root_.GlobalTheory.MumPull.exists_pull R' R'' σ hσ.2.1 hσl D'
  obtain ⟨G'', _, _, A'', hG, ⟨U⟩⟩ := _root_.GlobalTheory.Mum.has_pull R' R'' σ hρ.1 hσ.1 hσ.2.1 hσl D' D'' ⟨q⟩ hH
  obtain ⟨r⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hρ.2.1 hσ.2.1 p q
  obtain ⟨act⟩ := _root_.GlobalTheory.Mum.galAct_exists R R'' (σ.comp ρ) hR hc hg D D'' r A'' G'' hG U
  exact _root_.GlobalTheory.Mum.has_of_galois_action R R'' (σ.comp ρ) hR hc hg D D'' r A'' G'' hG U act

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftDeterminesModFil
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KSGraph

theorem connectedSpace_sp_dualNumber (k : Type) [Field k] : ConnectedSpace (Sp (DualNumber k)) := by
  change ConnectedSpace (PrimeSpectrum (DualNumber k))
  have : PreconnectedSpace (PrimeSpectrum (DualNumber k)) := by
    refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint (DualNumber k)) fun y _ ↦
      ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
    exact (IsLocalRing.specializes_closedPoint y).mem_closure
  exact ⟨inferInstance⟩

theorem exists_dim {k : Type} [Field k] (A' : Over (Sp (DualNumber k))) [GrpObj A']
    (hA' : IsAbelianScheme A') : ∃ g, SmoothOfRelativeDimension g A'.hom := by
  have := hA'.smooth
  have := hA'.geomConnected
  have := connectedSpace_sp_dualNumber k
  have : ConnectedSpace A'.left := GeometricallyConnected.connectedSpace A'.hom A'.hom.isOpenMap
  exact exists_dim_of_preconnected A'.hom (Classical.arbitrary _)

theorem isFilLift_iff_sub_mem : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A' : Over (Sp (DualNumber k))) [GrpObj A'] (i : A₀.left ⟶ A'.left) (h : IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i), IsAbelianScheme A' → ∀ x ∈ Fil A₀, ∀ y y' : HdR A₀, IsFilLift h x y → (IsFilLift h x y' ↔ y' - y ∈ Fil A₀) := by
  intro k _ A₀ _ A' _ i h hA' x hx y y' hy
  obtain ⟨g, hg⟩ := exists_dim A' hA'
  have P := GlobalTheory.abelianDeRham
  have hA₀ : IsAbelianScheme A₀ := by
    have := hA'.comm
    have hc : IsCommMonObj A₀ := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA'.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hA'.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA'.geomConnected⟩
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  have hL := (P.2.1 k A₀ g hA₀ g₀).1
  have reg := ksRegular_of_isAbelianScheme P h hA' hg
  constructor
  · intro hy'
    obtain ⟨w, hw, -⟩ := hL.1 y
    obtain ⟨w', hw', -⟩ := hL.1 y'
    have e := (reg x hx).unique ⟨y, hy, hw⟩ ⟨y', hy', hw'⟩
    subst e
    exact hw'.sub_mem hw
  · intro hz
    obtain ⟨v, ⟨z, hz', -⟩, -⟩ := reg (y' - y) hz
    obtain ⟨d, hd, e⟩ := hy
    obtain ⟨d', hd', e'⟩ := hz'
    refine ⟨d + (TrivSqZeroExt.inr 1 : DualNumber k) • d', add_mem hd (Submodule.smul_mem _ _ hd'), fun c ↦ ?_⟩
    rw [LinearMap.add_apply, LinearMap.smul_apply, e, e', smul_eq_mul]
    ext <;> simp

end GlobalTheory.KSGraph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceEtale
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.HomotopyInv

variable {R : Type} [CommRing R]

attribute [local instance] Polynomial.algebra

theorem eqv_baseChange (q : ℕ) (A : Type) [CommRing A] (i : ℤ) (A' : Type) [CommRing A']
    (s : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A))
    (h : Eqv _ (spMap (Polynomial.C : A' →+* Polynomial A')) (tw q i)) :
    Eqv _ (sch.map (pullback.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 _) s (𝟙 _) s
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) := by
  first
  | exact @_root_.GlobalTheory.PolynomialPushoutEquivalence.main
  | exact _root_.GlobalTheory.PolynomialPushoutEquivalence.main
  | (apply _root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialPushoutEquivalence.main ..)

theorem homotopy_invariance_etale : GlobalTheory.EtC.C4 := by
  intro q _ A _ hq i
  have hqΓ : IsUnit ((q : ℕ) : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  refine GlobalTheory.T.etC_b3 q (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))
    (𝟙 (Spec (CommRingCat.of A))) hqΓ i ?_
  intro A' _ s hA'
  refine eqv_baseChange q A i A' s ?_
  have hq' : IsUnit (q : A') := by simpa using hq.map (Spec.preimage s).hom
  exact GlobalTheory.T.homotopyInvariance_tateTwist_strictlyHenselian q A' hA' hq' i

end GlobalTheory.EtC.HomotopyInv
end
end

