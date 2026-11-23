module

public import Development.EtaleCohomology.CohomologicalPurity.LeafDictPf
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0006
public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0010
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0005

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafEvPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.KummerTheory.FlasquePf

namespace LateralTheory.CohomologicalPurity.DictPf

section
variable {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}}

theorem ev_res' (m : (free R).obj (yoneda.obj X) ⟶ G) {V : Scheme.{0}} (h : V ⟶ X) :
    (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V h) = Sec.res h (ev m) := by
  calc (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V h)
      = (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V ((yoneda.obj X).map h.op (𝟙 X))) := by simp
    _ = (m.hom.app (op V)).hom (Sec.res h (freeGen R (yoneda.obj X) X (𝟙 X))) := by rw [freeGen_res]
    _ = Sec.res h (ev m) := by
      have := congrArg (fun φ => ModuleCat.Hom.hom φ (freeGen R (yoneda.obj X) X (𝟙 X))) (m.hom.naturality h.op)
      exact this

theorem eq_ofSec (m : (free R).obj (yoneda.obj X) ⟶ G) : m = ofSec G (ev m) := by
  apply ((sheafificationAdjunction _ _).homEquiv _ G).injective
  unfold ofSec
  rw [Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  apply ModuleCat.free_hom_ext
  intro x
  change (m.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down) = _
  rw [ev_res']
  unfold toG
  symm
  change ModuleCat.freeDesc _ (ModuleCat.freeMk x) = _
  refine (ModuleCat.freeDesc_apply _ _).trans ?_
  rfl

end

theorem LeafEv_of : LeafEv := by
  intro R _ G X
  refine ⟨?_, ?_, ?_⟩
  · intro m m' h
    rw [eq_ofSec m, eq_ofSec m', h]
  · intro m m'
    rfl
  · intro Y f m
    change (m.hom.app (op Y)).hom ((((free R).map (yoneda.map f)).hom.app (op Y)).hom
      (freeGen R (yoneda.obj Y) Y (𝟙 Y))) = _
    rw [freeGen_map]
    simp only [yoneda_map_app]
    exact ev_res' m f

end LateralTheory.CohomologicalPurity.DictPf
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafExcIdentPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

theorem HK.pull_sub' (R : Type) [CommRing R] {K L : Cx R} (f g : K ⟶ L) (F : Shv R) (n : ℤ)
    (x : HK R L F n) : HK.pull R (f - g) F n x = HK.pull R f F n x - HK.pull R g F n x := by
  rcases x.mk_surjective with ⟨z, rfl⟩
  simp only [HK.pull, HK.pre, cpre_mk]
  rw [← CohomologyClass.mk_sub]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_sub, Cochain.sub_comp]

theorem HK.pull_zero' (R : Type) [CommRing R] {K L : Cx R} (F : Shv R) (n : ℤ)
    (x : HK R L F n) : HK.pull R (0 : K ⟶ L) F n x = 0 := by
  have h := HK.pull_sub' R (0 : K ⟶ L) 0 F n x
  rw [sub_self, sub_self] at h
  exact h

def secC (q : ℕ) (P : Arrow Spc) :
    cokernel ((chains (ZMod q)).map (dbl.inr P)) ⟶ (chains (ZMod q)).obj (dbl P) :=
  cokernel.desc _ (𝟙 _ - (chains (ZMod q)).map (dbl.fold P) ≫ (chains (ZMod q)).map (dbl.inr P)) (by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, ← Functor.map_comp, dbl.inr_fold,
      CategoryTheory.Functor.map_id, Category.id_comp, sub_self])

theorem pi_secC (q : ℕ) (P : Arrow Spc) :
    cokernel.π ((chains (ZMod q)).map (dbl.inr P)) ≫ secC q P =
      𝟙 _ - (chains (ZMod q)).map (dbl.fold P) ≫ (chains (ZMod q)).map (dbl.inr P) := by
  simp [secC]

theorem secC_pi (q : ℕ) (P : Arrow Spc) :
    secC q P ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr P)) = 𝟙 _ := by
  rw [← cancel_epi (cokernel.π _), ← Category.assoc, pi_secC, Category.comp_id, Preadditive.sub_comp,
    Category.id_comp, Category.assoc, cokernel.condition, Limits.comp_zero, sub_zero]

def eHom (q : ℕ) (n i : ℤ) (P : Arrow Spc) :
    HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n →+ Hs q P n i :=
  (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n).codRestrict _ fun x => by
    change HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.inr P)) (tw q i) n
      (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n x) = 0
    rw [← HK.pull_comp', cokernel.condition, HK.pull_zero']

def eEquiv (q : ℕ) (n i : ℤ) (P : Arrow Spc) :
    HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n ≃+ Hs q P n i where
  toFun := eHom q n i P
  invFun y := HK.pull (ZMod q) (secC q P) (tw q i) n y.1
  left_inv x := by
    change HK.pull (ZMod q) (secC q P) (tw q i) n
      (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n x) = x
    rw [← HK.pull_comp', secC_pi, HK.pull_id']
  right_inv y := by
    apply Subtype.ext
    change HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n
      (HK.pull (ZMod q) (secC q P) (tw q i) n y.1) = y.1
    have hy : HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.inr P)) (tw q i) n y.1 = 0 := y.2
    rw [← HK.pull_comp', pi_secC, HK.pull_sub', HK.pull_id', HK.pull_comp', hy, map_zero, sub_zero]
  map_add' := map_add _

theorem EtaleExcIdent : LeafExcIdent := by
  intro q n i
  refine ⟨eEquiv q n i, fun {P' P} φ x => ?_⟩
  apply Subtype.ext
  change HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.map φ)) (tw q i) n
      (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n x) =
    HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P'))) (tw q i) n
      (HK.pull (ZMod q) (cokC q φ) (tw q i) n x)
  rw [← HK.pull_comp', ← HK.pull_comp']
  congr 2
  simp [cokC]

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafExcLevelPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def MM {P' P : Arrow Spc} (φ : P' ⟶ P) : Spc := pushout P'.hom (P'.hom ≫ φ.right)

def gM {P' P : Arrow Spc} (φ : P' ⟶ P) : MM φ ⟶ dbl P :=
  pushout.desc (φ.right ≫ dbl.inl P) (dbl.inr P) (by
    rw [← Category.assoc, ← Arrow.w φ, Category.assoc, Category.assoc]
    exact congrArg (φ.left ≫ ·) (pushout.condition (f := P.hom) (g := P.hom)))

def LeafExcOfEqv : Prop := ∀ (q : ℕ) (P' P : Arrow Spc) (φ : P' ⟶ P), (∀ i, Eqv (ZMod q) (gM φ) (tw q i)) → Exc q φ

def LeafEqvOfExc : Prop := ∀ (q : ℕ) (P' P : Arrow Spc) (φ : P' ⟶ P), Exc q φ → ∀ i, Eqv (ZMod q) (gM φ) (tw q i)

def LeafMLev : Prop := ∀ (P' P : Arrow Spc) (φ : P' ⟶ P) (n : SimplexCategoryᵒᵖ),
  ∃ (a : disc.obj ((MM φ).obj n) ≅ MM ((lev n).map φ)) (b : disc.obj ((dbl P).obj n) ≅ dbl ((lev n).obj P)),
    disc.map ((gM φ).app n) ≫ b.hom = a.hom ≫ gM ((lev n).map φ)

theorem LeafExcLevel_of (h1 : LeafExcOfEqv) (h2 : LeafEqvOfExc) (h3 : LeafMLev) : LeafExcLevel := by
  intro a3 q P' P φ hl
  apply h1 q P' P φ
  intro i
  apply a3
  intro n
  obtain ⟨a, b, w⟩ := h3 P' P φ n
  have e : disc.map ((gM φ).app n) = a.hom ≫ gM ((lev n).map φ) ≫ b.inv := by
    rw [← Category.assoc, ← w, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]
  exact eqv_comp (eqv_iso _ _) (eqv_comp (h2 q _ _ _ (hl n) i) (eqv_iso _ _))

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafExcPPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP

def LeafFive : Prop := ∀ δ, IsBd δ → ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), Mono P'.hom → Mono P.hom →
  (∀ i, Eqv _ φ.left (tw q i)) → (∀ i, Eqv _ φ.right (tw q i)) → Exc q φ

def LeafChartFact : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
  (I : Ideal (MvPolynomial (Fin d) R)), Ideal.span (Set.range MvPolynomial.X) = I → IsUnit (q : R) →
  ∀ Φ : opn (off (MvPolynomial (Fin d) R) I) ⟶ pr d R,
  Φ.right = (prod.lift (Pj.pt (vec1 MvPolynomial.X)) (spMap MvPolynomial.C) :
    sp (MvPolynomial (Fin d) R) ⟶ PR (d + 1) 0 R) →
  ∃ (P : Arrow Spc) (α : opn (off (MvPolynomial (Fin d) R) I) ⟶ P) (β : P ⟶ pr d R), α ≫ β = Φ ∧
    Mono (opn (off (MvPolynomial (Fin d) R) I)).hom ∧ Mono P.hom ∧
    (∀ i, Eqv _ α.left (tw q i)) ∧ (∀ i, Eqv _ α.right (tw q i)) ∧
    IsPullback P.hom β.left β.right (pr d R).hom ∧ Cover2 (ZMod q) β.right (pr d R).hom

theorem dbl_hom_ext {P : Arrow Spc} {X : Spc} {f g : dbl P ⟶ X} (h0 : dbl.inl P ≫ f = dbl.inl P ≫ g)
    (h1 : dbl.inr P ≫ f = dbl.inr P ≫ g) : f = g := pushout.hom_ext h0 h1

theorem dbl_map_comp {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) :
    dbl.map (α ≫ β) = dbl.map α ≫ dbl.map β := by
  apply dbl_hom_ext
  · rw [inl_map, ← Category.assoc, inl_map, Category.assoc, inl_map, Arrow.comp_right, Category.assoc]
  · rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, Arrow.comp_right, Category.assoc]

theorem pull_comp_apply (q : ℕ) {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q (α ≫ β) n i x = Hs.pull q α n i (Hs.pull q β n i x) := by
  apply Subtype.ext
  change GlobalTheory.EtC.pull _ (dbl.map (α ≫ β)) _ n x.1 = GlobalTheory.EtC.pull _ (dbl.map α) _ n (GlobalTheory.EtC.pull _ (dbl.map β) _ n x.1)
  rw [dbl_map_comp, pull_comp]

theorem exc_comp (q : ℕ) {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) (hα : Exc q α) (hβ : Exc q β) :
    Exc q (α ≫ β) := fun n i => by
  have : (Hs.pull q (α ≫ β) n i : Hs q P n i → Hs q P'' n i) = Hs.pull q α n i ∘ Hs.pull q β n i :=
    funext (pull_comp_apply q α β n i)
  rw [this]
  exact (hα n i).comp (hβ n i)

theorem fgt_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = GlobalTheory.EtC.pull _ φ.right _ n (Hs.fgt q P n i x) := by
  change GlobalTheory.EtC.pull _ (dbl.inl P') _ n (GlobalTheory.EtC.pull _ (dbl.map φ) _ n x.1) =
    GlobalTheory.EtC.pull _ φ.right _ n (GlobalTheory.EtC.pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, inl_map, pull_comp]

theorem res_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (c : Ht q P.right n i) :
    GlobalTheory.EtC.pull _ P'.hom (tw q i) n (GlobalTheory.EtC.pull _ φ.right _ n c) =
      GlobalTheory.EtC.pull _ φ.left _ n (GlobalTheory.EtC.pull _ P.hom (tw q i) n c) := by
  rw [← pull_comp, ← pull_comp, Arrow.w φ]

theorem five (δ : ∀ (q : ℕ) (P : Arrow Spc) (n i : ℤ), Ht q P.left n i →+ Hs q P (n + 1) i) (hδ : IsBd δ)
    (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (h' : Mono P'.hom) (h : Mono P.hom)
    (hl : ∀ i, Eqv _ φ.left (tw q i)) (hr : ∀ i, Eqv _ φ.right (tw q i)) (m i : ℤ) :
    Function.Bijective (Hs.pull q φ (m + 1) i) := by
  obtain ⟨hex, hnat, -⟩ := hδ
  obtain ⟨-, e2, e3⟩ := hex q P h m i
  obtain ⟨-, e2', e3'⟩ := hex q P' h' m i
  obtain ⟨e1, -, -⟩ := hex q P h (m + 1) i
  obtain ⟨e1', -, -⟩ := hex q P' h' (m + 1) i
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hf : Hs.fgt q P (m + 1) i x = 0 := by
      apply (hr i (m + 1)).1
      rw [← fgt_pull, hx, map_zero, map_zero]
    obtain ⟨u, rfl⟩ := (e3 x).1 hf
    have hu : δ q P' m i (GlobalTheory.EtC.pull _ φ.left _ m u) = 0 := by rw [← hnat q P' P φ h' h m i u]; exact hx
    obtain ⟨w', hw'⟩ := (e2' _).1 hu
    obtain ⟨w, rfl⟩ := (hr i m).2 w'
    rw [res_pull] at hw'
    have := (hl i m).1 hw'
    rw [← this]
    exact (e2 _).2 ⟨w, rfl⟩
  · intro y
    obtain ⟨c, hc⟩ := (hr i (m + 1)).2 (Hs.fgt q P' (m + 1) i y)
    have hc0 : GlobalTheory.EtC.pull _ P.hom (tw q i) (m + 1) c = 0 := by
      apply (hl i (m + 1)).1
      rw [← res_pull, hc, map_zero]
      exact (e1' _).2 ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := (e1 c).1 hc0
    have hd : Hs.fgt q P' (m + 1) i (y - Hs.pull q φ (m + 1) i x) = 0 := by
      rw [map_sub, fgt_pull, hx, hc, sub_self]
    obtain ⟨u', hu'⟩ := (e3' _).1 hd
    obtain ⟨u, rfl⟩ := (hl i m).2 u'
    refine ⟨x + δ q P m i u, ?_⟩
    rw [map_add (f := _), hnat q P' P φ h' h m i u, hu', add_sub_cancel]

theorem leafFive : LeafFive := by
  intro δ hδ q P' P φ h' h hl hr n i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  exact five δ hδ q φ h' h hl hr m i

end LateralTheory.CohomologicalPurity.Thom.ExcP

namespace LateralTheory.CohomologicalPurity.Thom

theorem excision_of_thom_chart_factorization (hBd : LeafBd) (hSp : LeafExcSp) (hFact : ExcP.LeafChartFact) :
    LeafExcP := by
  intro hH q _ d R _ I hI hq Φ hΦ
  obtain ⟨δ, hδ⟩ := hBd
  obtain ⟨P, α, β, hαβ, hm1, hm2, hl, hr, hpb, hcov⟩ := hFact hH q d R I hI hq Φ hΦ
  rw [← hαβ]
  exact ExcP.exc_comp q α β (ExcP.leafFive δ hδ q α hm1 hm2 hl hr) (hSp hH.1 q β hpb hcov)

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafExcSpPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem sqw {R : Type} [CommRing R] {K L K' L' : Cx R} {f : K ⟶ L} {f' : K' ⟶ L'} {a : K ⟶ K'} {b : L ⟶ L'}
    (comm : f ≫ b = a ≫ f') (n : ℤ) : f.f n ≫ b.f n = a.f n ≫ f'.f n := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, comm]

theorem chains_sq (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    (chains R).map P'.hom ≫ (chains R).map φ.right = (chains R).map φ.left ≫ (chains R).map P.hom := by
  rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg (chains R).map (Arrow.w φ).symm

def coneMap (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    CochainComplex.mappingCone ((chains R).map P'.hom) ⟶ CochainComplex.mappingCone ((chains R).map P.hom) :=
  CochainComplex.mappingCone.map _ _ ((chains R).map φ.left) ((chains R).map φ.right) (chains_sq R φ)

def LeafConeQI : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsPullback P'.hom φ.left φ.right P.hom →
  Cover2 (ZMod q) φ.right P.hom → QuasiIso (coneMap (ZMod q) φ)

def LeafHsRel : Prop := A1 → ∀ (q : ℕ) (i : ℤ), ∃ e : ∀ (P : Arrow Spc) (n : ℤ), Mono P.hom →
    (Hs q P n i ≃+ Hrel (ZMod q) P.hom (tw q i) n),
  ∀ (P' P : Arrow Spc) (φ : P' ⟶ P) (h' : Mono P'.hom) (h : Mono P.hom) (n : ℤ) (x : Hs q P n i),
    e P' n h' (Hs.pull q φ n i x) = HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n (e P n h x)

def LeafChainsMono : Prop := ∀ (R : Type) [CommRing R] {E' E : Spc} (f : E' ⟶ E), Mono f → ∀ n : ℤ, Mono (((chains R).map f).f n)

def LeafCokIso : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsPullback P'.hom φ.left φ.right P.hom →
  Cover2 (ZMod q) φ.right P.hom → ∀ n : ℤ,
  IsIso (cokernel.map _ _ _ _ (sqw (chains_sq (ZMod q) φ) n))

def LeafConeCok : Prop := ∀ (R : Type) [CommRing R] {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L')
  (a : K ⟶ K') (b : L ⟶ L') (comm : f ≫ b = a ≫ f'), (∀ n, Mono (f.f n)) → (∀ n, Mono (f'.f n)) →
  (∀ n, IsIso (cokernel.map _ _ _ _ (sqw comm n))) → QuasiIso (CochainComplex.mappingCone.map f f' a b comm)

theorem leafExcSp_of (hQ : LeafConeQI) (hR : LeafHsRel) : LeafExcSp := by
  intro h1 q P' P φ hpb hc n i
  have hm : Mono P.hom := hc.2.1
  have hm' : Mono P'.hom := hpb.mono_fst_of_mono
  obtain ⟨e, he⟩ := hR h1 q i
  have := hQ q φ hpb hc
  have hb : Function.Bijective (HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n) := h1 (ZMod q) _ (tw q i) n
  have : (Hs.pull q φ n i : Hs q P n i → Hs q P' n i) =
      (e P' n hm').symm ∘ HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n ∘ e P n hm := by
    funext x
    simp [← he P' P φ hm' hm n x]
  rw [this]
  exact (e P' n hm').symm.bijective.comp (hb.comp (e P n hm).bijective)

theorem leafConeQI_of (hM : LeafChainsMono) (hK : LeafCokIso) (hC : LeafConeCok) : LeafConeQI := by
  intro q P' P φ hpb hc
  have hm : Mono P.hom := hc.2.1
  have hm' : Mono P'.hom := hpb.mono_fst_of_mono
  exact hC (ZMod q) _ _ _ _ (chains_sq (ZMod q) φ) (hM _ _ hm') (hM _ _ hm) (hK q φ hpb hc)

theorem leafExcSp_of' (hM : LeafChainsMono) (hK : LeafCokIso) (hC : LeafConeCok) (hR : LeafHsRel) : LeafExcSp :=
  leafExcSp_of (leafConeQI_of hM hK hC) hR

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def pcok (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A) (b : B' ⟶ B)
    (w : i' ≫ b = a ≫ i) : cokernel ((freeP R).map i') ⟶ cokernel ((freeP R).map i) :=
  cokernel.map _ _ ((freeP R).map a) ((freeP R).map b) (by rw [← Functor.map_comp, ← Functor.map_comp, w])

theorem isIso_cokernel_map_of_etale_local_iso (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i) (hW : Scheme.etaleTopology.W (pcok R i' i a b w)) :
    IsIso (cokernel.map ((free R).map i') ((free R).map i) ((free R).map a) ((free R).map b)
      (by rw [← Functor.map_comp, ← Functor.map_comp, w])) := by
  rw [GrothendieckTopology.W_iff] at hW
  let G := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  have w' : (freeP R).map i' ≫ (freeP R).map b = (freeP R).map a ≫ (freeP R).map i := by
    rw [← Functor.map_comp, ← Functor.map_comp, w]
  have key := cokernel_map_comp_cokernelComparison ((freeP R).map i') G ((freeP R).map i) ((freeP R).map a)
    ((freeP R).map b) w'
  have h2 : IsIso (cokernelComparison ((freeP R).map i') G ≫ G.map (pcok R i' i a b w)) := by
    have : IsIso (G.map (pcok R i' i a b w)) := hW
    infer_instance
  have h3 : IsIso (cokernel.map (G.map ((freeP R).map i')) (G.map ((freeP R).map i)) (G.map ((freeP R).map a))
      (G.map ((freeP R).map b)) (by rw [← G.map_comp, w', G.map_comp])) := by
    have h4 : IsIso (cokernel.map (G.map ((freeP R).map i')) (G.map ((freeP R).map i)) (G.map ((freeP R).map a))
      (G.map ((freeP R).map b)) (by rw [← G.map_comp, w', G.map_comp]) ≫ cokernelComparison _ G) := by
      rw [key]; exact h2
    exact IsIso.of_isIso_comp_right _ (cokernelComparison ((freeP R).map i) G)
  exact h3

def LeafFreeCokSurj : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
    (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y) →
  Presheaf.IsLocallySurjective Scheme.etaleTopology (pcok R i' i a b w)

def LeafFreeCokInj : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B'.obj (op T)) (x : A.obj (op T)), i.app (op T) x = b.app (op T) y →
    ∃ x' : A'.obj (op T), i'.app (op T) x' = y) →
  (∀ (T : Scheme.{0}) (y₁ y₂ : B'.obj (op T)), b.app (op T) y₁ = b.app (op T) y₂ →
    ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      B'.map g.op y₁ = B'.map g.op y₂ ∨ ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op y₁)) →
  Presheaf.IsLocallyInjective Scheme.etaleTopology (pcok R i' i a b w)

theorem LeafFreeCok_of (hS : LeafFreeCokSurj) (hI : LeafFreeCokInj) : LeafFreeCok := by
  intro R _ A' B' A B i' i a b w h1 h2 h3
  apply isIso_cokernel_map_of_etale_local_iso
  have := hS R i' i a b w h2
  have := hI R i' i a b w h1 h3
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafLevelPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.LeafLevelPf
open LateralTheory.CohomologicalPurity.TubeCut

variable {J : Type} [SmallCategory J]

theorem elt_eqToHom {F : J ⥤ Type} {a b : F.Elements} (h : a = b) :
    (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by subst h; rfl

theorem chn_eq (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) (x : ((hoc D).obj n).obj U) :
    (inj D n (chn x ⋙ Functor.Elements.π _)).app U (chn x |>.obj 0).val = x := by
  change mkChn (F := D.flip.obj U) _ _ _ = chn x
  fapply CategoryTheory.Functor.ext
  · intro i
    let f := (chn x).map (homOfLE (Fin.zero_le i))
    refine Functor.Elements.ext _ _ (by rfl) ?_
    change (D.flip.obj U).map (𝟙 ((chn x).obj i).obj)
      ((D.flip.obj U).map f.hom ((chn x).obj 0).val) = ((chn x).obj i).val
    rw [(D.flip.obj U).map_id]
    exact f.map_val
  · intro i k g
    apply Functor.Elements.hom_ext
    rw [Functor.Elements.comp_hom, Functor.Elements.comp_hom]
    erw [elt_eqToHom, elt_eqToHom]
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

theorem bij (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) :
    Function.Bijective (Cofan.mk (((hoc D).obj n).obj U) (fun σ => ((evaluation _ _).obj U).map (inj D n σ)) :
      Cofan fun σ : Fin (n.unop.len + 1) ⥤ J => ((evaluation _ _).obj U).obj (D.obj (σ.obj 0))).cofanTypes.fromSigma := by
  constructor
  · rintro ⟨σ, a⟩ ⟨σ', a'⟩ h
    change (inj D n σ).app U a = (inj D n σ').app U a' at h
    have e : σ = σ' := congrArg (fun F => F ⋙ Functor.Elements.π (D.flip.obj U)) h
    subst e
    have h2 := congrArg (fun F : Fin (n.unop.len + 1) ⥤ (D.flip.obj U).Elements => F.obj 0) h
    have h3 : (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U a =
        (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U a' := by
      change (D.flip.obj U).elementsMk (σ.obj 0) _ = (D.flip.obj U).elementsMk (σ.obj 0) _ at h2
      injection h2
    have hid : ∀ b : ((evaluation _ _).obj U).obj (D.obj (σ.obj 0)), (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U b = b := by
      intro b
      have : (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))) = 𝟙 _ := rfl
      rw [this, σ.map_id, D.map_id]; rfl
    rw [hid, hid] at h3
    subst h3; rfl
  · intro x
    exact ⟨⟨chn x ⋙ Functor.Elements.π _, (chn x |>.obj 0).val⟩, chn_eq D n U x⟩

theorem LeafLevel_of : LeafLevel := by
  intro J _ D n
  refine ⟨evaluationJointlyReflectsColimits _ fun U => ?_⟩
  refine (isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj U) _ _).symm ?_
  exact Classical.choice ((Cofan.nonempty_isColimit_iff_bijective_fromSigma _).2 (bij D n U))

end LateralTheory.CohomologicalPurity.LeafLevelPf
end
end

