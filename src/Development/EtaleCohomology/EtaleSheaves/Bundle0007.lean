module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0003
public import Development.EtaleCohomology.EtaleSheaves.LeafTwSecKillCut
public import Development.EtaleCohomology.TateTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafConeZeroPf
section
noncomputable section
open CategoryTheory Limits Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC Pretriangulated

namespace LateralTheory.E.E8.ExciseCut.ConeZeroPf

universe u v

theorem tri_zero {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor D n)] [Pretriangulated D]
    (T : Triangle D) (hT : T ∈ distTriang D) (Y : ℤ → D) (e : ∀ n, Y n ≅ (Y (n - 1))⟦(1 : ℤ)⟧)
    (hb : ∀ n, Function.Bijective (fun g : T.obj₂ ⟶ Y n => T.mor₁ ≫ g)) (n : ℤ) (x : T.obj₃ ⟶ Y n) : x = 0 := by
  have hy : T.mor₂ ≫ x = 0 := by
    apply (hb n).1
    simp only [comp_zero, ← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]
  obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₃ T hT x hy
  obtain ⟨h, hh⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective (g ≫ (e n).hom)
  obtain ⟨k, rfl⟩ := (hb (n - 1)).2 h
  have : g = (CategoryTheory.shiftFunctor D (1 : ℤ)).map (T.mor₁ ≫ k) ≫ (e n).inv := by
    rw [hh, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this, Functor.map_comp]
  simp only [← Category.assoc, comp_distTriang_mor_zero₃₁ T hT, zero_comp]

variable (R : Type) [CommRing R]

theorem pull_toHom {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (n : ℤ) (x : HK R L F n) :
    CohomologyClass.toHom (HK.pull R φ F n x) =
      (HomotopyCategory.quotient _ _).map φ ≫ CohomologyClass.toHom x := by
  obtain ⟨b, rfl⟩ := x.mk_surjective
  have : zcomp (Cocycle.ofHom φ) b (zero_add n) = b.precomp φ := by
    ext p q hpq
    simp [zcomp, Cocycle.precomp]
  change CohomologyClass.toHom (CohomologyClass.mk (zcomp (Cocycle.ofHom φ) b (zero_add n))) = _
  rw [this, CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_precomp, Functor.map_comp]

theorem hb' {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (hb : ∀ n, Function.Bijective (HK.pull R φ F n)) (n : ℤ) :
    Function.Bijective (fun g : (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦n⟧) =>
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map φ ≫ g) := by
  have : (fun g : (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦n⟧) =>
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map φ ≫ g) =
      (CohomologyClass.homAddEquiv) ∘ (HK.pull R φ F n) ∘ (CohomologyClass.homAddEquiv.symm) := by
    funext g
    simp only [Function.comp_apply, CohomologyClass.homAddEquiv_apply, pull_toHom]
    congr 1
    exact (CohomologyClass.homAddEquiv.apply_symm_apply g).symm
  rw [this]
  exact CohomologyClass.homAddEquiv.bijective.comp ((hb n).comp CohomologyClass.homAddEquiv.symm.bijective)

def shIso (E : Cx R) (n : ℤ) :
    (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj (E⟦n⟧) ≅
      ((HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj (E⟦n - 1⟧))⟦(1 : ℤ)⟧ :=
  (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).mapIso
    ((CategoryTheory.shiftFunctorAdd' (CochainComplex (Shv R) ℤ) (n - 1) 1 n (by omega)).app E) ≪≫
    ((HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).app (E⟦n - 1⟧)

end LateralTheory.E.E8.ExciseCut.ConeZeroPf

open LateralTheory.E.E8.ExciseCut.ConeZeroPf in
theorem LateralTheory.E.E8.ExciseCut.LeafConeZero_of : LateralTheory.E.E8.ExciseCut.LeafConeZero := by
  intro R _ K L φ F hb n
  refine ⟨fun x y => ?_⟩
  apply (CohomologyClass.toHom_bijective _ _ _).1
  have hz := fun x : HK R (mappingCone φ) F n =>
    tri_zero (mappingCone.triangleh φ) (HomotopyCategory.mappingCone_triangleh_distinguished φ)
      (fun n => (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦n⟧))
      (shIso R (res R F)) (hb' R φ F hb) n (CohomologyClass.toHom x)
  exact (hz x).trans (hz y).symm
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafNatCupPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNatCupPf

section

variable {R : Type} [CommRing R]

theorem chainsXIso_inv_map {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  rw [ComplexShape.embeddingDownNat.extendFunctor_map (C := Shv R)]
  erw [HomologicalComplex.extendMap_f _ _ (i := p) (i' := -(p : ℤ)) rfl]
  simp only [chainsN]
  erw [Iso.inv_hom_id_assoc]
  simp
  rfl

theorem free_map_freeGen {P Q : PSh} (g : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  have h2 : (((freeP R).map g).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (g.app (op U) x)) :=
    ModuleCat.free_map_apply (R := ULift.{1} R) _ _
  exact h.symm.trans (congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom h2)

theorem ev_pull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  simp only [ev]
  rw [Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (add_zero _) h, Cochain.ofHom_v,
    ← Category.assoc, chainsXIso_inv_map, Category.assoc]
  rw [← free_map_freeGen]
  rfl

theorem sub_pull {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (f.app (op (SimplexCategory.mk l))).app (op U) (x.sub j l h) =
      Sx.sub (E := E') (N := N) ((f.app (op (SimplexCategory.mk N))).app (op U) x) j l h := by
  have := ConcreteCategory.congr_hom (congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op U)) x
  simp only [Sx.sub]
  exact this

theorem isAW_pull {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E') I n) (β : Cochain ((chains R).obj E') J m) (γ : Cochain ((chains R).obj E') K k)
    (hγ : μ.IsAW hk α β γ) :
    μ.IsAW hk ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n))
      ((Cochain.ofHom ((chains R).map f)).comp β (zero_add m))
      ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add k)) := by
  intro N w h U x
  rw [ev_pull, hγ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_pull, ev_pull, sub_pull, sub_pull]

theorem pull_mk {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) (z : Cocycle ((chains R).obj E') (res R F) n) :
    pull R f F n (CohomologyClass.mk z) = CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)) :=
  rfl

theorem zcomp_ofHom_val {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (z : Cocycle ((chains R).obj E') I n) :
    (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)).1 = (Cochain.ofHom ((chains R).map f)).comp z.1 (zero_add n) :=
  rfl

end

open CupProductRingLaws in
theorem LeafNatCup_of (hc : LeafCupSpec) : LeafNatCup := by
  intro q _ E E' f n m i j a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (hc (ZMod q) (twPair q i j) E' rfl).1 α β
  have e1 : cup q (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
    (hc (ZMod q) (twPair q i j) E' rfl).2 α β γ hγ
  have hAW := isAW_pull (twPair q i j) f rfl α.1 β.1 γ.1 hγ
  rw [← zcomp_ofHom_val, ← zcomp_ofHom_val, ← zcomp_ofHom_val] at hAW
  have e2 := (hc (ZMod q) (twPair q i j) E rfl).2 _ _ _ hAW
  rw [e1, pull_mk, pull_mk, pull_mk]
  exact e2.symm

end LateralTheory.E.LeafNatCupPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafOfRingsLocInjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

theorem jointlySurj_prec (P : MorphismProperty Scheme.{0}) : Scheme.JointlySurjective (Scheme.precoverage P) :=
  inferInstance

theorem LeafOfRingsLocInj_of : LeafOfRingsLocInj := by
  intro R _ M U t ht u
  have h0 : (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U) t =
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U) 0 := by
    have : ofRings.sec M U t = 0 := ht
    simp only [ofRings.sec] at this
    rw [map_zero]
    exact this
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) t 0 h0
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  have := jointlySurj_prec @Etale
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
  refine ⟨𝒰.X i, 𝒰.f i, 𝒰.map_prop i, ⟨y, hy⟩, ?_⟩
  have hm := hle _ _ (Presieve.ofArrows.mk i)
  have hm' : ((Scheme.Γ ⋙ M).map (𝒰.f i).op).hom t = ((Scheme.Γ ⋙ M).map (𝒰.f i).op).hom 0 := hm
  rw [map_zero] at hm'
  exact hm'

end LateralTheory.E.E8.TwSec
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafOfRingsLocSurjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafOfRingsLocSurjPf

theorem cover_hit {X : Scheme.{0}} (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X) (x : X) :
    ∃ (U : Scheme.{0}) (w : U ⟶ X), Etale w ∧ x ∈ Set.range w ∧ S.arrows w := by
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff).1 hS
  obtain ⟨i, hi⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 x
  exact ⟨𝒰.X i, 𝒰.f i, 𝒰.map_prop i, hi, h𝒰 _ _ (Presieve.ofArrows.mk i)⟩

theorem LeafOfRingsLocSurj_of : LateralTheory.E.E8.TwSec.LeafOfRingsLocSurj := by
  intro R _ M X s x
  have hS := Presheaf.imageSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op X) s
  obtain ⟨U, w, hw, hx, t, ht⟩ := cover_hit _ hS x
  exact ⟨U, w, hw, hx, t, ht.symm⟩

end LateralTheory.E.LeafOfRingsLocSurjPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafOneSpecPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneSpecPf

open LateralTheory.E.CupProductRingLaws

theorem res_neg_zero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) := by
  unfold res
  unfold InjectiveResolution.cochainComplex
  apply HomologicalComplex.isZero_extend_X
  rintro i rfl
  change ((i : ℤ)) < 0 at hn
  omega
theorem chains_pos_zero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) : IsZero (((chains R).obj E).X n) := by
  unfold chains
  simp only [Functor.comp_obj, ComplexShape.Embedding.extendFunctor_obj]
  apply HomologicalComplex.isZero_extend_X
  rintro i rfl
  change 0 < -((i : ℤ)) at hn
  omega
theorem free_hom_ext (R : Type) [CommRing R] (P : PSh) (G : Shv R) (f g : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) :
    f = g := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ G.property
  ext U : 2
  apply ModuleCat.free_hom_ext
  intro x
  exact h U.unop x.down
theorem cochain0_ext (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (α β : Cochain ((chains R).obj E) (res R F) 0)
    (h : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := R) α 0 0 (by simp) U x = ev (R := R) β 0 0 (by simp) U x) : α = β := by
  apply Cochain.ext
  intro p q hpq
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · exact (res_neg_zero R F q (by omega)).eq_of_tgt _ _
  · have key : (chainsXIso R E 0).inv ≫ α.v (-((0 : ℕ) : ℤ)) 0 (by simp) =
        (chainsXIso R E 0).inv ≫ β.v (-((0 : ℕ) : ℤ)) 0 (by simp) :=
      free_hom_ext R _ _ _ _ (fun U x => h U x)
    obtain rfl : q = 0 := by omega
    simpa using key
  · exact (chains_pos_zero R E p hp).eq_of_src _ _

def LeafCochain0Ext : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc)
  (α β : Cochain ((chains R).obj E) (res R F) 0),
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := R) α 0 0 (by simp) U x = ev (R := R) β 0 0 (by simp) U x) → α = β

theorem leafCochain0Ext_pf : LeafCochain0Ext := fun R _ F E α β h => cochain0_ext R F E α β h

def LeafOneExists : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∃ α, IsOneCocycle q E α

def LeafPrimCover : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  ∃ S : Sieve U, S ∈ Scheme.etaleTopology U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Nonempty (Prim q Γ(V, ⊤))

def LeafSecPrimLocal : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (q : ℕ) [NeZero q] (U : Scheme.{0}) (a b : Sec F U),
  IsUnit (q : Γ(U, ⊤)) → (∀ (V : Scheme.{0}) (g : V ⟶ U), Nonempty (Prim q Γ(V, ⊤)) → Sec.res g a = Sec.res g b) → a = b

theorem sec_sep (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (a b : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g a = Sec.res g b) : a = b := by
  have hF := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact (hF S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

theorem leafSecPrimLocal_of (hP : LeafPrimCover) : LeafSecPrimLocal := by
  intro R _ F q _ U a b hq h
  obtain ⟨S, hS, hSP⟩ := hP q U hq
  exact sec_sep R F U S hS a b fun V g hg => h V g (hSP V g hg)

theorem one_cocycle_eq (hB : LeafCochain0Ext) (hC : LeafSecPrimLocal) (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E)
    (α β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) (hα : IsOneCocycle q E α) (hβ : IsOneCocycle q E β) :
    α = β := by
  apply Subtype.ext
  apply hB (ZMod q) (tw q 0) E α.1 β.1
  intro U x
  refine hC (ZMod q) _ q U _ _ (hE U ⟨x⟩) ?_
  rintro V g ⟨ζ⟩
  rw [← LateralTheory.EtaleFoundations.ev_nat_pf α.1 0 0 (by simp) g x, ← LateralTheory.EtaleFoundations.ev_nat_pf β.1 0 0 (by simp) g x]
  exact (hα V _ ζ).trans (hβ V _ ζ).symm

theorem LeafOneSpec_of (hA : LeafOneExists) (hP : LeafPrimCover) : LeafOneSpec := by
  have hB := leafCochain0Ext_pf
  have hC := leafSecPrimLocal_of hP
  intro q _ E hE
  refine ⟨hA q E hE, fun α hα => ?_⟩
  obtain ⟨α₀, h₀⟩ := hA q E hE
  obtain ⟨α₁, h₁, hα₁⟩ := pick_spec (P := fun c : Ht q E 0 0 => ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0,
    CohomologyClass.mk α = c ∧ ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)),
      ev (R := ZMod q) α.1 0 0 (by simp) U x = resGen 0 ζ) ⟨CohomologyClass.mk α₀, α₀, rfl, h₀⟩
  change pick _ = _
  rw [← h₁, one_cocycle_eq hB hC q E hE α₁ α hα₁ hα]

end LateralTheory.E.LeafOneSpecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafRingUnitPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafRingUnitPf
open LateralTheory.E.CupProductRingLaws

def UnitProp {q : ℕ} {i : ℤ} (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i)))) : Prop :=
  ∀ (U : Scheme.{0}) (t w : ℤ) (h : 0 + t = w) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
    Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → HEq (μ.mul U 0 t w h a b) b

def LeafUnitPair : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ),
  ∃ μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i))), IsTwPair μ ∧ UnitProp μ

def OneLoc {q : ℕ} {E : Spc} (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) : Prop :=
  ∀ (U : Scheme.{0}) (x : Sx E 0 U), Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g (ev (R := ZMod q) α.1 0 0 (by simp) U x) = resGen 0 ζ)

def LeafOneLoc : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E →
  ∀ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, IsOneCocycle q E α → OneLoc α

def LeafUnitAW : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) (i : ℤ)
  (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i)))), UnitProp μ →
  ∀ (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0), OneLoc α →
  ∀ (n : ℤ) (β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q i)) n),
    ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (0 + i))) (0 + n), μ.IsAW rfl α.1 β.1 γ.1 ∧
      CohomologyClass.mk γ = Ht.cast (by ring) (by ring) (CohomologyClass.mk β : Ht q E n i)

theorem LeafRingUnit_of (hcup : LeafCupSpec) (hex : LeafTwPairExists) (hun : LeafTwPairUnique) (hone : LeafOneSpec)
    (h1 : LeafUnitPair) (h2a : LeafOneLoc) (h2 : LeafUnitAW) : LeafRingUnit := by
  intro q _ E hE n i a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨μ, hμ, hU⟩ := h1 q i
  obtain ⟨⟨α, hα⟩, hαone⟩ := hone q E hE
  obtain ⟨γ, hγ, hγc⟩ := h2 q E i μ hU α (h2a q E hE α hα) n β
  have htw : IsTwPair (twPair q 0 i) := pick_spec (hex q 0 i)
  have hc : cup q (one q E) (CohomologyClass.mk β) = (twPair q 0 i).cup E rfl (one q E) (CohomologyClass.mk β) := rfl
  rw [hc, hun q 0 i _ μ htw hμ E rfl, hαone α hα, (hcup (ZMod q) μ E rfl).2 α β γ hγ, hγc]

end LateralTheory.E.LeafRingUnitPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwAdjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.E8.TwSec

theorem twAdj_comap_surj (A : Type) [CommRing A] (q : ℕ) [NeZero q] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (cyclotomic q A)))) := by
  have hm := cyclotomic.monic q A
  have := Module.Free.of_basis (AdjoinRoot.powerBasis' hm).basis
  have : Module.Finite A (AdjoinRoot (cyclotomic q A)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' hm).basis
  intro p
  have : Nontrivial A := by
    rcases subsingleton_or_nontrivial A with h | h
    · exact absurd (Subsingleton.elim p.asIdeal ⊤) p.isPrime.ne_top
    · exact h
  have : Nontrivial (AdjoinRoot (cyclotomic q A)) := by
    have hd : 0 < (cyclotomic q A).natDegree := by
      rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q)
    have : Nonempty (Fin (cyclotomic q A).natDegree) := ⟨⟨0, hd⟩⟩
    exact (AdjoinRoot.powerBasisAux' hm).repr.symm.injective.nontrivial
  exact Algebra.IsIntegral.comap_surjective A _ p

theorem twAdj_etale (A : Type) [CommRing A] (q : ℕ) (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyclotomic q A)) := by
  have hsep : (cyclotomic q A).Separable :=
    (separable_X_pow_sub_C_unit (1 : Aˣ) hq).of_dvd (by simpa using cyclotomic.dvd_X_pow_sub_one q A)
  obtain ⟨a, b, hab⟩ := hsep
  let P : StandardEtalePair A := ⟨cyclotomic q A, cyclotomic.monic q A, 1,
    ⟨b, a, 0, by rw [pow_zero, ← hab]; ring⟩⟩
  let e1 : P.Ring ≃ₐ[A] Localization.Away (AdjoinRoot.mk (cyclotomic q A) 1) := P.equivAwayAdjoinRoot
  let e2 : AdjoinRoot (cyclotomic q A) ≃ₐ[AdjoinRoot (cyclotomic q A)]
      Localization.Away (AdjoinRoot.mk (cyclotomic q A) 1) :=
    IsLocalization.atUnit _ _ (AdjoinRoot.mk (cyclotomic q A) 1) (by rw [map_one]; exact isUnit_one)
  have := Algebra.IsStandardEtale.of_equiv (e1.trans (e2.symm.restrictScalars A))
  infer_instance

theorem LeafTwAdj_of : LeafTwAdj := by
  intro q _ U u hq
  obtain ⟨R, f, hf, ⟨x, rfl⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := U) (x := u) (U := ⊤) (by simp)
  have hqR : IsUnit ((q : ℕ) : R) := by
    simpa using (hq.map f.appTop.hom).map (Scheme.ΓSpecIso R).hom.hom
  have := twAdj_etale R q hqR
  let φ : R ⟶ CommRingCat.of (AdjoinRoot (cyclotomic q R)) :=
    CommRingCat.ofHom (algebraMap R (AdjoinRoot (cyclotomic q R)))
  have hφ : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr this)
  refine ⟨Spec (.of (AdjoinRoot (cyclotomic q R))), Spec.map φ ≫ f, inferInstance, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := twAdj_comap_surj R q x
    refine ⟨y, ?_⟩
    subst hy
    rfl
  · let ψ := (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (cyclotomic q R)))).inv.hom
    refine ⟨⟨ψ (AdjoinRoot.root _), ?_, ?_⟩⟩
    · simpa using (hqR.map (algebraMap R (AdjoinRoot (cyclotomic q R)))).map ψ
    · have h0 : aeval (AdjoinRoot.root (cyclotomic q R)) (cyclotomic q ℤ) = 0 := by
        rw [← aeval_map_algebraMap R, map_cyclotomic, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      have := aeval_algHom_apply ψ.toIntAlgHom (AdjoinRoot.root (cyclotomic q R)) (cyclotomic q ℤ)
      rw [h0, map_zero] at this
      exact this

end LateralTheory.E.E8.TwSec
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwPairExistsPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairExistsPf

variable {R : Type} [CommRing R]

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) x
  simpa using h.symm

theorem map_map {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := by
  simp [Sec.map]

def post {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom
  nat g s t w h a b := by
    change Sec.res g (Sec.map (u.f w) _) = Sec.map (u.f w) _
    rw [res_map, μ.nat]
  leibniz U s t w h a b := by
    change Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) _) =
      Sec.map (u.f (w + 1)) _ + s.negOnePow • Sec.map (u.f (w + 1)) _
    rw [map_map, u.comm w (w + 1), ← map_map, μ.leibniz]
    simp only [Sec.map, map_add (f := _), map_zsmul_unit]

theorem post_mul {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : (post μ u).mul U s t w h a b = Sec.map (u.f w) (μ.mul U s t w h a b) := rfl

def LeafTwTensEx : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ (T : Cx (ZMod q)) (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T), τ.IsTensor

def LeafTwTensRes : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) (T : Cx (ZMod q))
  (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T), τ.IsTensor →
    IsTwRes q (i + j) T (fun U ζ => τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ))

def LeafTwResExt : Prop := ∀ (q : ℕ) [NeZero q] (k : ℤ) (T : Cx (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
  IsTwRes q k T e → ∃ u : T ⟶ res _ (tw q k), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen k ζ

theorem LeafTwPairExists_of (h1 : LeafTwTensEx) (h2 : LeafTwTensRes) (h3 : LeafTwResExt) :
    LateralTheory.E.CupProductRingLaws.LeafTwPairExists := by
  intro q _ i j
  obtain ⟨T, τ, hτ⟩ := h1 q i j
  obtain ⟨u, hu⟩ := h3 q (i + j) T _ (h2 q i j T τ hτ)
  exact ⟨post τ u, fun U ζ => by rw [post_mul]; exact hu U ζ⟩

end LateralTheory.E.LeafTwPairExistsPf
end
end

