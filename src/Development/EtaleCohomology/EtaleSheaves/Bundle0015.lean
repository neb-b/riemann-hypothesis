module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
public import Development.EtaleCohomology.EtaleSheaves.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.EtaleSheaves.Bundle0007

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPtPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

theorem eq_generic_of_dim {X : Scheme.{0}} [IsIntegral X] (hd : topologicalKrullDim X ≤ 0) (x : X) :
    x = genericPoint X := by
  have hmax := (Order.krullDim_nonpos_iff_forall_isMax).1 hd
  let S : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hST : S ≤ T := fun _ _ => Set.mem_univ _
  have hTS : T ≤ S := hmax S hST
  have h1 : genericPoint X ⤳ x := genericPoint_specializes x
  have h2 : x ⤳ genericPoint X := by
    rw [specializes_iff_mem_closure]
    exact hTS (Set.mem_univ (genericPoint X))
  exact (h2.antisymm h1).eq

theorem subsingleton_of_dim {X : Scheme.{0}} [IsIntegral X] (hd : topologicalKrullDim X ≤ 0) : Subsingleton X :=
  ⟨fun x y => (eq_generic_of_dim hd x).trans (eq_generic_of_dim hd y).symm⟩

theorem leafPtIso (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p]
    (hd : topologicalKrullDim X ≤ 0) : IsIso p := by
  haveI := subsingleton_of_dim hd
  haveI : IsAffine X := inferInstance
  let F : CommRingCat.of k ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso _).inv ≫ p.appTop
  have hfin : p.appTop.hom.Finite := finite_appTop_of_universallyClosed k p
  have hFfin : F.hom.Finite := by
    simp only [F, CommRingCat.hom_comp]
    exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.surjective)
  letI : Algebra k Γ(X, ⊤) := F.hom.toAlgebra
  haveI : Algebra.IsIntegral k Γ(X, ⊤) := ⟨fun a => hFfin.to_isIntegral a⟩
  have hb : Function.Bijective F.hom := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))
  haveI : IsIso F := (ConcreteCategory.isIso_iff_bijective F).2 hb
  haveI : IsIso p.appTop := by
    have : p.appTop = (Scheme.ΓSpecIso _).hom ≫ F := by simp [F]
    rw [this]; infer_instance
  have e : p = X.isoSpec.hom ≫ Spec.map p.appTop ≫ (Sp k).isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]; infer_instance

theorem sh_of_isAlgClosed (k : Type) [Field k] [IsAlgClosed k] : SH k := by
  refine ⟨inferInstance, ?_⟩
  have hb : Function.Bijective (IsLocalRing.residue k) := by
    exact ⟨(IsLocalRing.residue k).injective, IsLocalRing.residue_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField k) := IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective _ hb)
  infer_instance

theorem finite_sp (hH : Hyps) (h0 : H0TwistOverClosedField) (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] (hq : IsUnit (q : k))
    (n i : ℤ) : Finite (Ht q (sch.obj (Sp k)) n i) := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · haveI := (hH.2.2.2.2.2.2.2.1 (ZMod q) (tw q i)).1 (sch.obj (Sp k)) n hn
    exact Finite.of_subsingleton
  · exact (h0 hH q k hq i).1
  · haveI := hH.2.2.2.2.2.2.2.2.2.2.2.1 (ZMod q) k (sh_of_isAlgClosed k) (tw q i) n hn
    exact Finite.of_subsingleton

theorem LeafPt_of (h0 : H0TwistOverClosedField) : LeafPt := by
  intro hH q _ k _ _ hq X _ p _ hd n i
  have := leafPtIso k p hd
  haveI := finite_sp hH h0 q k hq n i
  refine Finite.of_injective (pull (ZMod q) (sch.map (inv p)) (tw q i) n) ?_
  intro x y hxy
  have key : ∀ z : Ht q (sch.obj X) n i,
      pull (ZMod q) (sch.map p) (tw q i) n (pull (ZMod q) (sch.map (inv p)) (tw q i) n z) = z := by
    intro z
    rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [← key x, ← key y, hxy]

end LateralTheory.E.E4
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSupport
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafA6suppPf

def LeafAWSpec : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ}
  (α : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i)) n)
  (β : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q j)) m),
  ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q (i + j))) (n + m),
    (twPair q i j).IsAW rfl α.1 β.1 γ.1 ∧
    cup q (CohomologyClass.mk α : Ht q E n i) (CohomologyClass.mk β : Ht q E m j) = CohomologyClass.mk γ

def LeafRepVanish : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E), Mono f → ∀ (F : Shv R) (n : ℤ)
  (a : H R E F n), pull R f F n a = 0 →
  ∃ α : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk α = a ∧
    ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + n = w) (Y : Scheme.{0}) (y : Sx U N Y), ev α.1 N w h Y ((f.app _).app _ y) = 0

def LeafCochainVanish : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ (K : Cx R) (k : ℤ) (γ : Cochain ((chains R).obj E) K k),
    (∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx U N Y), ev γ N w h Y ((f.app _).app _ y) = 0) →
    (∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx V N Y), ev γ N w h Y ((g.app _).app _ y) = 0) →
    γ = 0

theorem sub_map {U E : Spc} (f : U ⟶ E) {N : ℕ} {Y : Scheme.{0}} (y : Sx U N Y) (j l : ℕ) (h : j + l ≤ N) :
    Sx.sub ((f.app _).app _ y) j l h = (f.app _).app _ (Sx.sub y j l h) := by
  unfold Sx.sub
  have e := NatTrans.congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op Y)
  exact (ConcreteCategory.congr_hom e y).symm

theorem LeafA6supp_of (h1 : LeafAWSpec) (h2 : LeafRepVanish) (h3 : LeafCochainVanish) : LateralTheory.E.D2.LeafA6supp := by
  intro q _ U V E f g hc n m i j a b ha hb
  obtain ⟨α, rfl, hα⟩ := h2 (ZMod q) f hc.1 (tw q i) n a ha
  obtain ⟨β, rfl, hβ⟩ := h2 (ZMod q) g hc.2.1 (tw q j) m b hb
  obtain ⟨γ, hAW, hcup⟩ := h1 q E α β
  rw [hcup]
  have : γ.1 = 0 := by
    apply h3 (ZMod q) f g hc
    · intro N w h Y y
      rw [hAW N w h Y]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [sub_map f y 0 (p : ℕ), hα]
      simp
    · intro N w h Y y
      rw [hAW N w h Y]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [sub_map g y (p : ℕ) (N - p), hβ]
      simp
  have hγ : γ = 0 := Subtype.ext this
  rw [hγ]
  exact CohomologyClass.mk_zero _ _ _

end LateralTheory.E.LeafA6suppPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwPairHtpyPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairHtpyPf

def LeafTwTensExists : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ (T : Cx (ZMod q)) (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T), τ.IsTensor

def LeafTensFactor : Prop := ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor →
  ∀ ν : Pair I J K, ∃ u : T ⟶ K, τ.Compat ν (𝟙 I) (𝟙 J) u

def LeafTwTensRes : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) {T : Cx (ZMod q)} (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T),
  τ.IsTensor → IsTwRes q (i + j) T (fun U ζ => τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ))

def LeafTwResHtpy : Prop := ∀ (q : ℕ) [NeZero q] (k : ℤ) {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
  IsTwRes q k T e → ∀ u u' : T ⟶ res _ (tw q k), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u')

theorem secMap_add {R : Type} [CommRing R] {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

theorem secMap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem secMap_id_f {R : Type} [CommRing R] (I : Cx R) (s : ℤ) {U : Scheme.{0}} (x : Sec (I.X s) U) :
    Sec.map ((𝟙 I : I ⟶ I).f s) x = x := by
  rw [HomologicalComplex.id_f]; rfl

theorem secMap_addx {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ x y

theorem secMap_usmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℤˣ) (x : Sec F U) :
    Sec.map φ (n • x) = n • Sec.map φ x := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem hom_reindex {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (Hh : ∀ i j, T.X i ⟶ K.X j)
    (U : Scheme.{0}) (s t v n : ℤ) (hv : v + 1 = n) (hs : s + t = n) (hs' : s + t = v + 1)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (Hh (v + 1) v) (τ.mul U s t (v + 1) hs' a b) = Sec.map (Hh n v) (τ.mul U s t n hs a b) := by
  subst hv; rfl

theorem pairHtpy_of_homotopy {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (μ μ' : Pair I J K) (u u' : T ⟶ K)
    (hu : τ.Compat μ (𝟙 I) (𝟙 J) u) (hu' : τ.Compat μ' (𝟙 I) (𝟙 J) u') (H : Homotopy u u') :
    LateralTheory.E.LeafTwPairUniquePf.PairHtpy μ μ' := by
  refine ⟨fun U s t w hw => (τ.mul U s t (w + 1) hw).compr₂ (((H.hom (w + 1) w).hom.app (op U)).hom), ?_, ?_⟩
  · intro V U g s t w hw a b
    simp only [LinearMap.compr₂_apply]
    rw [← τ.nat g s t (w + 1) hw a b]
    exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) (τ.mul _ s t (w + 1) hw a b)) ((H.hom (w + 1) w).hom.naturality g.op)).symm
  · intro U s t w hw a b
    simp only [LinearMap.compr₂_apply]
    have e1 := hu U s t w hw a b
    have e2 := hu' U s t w hw a b
    rw [secMap_id_f, secMap_id_f] at e1 e2
    rw [← e1, ← e2]
    have hc := H.comm w
    rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel w (w + 1) by simp),
      prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (w - 1) w by simp)] at hc
    rw [hc, secMap_add, secMap_add, secMap_comp, secMap_comp]
    have e3 := hom_reindex τ H.hom U s t (w - 1) w (by omega) hw (by omega) a b
    have e3' : (ModuleCat.Hom.hom ((H.hom (w - 1 + 1) (w - 1)).hom.app (op U))) (τ.mul U s t (w - 1 + 1) (by omega) a b) =
        Sec.map (H.hom w (w - 1)) (τ.mul U s t w hw a b) := e3
    rw [e3']
    rw [τ.leibniz, secMap_addx, secMap_usmul]
    dsimp only [Sec.map]
    abel

end LateralTheory.E.LeafTwPairHtpyPf

open LateralTheory.E.LeafTwPairHtpyPf in
theorem LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy_of (hE : LeafTwTensExists) (hF : LeafTensFactor) (hR : LeafTwTensRes)
    (hH : LeafTwResHtpy) : LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy := by
  intro q _ i j μ μ' hμ hμ'
  obtain ⟨T, τ, hτ⟩ := hE q i j
  obtain ⟨u, hu⟩ := hF (ZMod q) τ hτ μ
  obtain ⟨u', hu'⟩ := hF (ZMod q) τ hτ μ'
  obtain ⟨H⟩ := hH q (i + j) _ (hR q i j τ hτ) u u' (fun U ζ => by
    have a1 := hu U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    have a2 := hu' U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [secMap_id_f, secMap_id_f] at a1 a2
    rw [a1, a2, hμ U ζ, hμ' U ζ])
  exact pairHtpy_of_homotopy τ μ μ' u u' hu hu' H
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwTensExPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafTwTensExPf

open Classical in
section
variable {R : Type} [CommRing R] (I J : Cx R)

theorem tres_tmul {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (a ⊗ₜ b)) =
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V) p (Sec.res g a ⊗ₜ Sec.res g b) := by
  simp [Tens.res]

def TP (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp_all
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp_all
      | tmul a b =>
        have := tres_tmul I J (𝟙 U.unop) w p a b
        simp only [DirectSum.lof_eq_of] at this
        simp [this, Sec.res]
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp_all
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp_all
      | tmul a b =>
        have h1 := tres_tmul I J (g.unop ≫ f.unop) w p a b
        have h2 := tres_tmul I J f.unop w p a b
        have h3 := tres_tmul I J g.unop w p (Sec.res f.unop a) (Sec.res f.unop b)
        simp only [DirectSum.lof_eq_of] at h1 h2 h3
        simp [h1, h2, Sec.res]
        exact h3.symm
end
end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

abbrev lo {U : Scheme.{0}} {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w}) :
    Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U →ₗ[ULift.{1} R] Tens I J U w :=
  DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p

def dT (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    lo I J (U := U) (w := w + 1) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
    ((p.1.1.negOnePow : ℤˣ) : ℤ) • (lo I J (U := U) (w := w + 1) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom)

theorem dT_tmul (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    dT I J U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      lo I J ⟨(s + 1, t), by simp only; omega⟩ (Sec.map (I.d s (s + 1)) a ⊗ₜ b) +
      ((s.negOnePow : ℤˣ) : ℤ) • lo I J ⟨(s, t + 1), by simp only; omega⟩ (a ⊗ₜ Sec.map (J.d t (t + 1)) b) := by
  simp [dT, lo, DirectSum.toModule_lof]

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

theorem dd0 {K : Cx R} {U : Scheme.{0}} (s : ℤ) (a : Sec (K.X s) U) :
    Sec.map (K.d (s + 1) (s + 1 + 1)) (Sec.map (K.d s (s + 1)) a) = 0 := by
  rw [LateralTheory.E.LeafTwPairExistsPf.map_map, HomologicalComplex.d_comp_d]
  simp [Sec.map]

theorem dT_nat {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    dT I J V w ∘ₗ Tens.res g w = Tens.res g (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  erw [tres_tmul, dT_tmul, dT_tmul, map_add, map_zsmul, tres_tmul, tres_tmul,
    LateralTheory.E.LeafTwPairExistsPf.res_map, LateralTheory.E.LeafTwPairExistsPf.res_map]

theorem dT_dT (U : Scheme.{0}) (w : ℤ) : dT I J U (w + 1) ∘ₗ dT I J U w = 0 := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [dT_tmul, map_add (f := _), map_zsmul]
  rw [dT_tmul (s := s + 1) (t := t) (w := w + 1)]
  rw [dT_tmul (s := s) (t := t + 1) (w := w + 1)]
  rw [dd0 (K := I), dd0 (K := J)]
  simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, zero_add, smul_zero, add_zero,
    Int.negOnePow_succ, Units.val_neg, neg_smul, neg_add_cancel]

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

def dTP (w : ℤ) : TP I J w ⟶ TP I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality _ _ g := ModuleCat.hom_ext (dT_nat I J g.unop w)

def PC : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ :=
  CochainComplex.of (TP I J) (dTP I J) (fun w => by
    ext U : 2
    exact ModuleCat.hom_ext (dT_dT I J U.unop w))

def TC : Cx R := ((presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex _).obj (PC I J)

abbrev un (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec ((TC I J).X w) U :=
  ((toSheafify Scheme.etaleTopology.{0} (TP I J w)).app (op U)).hom

theorem un_nat {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Sec.res g (un I J U w x) = un I J V w (Tens.res g w x) :=
  (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology.{0} (TP I J w)).naturality g.op)) x).symm

theorem un_d (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map ((TC I J).d w (w + 1)) (un I J U w x) = un I J U (w + 1) (dT I J U w x) := by
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (congrArg (fun f => f.app (op U)) (toSheafify_naturality Scheme.etaleTopology.{0} (dTP I J w)))) x
  simp only [TC, PC, Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d] at this ⊢
  exact this.symm

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

def tau : Pair I J (TC I J) where
  mul U s t w h := (TensorProduct.mk _ _ _).compr₂ (un I J U w ∘ₗ lo I J ⟨(s, t), h⟩)
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply]
    rw [un_nat]
    congr 1
    exact tres_tmul I J g w ⟨(s, t), h⟩ a b
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply]
    rw [un_d, dT_tmul, map_add (f := _), map_zsmul, Units.smul_def]

theorem tau_lift (U : Scheme.{0}) (w : ℤ) : (tau I J).lift U w = un I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp [Pair.lift, tau]

theorem tau_isTensor : (tau I J).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} (TP I J w))
      (U := op U) y, fun V g ⟨t, ht⟩ => ⟨t, ?_⟩⟩
    rw [tau_lift]
    exact ht
  · rw [tau_lift] at hx
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} (TP I J w))
      (X := op U) x 0 (by rw [map_zero]; exact hx), fun V g hg => ?_⟩
    have : Tens.res g w x = Tens.res g w 0 := hg
    rwa [map_zero] at this

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf

theorem LeafTwTensEx_of : LateralTheory.E.LeafTwPairExistsPf.LeafTwTensEx := by
  intro q _ i j
  exact ⟨_, tau _ _, tau_isTensor _ _⟩

end LateralTheory.E.LeafTwTensExPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitAWPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitAWPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf

theorem sec_sub {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) (U : Scheme.{0}) :
    Subsingleton (Sec ((res R F).X s) U) := by
  have hz : IsZero ((res R F).X s) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have h2 : IsZero (((res R F).X s).obj.obj (op U)) :=
    Functor.map_isZero ((sheafToPresheaf _ _) ⋙ (evaluation _ _).obj (op U)) hz
  exact ModuleCat.isZero_iff_subsingleton.mp h2

theorem sub_zero_self {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval (n := N) 0 N h = 𝟙 _ := by
    ext i : 3
    simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem main_gen (q : ℕ) [NeZero q] (E : Spc) (i j : ℤ) (hij : i = j)
    (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q j)))
    (hU : ∀ (U : Scheme.{0}) (t w : ℤ) (h : 0 + t = w) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → HEq (μ.mul U 0 t w h a b) b)
    (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) (hα : OneLoc α)
    (n k : ℤ) (hnk : n = k) (β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q i)) n) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q j)) k, μ.IsAW (show 0 + n = k by omega) α.1 β.1 γ.1 ∧
      CohomologyClass.mk γ = Ht.cast hnk hij (CohomologyClass.mk β : Ht q E n i) := by
  subst hij hnk
  refine ⟨β, ?_, rfl⟩
  intro N w h U x
  have hmz : ∀ (s t w : ℤ) (h : s + t = w) (a : Sec ((res _ (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
      s < 0 → μ.mul U s t w h a b = 0 := by
    intro s t w h a b hs
    have := sec_sub (tw q 0) s hs U
    rw [Subsingleton.elim a 0]
    simp
  rw [Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · subst h
    show _ = (n * ((0 : ℕ) : ℤ)).negOnePow • μ.mul U (-((0 : ℕ) : ℤ) + 0) (-((N - 0 : ℕ) : ℤ) + n) (-(N : ℤ) + n) (by omega)
      (ev α.1 0 _ rfl U (x.sub 0 0 (by omega))) (ev β.1 (N - 0) _ rfl U (x.sub 0 (N - 0) (by omega)))
    have h1 : (n * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
    rw [h1, one_smul]
    show _ = μ.mul U 0 (-(N : ℤ) + n) (-(N : ℤ) + n) (by omega)
      (ev α.1 0 0 (by simp) U (x.sub 0 0 (by omega))) (ev β.1 N _ rfl U (x.sub 0 N (by omega)))
    rw [sub_zero_self]
    exact (eq_of_heq (hU U _ _ (by omega) _ (ev β.1 N _ rfl U x) (hα U (x.sub 0 0 (by omega))))).symm
  · intro p _
    rw [hmz, smul_zero]
    simp
    omega

theorem LeafUnitAW_of : LeafUnitAW := by
  intro q _ E i μ hU α hα n β
  exact main_gen q E i (0 + i) (by ring) μ hU α hα n (0 + n) (by ring) β

end LateralTheory.E.LeafUnitAWPf
end
end

