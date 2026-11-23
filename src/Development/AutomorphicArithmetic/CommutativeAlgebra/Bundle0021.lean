module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Development.EtaleCohomology.EtaleSheaves.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
public import Development.EtaleCohomology.EtaleSheaves.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveIffTotalQuasiIsoOfTotalModels
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.DegreeAdditivity

private theorem D_add {C : DC} (n : ℤ) (x y : C.Tot) : C.D n (x + y) = C.D n x + C.D n y := by
  funext p t
  rcases p with _ | p
  · simp [DC.D, map_add (f := _)]
  · simp only [DC.D, Pi.add_apply, map_add (f := _), smul_add]
    abel

private theorem D_sub {C : DC} (n : ℤ) (x y : C.Tot) : C.D n (x - y) = C.D n x - C.D n y := by
  funext p t
  rcases p with _ | p
  · simp [DC.D, map_sub]
  · simp only [DC.D, Pi.sub_apply, map_sub, smul_sub]
    abel

private theorem D_zero {C : DC} (n : ℤ) : C.D n (0 : C.Tot) = 0 := by
  funext p t
  rcases p with _ | p <;> simp [DC.D]

private theorem Deg_zero {C : DC} {n : ℤ} : C.Deg n (0 : C.Tot) := fun _ _ _ => rfl

private theorem Deg_add {C : DC} {n : ℤ} {x y : C.Tot} (hx : C.Deg n x) (hy : C.Deg n y) :
    C.Deg n (x + y) := fun p s h => by
  change x p s + y p s = 0
  rw [hx p s h, hy p s h, add_zero]

private theorem Deg_sub {C : DC} {n : ℤ} {x y : C.Tot} (hx : C.Deg n x) (hy : C.Deg n y) :
    C.Deg n (x - y) := fun p s h => by
  change x p s - y p s = 0
  rw [hx p s h, hy p s h, sub_zero]

private theorem tot_add {C C' : DC} (Φ : C.Hom C') (x y : C.Tot) :
    Φ.tot (x + y) = Φ.tot x + Φ.tot y := by
  funext p s
  exact map_add _ _ _

private theorem tot_sub {C C' : DC} (Φ : C.Hom C') (x y : C.Tot) :
    Φ.tot (x - y) = Φ.tot x - Φ.tot y := by
  funext p s
  exact map_sub _ _ _

private theorem tot_zero {C C' : DC} (Φ : C.Hom C') : Φ.tot (0 : C.Tot) = 0 := by
  funext p s
  exact map_zero _

private theorem Deg_tot {C C' : DC} (Φ : C.Hom C') {n : ℤ} {x : C.Tot} (h : C.Deg n x) :
    C'.Deg n (Φ.tot x) := fun p s hne => by
  change Φ p s (x p s) = 0
  rw [h p s hne, map_zero]

private theorem hom_d {C C' : DC} {Φ : C.Hom C'} (h : Φ.Ok) (p : ℕ) (s t : ℤ) (e : t = s + 1)
    (x : C.A p s) : Φ p t (C.d p s t x) = C'.d p s t (Φ p s x) := by
  subst e
  exact h.1 p s x

private theorem tot_D {C C' : DC} {Φ : C.Hom C'} (h : Φ.Ok) (n : ℤ) (x : C.Tot) :
    Φ.tot (C.D n x) = C'.D n (Φ.tot x) := by
  funext p t
  rcases p with _ | p
  · simp only [DC.D, DC.Hom.tot]
    exact hom_d h 0 (t - 1) t (by ring) _
  · simp only [DC.D, DC.Hom.tot, map_add (f := _), Units.smul_def, map_zsmul]
    rw [hom_d h (p + 1) (t - 1) t (by ring), h.2]

private theorem rel_zero {C : DC} {n : ℤ} {H : Type 1} [AddCommGroup H] {rel : C.Tot → H → Prop}
    (h : TModel C n rel) : rel 0 0 := by
  obtain ⟨x, -, -, r⟩ := h.surj 0
  have := h.sub x 0 x 0 r r
  simpa using this

end UpperTheory.DegreeAdditivity

open UpperTheory.DegreeAdditivity in
theorem UpperTheory.bijective_iff_totalQuasiIso_of_totalModels :
    ∀ (C C' : DC) (Φ : C.Hom C'), C.Ok → C'.Ok → Φ.Ok → ∀ (H H' : ℤ → Type 1) [∀ n, AddCommGroup (H n)] [∀ n, AddCommGroup (H' n)] (rel : ∀ n, C.Tot → H n → Prop) (rel' : ∀ n, C'.Tot → H' n → Prop) (F : ∀ n, H n → H' n),
    (∀ n, TModel C n (rel n)) → (∀ n, TModel C' n (rel' n)) → (∀ n x a, rel n x a → rel' n (Φ.tot x) (F n a)) → ((∀ n, Function.Bijective (F n)) ↔ Φ.TotEx) := by
  intro C C' Φ hC hC' hΦ H H' _ _ rel rel' F hM hM' hF
  constructor
  · intro hbij n a y ha hy hDa hΦa
    obtain ⟨ca, ra⟩ := (hM (n + 1)).ex a ha hDa
    have r0 : rel' (n + 1) 0 (F (n + 1) 0) := by
      have := hF (n + 1) 0 0 (rel_zero (hM (n + 1)))
      rwa [tot_zero] at this
    have hF0 : F (n + 1) 0 = 0 :=
      ((hM' (n + 1)).zero 0 (F (n + 1) 0) Deg_zero r0).2 ⟨0, Deg_zero, D_zero _⟩
    have hFa : F (n + 1) ca = 0 := by
      refine ((hM' (n + 1)).zero _ _ (Deg_tot Φ ha) (hF (n + 1) a ca ra)).2 ⟨y, ?_, ?_⟩
      · simpa using hy
      · simpa using hΦa.symm
    have hca : ca = 0 := (hbij (n + 1)).1 (hFa.trans hF0.symm)
    obtain ⟨a', ha', hDa'⟩ := ((hM (n + 1)).zero a ca ha ra).1 hca
    simp only [add_sub_cancel_right] at ha' hDa'
    have hz : C'.Deg n (y - Φ.tot a') := Deg_sub hy (Deg_tot Φ ha')
    have hDz : C'.D n (y - Φ.tot a') = 0 := by
      rw [D_sub, ← tot_D hΦ, hDa', hΦa, sub_self]
    obtain ⟨cz, rz⟩ := (hM' n).ex _ hz hDz
    obtain ⟨c, hc⟩ := (hbij n).2 cz
    obtain ⟨w, hw, hDw, rw⟩ := (hM n).surj c
    have r2 := (hM' n).sub _ _ _ _ rz (hF n w c rw)
    rw [hc, sub_self] at r2
    obtain ⟨y', hy', hDy'⟩ :=
      ((hM' n).zero _ _ (Deg_sub hz (Deg_tot Φ hw)) r2).1 rfl
    refine ⟨a' + w, y', Deg_add ha' hw, hy', ?_, ?_⟩
    · rw [D_add, hDa', hDw, add_zero]
    · rw [tot_add, hDy']
      abel
  · intro hT m
    constructor
    · intro c1 c2 h12
      obtain ⟨x1, hx1, hD1, r1⟩ := (hM m).surj c1
      obtain ⟨x2, hx2, hD2, r2⟩ := (hM m).surj c2
      have r12 := (hM m).sub _ _ _ _ r1 r2
      have r12' := (hM' m).sub _ _ _ _ (hF m _ _ r1) (hF m _ _ r2)
      rw [h12, sub_self, ← tot_sub] at r12'
      obtain ⟨y, hy, hDy⟩ :=
        ((hM' m).zero _ 0 (Deg_tot Φ (Deg_sub hx1 hx2)) r12').1 rfl
      obtain ⟨a', -, ha', -, hDa', -⟩ := hT (m - 1) (x1 - x2) y
        (by simpa using Deg_sub hx1 hx2) hy
        (by rw [sub_add_cancel, D_sub, hD1, hD2, sub_self]) hDy.symm
      exact sub_eq_zero.mp (((hM m).zero _ _ (Deg_sub hx1 hx2) r12).2 ⟨a', ha', hDa'⟩)
    · intro c'
      obtain ⟨y, hy, hDy, ry⟩ := (hM' m).surj c'
      obtain ⟨a', y', ha', hy', hDa', hyeq⟩ :=
        hT m 0 y Deg_zero hy (D_zero _) (by rw [tot_zero, hDy])
      obtain ⟨c, rc⟩ := (hM m).ex a' ha' hDa'
      refine ⟨c, ?_⟩
      have r := (hM' m).sub _ _ _ _ ry (hF m _ _ rc)
      have h0 : c' - F m c = 0 :=
        ((hM' m).zero _ _ (Deg_sub hy (Deg_tot Φ ha')) r).2 ⟨y', hy', by rw [hyeq]; abel⟩
      exact (sub_eq_zero.mp h0).symm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveSemiMapOpOfBijectiveCochainPushforward
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private noncomputable def UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward.toRcx {R : Type} [CommRing R] {L B : Cx R} (ρ : SemiMap L B) :
    SemiMap L ((rcx (Int.castRingHom R)).obj B) where
  app U s := ((idSemi (Int.castRingHom R) B).app U s).comp (ρ.app U s)
  nat g s a := ((idSemi (Int.castRingHom R) B).nat g s _).trans
    (congrArg ((idSemi (Int.castRingHom R) B).app _ s) (ρ.nat g s a))
  comm U s t a := ((idSemi (Int.castRingHom R) B).comm U s t _).trans
    (congrArg ((idSemi (Int.castRingHom R) B).app U t) (ρ.comm U s t a))

theorem UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward :
    ∀ (R : Type) [CommRing R] (L B : Cx R) (ρ : SemiMap L B) (E : Spc) (n : ℤ), Function.Bijective (cpush ((chains ℤ).obj E) ρ.toZ n) → Function.Bijective (ρ.op.app E n) := by
  intro R _ L B ρ E n hb
  have idBij : ∀ (K : Cx R) (U : Scheme.{0}) (s : ℤ),
      Function.Bijective ((idSemi (Int.castRingHom R) K).app U s) :=
    fun _ _ _ => ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩
  have bL := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective R ℤ (idSemi (Int.castRingHom R) L) (idSemi (Int.castRingHom R) L) (𝟙 _)
    (fun _ _ _ => rfl)).2 (idBij L) E n
  have bB := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective R ℤ (idSemi (Int.castRingHom R) B) (idSemi (Int.castRingHom R) B) (𝟙 _)
    (fun _ _ _ => rfl)).2 (idBij B) E n
  have key : ∀ x, (idSemi (Int.castRingHom R) B).op.app E n (ρ.op.app E n x) =
      cpush ((chains ℤ).obj E) ρ.toZ n ((idSemi (Int.castRingHom R) L).op.app E n x) := by
    intro x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R R ρ).1 E n α
    obtain ⟨γ, hγ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ (idSemi (Int.castRingHom R) B)).1 E n β
    have h1 := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R R ρ).2 E n α β hβ
    have h2 := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ (idSemi (Int.castRingHom R) B)).2 E n β γ hγ
    have h3 := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ (UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward.toRcx ρ)).2 E n α γ
      (fun p s h U y => (hγ p s h U y).trans (congrArg _ (hβ p s h U y)))
    rw [h1, h2, ← h3]
    exact (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective R ℤ (idSemi (Int.castRingHom R) L) (UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward.toRcx ρ) ρ.toZ
      (fun _ _ _ => rfl)).1 E n _
  have comp : Function.Bijective
      ((idSemi (Int.castRingHom R) B).op.app E n ∘ ρ.op.app E n) := by
    have : ((idSemi (Int.castRingHom R) B).op.app E n ∘ ρ.op.app E n) =
        (cpush ((chains ℤ).obj E) ρ.toZ n ∘ (idSemi (Int.castRingHom R) L).op.app E n) := funext key
    rw [this]
    exact hb.comp bL
  exact (Function.Bijective.of_comp_iff' bB _).1 comp
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyBaseChangeIntegralSurjectiveCech
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.DescIntPf

private theorem level_rel {Y X Y₀ S S₀ L : Scheme.{0}} (k : Y ⟶ X) (r : X ⟶ S) (c : S₀ ⟶ S)
    (k₀ : Y₀ ⟶ pullback r c) (m : cech k₀ ⟶ cech k)
    (hm : IsPullback m (cechAug k₀) (cechAug k) (sch.map (pullback.fst r c)))
    (p : SimplexCategoryᵒᵖ) (l : L ⟶ X) (e : yoneda.obj L ≅ (cech k).obj p)
    (he : e.hom ≫ (cechAug k).app p = yoneda.map l) (q : ℕ) (i n : ℤ)
    (h : RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst (l ≫ r) c))) :
    RelZS (ZMod q) (tw q i) n (disc.map (m.app p)) := by
  have hp : IsPullback (m.app p) ((cechAug k₀).app p) ((cechAug k).app p)
      (yoneda.map (pullback.fst r c)) :=
    hm.map ((evaluation _ _).obj p)
  have hB : IsPullback (m.app p ≫ e.inv) ((cechAug k₀).app p) (yoneda.map l)
      (yoneda.map (pullback.fst r c)) := by
    refine hp.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · rw [Iso.refl_hom, Iso.symm_hom, ← he]
      erw [Iso.inv_hom_id_assoc, Category.comp_id]
    · erw [Category.comp_id]
      try erw [Category.id_comp]
  let φ : pullback (l ≫ r) c ⟶ pullback r c :=
    pullback.lift (pullback.fst (l ≫ r) c ≫ l) (pullback.snd (l ≫ r) c)
      (by simp [pullback.condition])
  have hφ₁ : φ ≫ pullback.fst r c = pullback.fst (l ≫ r) c ≫ l := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd r c = pullback.snd (l ≫ r) c := pullback.lift_snd _ _ _
  have hS : IsPullback (pullback.fst (l ≫ r) c) φ l (pullback.fst r c) := by
    refine IsPullback.of_bot ?_ hφ₁.symm (IsPullback.of_hasPullback r c)
    rw [hφ₂]
    exact IsPullback.of_hasPullback (l ≫ r) c
  have hA := hS.map yoneda
  let ι := IsPullback.isoIsPullback _ _ hA hB
  have hι : ι.hom ≫ m.app p ≫ e.inv = yoneda.map (pullback.fst (l ≫ r) c) :=
    IsPullback.isoIsPullback_hom_fst _ _ hA hB
  have key : yoneda.map (pullback.fst (l ≫ r) c) ≫ e.hom = ι.hom ≫ m.app p := by
    rw [← hι]
    simp
  refine RelZS.of_iso (ZMod q) (tw q i) (sch.map (pullback.fst (l ≫ r) c)) (disc.map (m.app p))
    (disc.mapIso ι) (disc.mapIso e) ?_ n h
  have := congrArg (fun f => disc.map f) key
  simp only [Functor.map_comp] at this
  exact this

private noncomputable def wpOne {A B : Scheme.{0}ᵒᵖ ⥤ Type} (f : A ⟶ B) :
    A ≅ widePullback B (fun _ : Fin (0 + 1) => A) (fun _ => f) where
  hom := WidePullback.lift f (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  inv := WidePullback.π (fun _ : Fin (0 + 1) => f) 0
  hom_inv_id := WidePullback.lift_π _ _ _ _ _
  inv_hom_id := by
    apply WidePullback.hom_ext (fun _ : Fin (0 + 1) => f)
    · intro j
      obtain rfl : j = 0 := Fin.fin_one_eq_zero j
      rw [Category.assoc, WidePullback.lift_π]
      simp
    · rw [Category.assoc, WidePullback.lift_base]
      simp

private noncomputable def cech_zero {Y X : Scheme.{0}} (k : Y ⟶ X) :
    yoneda.obj Y ≅ (cech k).obj (Opposite.op (SimplexCategory.mk 0)) :=
  wpOne (yoneda.map k)

private theorem cech_zero_aug {Y X : Scheme.{0}} (k : Y ⟶ X) :
    (cech_zero k).hom ≫ (cechAug k).app (Opposite.op (SimplexCategory.mk 0)) = yoneda.map k :=
  WidePullback.lift_base _ _ _ _

theorem UpperTheory.cohomology_base_change_integral_surjective_cech :
    B4 → ∀ (q : ℕ) (i : ℤ) {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) [IsIntegralHom k] [Surjective k] (r : X ⟶ S) (c : S₀ ⟶ S), IsUnit (q : Γ(X, ⊤)) → ∃ (U E : Spc) (u : U ⟶ E) (a' : U ⟶ sch.obj (pullback r c)) (a : E ⟶ sch.obj X), u ≫ a = a' ≫ sch.map (pullback.fst r c) ∧ Eqv _ a (tw q i) ∧ Eqv _ a' (tw q i) ∧ (∀ p : ℕ, ∃ (L : Scheme.{0}) (l : L ⟶ X), IsIntegralHom l ∧ ∀ m, RelZS (ZMod q) (tw q i) m (sch.map (pullback.fst (l ≫ r) c)) → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) ∧ ∀ m, RelZS (ZMod q) (tw q i) m (sch.map (pullback.fst (k ≫ r) c)) → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk 0)))) := by
  intro b4 q i Y X S S₀ k _ _ r c hq
  have hP := IsPullback.of_hasPullback k (pullback.fst r c)
  obtain ⟨u, hu, -⟩ := GlobalTheory.cech_baseChange Y X _ _ _ _ k (pullback.fst r c) hP
  have hq₀ : IsUnit (q : Γ(pullback r c, ⊤)) := by
    simpa using hq.map (pullback.fst r c).appTop.hom
  haveI : IsIntegralHom (pullback.snd k (pullback.fst r c)) := MorphismProperty.of_isPullback hP inferInstance
  haveI : Surjective (pullback.snd k (pullback.fst r c)) := MorphismProperty.of_isPullback hP inferInstance
  refine ⟨_, _, u, cechAug _, cechAug k, hu.w, b4 q k hq i, b4 q _ hq₀ i, fun p => ?_, fun n h => ?_⟩
  · obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.EtC.cech_level_representable (@IsIntegralHom) Y X k inferInstance
      (Opposite.op (SimplexCategory.mk p))
    haveI : IsIntegralHom π := hπ
    exact ⟨Z, π ≫ k, inferInstance, fun n h =>
      level_rel k r c _ u hu _ (π ≫ k) e he q i n h⟩
  · exact level_rel k r c _ u hu _ k (cech_zero k) (cech_zero_aug k) q i n h
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyClassInLSurjectiveAndInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

namespace UpperTheory.Kun.InL

variable {R : Type} [CommRing R]

private theorem sgn {A : Type*} [AddCommGroup A] (a b : ℤˣ) (x : A) : b • a • a • b • x = x := by
  rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;> simp

private theorem inL_coe {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) :
    (inL h α₁ α₂).1 = α₁.1.comp (Cochain.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
      n.negOnePow • (α₂.1.rightShift (-1) n (by omega)).comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n) := rfl

private theorem inL_fst {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) :
    (inL h α₁ α₂).1.comp (Cochain.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero n) = α₁.1 := by
  rw [inL_coe, Cochain.add_comp, Cochain.units_smul_comp, Cochain.comp_assoc_of_second_is_zero_cochain,
    Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    biprod.inl_fst, biprod.inr_fst, Cochain.comp_id]
  simp

private theorem inL_snd {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) :
    (inL h α₁ α₂).1.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n) =
      n.negOnePow • α₂.1.rightShift (-1) n (by omega) := by
  rw [inL_coe, Cochain.add_comp, Cochain.units_smul_comp, Cochain.comp_assoc_of_second_is_zero_cochain,
    Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    biprod.inl_snd, biprod.inr_snd, Cochain.comp_id]
  simp

private theorem decomp {K I Q : Cx R} {n : ℤ} (x : Cochain K (LL I Q) n) :
    (x.comp (Cochain.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero n)).comp (Cochain.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
      (x.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n)).comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n) = x := by
  rw [Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.comp_assoc_of_second_is_zero_cochain,
    ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, ← Cochain.comp_add, ← Cochain.ofHom_add, biprod.total, Cochain.comp_id]

private theorem unsh {K Q : Cx R} {m n : ℤ} (h : m + 1 = n) (ε : ℤˣ) (y : Cocycle K (sh Q) n) :
    ∃ a : Cocycle K Q m, ε • a.1.rightShift (-1) n (by omega) = y.1 := by
  have hy : n + -1 = m := by omega
  refine ⟨Cocycle.mk (ε • y.1.rightUnshift m hy) (m + 1) rfl ?_, ?_⟩
  · rw [δ_units_smul, Cochain.δ_rightUnshift _ m hy (m + 1) (n + 1) (by omega), Cocycle.δ_eq_zero]
    simp
  · change ε • (ε • y.1.rightUnshift m hy).rightShift (-1) n hy = y.1
    rw [Cochain.rightShift_units_smul, Cochain.rightShift_rightUnshift, smul_smul, Int.units_mul_self, one_smul]

end UpperTheory.Kun.InL

open UpperTheory.Kun.InL in
theorem UpperTheory.cohomologyClass_inL_surjective_and_injective :
    ∀ (R : Type) [CommRing R] {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n),
        (∀ x : Cocycle K (LL I Q) n, ∃ (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m), CohomologyClass.mk x = CohomologyClass.mk (inL h α₁ α₂)) ∧
        ∀ (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m), CohomologyClass.mk (inL h α₁ α₂) = 0 → CohomologyClass.mk α₁ = 0 ∧ CohomologyClass.mk α₂ = 0 := by
  intro R _ K I Q m n h
  refine ⟨fun x => ?_, fun α₁ α₂ h0 => ?_⟩
  · obtain ⟨a, ha⟩ := unsh (K := K) (Q := Q) h n.negOnePow (zcomp x (Cocycle.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n))
    refine ⟨zcomp x (Cocycle.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero n), a, ?_⟩
    congr 1
    apply Cocycle.ext
    rw [inL_coe]
    have e : n.negOnePow • a.1.rightShift (-1) n (by omega) = x.1.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero n) := ha
    rw [← Cochain.units_smul_comp, e]
    exact (decomp x.1).symm
  · obtain ⟨p, hp, y, hy⟩ := (CohomologyClass.mk_eq_zero_iff _).1 h0
    have hy' : δ p n y = (inL h α₁ α₂).1 := hy
    constructor
    · rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨p, hp, y.comp (Cochain.ofHom (biprod.fst : LL I Q ⟶ I)) (add_zero p), ?_⟩
      rw [δ_comp_ofHom, hy', inL_fst]
    · rw [CohomologyClass.mk_eq_zero_iff]
      have hs : δ p n (y.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero p)) =
          n.negOnePow • α₂.1.rightShift (-1) n (by omega) := by
        rw [δ_comp_ofHom, hy', inL_snd]
      have hn : n + -1 = m := by omega
      have e : δ (p + -1) m ((y.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero p)).rightUnshift (p + -1) rfl) =
          (-1 : ℤ).negOnePow • n.negOnePow • α₂.1 := by
        rw [Cochain.δ_rightUnshift _ (p + -1) rfl m n hn, hs, Cochain.rightUnshift_units_smul, Cochain.rightUnshift_rightShift]
      refine ⟨p + -1, by omega, n.negOnePow • (-1 : ℤ).negOnePow •
        (y.comp (Cochain.ofHom (biprod.snd : LL I Q ⟶ sh Q)) (add_zero p)).rightUnshift (p + -1) rfl, ?_⟩
      rw [δ_units_smul, δ_units_smul, e, sgn]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ColumnExactZeroOfTotalExactOfVerticalZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.ExtensionByZero

private noncomputable def ext0 (C : DC) (s : ℤ) (a : C.A 0 s) : C.Tot
  | 0, t => (Pi.single s a : ∀ t, C.A 0 t) t
  | _ + 1, _ => 0

private theorem extByZero_same (C : DC) (s : ℤ) (a : C.A 0 s) : ext0 C s a 0 s = a :=
  Pi.single_eq_same (M := fun t => C.A 0 t) s a

private theorem unitCharacterExtendByZero_ne_zero_of_isUnit (C : DC) (s : ℤ) (a : C.A 0 s) {t : ℤ} (h : t ≠ s) : ext0 C s a 0 t = 0 :=
  Pi.single_eq_of_ne (M := fun t => C.A 0 t) h a

private theorem extByZero_succ (C : DC) (s : ℤ) (a : C.A 0 s) (p : ℕ) (t : ℤ) : ext0 C s a (p + 1) t = 0 := rfl

private theorem extByZero_degree (C : DC) (s : ℤ) (a : C.A 0 s) : C.Deg s (ext0 C s a) := by
  intro p t h
  rcases p with _ | p
  · exact unitCharacterExtendByZero_ne_zero_of_isUnit C s a (fun e => h (by simp [e]))
  · rfl

private theorem d_idx (C : DC) (f : ∀ t, C.A 0 t) {u s : ℤ} (t : ℤ) (h : u = s) :
    C.d 0 u t (f u) = C.d 0 s t (f s) := by
  subst h; rfl

end UpperTheory.ExtensionByZero

open UpperTheory.ExtensionByZero in
theorem UpperTheory.columnExact_zero_of_totalExact_of_vertical_zero :
    ∀ (C C' : DC) (Φ : C.Hom C'), (∀ s x, C.δ 0 s x = 0) → (∀ s x, C'.δ 0 s x = 0) → Φ.TotEx → Φ.ColEx 0 := by
  intro C C' Φ h0 h0' hT s a y hda hΦ
  have hD : C.D (s + 1) (ext0 C (s + 1) a) = 0 := by
    funext p t
    rcases p with _ | p
    · change C.d 0 (t - 1) t (ext0 C (s + 1) a 0 (t - 1)) = 0
      by_cases h : t - 1 = s + 1
      · obtain rfl : t = s + 1 + 1 := by omega
        rw [d_idx C (ext0 C (s + 1) a 0) _ h, extByZero_same]
        exact hda
      · rw [unitCharacterExtendByZero_ne_zero_of_isUnit C _ a h, map_zero]
    · change C.d (p + 1) (t - 1) t (ext0 C (s + 1) a (p + 1) (t - 1)) +
        (s + 1 + 1).negOnePow • C.δ p t (ext0 C (s + 1) a p t) = 0
      rw [extByZero_succ, map_zero, zero_add]
      rcases p with _ | p
      · rw [h0, smul_zero]
      · rw [extByZero_succ, map_zero, smul_zero]
  have hE : Φ.tot (ext0 C (s + 1) a) = C'.D s (ext0 C' s y) := by
    funext p t
    rcases p with _ | p
    · change Φ 0 t (ext0 C (s + 1) a 0 t) = C'.d 0 (t - 1) t (ext0 C' s y 0 (t - 1))
      by_cases h : t = s + 1
      · subst h
        rw [d_idx C' (ext0 C' s y 0) _ (by omega : s + 1 - 1 = s), extByZero_same, extByZero_same]
        exact hΦ
      · rw [unitCharacterExtendByZero_ne_zero_of_isUnit C _ a h, unitCharacterExtendByZero_ne_zero_of_isUnit C' _ y (fun e => h (by omega)), map_zero, map_zero]
    · change Φ (p + 1) t (ext0 C (s + 1) a (p + 1) t) =
        C'.d (p + 1) (t - 1) t (ext0 C' s y (p + 1) (t - 1)) +
          (s + 1).negOnePow • C'.δ p t (ext0 C' s y p t)
      rw [extByZero_succ, extByZero_succ, map_zero, map_zero, zero_add]
      rcases p with _ | p
      · rw [h0', smul_zero]
      · rw [extByZero_succ, map_zero, smul_zero]
  obtain ⟨a', y', -, -, h1, h2⟩ :=
    hT s (ext0 C (s + 1) a) (ext0 C' s y) (extByZero_degree C _ a) (extByZero_degree C' _ y) hD hE
  refine ⟨a' 0 s, y' 0 (s - 1), ?_, ?_⟩
  · have h := congrFun (congrFun h1 0) (s + 1)
    change C.d 0 (s + 1 - 1) (s + 1) (a' 0 (s + 1 - 1)) = ext0 C (s + 1) a 0 (s + 1) at h
    rw [d_idx C (a' 0) _ (by omega : s + 1 - 1 = s), extByZero_same] at h
    exact h
  · have h := congrFun (congrFun h2 0) s
    rw [show ext0 C' s y 0 s = y from extByZero_same C' s y] at h
    exact h
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIdempotentSubmonoidIsLocalizationAtPrime
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace LateralTheory.E.BuildCut

theorem UpperTheory.exists_idempotent_submonoid_isLocalization_atPrime :
    ∀ {W : Type} [CommRing W], ProdACF W → ∀ (q : PrimeSpectrum W),
        ∃ T : Submonoid W, (∀ s ∈ T, IsIdempotentElem s ∧ s ∉ q.asIdeal) ∧ IsLocalization T (Localization.AtPrime q.asIdeal) := by
  intro W _ hW q
  let T : Submonoid W :=
    { carrier := {s | IsIdempotentElem s ∧ s ∉ q.asIdeal}
      one_mem' := ⟨IsIdempotentElem.one, (Ideal.ne_top_iff_one _).mp q.isPrime.ne_top⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨ha.1.mul hb.1, fun h => (q.isPrime.mem_or_mem h).elim ha.2 hb.2⟩ }
  refine ⟨T, fun s hs => hs, ?_⟩
  have hT : ∀ s ∈ T, s ∈ q.asIdeal.primeCompl := fun s hs => hs.2
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    exact IsLocalization.map_units (Localization.AtPrime q.asIdeal)
      (⟨s, hT s hs⟩ : q.asIdeal.primeCompl)
  · intro z
    obtain ⟨⟨x, ⟨s, hs⟩⟩, hz⟩ := IsLocalization.surj q.asIdeal.primeCompl z
    obtain ⟨e, u, he, hu, rfl⟩ := hW.2 s
    have he_q : e ∉ q.asIdeal := fun h => hs (q.asIdeal.mul_mem_right u h)
    refine ⟨⟨x * ↑hu.unit⁻¹, ⟨e, he, he_q⟩⟩, ?_⟩
    simp only at hz ⊢
    calc z * algebraMap W _ e = z * algebraMap W _ (e * u * ↑hu.unit⁻¹) := by
          rw [mul_assoc e, IsUnit.mul_val_inv, mul_one]
      _ = (z * algebraMap W _ (e * u)) * algebraMap W _ ↑hu.unit⁻¹ := by
          rw [map_mul (algebraMap W _) (e * u), mul_assoc]
      _ = algebraMap W _ x * algebraMap W _ ↑hu.unit⁻¹ := by rw [hz]
      _ = algebraMap W _ (x * ↑hu.unit⁻¹) := (map_mul _ _ _).symm
  · intro x y hxy
    obtain ⟨⟨c, hc⟩, hcxy⟩ := (IsLocalization.eq_iff_exists q.asIdeal.primeCompl _).mp hxy
    obtain ⟨e, u, he, hu, rfl⟩ := hW.2 c
    have he_q : e ∉ q.asIdeal := fun h => hc (q.asIdeal.mul_mem_right u h)
    refine ⟨⟨e, he, he_q⟩, ?_⟩
    simp only at hcxy ⊢
    have huv : u * ↑hu.unit⁻¹ = 1 := IsUnit.mul_val_inv hu
    calc e * x = e * u * x * ↑hu.unit⁻¹ := by linear_combination (-(e * x)) * huv
      _ = e * u * y * ↑hu.unit⁻¹ := by rw [hcxy]
      _ = e * y := by linear_combination (e * y) * huv
end

