module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion
public import Development.EtaleCohomology.EtaleTrace.LRingPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
public import Development.EtaleCohomology.EtaleTrace.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.CupOneRight
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di.PUntw

open LateralTheory.EtaleTrace.LRingPf

private theorem inv_sch {q : ℕ} {X : Scheme.{0}} (hq : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  intro U ⟨f⟩
  have h := hq.map (Scheme.Hom.appTop f).hom
  simpa using h

private theorem swap0 (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {E : Spc} {m d n i t s w : ℤ}
    (a : Ht q E m i) (c : Ht q E d t) (ρ : Ht q E 0 s)
    (hn : m + (d + 0) = n) (hi : i + (t + s) = w) (hn' : m + 0 + d = n) (hi' : i + s + t = w) :
    Ht.cast hn hi (cup q a (cup q c ρ)) = Ht.cast hn' hi' (cup q (cup q a ρ) c) := by
  have hc : cup q c ρ = Ht.cast (by ring) (by ring) (cup q ρ c) := by
    rw [(h6 q E).2.2 c ρ]
    simp
  have hA : cup q (cup q a ρ) c = Ht.cast (by ring) (by ring) (cup q a (cup q ρ c)) :=
    (h6 q E).2.1 a ρ c
  rw [hc, cup_cast_right, LRingPf.cast_cast, hA, LRingPf.cast_cast]

private theorem cup_one_right (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {E : Spc} (hE : Inv q E) {m t : ℤ}
    (a : Ht q E m t) (hn : m + 0 = m) (ht : t + 0 = t) : Ht.cast hn ht (cup q a (one q E)) = a := by
  have hc : cup q a (one q E) = Ht.cast (by ring) (by ring) (cup q (one q E) a) := by
    rw [(h6 q E).2.2 a (one q E)]
    simp
  have hu : cup q (one q E) a = Ht.cast (by ring) (by ring) a := (h6 q E).1 hE a
  rw [hc, hu, LRingPf.cast_cast, LRingPf.cast_cast]
  rfl

private theorem root_idx {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) {i j : ℤ} (h : i = j) :
    rootClass j ζ = Ht.cast rfl h (rootClass i ζ) := by
  subst h; rfl

private theorem two_roots (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {X : Scheme.{0}} (hE : Inv q (sch.obj X))
    (ζ : Prim q Γ(X, ⊤)) {m t i j : ℤ} (a : Ht q (sch.obj X) m t) (hij : i + j = 0)
    (hn : m + 0 + 0 = m) (ht : t + i + j = t) :
    Ht.cast hn ht (cup q (cup q a (rootClass i ζ)) (rootClass j ζ)) = a := by
  have hA : cup q (cup q a (rootClass i ζ)) (rootClass j ζ) =
      Ht.cast (by ring) (by ring) (cup q a (cup q (rootClass i ζ) (rootClass j ζ))) :=
    (h6 q (sch.obj X)).2.1 a _ _
  rw [hA, ((GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).2 X ζ i j).1, root_idx ζ hij.symm, ((GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).2 X ζ 0 0).2,
    LRingPf.cast_cast, LRingPf.cast_cast, cup_cast_right, LRingPf.cast_cast]
  exact cup_one_right h6 hE a (by ring) (by ring)

private theorem bij_root (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {X : Scheme.{0}} (hE : Inv q (sch.obj X))
    (ζ : Prim q Γ(X, ⊤)) (m w : ℤ) :
    Function.Bijective fun a : Ht q (sch.obj X) m 0 =>
      Ht.cast (add_zero m) (zero_add w) (cup q a (rootClass w ζ)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun b => Ht.cast (add_zero m) (add_neg_cancel w) (cup q b (rootClass (-w) ζ)), ?_, ?_⟩
  · intro a
    simp only
    rw [cup_cast_left, LRingPf.cast_cast]
    exact two_roots h6 hE ζ a (add_neg_cancel w) (by ring) (by ring)
  · intro b
    simp only
    rw [cup_cast_left, LRingPf.cast_cast]
    exact two_roots h6 hE ζ b (neg_add_cancel w) (by ring) (by ring)

private theorem term (hI : In) (hR : RootNat) (hP : PowRoot) {q : ℕ} [NeZero q] {E Z : Scheme.{0}} (r : E ⟶ Z)
    (ζ : Prim q Γ(Z, ⊤)) (x : Ht q (sch.obj E) 2 1) (n : ℤ) (j : ℕ) (a : Ht q (sch.obj Z) (n - 2 * (j : ℤ)) 0) :
    cup0 q (sub_add_cancel n _) (pull _ (sch.map r) _ _ a)
        (pow0 q (untw q x (rootClass (-1) (ζ.map r.appTop.hom))) j) =
      ((cup q (pull _ (sch.map r) _ _ (Ht.cast (add_zero _) (zero_add _) (cup q a (rootClass ((0 : ℤ) - (j : ℤ)) ζ))))
        (cpow q x j)).cast (by ring) (by ring) : Ht q _ n 0) := by
  have h6 := hI.a6ring
  have hN := (hI.a6nat q).1 (sch.map r) a (rootClass ((0 : ℤ) - (j : ℤ)) ζ)
  rw [hP hI q (ζ.map r.appTop.hom) x j]
  simp only [cup0]
  rw [cup_cast_right, LRingPf.cast_cast, pull_cast, hN, hR q _ r ζ, cup_cast_left, LRingPf.cast_cast,
    root_idx (ζ.map r.appTop.hom) (show (0 : ℤ) - j = -j by ring), cup_cast_right, cup_cast_right,
    LRingPf.cast_cast]
  exact swap0 h6 _ _ _ _ _ _ _

end UpperTheory.Gal.KunnethLefschetz.Di.PUntw

open UpperTheory.Gal.KunnethLefschetz.Di.PUntw in
theorem UpperTheory.Gal.KunnethLefschetz.Di.untw_holds :
    UpperTheory.Gal.KunnethLefschetz.Di.Untw := by
  intro hI hR hP q _ N E Z r ζ x hT n
  have h6 := hI.a6ring
  have hE : Inv q (sch.obj Z) := inv_sch ζ.2.1
  let Φ : ((j : Fin N) → Ht q (sch.obj Z) (n - 2 * ((j : ℕ) : ℤ)) 0) →
      ((j : Fin N) → Ht q (sch.obj Z) (n - 2 * ((j : ℕ) : ℤ)) ((0 : ℤ) - ((j : ℕ) : ℤ))) :=
    fun a j => Ht.cast (add_zero _) (zero_add _) (cup q (a j) (rootClass ((0 : ℤ) - ((j : ℕ) : ℤ)) ζ))
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro a b h
      funext j
      exact (bij_root h6 hE ζ _ _).1 (congrFun h j)
    · intro c
      choose a ha using fun j : Fin N => (bij_root h6 hE ζ _ ((0 : ℤ) - ((j : ℕ) : ℤ))).2 (c j)
      exact ⟨a, funext ha⟩
  have hc := (hT n 0).comp hΦ
  convert hc using 1
  funext a
  refine Finset.sum_congr rfl fun j _ => ?_
  exact term hI hR hP r ζ x n j (a j)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.FirstChernClassIsBaseChange
section
set_option backward.isDefEq.respectTransparency false

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di.ChernBaseChange

private def sq {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X) (τ : Y ⟶ Y') (hτ : τ ≫ f' = f) :
    Arrow.mk (yoneda.map f) ⟶ Arrow.mk (yoneda.map f') :=
  Arrow.homMk (yoneda.map τ) (𝟙 _) (by simp [← Functor.map_comp, hτ])

private def cm {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X) (τ : Y ⟶ Y') (hτ : τ ≫ f' = f) : cech f ⟶ cech f' :=
  Arrow.mapCechNerve (sq f f' τ hτ)

private theorem cm_aug {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X) (τ : Y ⟶ Y') (hτ : τ ≫ f' = f) :
    cm f f' τ hτ ≫ cechAug f' = cechAug f := by
  refine ((Arrow.mapAugmentedCechNerve (sq f f' τ hτ)).w).trans ?_
  exact (congrArg (fun t => (Arrow.mk (yoneda.map f)).augmentedCechNerve.hom ≫ t)
    (CategoryTheory.Functor.map_id (SimplicialObject.const _) (yoneda.obj X))).trans (Category.comp_id _)

private theorem cm_pt {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X) (τ : Y ⟶ Y') (hτ : τ ≫ f' = f) (k : ℕ)
    {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x) :
    ((cm f f' τ hτ).app (op (SimplexCategory.mk k))).app (op U) (cechPt f k x y h) =
      cechPt f' k x (fun i => y i ≫ τ) (fun i => by rw [Category.assoc, hτ, h]) := by
  have e : WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x) (fun i => yoneda.map (y i))
        (fun i => by rw [← yoneda.map_comp, h i]) ≫ (cm f f' τ hτ).app (op (SimplexCategory.mk k)) =
      WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f') (yoneda.map x) (fun i => yoneda.map (y i ≫ τ))
        (fun i => by rw [← yoneda.map_comp, Category.assoc, hτ, h i]) := by
    apply WidePullback.hom_ext
    · intro j
      simp [cm, sq, Arrow.mapCechNerve]
    · simp [cm, sq, Arrow.mapCechNerve]
  exact congrArg (fun t => t.app (op U) (𝟙 U)) e

private theorem cech_inv (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) (hq : IsUnit (q : Γ(X, ⊤))) : Inv q (cech f) := by
  intro U ⟨x⟩
  let s : U ⟶ Y := (WidePullback.π (fun _ : Fin 1 => yoneda.map f) 0).app (op U) x
  have h := hq.map ((s ≫ f).appTop).hom
  simpa using h

private theorem u_congr {X : Scheme.{0}} (D : CrystallineSemistableComparison.E.LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (ha : a = a') (hb : b = b') (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ha hb
  rfl

end UpperTheory.Gal.KunnethLefschetz.Di.ChernBaseChange

open UpperTheory.Gal.KunnethLefschetz.Di.ChernBaseChange in
theorem UpperTheory.Gal.KunnethLefschetz.Di.first_chern_class_isBaseChange :
    UpperTheory.Gal.KunnethLefschetz.Di.FirstChernClassBaseChange := by
  intro hI q _ Y Y₁ Y₂ D a c D' π hBC hq x ⟨L, hL, hx⟩
  obtain ⟨h1, h2, h3⟩ := hBC
  let π₂ : ((D.pb a).pb c).Y ⟶ D.Y := pullback.fst (D.pb a).f c ≫ pullback.fst D.f a
  have hπ : π₂ ≫ D.f = ((D.pb a).pb c).f ≫ c ≫ a := by
    have e₁ : pullback.fst (D.pb a).f c ≫ (D.pb a).f = ((D.pb a).pb c).f ≫ c := pullback.condition
    have e₂ : pullback.fst D.f a ≫ D.f = (D.pb a).f ≫ a := pullback.condition
    change (pullback.fst (D.pb a).f c ≫ pullback.fst D.f a) ≫ D.f = _
    rw [Category.assoc, e₂, ← Category.assoc, e₁, Category.assoc]
  obtain ⟨τ, hτ, hτf⟩ := h2 _ π₂ _ hπ
  refine ⟨cm _ _ τ hτf ≫ L, ?_, ?_⟩
  · intro V z b hb
    change lineUnit L (((cm _ _ τ hτf).app (op (SimplexCategory.mk 1))).app (op V) (cechPt _ 1 z b hb)) = _
    have hh : ((b 0 ≫ τ) ≫ π) ≫ D.f = ((b 1 ≫ τ) ≫ π) ≫ D.f := by
      simp only [Category.assoc, h1]
      rw [← Category.assoc τ, hτf, ← Category.assoc (b 0), ← Category.assoc (b 1), hb 0, hb 1]
    rw [cm_pt, hL, h3 V _ _ _ hh]
    exact u_congr D (by simp only [Category.assoc, hτ]; rfl) (by simp only [Category.assoc, hτ]; rfl) _ _
  · have hinv := cech_inv q D'.f hq
    have e := (hI.a6nat q).2.2.1 (cm _ _ τ hτf) L hinv
    rw [← e, ← hx, ← pull_comp, cm_aug]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PClear
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di.ClearPf

variable {l : ℕ} [Fact l.Prime]

private theorem coe_ne {b : ℤ_[l]} (hb : b ≠ 0) : (b : ℚ_[l]) ≠ 0 := by
  rwa [Ne, PadicInt.coe_eq_zero]

private theorem den {M : Type*} [AddCommGroup M] [Module ℤ_[l] M] (z : ℚ_[l] ⊗[ℤ_[l]] M) :
    ∃ b : ℤ_[l], b ≠ 0 ∧ ∀ B : ℤ_[l], b ∣ B → ∃ y : M, (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y = (B : ℚ_[l]) • z := by
  obtain ⟨b, x, hb, rfl⟩ := H0LimitCoherence.tensor_form l z
  refine ⟨b, hb, fun B hB => ?_⟩
  obtain ⟨c, rfl⟩ := hB
  refine ⟨c • x, ?_⟩
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  congr 1
  have hb' := coe_ne hb
  rw [Algebra.smul_def, smul_eq_mul, PadicInt.coe_mul, mul_one]
  simp only [PadicInt.algebraMap_apply]
  field_simp

private theorem toV_cup (R : Ring l) {X : Scheme.{0}} {i j : ℕ} {x : TT l X i} {y : TT l X j} {z : TT l X (i + j)}
    (hz : CupL x y z) (hh : (i : ℤ) + j = ((i + j : ℕ) : ℤ)) : toV z = cupV l X hh (toV x) (toV y) := by
  exact (R.isCup X (i : ℤ) (j : ℤ) _ hh x y z (fun k => (hz k).trans rfl)).symm

private theorem ex_cup (h11 : A11) {X : Scheme.{0}} {i j : ℕ} (x : TT l X i) (y : TT l X j) :
    ∃ z : TT l X (i + j), CupL x y z :=
  ⟨LRingPf.cupL l (sch.obj X) (Nat.cast_add i j).symm h11 x y, fun _ => rfl⟩

private theorem toV_castL (R : Ring l) {X : Scheme.{0}} {i j n : ℕ} {x : TT l X i} {y : TT l X j} {z : TT l X (i + j)}
    (hz : CupL x y z) (hn : i + j = n) (hh : (i : ℤ) + j = (n : ℤ)) :
    toV (castL hn z) = cupV l X hh (toV x) (toV y) := by
  subst hn
  exact toV_cup R hz hh

private theorem scale {X P : Scheme.{0}} (p₁ p₂ : P ⟶ X) {i j : ℕ} {r : ℤ} (hh : (i : ℤ) + j = r) (β : ℚ_[l])
    {a : V l X i} {b : V l X j} {ah : TT l X i} {bh : TT l X j} (ha : toV ah = β • a) (hb : toV bh = β • b) :
    cupV l P hh (toV (pullHl l (sch.map p₁) _ 0 ah)) (toV (pullHl l (sch.map p₂) _ 0 bh)) =
      β • β • cupV l P hh (pb l p₁ _ a) (pb l p₂ _ b) := by
  have e₁ : toV (pullHl l (sch.map p₁) (i : ℤ) 0 ah) = pb l p₁ (i : ℤ) (toV ah) :=
    (LRingPf.pb_tmul l p₁ (i : ℤ) ah).symm
  have e₂ : toV (pullHl l (sch.map p₂) (j : ℤ) 0 bh) = pb l p₂ (j : ℤ) (toV bh) :=
    (LRingPf.pb_tmul l p₂ (j : ℤ) bh).symm
  rw [e₁, e₂, ha, hb]
  simp only [map_smul, LinearMap.smul_apply]

end UpperTheory.Gal.KunnethLefschetz.Di.ClearPf

open UpperTheory.Gal.KunnethLefschetz.Di.ClearPf in
theorem UpperTheory.Gal.KunnethLefschetz.Di.clear_holds :
    UpperTheory.Gal.KunnethLefschetz.Di.Clear := by
  intro hIn l _ R d X P W p₁ p₂ π hl e hQ
  obtain ⟨δ, m, s, a, b, t, i, j, hij, u, v, hπ, hlin, hsum, hj, hδ⟩ := hQ
  have h11 := hIn.a11
  obtain ⟨bm, hbm0, hbm⟩ := den (l := l) m
  choose ba hba0 hba using fun c => den (l := l) (a c)
  choose bb hbb0 hbb using fun c => den (l := l) (b c)
  choose bu hbu0 hbu using fun c => den (l := l) (u c)
  choose bv hbv0 hbv using fun c => den (l := l) (v c)
  set D : ℤ_[l] := bm * (∏ c, ba c * bb c) * (∏ c, bu c * bv c) with hD
  have hD0 : D ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hbm0 ?_) ?_
    · exact Finset.prod_ne_zero_iff.mpr fun c _ => mul_ne_zero (hba0 c) (hbb0 c)
    · exact Finset.prod_ne_zero_iff.mpr fun c _ => mul_ne_zero (hbu0 c) (hbv0 c)
  have dA : ∀ c, ba c ∣ D := fun c => dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right ((dvd_mul_right _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ c))) _) _
  have dB : ∀ c, bb c ∣ D := fun c => dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right ((dvd_mul_left _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ c))) _) _
  have dU : ∀ c, bu c ∣ D := fun c =>
    dvd_mul_of_dvd_right ((dvd_mul_right _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ c))) _
  have dV : ∀ c, bv c ∣ D := fun c =>
    dvd_mul_of_dvd_right ((dvd_mul_left _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ c))) _
  have dM : bm ∣ D * D := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  clear_value D
  obtain ⟨w, hw⟩ := hbm _ dM
  choose a₀ ha₀ using fun c => hba c D (dA c)
  choose b₀ hb₀ using fun c => hbb c D (dB c)
  choose a₁ ha₁ using fun c => hbu c D (dU c)
  choose b₁ hb₁ using fun c => hbv c D (dV c)
  obtain ⟨z, hz⟩ := ex_cup h11 e w
  choose ab₀ hab₀ using fun c =>
    ex_cup h11 (pullHl l (sch.map p₁) _ 0 (a₀ c)) (pullHl l (sch.map p₂) _ 0 (b₀ c))
  choose ab hab using fun c =>
    ex_cup h11 (pullHl l (sch.map p₁) _ 0 (a₁ c)) (pullHl l (sch.map p₂) _ 0 (b₁ c))
  obtain ⟨one₀, hone, hone'⟩ := R.one_def X hl
  have hc : toV (∑ c, ab₀ c + ∑ c, castL (hij c) (ab c)) =
      ∑ c, toV (ab₀ c) + ∑ c, toV (castL (hij c) (ab c)) := by
    simp only [toV, TensorProduct.tmul_add, TensorProduct.tmul_sum]
  refine ⟨∑ c, ab₀ c + ∑ c, castL (hij c) (ab c), w, z, s, a₀, b₀, ab₀, t, i, j, hij, a₁, b₁, ab, one₀,
    (D : ℚ_[l]), hz, ?_, hab₀, hab, hj, hc, hone, coe_ne hD0, ?_, ?_⟩
  · refine (LRingPf.pb_tmul l π _ _).symm.trans ?_
    change pb l π _ (toV (∑ c, ab₀ c + ∑ c, castL (hij c) (ab c))) = toV z
    have hw' : toV w = ((D * D : ℤ_[l]) : ℚ_[l]) • m := hw
    rw [hc, toV_cup R hz (by push_cast; ring), hw', map_smul, ← hπ, ← map_smul]
    congr 1
    rw [hδ, smul_add, Finset.smul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [toV_cup R (hab₀ c) (by push_cast; ring), scale p₁ p₂ _ _ (ha₀ c) (hb₀ c), ← mul_smul,
        ← PadicInt.coe_mul]
      rfl
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [toV_castL R (hab c) (hij c) (by exact_mod_cast hij c), scale p₁ p₂ _ _ (ha₁ c) (hb₁ c),
        ← mul_smul, ← PadicInt.coe_mul]
  · have hfun : (fun c => toV (a₀ c)) = fun c => (D : ℚ_[l]) • a c := funext ha₀
    rw [hfun]
    exact hlin.units_smul fun _ => Units.mk0 _ (coe_ne hD0)
  · have hb : ∀ c, toV (b₀ c) = (D : ℚ_[l]) • b c := hb₀
    rw [Finset.sum_congr rfl fun c _ => hb c, ← Finset.smul_sum, hsum, hone']
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PDiagSq
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.EtaleTrace
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k]

private theorem pullback_exterior_product (hR : Ring l) {X P : Scheme.{0}} (p : X ⟶ S k) {p₁ p₂ : P ⟶ X} {φ : P ⟶ pullback p p}
    (h₁ : φ ≫ pullback.fst p p = p₁) (h₂ : φ ≫ pullback.snd p p = p₂) {a b w : ℤ} (h : a + b = w)
    (u : V l X a) (v : V l X b) :
    pb l φ w (ext2 l p h u v) = cupV l P h (pb l p₁ a u) (pb l p₂ b v) := by
  subst h₁ h₂
  rw [ext2, hR.nat, pb_comp, pb_comp]
  rfl

private theorem lift_gen (hR : Ring l) {X P : Scheme.{0}} (p : X ⟶ S k) {p₁ p₂ : P ⟶ X} {φ : P ⟶ pullback p p}
    (h₁ : φ ≫ pullback.fst p p = p₁) (h₂ : φ ≫ pullback.snd p p = p₂) (d : ℕ) {w : ℤ}
    (hw : w = ((2 + 2 * d : ℕ) : ℤ)) (c : ℚ_[l]) (x : V l (pullback p p) w)
    (hx : ∃ (n n' : ℤ) (h : n + n' = w) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ x = ext2 l p h u v) :
    ∃ (i j : ℕ) (_ : i + j = 2 + 2 * d) (u : V l X i) (v : V l X j), j ≠ 0 ∧
      ∀ hh : (i : ℤ) + j = w, c • pb l φ w x = cupV l P hh (pb l p₁ _ u) (pb l p₂ _ v) := by
  obtain ⟨n, n', h, u, v, h0, h1, rfl⟩ := hx
  obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le h1.le
  refine ⟨i, j, by omega, c • u, v, by omega, fun hh => ?_⟩
  rw [pullback_exterior_product hR p h₁ h₂, map_smul, map_smul, LinearMap.smul_apply]

private theorem core (hR : Ring l) (d : ℕ) {X P W : Scheme.{0}} (p : X ⟶ S k) {p₁ p₂ : P ⟶ X}
    {φ : P ⟶ pullback p p} (π : W ⟶ P) (h₁ : φ ≫ pullback.fst p p = p₁) (h₂ : φ ≫ pullback.snd p p = p₂)
    (e : V l W ((2 : ℕ) : ℤ)) {w w' : ℤ} (hw : w = ((2 + 2 * d : ℕ) : ℤ)) (hw' : w' = ((2 * d : ℕ) : ℤ))
    (h2 : ((2 : ℕ) : ℤ) + w' = w) (δ : V l (pullback p p) w) (m : V l W w') (s : ℕ) (a : Fin s → V l X w)
    (b : Fin s → V l X 0) (hδ : pb l (π ≫ φ) w δ = cupV l W h2 e m) (ha : LinearIndependent ℚ_[l] a)
    (hb : ∑ t, b t = oneV l X)
    (hs : δ - ∑ t, ext2 l p (add_zero _) (a t) (b t) ∈ Submodule.span ℚ_[l] {x : V l (pullback p p) w |
      ∃ (n n' : ℤ) (h : n + n' = w) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ x = ext2 l p h u v}) :
    DiagQ l d p₁ p₂ π e := by
  subst hw hw'
  obtain ⟨t, f, g, hsum⟩ := Submodule.mem_span_set'.1 hs
  choose i j hij u v hj huv using fun c => lift_gen hR p h₁ h₂ d rfl (f c) (g c).1 (g c).2
  refine ⟨pb l φ _ δ, m, s, a, b, t, i, j, hij, u, v, ?_, ha, hb, hj, ?_⟩
  · exact (LinearMap.congr_fun (pb_comp l π φ _) δ).symm.trans hδ
  · have hδ' : δ = ∑ t, ext2 l p (add_zero _) (a t) (b t) + ∑ c, f c • (g c : V l (pullback p p) _) := by
      rw [hsum]; abel
    have e1 : pb l φ _ δ = ∑ t, pb l φ _ (ext2 l p (add_zero _) (a t) (b t)) +
        ∑ c, f c • pb l φ _ (g c : V l (pullback p p) _) := by
      rw [congrArg (pb l φ _) hδ']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_smul]
    refine e1.trans (congrArg₂ (· + ·) (Finset.sum_congr rfl fun c _ => pullback_exterior_product hR p h₁ h₂ _ _ _)
      (Finset.sum_congr rfl fun c _ => huv c _))

theorem diagSq_holds : DiagSq := by
  intro hQ l _ k _ _ hl hR d X P p p₁ p₂ Δ h hΔ₁ hΔ₂ hSP hProj W E π i r c hsq hpair hr U hoff e he hpb
  have e₁ : h.isoPullback.hom ≫ pullback.fst p p = p₁ := h.isoPullback_hom_fst
  have e₂ : h.isoPullback.hom ≫ pullback.snd p p = p₂ := h.isoPullback_hom_snd
  have hdiag : Δ ≫ h.isoPullback.hom = pullback.diagonal p := by
    apply pullback.hom_ext
    · rw [Category.assoc, e₁, hΔ₁, pullback.diagonal_fst]
    · rw [Category.assoc, e₂, hΔ₂, pullback.diagonal_snd]
  have hsq' : IsPullback i r (π ≫ h.isoPullback.hom) (pullback.diagonal p) :=
    IsPullback.of_iso hsq (Iso.refl _) (Iso.refl _) (Iso.refl _) h.isoPullback (by simp) (by simp) (by simp)
      (by simp [hdiag])
  have hpair' : IsPair 1 c ((π ≫ h.isoPullback.hom) ≫ pullback.fst p p ≫ p) i := by
    have hc : (π ≫ h.isoPullback.hom) ≫ pullback.fst p p ≫ p = π ≫ p₁ ≫ p := by
      rw [Category.assoc, ← Category.assoc h.isoPullback.hom, e₁]
    rw [hc]
    exact hpair
  obtain ⟨δ, m, s, a, b, h1, h2, h3, h4⟩ :=
    hQ l k hl d p hSP hProj (π ≫ h.isoPullback.hom) i r c hsq' hpair' hr U hoff e he hpb
  exact core hR d p π e₁ e₂ e (by push_cast; rfl) (by push_cast; rfl) rfl δ m s a b h1 h2 h3 h4

end UpperTheory.Gal.KunnethLefschetz.Di
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PGeoPB
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Gal.KunnethLefschetz.Di

section Sq
variable {C : Type*} [Category C] [HasPullbacks C]

private theorem sq_left {X Y B B' : C} (p : X ⟶ B) (q : Y ⟶ B) (s : B' ⟶ B) (u : X ⟶ Y) (hu : u ≫ q = p)
    (g : pullback p s ⟶ pullback q s) (e : g ≫ pullback.fst q s = pullback.fst p s ≫ u)
    (e' : g ≫ pullback.snd q s = pullback.snd p s) :
    IsPullback (pullback.fst p s) g u (pullback.fst q s) := by
  have outer : IsPullback (g ≫ pullback.snd q s) (pullback.fst p s) s (u ≫ q) := by
    rw [e', hu]
    exact (IsPullback.of_hasPullback p s).flip
  exact (IsPullback.of_right outer e (IsPullback.of_hasPullback q s).flip).flip

private theorem sq_right {X P B B' : C} (p : X ⟶ B) (q : P ⟶ B) (s : B' ⟶ B) (p₁ p₂ : P ⟶ X)
    (h₁ : p₁ ≫ p = q) (h : IsPullback p₁ p₂ p p) (g₁ g₂ : pullback q s ⟶ pullback p s)
    (e₁ : g₁ ≫ pullback.fst p s = pullback.fst q s ≫ p₁) (e₁' : g₁ ≫ pullback.snd p s = pullback.snd q s)
    (e₂ : g₂ ≫ pullback.fst p s = pullback.fst q s ≫ p₂) (e₂' : g₂ ≫ pullback.snd p s = pullback.snd q s) :
    IsPullback g₁ g₂ (pullback.snd p s) (pullback.snd p s) := by
  have A := sq_left q p s p₂ (h.w.symm.trans h₁) g₂ e₂ e₂'
  have outer := A.paste_horiz h
  rw [← e₁, pullback.condition] at outer
  exact IsPullback.of_right outer (e₁'.trans e₂'.symm) (IsPullback.of_hasPullback p s)

end Sq

theorem geoPB_holds : GeoPB := by
  intro K Ω _ _ _
  constructor
  · intro X Y p q u hu
    exact sq_left p q _ u hu _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  · intro X P p q p₁ p₂ h₁ h₂ h
    exact sq_right p q _ p₁ p₂ h₁ h _ _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end UpperTheory.Gal.KunnethLefschetz.Di
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PRootNat
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open scoped TensorProduct

theorem UpperTheory.Gal.KunnethLefschetz.Di.rootNat_holds :
    UpperTheory.Gal.KunnethLefschetz.Di.RootNat := by
  intro q _ i V U g ζ
  have hroot := (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.2
  have hnat := (GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q i) U).2.2.2.1 g (twGen i ζ)
  have hres := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ
  rw [hroot i U ζ, hroot i V (ζ.map g.appTop.hom), ← hres]
  exact hnat
end
end

