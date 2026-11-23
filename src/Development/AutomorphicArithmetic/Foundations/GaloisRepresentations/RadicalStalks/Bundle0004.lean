module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Factor
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.factor :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p →
      ∀ (S S' S'' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (s'' : S'' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (o'' : Obj b N s'') (f : S' ⟶ S) (g : S'' ⟶ S'),
      f ≫ s = s' → g ≫ s' = s'' → ObjMap o' o f → ObjMap o'' o (g ≫ f) → Nonempty (ObjMap o'' o' g) := by
  intro p _ D R _ b N hN hNp S S' S'' s s' s'' o o' o'' f g hf hg m1 m2
  have hw : m2.φ ≫ o.A.hom = (o''.A.hom ≫ g) ≫ f := by
    rw [m2.cart.1.w, Category.assoc]
  let φ' : o''.A.left ⟶ o'.A.left := m1.cart.1.lift m2.φ (o''.A.hom ≫ g) hw
  have h1 : φ' ≫ m1.φ = m2.φ := m1.cart.1.lift_fst _ _ _
  have h2 : φ' ≫ o'.A.hom = o''.A.hom ≫ g := m1.cart.1.lift_snd _ _ _
  let φ₂' : (G2 o''.A).left ⟶ (G2 o'.A).left :=
    pullback.lift (pullback.fst _ _ ≫ φ') (pullback.snd _ _ ≫ φ')
      (by simp only [Category.assoc, h2]; rw [pullback.condition_assoc])
  have sq : Geo.Tor.IsSquare φ' φ₂' := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have h3 : φ₂' ≫ m1.φ₂ = m2.φ₂ := by
    apply pullback.hom_ext
    · change φ₂' ≫ m1.φ₂ ≫ Over.Hom.left (fst o.A o.A) = m2.φ₂ ≫ Over.Hom.left (fst o.A o.A)
      rw [m1.sq.1, m2.sq.1, ← Category.assoc, sq.1, Category.assoc, h1]
    · change φ₂' ≫ m1.φ₂ ≫ Over.Hom.left (snd o.A o.A) = m2.φ₂ ≫ Over.Hom.left (snd o.A o.A)
      rw [m1.sq.2, m2.sq.2, ← Category.assoc, sq.2, Category.assoc, h1]
  have cart : IsGrpPullback o''.A o'.A g φ' := by
    refine IsGrpPullback.cancel m1.cart ?_ h2
    rw [h1]
    exact m2.cart
  have pol : LBIso o''.P (o'.P.pull φ₂') := by
    rw [← GlobalTheory.CechPic.cls_eq_iff o''.isLB (pull_isLB o'.isLB φ₂'), GlobalTheory.CechPic.cls_pull o'.isLB,
      ← Rigid.pull_cls_P m1, ← GlobalTheory.CechPic.pull_comp, h3, Rigid.pull_cls_P m2]
  have act : ∀ c : D.O, Over.Hom.left (o''.act.act c) ≫ φ' = φ' ≫ Over.Hom.left (o'.act.act c) := by
    intro c
    apply m1.cart.1.hom_ext
    · simp only [Category.assoc, reassoc_of% h1, h1, m1.act c, m2.act c]
    · simp only [Category.assoc, h2, Over.w_assoc, Over.w]
  have eta : ∀ y : D.La, Over.Hom.left (o''.eta y) ≫ φ' = g ≫ Over.Hom.left (o'.eta y) := by
    intro y
    apply m1.cart.1.hom_ext
    · simp only [Category.assoc, h1, m2.eta y, m1.eta y]
    · simp [h2]
  exact ⟨⟨φ', φ₂', cart, sq, act, pol, eta⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Transl
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.transl :
    ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (σ : k →+* k) (ψ : A.left ⟶ A.left), SMor A σ ψ →
      (∀ v : epsR k ⟶ A, IsTangent v → IsConst (v.left ≫ ψ)) → ∀ v : epsR k ⟶ A, IsConst (v.left ≫ ψ) := by
  intro k _ A _ σ ψ m hT v
  let z : Sp k ⟶ Sp (DualNumber k) := spMap (TrivSqZeroExt.fstHom k k k).toRingHom
  let r : Sp (DualNumber k) ⟶ Sp k := spMap (algebraMap k (DualNumber k))
  have hq : spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) = r ≫ z := by
    simp only [r, z, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hzr : z ≫ r = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
      ext x; simp
    simp only [r, z, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have hqq : (r ≫ z) ≫ r ≫ z = r ≫ z := by
    rw [Category.assoc, reassoc_of% hzr]
  let c : epsR k ⟶ epsR k := Over.homMk (r ≫ z) (by
    show (r ≫ z) ≫ r = r
    rw [Category.assoc, hzr, Category.comp_id])
  let zz : 𝟙_ (Over (Sp k)) ⟶ epsR k := Over.homMk z hzr
  have hzc : zz ≫ c = zz := Over.OverMorphism.ext (by
    show z ≫ r ≫ z = z
    rw [reassoc_of% hzr])
  let v0 : epsR k ⟶ A := c ≫ v
  let t : epsR k ⟶ A := v0⁻¹ * v
  have hvt : v = v0 * t := by simp [t]
  have hzt : zz ≫ t = 1 := by
    have a : zz ≫ v0 = zz ≫ v := by simp only [v0, ← Category.assoc, hzc]
    calc zz ≫ t = (zz ≫ v0⁻¹) * (zz ≫ v) := MonObj.comp_mul _ _ _
      _ = (zz ≫ v0⁻¹) * (zz ≫ v0) := by rw [a]
      _ = zz ≫ (v0⁻¹ * v0) := (MonObj.comp_mul _ _ _).symm
      _ = 1 := by rw [inv_mul_cancel, MonObj.comp_one]
  have htan : IsTangent t := by
    have e1 : (1 : 𝟙_ (Over (Sp k)) ⟶ A) = η[A] := by
      show toUnit _ ≫ η[A] = _
      rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    show z ≫ t.left = η[A].left
    rw [← e1, ← hzt]
    rfl
  let Y : Over (Sp k) := Over.mk ((epsR k).hom ≫ spMap σ)
  let Q : Y ⟶ Y := Over.homMk (r ≫ z) (by
    show (r ≫ z) ≫ r ≫ spMap σ = r ≫ spMap σ
    rw [Category.assoc, reassoc_of% hzr])
  let down (x : epsR k ⟶ A) : Y ⟶ A :=
    Over.homMk (x.left ≫ ψ) (by simp [Y, m.w])
  have down_mul (x y : epsR k ⟶ A) : down (x * y) = down x * down y :=
    Over.OverMorphism.ext (m.mul (epsR k) x y (down x) (down y) rfl rfl).symm
  have h0 : Q ≫ down v0 = down v0 := Over.OverMorphism.ext (by
    show (r ≫ z) ≫ ((r ≫ z) ≫ v.left) ≫ ψ = ((r ≫ z) ≫ v.left) ≫ ψ
    simp only [← Category.assoc]
    rw [show ((r ≫ z) ≫ r) ≫ z = r ≫ z by simpa using hqq])
  have h1 : Q ≫ down t = down t := Over.OverMorphism.ext (by
    have := hT t htan
    unfold IsConst at this
    rw [hq] at this
    exact this)
  have key : Q ≫ down v = down v := by
    rw [hvt, down_mul, MonObj.comp_mul, h0, h1]
  unfold IsConst
  rw [hq]
  exact congrArg (fun u => u.left) key
end

