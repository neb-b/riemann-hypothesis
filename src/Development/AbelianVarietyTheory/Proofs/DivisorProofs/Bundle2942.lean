module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUniformisedFourierFrameAbsOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartUniqueLeastVectorAttainsExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRaynaudExtensionNoetherianLocal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RayInt

open ReciprocityTheory.ChartRestriction.G.Semi TopologicalSpace

attribute [local instance] SplitExt.free SplitExt.finite

theorem mem_chart_of_mem {S : Scheme.{0}} (E : SplitExt S) (j : E.ChartIdx) (b : E.B.left)
    (h : ∀ k, b ∈ (E.O (E.basis k)).L.U (j k)) : b ∈ E.chart j := by
  have e : E.chart j = Finset.univ.inf (fun k => (E.O (E.basis k)).L.U (j k)) :=
    (Finset.inf_univ_eq_iInf _).symm
  rw [e, ← SetLike.mem_coe, Opens.coe_finset_inf]
  simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Set.iInf_eq_iInter, Set.mem_iInter,
    Function.comp_apply, SetLike.mem_coe]
  exact h

theorem isIntegral_of_isGt (R : Type) [CommRing R] [IsDomain R] (E : SplitExt (Spec (CommRingCat.of R)))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (hG : E.IsGt G) (hs : Smooth G.hom) :
    IsIntegral G.left := by
  obtain ⟨d⟩ := hG
  have hB := E.isAbelian
  haveI : Smooth E.B.hom := hB.smooth
  haveI : GeometricallyConnected E.B.hom := hB.geomConnected
  have hSne : Nonempty (Spec (CommRingCat.of R)) := inferInstance
  have hBne : Nonempty E.B.left := ⟨(η[E.B] : 𝟙_ _ ⟶ E.B).left (show (𝟙_ (Over _)).left from hSne.some)⟩
  haveI : IrreducibleSpace E.B.left :=
    GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain R E.B ‹_› ‹_› hBne
  haveI : IsReduced E.B.left := GlobalTheory.isReduced_of_smooth_of_isReduced E.B.hom
  haveI : IsIntegral E.B.left := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : IsReduced G.left := GlobalTheory.isReduced_of_smooth_of_isReduced G.hom
  obtain ⟨b⟩ := hBne
  have hk : ∀ k, ∃ i, b ∈ (E.O (E.basis k)).L.U i := fun k => by
    have hb : b ∈ (⊤ : E.B.left.Opens) := trivial
    rw [← (E.O (E.basis k)).isLB.cover, Opens.mem_iSup] at hb
    exact hb
  choose j hj using hk
  have hbj : b ∈ E.chart j := mem_chart_of_mem E j b hj
  obtain ⟨V, hV, hbV, hVj⟩ := (Opens.isBasis_iff_nbhd.mp E.B.left.isBasis_affineOpens) hbj
  have hbV' : b ∈ V := hbV
  haveI : Nonempty V := ⟨⟨b, hbV'⟩⟩
  haveI := d.q_affine
  haveI := d.q_flat
  have hsurj := d.q_surjective
  set W : G.left.Opens := d.q.left ⁻¹ᵁ V with hWdef
  have hV : IsAffineOpen V := hV
  have hW : IsAffineOpen W := hV.preimage d.q.left
  have hbij := d.coord j V hV hVj
  haveI : IsDomain Γ(G.left, W) :=
    Function.Injective.isDomain (RingEquiv.ofBijective _ hbij).symm.toRingHom
      (RingEquiv.ofBijective _ hbij).symm.injective
  obtain ⟨g, hg⟩ := hsurj.surj b
  have hgW : g ∈ W := by show d.q.left g ∈ V; rw [hg]; exact hbV'
  haveI : Nonempty W := ⟨⟨g, hgW⟩⟩
  haveI : IsAffine W := hW
  haveI : IsDomain Γ(W, ⊤) :=
    Function.Injective.isDomain (W.topIso).commRingCatIsoToRingEquiv.toRingHom
      (W.topIso).commRingCatIsoToRingEquiv.injective
  haveI : IsIntegral W := isIntegral_of_isAffine_of_isDomain W
  have hirrW : IsIrreducible (W : Set G.left) := by
    have hI := (IrreducibleSpace.isIrreducible_univ W).image (⇑W.ι) (Scheme.Hom.continuous _).continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at hI
  have hη : genericPoint E.B.left ∈ V :=
    ((genericPoint_spec E.B.left).mem_open_set_iff V.isOpen).2 ⟨b, trivial, hbV'⟩
  have hcl : closure (W : Set G.left) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap d.q.left (genericPoint_specializes (d.q.left z))
    have hz'W : z' ∈ (W : Set G.left) := by show d.q.left z' ∈ V; rw [e]; exact hη
    exact closure_mono (Set.singleton_subset_iff.2 hz'W) (specializes_iff_mem_closure.mp hz')
  haveI : IrreducibleSpace G.left := by
    rw [irreducibleSpace_def]
    have := hirrW.closure
    rwa [hcl] at this
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem isIntegral_H : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), IsIntegral Y.H.left := by
  intro R _ _ _ _ Q O _ _ _ oa Y
  exact isIntegral_of_isGt R _ Y.H Y.isGt (GlobalTheory.RayTan.smooth_H R Q O oa Y)

end GlobalTheory.RayInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRigidOfBase
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TautRigid

def dlog (k : Type) [Field k] : (DualNumber k)ˣ →* Multiplicative k where
  toFun x := Multiplicative.ofAdd ((x : DualNumber k).snd / (x : DualNumber k).fst)
  map_one' := by simp
  map_mul' x y := by
    have fne : ∀ x : (DualNumber k)ˣ, (x : DualNumber k).fst ≠ 0 := fun x h => by
      have := congrArg TrivSqZeroExt.fst x.mul_inv
      rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at this
      exact zero_ne_one this
    have hx := fne x
    have hy := fne y
    rw [← ofAdd_add]
    congr 1
    simp only [Units.val_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    field_simp
    ring

theorem fst_ne_zero {k : Type} [Field k] (x : (DualNumber k)ˣ) : (x : DualNumber k).fst ≠ 0 := fun h => by
  have := congrArg TrivSqZeroExt.fst x.mul_inv
  rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at this
  exact zero_ne_one this

theorem dlog_apply {k : Type} [Field k] (x : (DualNumber k)ˣ) :
    Multiplicative.toAdd (dlog k x) = (x : DualNumber k).snd / (x : DualNumber k).fst := rfl

def onePlus {k : Type} [Field k] (s : k) : (DualNumber k)ˣ where
  val := 1 + TrivSqZeroExt.inr s
  inv := 1 - TrivSqZeroExt.inr s
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

theorem dlog_onePlus {k : Type} [Field k] (s : k) : Multiplicative.toAdd (dlog k (onePlus s)) = s := by
  rw [dlog_apply]; simp [onePlus]

end GlobalTheory.TautRigid

namespace GlobalTheory.TautRigid

open GlobalTheory.RigChart GlobalTheory.ToricData

variable {R : Type} [CommRing R] [IsDomain R]

def lamC (Q : DegPre R) {k : Type} [Field k] {B' : Scheme.{0}} {π₁ π₂ : B' ⟶ Q.P.A.left}
    (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B')) (y z : Q.X)
    (zz : Sp (DualNumber k)) (J : (Sp (DualNumber k) ⟶ Q.P.A.left) → Q.P.L.ι) : ((Sp (DualNumber k)).presheaf.stalk zz)ˣ :=
  gm (c' (y + z)) zz _ (w.s (fun _ => J (c' (y + z) ≫ π₂), fun _ => J (c' (y + z) ≫ π₁))) *
    (gm (c' y) zz _ (w.s (fun _ => J (c' y ≫ π₂), fun _ => J (c' y ≫ π₁))))⁻¹ *
    (gm (c' z) zz _ (w.s (fun _ => J (c' z ≫ π₂), fun _ => J (c' z ≫ π₁))))⁻¹ *
    gm (c' 0) zz _ (w.s (fun _ => J (c' 0 ≫ π₂), fun _ => J (c' 0 ≫ π₁)))

def AbConst (Q : DegPre R) {k : Type} [Field k] (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B']
    (π₁ π₂ : B'.left ⟶ Q.P.A.left) (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)) :
    Prop :=
  IsGrpPullback B' Q.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ ∧
    (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k),
      x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) ∧
    w.IsGen ∧ (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧
      c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left)

end GlobalTheory.TautRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam

def sig : Fin 8 → Fin 4 ⊕ Fin 4 :=
  ![.inl 0, .inl 1, .inl 2, .inl 3, .inr 0, .inr 1, .inr 2, .inr 3]

def oMat (d : ℕ) (k : Fin 8) : ord d :=
  ⟨Matrix.single (Sum.inl 0) (sig k) 1, fun i j => by simp [Matrix.single]⟩

def jlMap (h : ℕ) : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) where
  toFun a := fun
    | .inl i => if hi : (i : ℕ) < h then a (.inl ⟨i, hi⟩) else 0
    | .inr i => if hi : (i : ℕ) < h then a (.inr ⟨i, hi⟩) else 0
  map_zero' := by
    funext i; rcases i with i | i <;> simp
  map_add' a b := by
    funext i; rcases i with i | i <;> simp only [Pi.add_apply] <;> split_ifs <;> simp

def formZ (d h : ℕ) (X Y : Fin 8 → Fin h ⊕ Fin h → ℤ) : ℤ :=
  ∑ k, ∑ l, form d (sig k) (sig l) * omegaStd (X k) (Y l)

def KappaOK (h M d : ℕ) (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) : Prop :=
  (∀ a b, formZ d h (fun k => κ k a) (fun k => κ k b) ≡ omegaStd a b [ZMOD (M : ℤ)]) ∧
    (∀ a, κ 0 (jlMap h a) = a) ∧ ∀ k, k ≠ 0 → ∀ a, κ k (jlMap h a) = 0

section Obj

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

abbrev Zob : Over S := Out.powObj A 4 ⊗ Out.powObj B 4

def pa (i : Fin 4) : Zob A B ⟶ A := fst _ _ ≫ Out.powPr A i

def pb (j : Fin 4) : Zob A B ⟶ B := snd _ _ ≫ Out.powPr B j

def mkZ {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) : T ⟶ Zob A B :=
  lift ((Out.powIsLimit A 4).lift (Fan.mk T u)) ((Out.powIsLimit B 4).lift (Fan.mk T v))

def actZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (N : ord d) : Zob A B ⟶ Zob A B :=
  mkZ A B
    (fun i => ∏ j, (pa A B j ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inl i)) *
      (pb A B j ≫ mu) ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inl i) / (d : ℤ))))
    (fun i => ∏ j, ((pa A B j ≫ la) ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inr i)) *
      pb A B j ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inr i))))

def incZ : A ⟶ Zob A B := mkZ A B (fun i => if i = 0 then 𝟙 A else 1) (fun _ => 1)

def prZ : Zob A B ⟶ A := pa A B 0

def zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    CechPic.Pic (Zob A B ⊗ Zob A B).left :=
  (∑ i, CechPic.pull (lift (fst (Zob A B) (Zob A B) ≫ pa A B i) (snd (Zob A B) (Zob A B) ≫ pa A B i)).left
      (cls P hP)) +
    (∑ i, ∑ j, quat d j i • CechPic.pull (lift (fst (Zob A B) (Zob A B) ≫ pa A B i)
      (snd (Zob A B) (Zob A B) ≫ pb A B j)).left (cls Q hQ)) +
    (∑ i, ∑ j, quat d j i • CechPic.pull (lift (snd (Zob A B) (Zob A B) ≫ pa A B i)
      (fst (Zob A B) (Zob A B) ≫ pb A B j)).left (cls Q hQ)) +
    ∑ j, CechPic.pull (lift (snd (Zob A B) (Zob A B) ≫ pb A B j ≫ mu) (fst (Zob A B) (Zob A B) ≫ pb A B j)).left
      (cls Q hQ)

def zP {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    LB (Zob A B ⊗ Zob A B).left :=
  (cls_surj (zCls A B hP hQ d mu)).choose

theorem zarhinBundle_isLineBundle {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    (zP A B hP hQ d mu).IsLB :=
  (cls_surj (zCls A B hP hQ d mu)).choose_spec.choose

theorem cls_zP {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    cls (zP A B hP hQ d mu) (zarhinBundle_isLineBundle A B hP hQ d mu) = zCls A B hP hQ d mu :=
  (cls_surj (zCls A B hP hQ d mu)).choose_spec.choose_spec

end Obj

def levZ {S : Scheme.{0}} {A Z : Over S} [GrpObj Z] [IsCommMonObj Z] {O : Type} {h h' n : ℕ}
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (inc : A ⟶ Z) (act : O → (Z ⟶ Z)) (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (a : Fin h' ⊕ Fin h' → ℤ) : 𝟙_ (Over S) ⟶ Z :=
  (List.ofFn fun k => lev (κ k a) ≫ inc ≫ act (o k)).prod

def ZData {S : Scheme.{0}} {h M : ℕ} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t) (d : ℕ)
    (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) : Prop :=
  IsAbelianScheme B ∧ IsDual c.A B Q ∧ IsDual B c.A (swap Q) ∧ IsMonHom la ∧ IsMonHom mu ∧
    la ≫ mu = 𝟙 c.A ^ d ∧ mu ≫ la = 𝟙 B ^ d ∧ LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la))

end GlobalTheory.ZarhinFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthOfHeightOne
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.ColengthHtOne

open Module

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem le_finrank_coker_omegaMap [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ)
    (h1 : q ≫ q' = (p : ℤ_[p]) • 𝟙 G) (hF : frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1))
    (he : HasLogDeg q e) : e ≤ finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  unfold HasLogDeg at he
  obtain ⟨N, hN⟩ := he
  have hlev : finrank k (G.A 1 ⧸ kerIdeal (q.app 1)) = p ^ e := by
    rw [← GlobalTheory.Dieu.finrank_quot_kerIdeal_eq p k G H 1 (max N 1) q q' (by rw [pow_one]; exact h1)
      (le_max_right _ _)]
    exact hN _ (le_max_left _ _)
  obtain ⟨C, _, _, _, _, π, hπ, hker, hnil, hFaug⟩ := _root_.GlobalTheory.PDiv.FrobKerInter.exists_quotient_kerIdeal_sup_frobKerIdeal p k G H q
  have hker' : RingHom.ker π = kerIdeal (q.app 1) := by rw [hker]; exact sup_eq_left.2 hF
  have hC : finrank k C = p ^ e := by
    rw [← hlev, ← hker']
    exact ((Ideal.quotientKerAlgEquivOfSurjective (f := (π : G.A 1 →ₐ[k] C)) hπ).toLinearEquiv.finrank_eq).symm
  have hfrobC : frobKerIdeal p k C = ⊥ := by
    rw [eq_bot_iff]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    simp [hnil a ha]
  have hCq : finrank k C = finrank k (C ⧸ frobKerIdeal p k C) := by
    refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Ideal.Quotient.mkₐ k (frobKerIdeal p k C)).toLinearMap
      ⟨fun a b h => ?_, Ideal.Quotient.mkₐ_surjective k _⟩)
    have h' := Ideal.Quotient.eq.1 h
    rwa [hfrobC, Ideal.mem_bot, sub_eq_zero] at h'
  have hle := GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot p k C
  rw [← hCq, hC] at hle
  have hcot := (_root_.GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap p k G H q C π hπ).2.1 (by rw [hker]; exact sup_le_sup_left hFaug _) hker'.ge
  rw [hcot]
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle

theorem finrank_coker_lieMap {A B : PDivGroup p k} (f : A ⟶ B) [FiniteDimensional k A.omega]
    [FiniteDimensional k B.omega] (hd : finrank k A.omega = finrank k B.omega) :
    finrank k (B.Lie ⧸ LinearMap.range (lieMap A B f)) =
      finrank k (A.omega ⧸ LinearMap.range (omegaMap A B f)) := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range (lieMap A B f))
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range (omegaMap A B f))
  have h3 : finrank k (LinearMap.range (lieMap A B f)) = finrank k (LinearMap.range (omegaMap A B f)) :=
    LinearMap.finrank_range_dualMap_eq_finrank_range (omegaMap A B f)
  have h4 : finrank k B.Lie = finrank k B.omega := Subspace.dual_finrank_eq
  omega

theorem finrank_coker_lieMap_congr {A B A' B' : PDivGroup p k} (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B)
    (f' : A' ⟶ B') (hc : eA.hom ≫ f' = f ≫ eB.hom) :
    finrank k (B'.Lie ⧸ LinearMap.range (lieMap A' B' f')) =
      finrank k (B.Lie ⧸ LinearMap.range (lieMap A B f)) := by
  let L : B.Lie ≃ₗ[k] B'.Lie := LinearEquiv.ofLinear (lieMap B B' eB.hom) (lieMap B' B eB.inv)
    (by rw [← lieMap_comp, eB.inv_hom_id, lieMap_id]) (by rw [← lieMap_comp, eB.hom_inv_id, lieMap_id])
  have hA : LinearMap.range (lieMap A A' eA.hom) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun x => ⟨lieMap A' A eA.inv x, ?_⟩
    rw [← LinearMap.comp_apply, ← lieMap_comp, eA.inv_hom_id, lieMap_id, LinearMap.id_apply]
  have hr : LinearMap.range (lieMap A' B' f') = (LinearMap.range (lieMap A B f)).map (L : B.Lie →ₗ[k] B'.Lie) := by
    rw [← LinearMap.range_comp_of_range_eq_top _ hA, ← lieMap_comp, hc, lieMap_comp, LinearMap.range_comp]
    rfl
  rw [hr]
  exact (Submodule.Quotient.equiv _ _ L rfl).finrank_eq.symm

end GlobalTheory.Dieu.ColengthHtOne


open GlobalTheory.Dieu.ColengthHtOne in
theorem GlobalTheory.Dieu.le_colength_of_htOne : ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ), q ≫ q' = (p : ℤ_[p]) • 𝟙 G →
    q' ≫ q = (p : ℤ_[p]) • 𝟙 H → frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1) → HasLogDeg q e →
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M H.dual ⧸ LinearMap.range (T.map (dualHom G H q))) ∧
    e ≤ Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  intro p _ T k _ _ _ G H q q' e h1 h2 hF he
  have h3 := le_finrank_coker_omegaMap G H q q' e h1 hF he
  have hp0 : (p : k) = 0 := CharP.cast_eq_zero k p
  haveI := GlobalTheory.PDivGroup.finite_omega_of_eq_zero hp0 G
  haveI := GlobalTheory.PDivGroup.finite_omega_of_eq_zero hp0 H
  have hiso : IsIsog q := by
    unfold IsIsog
    exact ⟨1, q', by simpa only [pow_one] using h1, by simpa only [pow_one] using h2⟩
  have hd := (GlobalTheory.Dieu.isog_finrank_omega p T k G H q hiso).2.2.1
  have hL := (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k H.dual G.dual (dualHom G H q)).2
  rw [finrank_coker_lieMap_congr G.bidual H.bidual q _ (bidual_hom_dualHom_dualHom q),
    finrank_coker_lieMap q hd] at hL
  refine ⟨le_trans (by exact_mod_cast h3) (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k G H q).1, le_trans (by exact_mod_cast h3) hL, h3⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEvenClosing

theorem keyGlob : KeyGlob := by
  obtain ⟨κ, hH, hF, -, hT, -, hU, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  have h4 : MBLow.Rule4 κ := ⟨hH, hF, hT, hU⟩
  exact _root_.GlobalTheory.KeyEvenGlue.keyGlob_of_keyLoc κ hH hF (_root_.GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait κ hU (_root_.GlobalTheory.KeyEven.keyTrait_of_keyTraitU κ (_root_.GlobalTheory.KeyEven.keyTraitU_of_kapF κ (_root_.GlobalTheory.MBLow.KapFPf.kapF_of_rule4 κ h4))))

end GlobalTheory.KeyEvenClosing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsFormulasOfIdempotentImagePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZRelLevs

theorem zrel_levs : ∀ (h h' M : ℕ) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' T : Scheme.{0}) (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g → ZRel e jl o κ c' w' actw' → (∀ a, g ≫ (z.lev (jl a) ≫ act e).left = g ≫ (z.lev (jl a)).left) ∧ ∀ a, g ≫ (z.lev a).left = g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
  intro h h' M O _ e jl n o κ S' T t z act g c' w' actw' hpb hz
  obtain ⟨φ, φ₂, hφ, -, -, hl, ha⟩ := hpb
  obtain ⟨inc, pr, -, -, hip, hpi, -, hc, hw⟩ := hz
  have key : ∀ b (oo : O), (w'.lev b ≫ actw' oo).left ≫ φ = g ≫ (z.lev b ≫ act oo).left := by
    intro b oo
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, hl, Category.assoc]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← key, ← hl]
    congr 2
    rw [← hc, Category.assoc, ← hpi, ← Category.assoc inc, hip, Category.id_comp]
  · rw [← hl, hw a]
    have e1 : ((List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left ≫ φ =
        (pushHom hφ (𝟙_ (Over T)) (List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left := rfl
    rw [e1, map_list_prod, List.map_ofFn]
    have e2 : g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left =
        (toUnit (Over.mk ((𝟙_ (Over T)).hom ≫ g)) ≫
          (List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
      rw [Over.comp_left, Over.toUnit_left]
      rfl
    rw [e2, GlobalTheory.comp_list_prod_ofFn]
    congr 3
    funext k
    apply Over.OverMorphism.ext
    show (c'.lev (κ k a) ≫ inc ≫ actw' (o k)).left ≫ φ = _
    rw [← Category.assoc, hc, key]
    simp only [Over.comp_left, Over.toUnit_left, Over.mk_hom]
    rfl

end GlobalTheory.ZRelLevs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartUniqueLeastVectorAttainsExpStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightPart_unique_least_vector_attains_exp : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν, yy a = QuotientAddGroup.mk ν → (∀ χ, CongMod D.m χ ν → χ ≠ ν → qW W c.T.β ν < qW W c.T.β χ) → ∃ κ, ‖D.X.M.val (gPt p ≫ y) (GSum.part D z₁ z₂ a κ)‖ = Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
  first | exact @GlobalTheory.Poinc.GSumEx.main | exact GlobalTheory.Poinc.GSumEx.main | (intros; apply GlobalTheory.Poinc.GSumEx.main <;> assumption)
end

