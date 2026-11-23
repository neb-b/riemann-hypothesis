module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

section Bilinear

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Over S}
variable {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

def lamLeft (z : X ⟶ G) : (X ⟶ G) →* Multiplicative (Pic X.left) where
  toFun x := Multiplicative.ofAdd (lam (cls L hL) x z)
  map_one' := by rw [lam_one_left]; rfl
  map_mul' x y := by rw [lam_mul_left hL hΘ]; rfl

theorem lam_prod_left {κ : Type} [Fintype κ] (x : κ → (X ⟶ G)) (n : κ → ℤ) (z : X ⟶ G) :
    lam (cls L hL) (∏ i, x i ^ n i) z = ∑ i, n i • lam (cls L hL) (x i) z := by
  have h := congrArg Multiplicative.toAdd (map_prod (lamLeft hL hΘ z) (fun i => x i ^ n i) Finset.univ)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  exact h

theorem lam_prod_right {κ : Type} [Fintype κ] (x : X ⟶ G) (z : κ → (X ⟶ G)) (n : κ → ℤ) :
    lam (cls L hL) x (∏ i, z i ^ n i) = ∑ i, n i • lam (cls L hL) x (z i) := by
  rw [lam_comm, lam_prod_left hL hΘ]
  simp only [lam_comm _ (z _) x]

theorem lam_mul_right (x y z : X ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]

end Bilinear

section Tensor

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def pairP (T : Tens D D' W) (M : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    Pic X.left :=
  ∑ i, ∑ j, M i j • lam (cls D.P.L D.P.isLB) (u ≫ T.pr i) (v ≫ T.pr j)

theorem cls_tens (T : Tens D D' W) :
    cls D'.P.L D'.P.isLB = ∑ i, ∑ j, W i j • lam (cls D.P.L D.P.isLB) (T.pr i) (T.pr j) := by
  have hC := LB.isLB_linComb D.P.isLB (tensφ T.pr) (tensε W)
  refine ((cls_eq_iff D'.P.isLB hC).2 ⟨T.w, T.w_gen⟩).trans ?_
  rw [cls_linComb D.P.isLB, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, lam, mul_smul, ← smul_add]
  congr 1
  simp
  abel

theorem pull_tens (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (h : X ⟶ D'.P.A) :
    pull h.left (cls D'.P.L D'.P.isLB) = pairP T W h h := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cls_tens T, pairP, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, pull_lam]

end Tensor

end GlobalTheory.Mum.RosatiTens

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

section Tensor2

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem pairP_mul (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairP T W (u * v) (u * v) = pairP T W u u + pairP T W v v + pairP T (W + W.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ T.pr i = u ≫ T.pr i * v ≫ T.pr i := fun i => by
    haveI := T.pr_hom i
    exact MonObj.mul_comp _ _ _
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  have e : ∑ i, ∑ j, W i j • lam (cls D.P.L D.P.isLB) (v ≫ T.pr i) (u ≫ T.pr j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls D.P.L D.P.isLB) (u ≫ T.pr i) (v ≫ T.pr j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (v ≫ _)]
  simp only [pairP, hm, lam_mul_left D.P.isLB hΘ, lam_mul_right D.P.isLB hΘ, smul_add, Finset.sum_add_distrib,
    Matrix.add_apply, add_smul]
  rw [e]
  abel

def pre {X Y Z : Over (Spec (CommRingCat.of R))} [GrpObj Z] (u : X ⟶ Y) : (Y ⟶ Z) →* (X ⟶ Z) where
  toFun f := u ≫ f
  map_one' := by simp [Hom.one_def]
  map_mul' f g := MonObj.comp_mul u f g

theorem comp_act_pr (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (u : X ⟶ D'.P.A)
    (m : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    (u ≫ T.act m) ≫ T.pr i = ∏ k, (u ≫ T.pr k) ^ m i k := by
  rw [Category.assoc, Tens.act_pr]
  exact (map_prod (pre (Z := D.P.A) u) _ _).trans (Finset.prod_congr rfl fun k _ => map_zpow (pre (Z := D.P.A) u) _ _)

theorem pairP_act_left (T : Tens D D' W) (M m : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : pairP T M (u ≫ T.act m) v = pairP T (m.transpose * M) u v := by
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  simp only [pairP, comp_act_pr, lam_prod_left D.P.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pairP_act_right (T : Tens D D' W) (M m : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : pairP T M u (v ≫ T.act m) = pairP T (M * m) u v := by
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  simp only [pairP, comp_act_pr, lam_prod_right D.P.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

end Tensor2

end GlobalTheory.Mum.RosatiTens

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem symUnit_mul_star (h : IsUnit (W + W.transpose).det) (a : TensO (symUnitOf W h)) :
    (W + W.transpose) * TensO.mat _ (star a) = (TensO.mat _ a).transpose * (W + W.transpose) := by
  have hb : (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose := rfl
  rw [TensO.star_def]
  show (W + W.transpose) * ((((symUnitOf W h).1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (TensO.mat _ a).transpose * (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ)) = _
  rw [← hb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem rosatiAdj_core (T : Tens D D' W) (h : IsUnit (W + W.transpose).det) (a : TensO (symUnitOf W h)) :
    RosatiAdj D'.P.A D'.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  intro s
  refine ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb D'.P.isLB _ _)).1 ?_⟩
  rw [cls_linComb D'.P.isLB]
  let f := T.act (TensO.mat _ a)
  let g := T.act (TensO.mat _ (star a))
  let H : Fin 6 → (D'.P.A ⊗ D'.P.A ⟶ D'.P.A) := ![fst _ _ ≫ f * snd _ _, fst _ _ ≫ f, snd _ _,
    fst _ _ * snd _ _ ≫ g, fst _ _, snd _ _ ≫ g]
  have hH : rosatiφ D'.P.A f g = fun k => (H k).left := by
    funext k
    fin_cases k <;> simp [rosatiφ, H, padd, Hom.mul_def]
  have key : ∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB) = 0 := by
    simp only [hH, pull_tens T]
    simp only [Fin.sum_univ_six, H, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
    rw [pairP_mul, pairP_mul]
    rw [pairP_act_left T (W + W.transpose) (TensO.mat _ a) (fst _ _) (snd _ _),
      pairP_act_right T (W + W.transpose) (TensO.mat _ (star a)) (fst _ _) (snd _ _), symUnit_mul_star]
    simp only [one_smul, neg_smul]
    abel
  calc ∑ k, rosatiε k • pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)
      = pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι)
          (∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [pull_comp, map_sum, map_zsmul]
    _ = 0 := by rw [key, map_zero]

end GlobalTheory.Mum.RosatiTens


open GlobalTheory.Mum.RosatiTens in
theorem GlobalTheory.Mum.rosatiAdj_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (a : TensO (symUnitOf W h)), RosatiAdj D'.toPre.P.A D'.toPre.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  intro R _ _ _ _ D D' r W h _ T a
  exact rosatiAdj_core T h a
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioAppRestrict
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secRatio_app_restrict {Y Z : Scheme.{0}} (h : Z ⟶ Y) {U W : Y.Opens} (hle : W ≤ U)
    (hle' : h ⁻¹ᵁ W ≤ h ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (Z.presheaf.map (homOfLE hle').op).hom ((h.app U).hom x) =
      (h.app W).hom ((Y.presheaf.map (homOfLE hle).op).hom x) := by
  have := congrArg (fun φ => φ.hom x) (h.naturality (homOfLE hle).op)
  simpa using this.symm

theorem secRatioEq_comp : ∀ {X Y Z : Scheme.{0}} (L : LB X) {k k' : ℕ} (u v : Y ⟶ X) (h : Z ⟶ Y) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k'), SecRatioEq L u v s₁ s₂ t₁ t₂ → SecRatioEq L (h ≫ u) (h ≫ v) s₁ s₂ t₁ t₂ := by
  intro X Y Z L k k' u v h s₁ s₂ t₁ t₂ hR i i'
  have e := congrArg (h.app (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')).hom (hR i i')
  simp only [map_mul] at e
  simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [secRatio_app_restrict h (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i),
    secRatio_app_restrict h (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i'),
    secRatio_app_restrict h (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i),
    secRatio_app_restrict h (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')]
  exact e

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOfExpansionModMaximalIdeal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ExpandNonzero

open ReciprocityTheory.ChartRestriction.G.Semi

theorem mem_wchart {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : K → L.ι) (y : Y) : y ∈ LB.wchart L φ j ↔ ∀ k, (φ k).base y ∈ L.U (j k) := by
  show y ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X) ↔ _
  exact Set.mem_iInter

theorem sec_mem_basicOpen {X : Scheme.{0}} {L : LB X} (s : LB.Sec L) (i j : L.ι) {x : X}
    (hx : x ∈ X.basicOpen (s.f j)) (hi : x ∈ L.U i) : x ∈ X.basicOpen (s.f i) := by
  have hxj : x ∈ L.U j := X.basicOpen_le _ hx
  have h := congrArg X.basicOpen (s.compat i j)
  simp only [Scheme.basicOpen_res, Scheme.basicOpen_mul,
    Scheme.basicOpen_of_isUnit _ (L.g i j).isUnit] at h
  have hm : x ∈ (L.U i ⊓ L.U j) ⊓ ((L.U i ⊓ L.U j) ⊓ X.basicOpen (s.f j)) :=
    ⟨⟨hi, hxj⟩, ⟨hi, hxj⟩, hx⟩
  rw [← h] at hm
  exact hm.2

theorem nonzero_of_expandsAt_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (k : ℕ) (s : H0 U.LG.L k)
      (f : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt 0 k s f →
      (∀ α, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt 0).pG.left.app _).hom ((f α).f j) = 0) →
      ∀ y : (thickObj R (maximalIdeal R) 0 G).left,
      (∃ j : Fin 4 → D.toPre.P.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
          (((U.gt 0).pG.left.app _).hom ((f 0).f j))) →
      ∃ i : Fin 1 → U.LG.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
        (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s.f i)) := by
  intro R _ _ _ D A G _ _ U k s f hexp hzero y hy
  classical
  obtain ⟨j, hj⟩ := hy
  obtain ⟨S, hS, hE⟩ := hexp
  have hcovM : ∀ ψ : (thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left,
      ∃ i, ψ.base y ∈ D.toPre.P.L.U i := fun ψ => by
    have : ψ.base y ∈ ⨆ i, D.toPre.P.L.U i := by rw [D.toPre.P.isLB.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨iL, hiL⟩ : ∃ i, (fstG (maximalIdeal R) 0 G).left.base y ∈ U.LG.L.U i := by
    have : (fstG (maximalIdeal R) 0 G).left.base y ∈ ⨆ i, U.LG.L.U i := by
      rw [U.LG.isLB.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  let idx : ((thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι :=
    fun ψ => (hcovM ψ).choose
  have hidx : ∀ ψ, ψ.base y ∈ D.toPre.P.L.U (idx ψ) := fun ψ => (hcovM ψ).choose_spec
  refine ⟨fun _ => iL, ?_⟩
  have h0S : (0 : D.toPre.X) ∈ S := by
    by_contra h
    have h' := hS 0 h j
    rw [h', Scheme.basicOpen_zero] at hj
    exact hj
  have key := hE (fun _ => idx (U.gt 0).pG.left, fun _ => iL) (fun _ => iL)
    (fun α i => idx ((U.gt 0).pG.left ≫ D.toPre.famφB α i))
    (fun α i => idx (D.toPre.Oφ (U.gt 0).pG α i)) rfl (by
      intro a b hab
      rcases a with _ | (a | a) <;> rcases b with _ | (b | b) <;> exact congrArg idx hab)

  have hyW : y ∈ U.expW 0 (fun _ => idx (U.gt 0).pG.left, fun _ => iL) (fun _ => iL) S
      (fun α i => idx ((U.gt 0).pG.left ≫ D.toPre.famφB α i))
      (fun α i => idx (D.toPre.Oφ (U.gt 0).pG α i)) := by
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact (mem_wchart _ _ _ y).2 fun _ => hidx _
    · exact (mem_wchart _ _ _ y).2 fun _ => hiL
    · show (fstG (maximalIdeal R) 0 G).left.base y ∈ LB.wchart _ _ _
      exact (mem_wchart _ _ _ _).2 fun _ => hiL
    · refine Finset.inf_induction
        (p := fun V : (thickObj R (maximalIdeal R) 0 G).left.Opens => y ∈ V)
        (show y ∈ (⊤ : (thickObj R (maximalIdeal R) 0 G).left.Opens) from trivial)
        (fun a ha b hb => TopologicalSpace.Opens.mem_inf.2 ⟨ha, hb⟩) fun α _ =>
          TopologicalSpace.Opens.mem_inf.2 ⟨?_, ?_⟩
      · show (U.gt 0).pG.left.base y ∈ LB.wchart _ _ _
        exact (mem_wchart _ _ _ _).2 fun i => hidx ((U.gt 0).pG.left ≫ D.toPre.famφB α i)
      · exact (mem_wchart _ _ _ y).2 fun i => hidx _

  have hf0 : y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
      (((U.gt 0).pG.left.app _).hom
        ((f 0).f (fun i => idx ((U.gt 0).pG.left ≫ D.toPre.famφB 0 i)))) := by
    rw [← Scheme.preimage_basicOpen] at hj ⊢
    exact sec_mem_basicOpen (f 0) _ j hj
      ((mem_wchart _ _ _ _).2 fun i => hidx ((U.gt 0).pG.left ≫ D.toPre.famφB 0 i))
  rw [Finset.sum_eq_single ⟨0, h0S⟩ (fun b _ hb => by
      have hb' : b.1 ≠ 0 := fun h => hb (Subtype.ext h)
      refine mul_eq_zero_of_left ?_ _
      exact (congrArg _ (hzero b.1 hb' _)).trans (map_zero _))
    (fun h => absurd (Finset.mem_attach _ _) h)] at key
  have hL := (congrArg (fun a => y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen a) key).mpr (by
    simp only [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (Units.isUnit _),
      Scheme.basicOpen_res, TopologicalSpace.Opens.mem_inf]
    exact ⟨⟨hyW, hf0⟩, hyW⟩)
  simp only [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ ((Units.isUnit _).pow k),
    Scheme.basicOpen_res, TopologicalSpace.Opens.mem_inf] at hL
  exact hL.2.2

end GlobalTheory.Mum.ExpandNonzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericFibreHomExtendsNormalNoetheria
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.semiAbelian_end_generic_extends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom φ → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = φ := by
  intro R _ _ _ _ G _ hG φ hφ
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.of_isGenericPointHom
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R)
    (GlobalTheory.IsGenericPointHom.fractionField R (FractionRing R)) hG hG φ
  exact ⟨F, hF, hF'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpBundleFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def sharpPair (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (a b : Fin 8) : D.P.A.left ⟶ (G2 Q.B).left :=
  (lift (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr a))
    (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr b))).left

theorem sharp_cls_pair (W : Matrix (Fin 8) (Fin 8) ℤ) (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (a b : Fin 8) :
    (∏ I : ULift.{0} (Finset (Fin 2)), GlobalTheory.PrimNorm.cls Q.M.L (sharpPair ρ Q D pr a b ≫ (psum Q.B (x2 Q.B) I.down).left) ^
        ((-1 : ℤ) ^ (2 - I.down.card))) ^ W a b =
      ∏ k : Fin 4, GlobalTheory.PrimNorm.cls Q.M.L (lamPts (pr a) (pr b) k ≫ pullback.fst Q.B.hom (spMap ρ)) ^
        (-(W a b * negε k)) := by
  have h := isGrpPullback_pullback Q.B (spMap ρ)
  set xa := pushPt h.1.w (pr a) with hxa
  set xb := pushPt h.1.w (pr b) with hxb
  have e := GlobalTheory.PrimNorm.prod_square (lift xa xb) (fst Q.B Q.B) (snd Q.B Q.B) (GlobalTheory.PrimNorm.cls Q.M.L)
  rw [lift_fst, lift_snd] at e
  have e' : sharpPair ρ Q D pr a b = (lift xa xb).left := rfl
  rw [e', show x2 Q.B = ![fst Q.B Q.B, snd Q.B Q.B] from rfl, e]
  have m : (pr a * pr b).left ≫ pullback.fst Q.B.hom (spMap ρ) = (xa * xb).left :=
    (h.2 D.P.A (pr a) (pr b) xa xb rfl rfl).symm
  have o : (1 : D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B).left ≫ pullback.fst Q.B.hom (spMap ρ) =
      (1 : Over.mk (D.P.A.hom ≫ spMap ρ) ⟶ Q.B).left :=
    congrArg (fun z => z.left) (map_one (pushHom h D.P.A))
  rw [Fin.prod_univ_four]
  simp only [lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, m, o]
  change GlobalTheory.PrimNorm.diff₂ _ xa xb ^ W a b = _
  simp only [GlobalTheory.PrimNorm.diff₂]
  have ha : (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = xa.left := rfl
  have hb : (pr b).left ≫ pullback.fst Q.B.hom (spMap ρ) = xb.left := rfl
  rw [ha, hb]
  simp only [mul_neg, neg_neg, zpow_neg, mul_zpow, inv_zpow]
  ac_rfl

theorem sharp_bundle {W₀ : Type} [CommRing W₀] (W : Matrix (Fin 8) (Fin 8) ℤ) (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2))))
    (hw : w.IsGen) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (hM₀ : M₀.IsLB)
    (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left) (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)) (hw₀ : w₀.IsGen) :
    LBIso D.P.L (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
      (fun p => W p.1 p.2)) := by
  have hL : Q.M.L.IsLB := Q.M.isLB
  have hLam : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ hL _ _
  have hLam₀ : (abelian₂ B₀ M₀).IsLB := DVR.linComb_isLB _ hM₀ _ _
  have hS : (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ))
      (fun k => -(W k.1.1 k.1.2 * negε k.2))).IsLB := DVR.linComb_isLB _ hL _ _
  have h₂ : LBIso (LB.LinComb (abelian₂ Q.B Q.M.L) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2)
      (fun p => W p.1 p.2)) (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ))
      (fun k => -(W k.1.1 k.1.2 * negε k.2))) := by
    refine GlobalTheory.PrimNorm.lbIso_nested hL _ _ _ _ _ _ ?_
    refine Eq.trans ?_ (Fintype.prod_prod_type _).symm
    exact Finset.prod_congr rfl fun p _ => sharp_cls_pair W ρ Q D pr p.1 p.2
  have h₃ : LBIso (LB.LinComb (abelian₂ Q.B Q.M.L) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2)
      (fun p => W p.1 p.2)) (LB.LinComb ((abelian₂ B₀ M₀).pull β₂) (K := Fin 8 × Fin 8)
      (fun p => sharpPair ρ Q D pr p.1 p.2) (fun p => W p.1 p.2)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb ⟨w₀, hw₀⟩ _ _
  have h₄ : LBIso (LB.LinComb ((abelian₂ B₀ M₀).pull β₂) (K := Fin 8 × Fin 8)
      (fun p => sharpPair ρ Q D pr p.1 p.2) (fun p => W p.1 p.2))
      (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
        (fun p => W p.1 p.2)) :=
    LBIso.chartPull (chartPullLinComb (abelian₂ B₀ M₀) β₂ _ _ _ (𝟙 _) fun p => (Category.id_comp _).symm)
      (chartPullId _) ((GlobalTheory.PrimNorm.lbIso_iff hLam₀ _ _ _ _).2 rfl)
  have hN₁ := DVR.linComb_isLB (abelian₂ Q.B Q.M.L) hLam (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2)
    (fun p => W p.1 p.2)
  have hN₂ := DVR.linComb_isLB _ (pull_isLB hLam₀ β₂) (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2)
    (fun p => W p.1 p.2)
  have hN₃ := DVR.linComb_isLB (abelian₂ B₀ M₀) hLam₀ (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
    (fun p => W p.1 p.2)
  exact LBIso.trans D.P.isLB hS hN₃ ⟨w, hw⟩
    (LBIso.trans hS hN₁ hN₃ h₂.symm (LBIso.trans hN₁ hN₂ hN₃ h₃ h₄))

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothISupOpensCompOfForallSmoothStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_iSup_opens_comp_of_forall_smooth : ∀ (P' T : Scheme.{0}) (q : P' ⟶ T) (I : Type) (V : I → P'.Opens), (∀ i, Smooth ((V i).ι ≫ q)) → Smooth ((⨆ i, V i).ι ≫ q) := by
  first | exact @GlobalTheory.Mum.smooth_iSup_comp | exact GlobalTheory.Mum.smooth_iSup_comp | (intros; apply GlobalTheory.Mum.smooth_iSup_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFactorResidueFieldOfClosedPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spMap_residueField_of_forall_eq_closedPoint : ∀ (R : Type) [CommRing R] [IsLocalRing R] (Ω : Type) [Field Ω] (g : Sp Ω ⟶ Sp R), (∀ w, g w = closedPoint R) → ∃ κ : ResidueField R →+* Ω, g = spMap (κ.comp (residue R)) := by
  first | exact @GlobalTheory.Mum.spMap_factor_residueField_of_closedPoint | exact GlobalTheory.Mum.spMap_factor_residueField_of_closedPoint | (intros; apply GlobalTheory.Mum.spMap_factor_residueField_of_closedPoint <;> assumption)
end

