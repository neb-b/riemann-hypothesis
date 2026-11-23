module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecFinsum
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.WeightTwo

theorem exists_sec_finsum {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {I : Type} (s : Finset I) (d : I → LB.Sec (LB.LinComb L φ ε)) :
    ∃ t : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval t r z J = ∑ i ∈ s, sval (d i) r z J := by
  refine ⟨⟨fun j => ∑ i ∈ s, (d i).f j, fun j j' => ?_⟩, fun Z r z J hJ => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => (d i).compat j j'
  · exact DVR.gs_fsum r z _ (hJ.mem φ r) _ _

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem formEq_cancel (k l : ℕ) (α β : D.X) :
    FormEq (Sum.elim (fun a => (D.P.A ◁ g.pG).left ≫ Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i)
        (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i) a)
        (fun a => (snd D.P.A ((Over.map (thick R I e)).obj (thickObj R I e G))).left ≫ D.Oφ g.pG β a))
      (Sum.elim (Sum.elim (DegPre.famε k) (DegPre.famε l)) Oinvε)
      (Sum.elim (fun i => (fst D.P.A ((Over.map (thick R I e)).obj (thickObj R I e G))).left ≫ D.famφB α i)
        (fun _ : Unit => (snd D.P.A _ ≫ g.pG).left))
      (Sum.elim (DegPre.famε k) (fun _ => (l : ℤ))) := by
  intro U _ h
  have e₁ : (D.P.A ◁ g.pG).left ≫ (fst D.P.A D.P.A).left = (fst D.P.A _).left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  have e₂ : (D.P.A ◁ g.pG).left ≫ (snd D.P.A D.P.A).left = (snd D.P.A _).left ≫ g.pG.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  have f₀ : g.pG.left ≫ D.famφB β 0 = g.pG.left := Category.comp_id _
  have f₁ : g.pG.left ≫ D.famφB β 1 = D.Oφ g.pG β 0 := by
    change (g.pG ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c β)).left = (padd D.P.A g.pG (toUnit _ ≫ D.c β)).left
    congr 1
    simp only [padd, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
  have f₂ : g.pG.left ≫ D.famφB β 2 = D.Oφ g.pG β 1 := by
    change (g.pG ≫ toUnit _ ≫ D.c β).left = (toUnit _ ≫ D.c β).left
    rw [comp_toUnit_assoc]
  have f₃ : g.pG.left ≫ D.famφB β 3 = D.Oφ g.pG β 3 := by
    change (g.pG ≫ toUnit _ ≫ η[D.P.A]).left = (toUnit _ ≫ η[D.P.A]).left
    rw [comp_toUnit_assoc]
  have f₄ : D.Oφ g.pG β 2 = g.pG.left := rfl
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, reassoc_of% e₁, reassoc_of% e₂,
    Finset.univ_unique, Finset.prod_singleton]
  rw [_root_.mul_assoc]
  congr 1
  rw [Fin.prod_univ_four, Fin.prod_univ_four, f₀, f₁, f₂, f₃, f₄, Over.comp_left _ _ _ (snd D.P.A _) g.pG]
  generalize h (_ ≫ g.pG.left) = a
  generalize h (_ ≫ D.Oφ g.pG β 0) = b
  generalize h (_ ≫ D.Oφ g.pG β 1) = c
  generalize h (_ ≫ D.Oφ g.pG β 3) = d
  change a ^ ((l : ℤ) - 1) * b ^ (1 : ℤ) * c ^ (-1 : ℤ) * d ^ (1 : ℤ) *
    (b ^ (-1 : ℤ) * c ^ (1 : ℤ) * a ^ (1 : ℤ) * d ^ (-1 : ℤ)) = a ^ (l : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

theorem level (k l : ℕ) (d : ∀ p : D.X × D.X, LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4)
      (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB p.1 i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB p.2 i))
      (Sum.elim (DegPre.famε k) (DegPre.famε l)))) (s : Finset D.X)
    (H : ∀ (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ D.P.A) (xe ye : T.left ⟶ (thickObj R I e G).left),
      xe ≫ g.pG.left = x.left → ye ≫ g.pG.left = y.left →
      xe ≫ (thickObj R I e G).hom = ye ≫ (thickObj R I e G).hom → ∀ (z : T.left) (J), Good D.P.L z J →
      ∑ α ∈ s, ∑ β ∈ s, sval (d (α, β)) (lift x y).left z J *
        ((val (g.t α) xe z J).val * (val (g.t β) ye z J).val) = 0)
    (α : D.X) (hα : α ∈ s) (β : D.X) (hβ : β ∈ s) (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ D.P.A).left)
    (hr : ∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (D.P.A ⊗ D.P.A).hom)
    (z : Z) (J) (hJ : Good D.P.L z J) : sval (d (α, β)) r z J = 0 := by
  let Ge := (Over.map (thick R I e)).obj (thickObj R I e G)
  have hcl : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have ex : ∀ α : D.X, ∃ t : LB.Sec (LB.LinComb D.P.L
      (Sum.elim (fun i => (fst D.P.A Ge).left ≫ D.famφB α i) (fun _ : Unit => (snd D.P.A Ge ≫ g.pG).left))
      (Sum.elim (DegPre.famε k) (fun _ => (l : ℤ)))), ∀ (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ Ge).left) (z : Z) (J),
      Good D.P.L z J → sval t r z J = ∑ β ∈ s, sval (d (α, β)) (r ≫ (D.P.A ◁ g.pG).left) z J *
        (val (g.t β) (r ≫ (snd D.P.A Ge).left) z J).val := by
    intro α
    choose u hu using fun β : D.X => exists_sec D.P.isLB (formEq_cancel g k l α β)
      (pullMulSec (d (α, β)) (D.P.A ◁ g.pG).left (LB.pullGen D.P.L _ _ (g.t β) (snd D.P.A Ge).left)
        (DVR.pullGen_isGen D.P.L _ _ _ (g.t_gen β) _))
    obtain ⟨t, ht⟩ := exists_sec_finsum s u
    refine ⟨t, fun Z r z J hJ => (ht Z r z J hJ).trans (Finset.sum_congr rfl fun β _ => ?_)⟩
    rw [hu β Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, val_pull hJ]
  choose t ht using ex
  have h₁ := sval_eq_zero_of_sum_mul_coord R I D e G g (D.P.A ⊗ Ge) (fst _ _) _ _ _ t s (by
    intro Z x r hx z J hJ
    let r' : Over.mk (r ≫ (D.P.A ⊗ Ge).hom) ⟶ D.P.A ⊗ Ge := Over.homMk r rfl
    have E := H _ (r' ≫ fst _ _) (r' ≫ snd _ _ ≫ g.pG) x (r ≫ (snd D.P.A Ge).left) hx.symm
      (Category.assoc _ _ _) (by
        rw [← cancel_mono (thick R I e), Category.assoc, Category.assoc, Category.assoc]
        have w₁ : g.pG.left ≫ D.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w g.pG
        have w₂ : (snd D.P.A Ge).left ≫ (thickObj R I e G).hom ≫ thick R I e = (D.P.A ⊗ Ge).hom :=
          Over.w (snd D.P.A Ge)
        rw [w₂, ← w₁, ← Category.assoc, ← hx, Category.assoc, Over.w]) z J hJ
    have e₁ : lift (r' ≫ fst _ _) (r' ≫ snd _ _ ≫ g.pG) = r' ≫ D.P.A ◁ g.pG := by
      ext1 <;> simp
    rw [e₁] at E
    refine Eq.trans (Finset.sum_congr rfl fun α _ => ?_) E
    rw [ht α Z r z J hJ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [_root_.mul_assoc, mul_comm (val (g.t β) _ z J).val]
    rfl) α hα
  have h₂ := LiftTest.main R I D e G g (D.P.A ⊗ Ge) (fst _ _) _ D.P.L D.P.isLB _ _ _ (t α) h₁
  have h₃ := sval_eq_zero_of_sum_mul_coord R I D e G g (D.P.A ⊗ D.P.A) (snd _ _) _
    (fun β => Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i)
      (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i)) _ (fun β => d (α, β)) s (by
    intro Z y r hy z J hJ
    let r' : Over.mk (r ≫ (D.P.A ⊗ D.P.A).hom) ⟶ D.P.A ⊗ D.P.A := Over.homMk r rfl
    let y' : Over.mk (r ≫ (D.P.A ⊗ D.P.A).hom) ⟶ Ge := Over.homMk y (by
      change y ≫ Ge.hom = r ≫ (D.P.A ⊗ D.P.A).hom
      rw [← Over.w g.pG, ← Category.assoc, ← hy, Category.assoc, Over.w])
    have hy' : r' ≫ snd _ _ = y' ≫ g.pG := Over.OverMorphism.ext hy
    have e₁ : lift (r' ≫ fst _ _) y' ≫ D.P.A ◁ g.pG = r' := by
      ext1
      · simp
      · rw [hy', Category.assoc, whiskerLeft_snd, lift_snd_assoc]
    have e₂ : (lift (r' ≫ fst _ _) y').left ≫ (D.P.A ◁ g.pG).left = r := congrArg CommaMorphism.left e₁
    have e₃ : (lift (r' ≫ fst _ _) y').left ≫ (snd D.P.A Ge).left = y :=
      congrArg CommaMorphism.left (lift_snd (r' ≫ fst _ _) y')
    have E := h₂ Z (lift (r' ≫ fst _ _) y').left ⟨y ≫ (thickObj R I e G).hom, by
      rw [Over.w, Category.assoc]
      exact Over.w y'⟩ z J hJ
    rw [ht α _ _ z J hJ, e₂, e₃] at E
    exact E) β hβ
  exact LiftTest.main R I D e G g (D.P.A ⊗ D.P.A) (snd _ _) _ D.P.L D.P.isLB _ _ _ (d (α, β)) h₃ Z r hr z J hJ

theorem main : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (k l : ℕ) (d : ∀ p : D.X × D.X, LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB p.1 i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB p.2 i)) (Sum.elim (DegPre.famε k) (DegPre.famε l)))), (∀ e : ℕ, ∃ s₀ : Finset D.X, ∀ s : Finset D.X, s₀ ⊆ s → ∀ (T : Over (Spec (CommRingCat.of V))) (x y : T ⟶ D.P.A) (xe ye : T.left ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (U.gt e).pG.left = x.left → ye ≫ (U.gt e).pG.left = y.left → xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom = ye ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom → ∀ (z : T.left) (J), Good D.P.L z J → ∑ α ∈ s, ∑ β ∈ s, sval (d (α, β)) (lift x y).left z J * ((val ((U.gt e).t α) xe z J).val * (val ((U.gt e).t β) ye z J).val) = 0) → ∀ p j, (d p).f j = 0) := by
  classical
  intro V _ _ _ hV D A G _ _ U k l d H p j
  have := hV.1
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : Smooth (D.P.A ⊗ D.P.A).hom := inferInstanceAs (Smooth (pullback.fst D.P.A.hom D.P.A.hom ≫ D.P.A.hom))
  have : GeometricallyConnected (D.P.A ⊗ D.P.A).hom := by
    change GeometricallyConnected (pullback.fst D.P.A.hom D.P.A.hom ≫ D.P.A.hom)
    exact GeometricallyConnected.comp _ _
  refine sec_eq_zero_of_thickenings_of_section V (IsLocalRing.maximalIdeal V)
    (IsLocalRing.maximalIdeal_le_jacobson _) (D.P.A ⊗ D.P.A) (lift η[D.P.A] η[D.P.A]) _
    (DVR.linComb_isLB D.P.L D.P.isLB _ _) (d p) (fun e j => app_sec_eq_zero_of_sval D.P.isLB (d p) _ ?_ j) j
  obtain ⟨s₀, hs⟩ := H e
  exact level (U.gt e) k l d (insert p.1 (insert p.2 s₀))
    (hs _ ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))) p.1 (Finset.mem_insert_self _ _) p.2
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) _ _
    ⟨pullback.snd _ _, pullback.condition.symm⟩

end GlobalTheory.WeightTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.PullSec

section General
variable {X X' W Y Y₂ : Scheme.{0}}

theorem sec_eq {M : LB X} {s t : LB.Sec M} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s; cases t; congr; funext i; exact h i

theorem exists_pullSec {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y₂ ⟶ X)} {φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (h : Y ⟶ Y₂) (hc : ∀ k, φ' k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  have h1 : (LB.oneGen L (Y := Y)).IsGen := fun i j =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  obtain ⟨s', hs⟩ := exists_sec hL (φ' := φ') (ε' := ε) (fun U _ g => by
      refine ((Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) rfl (Fintype.prod_empty _)).trans
        (_root_.mul_one _))).trans ?_
      exact Finset.prod_congr rfl fun k _ => by rw [hc]; rfl) (pullMulSec s h (LB.oneGen L) h1)
  refine ⟨s', fun Z r z J hJ => (hs Z r z J hJ).trans ((sval_pullMulSec s h _ h1 r z hJ).trans ?_)⟩
  rw [val_one, Units.val_one, _root_.mul_one]

theorem exists_sec_of_iso {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {F : W ⟶ X} {F' : W ⟶ X'}
    (w : LB.Iso (L'.pull F') (L.pull F)) (hw : w.IsGen) (y₀ : Y ⟶ W) (h : Y ⟶ Y₂) (a : Y ⟶ X') (b : Y₂ ⟶ X)
    (ha : y₀ ≫ F' = a) (hb : y₀ ≫ F = h ≫ b) (k : ℕ)
    (σ : LB.Sec (LB.LinComb L (fun _ : Fin 1 => b) (fun _ => (k : ℤ)))) :
    ∃ t : LB.Sec (LB.LinComb L' (fun _ : Fin 1 => a) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι) (j : L'.ι), F (y₀ (r z)) ∈ L.U i → F' (y₀ (r z)) ∈ L'.U j →
        (gw w (r ≫ y₀) z i (fun _ => j)).val ^ k *
            gs r z (LB.wchart L' (fun _ : Fin 1 => a) (fun _ => j)) (t.f fun _ => j) =
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) := by
  subst ha
  have pw := (isGen_iff w).1 hw
  have pt : ∀ y : Y, b (h y) = F (y₀ y) := fun y => congrArg (fun g => g y) hb.symm
  have mb : ∀ (y : Y) (i : L.ι), F (y₀ y) ∈ L.U i → h y ∈ LB.wchart L (fun _ : Fin 1 => b) (fun _ => i) :=
    fun y i hi => Set.mem_iInter.2 fun _ => show b (h y) ∈ L.U i by rw [pt]; exact hi
  have tw : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i i' : L.ι) (j j' : L'.ι), F (y₀ (r z)) ∈ L.U i →
      F (y₀ (r z)) ∈ L.U i' → F' (y₀ (r z)) ∈ L'.U j → F' (y₀ (r z)) ∈ L'.U j' →
      ((gw w (r ≫ y₀) z i (fun _ => j))⁻¹ ^ k).val *
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) =
        (gm (r ≫ y₀ ≫ F') z (L'.U j ⊓ L'.U j') (L'.g j j') ^ (k : ℤ)).val *
          (((gw w (r ≫ y₀) z i' (fun _ => j'))⁻¹ ^ k).val *
            gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i')) (σ.f fun _ => i')) := by
    intro Z r z i i' j j' hi hi' hj hj'
    have e := pw Z (r ≫ y₀) z i i' (fun _ => j) (fun _ => j') hi hi' (mem_pull.2 hj) (mem_pull.2 hj')
    rw [gm_pull_g L' F' (r ≫ y₀) z (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')] at e
    rw [sec_trans σ (r ≫ h) z (mb _ i hi) (mb _ i' hi'), trF, Fintype.prod_unique, e, ← _root_.mul_assoc,
      ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    congr 2
    rw [Category.assoc r h b, ← hb, Category.assoc r y₀ F, Category.assoc r y₀ F', zpow_natCast, zpow_natCast,
      ← mul_pow, ← mul_pow]
    congr 1
    generalize gm (r ≫ y₀ ≫ F) z (L.U i ⊓ L.U i') (L.g i i') = P
    generalize gm (r ≫ y₀ ≫ F') z (L'.U j ⊓ L'.U j') (L'.g j j') = Q
    generalize gw w (r ≫ y₀) z i' (fun _ => j') = C
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ j : Fin 1 → L'.ι, ∃ s : Γ(Y, LB.wchart L' (fun _ : Fin 1 => y₀ ≫ F') j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι), F (y₀ (r z)) ∈ L.U i → F' (y₀ (r z)) ∈ L'.U (j 0) →
        gs r z _ s = ((gw w (r ≫ y₀) z i (fun _ => j 0))⁻¹ ^ k).val *
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) := by
    intro j
    obtain ⟨V, hV⟩ : ∃ V : L.ι → Y.Opens, ∀ i y, y ∈ V i ↔ F (y₀ y) ∈ L.U i ∧ F' (y₀ y) ∈ L'.U (j 0) :=
      ⟨fun i => y₀ ⁻¹ᵁ (F ⁻¹ᵁ L.U i) ⊓ y₀ ⁻¹ᵁ (F' ⁻¹ᵁ L'.U (j 0)), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, V i ≤ LB.wchart L' (fun _ : Fin 1 => y₀ ≫ F') j := fun i y hy =>
      Set.mem_iInter.2 fun c => by rw [Subsingleton.elim c 0]; exact ((hV i y).1 hy).2
    have l₁ : ∀ i, V i ≤ y₀ ⁻¹ᵁ ((L.pull F).U (fun _ => i) ⊓ (L'.pull F').U (fun _ => j 0)) := fun i y hy =>
      ⟨mem_pull.2 ((hV i y).1 hy).1, mem_pull.2 ((hV i y).1 hy).2⟩
    have l₂ : ∀ i, V i ≤ h ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => b) (fun _ => i) := fun i y hy =>
      mb y i ((hV i y).1 hy).1
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Y, V i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι), r z ∈ V i →
        gs r z (V i) (u i) = ((gw w (r ≫ y₀) z i (fun _ => j 0))⁻¹ ^ k).val *
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) :=
      ⟨fun i => ((res (l₁ i) (pullU y₀ _ (w.s (fun _ => i, fun _ => j 0))))⁻¹ ^ k).val *
          (Y.presheaf.map (homOfLE (l₂ i)).op).hom ((h.app _).hom (σ.f fun _ => i)), fun Z r z i hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans (congrArg Units.val
          ((map_pow _ _ _).trans (congrArg (· ^ k) ((map_inv _ _).trans (congrArg (·⁻¹)
            ((gm_res r z (l₁ i) hz _).trans (gm_pull r y₀ z _ (l₁ i hz) _))))))))
          ((gs_res r z (l₂ i) hz _).trans (gs_pull r h z _ (l₂ i hz) _)))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' V (LB.wchart L' (fun _ : Fin 1 => y₀ ≫ F') j)
      (fun i => homOfLE (l₀ i)) (fun y hy => by
        obtain ⟨i, hi⟩ := exists_chart hL (F (y₀ y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hV i y).2 ⟨hi, Set.mem_iInter.1 hy 0⟩⟩) u
      (fun i i' => fn_ext (V := V i ⊓ V i') fun y hy => by
        have h₁ := (hV i y).1 hy.1
        have h₂ := (hV i' y).1 hy.2
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y i hy.1, hu _ _ y i' hy.2, tw _ (𝟙 Y) y i i' (j 0) (j 0) h₁.1 h₂.1 h₁.2 h₁.2,
          gm_self hL' (𝟙 Y ≫ y₀ ≫ F') y h₁.2, one_zpow, Units.val_one, _root_.one_mul])
    refine ⟨s, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ V i := (hV i _).2 ⟨h₁, h₂⟩
    exact (gs_res r z (l₀ i) hz s).symm.trans ((congrArg (gs r z (V i)) (hs i)).trans (hu Z r z i hz))
  choose s hs using glue
  refine ⟨⟨s, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z i j hi hj => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hL (F (y₀ y))
    have m : F' (y₀ y) ∈ L'.U (j 0) := Set.mem_iInter.1 hy.1 0
    have m' : F' (y₀ y) ∈ L'.U (j' 0) := Set.mem_iInter.1 hy.2 0
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L' _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (hs j _ (𝟙 Y) y i hi m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y i hi m')).symm)
    rw [Fin.prod_univ_one]
    exact tw _ (𝟙 Y) y i i (j 0) (j' 0) hi hi m m'
  · refine (congrArg _ (hs (fun _ => j) Z r z i hi hj)).trans ?_
    rw [← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow,
      Units.val_one, _root_.one_mul]

end General

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem existsUnique_pullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (σ : U.SecGT T k) :
    ∃! t, U.PullG F φ k σ t := by
  let y₀ : (TFK (R := R) F ⊗ A.A).left ⟶ ((Over.pullback (jK R)).obj G).left :=
    (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left
  have ih : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id]; rfl
  have hi : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id]; rfl
  have ha : y₀ ≫ U.gen.hom.left = (snd (TFK (R := R) F) A.A).left :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ih).trans (Category.comp_id _))
  have hcomm : ((fst (TFK (R := R) F) A.A).left ≫ φ.left) ≫ T.hom = (y₀ ≫ pullback.fst G.hom (jK R)) ≫ G.hom := by
    have e₁ : φ.left ≫ T.hom = jFK (R := R) F ≫ jK R := Over.w φ
    have e₂ : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := Over.w U.gen.inv
    have e₃ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
      (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ jK R) e₃).trans ?_)))
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (y₀ ≫ ·) pullback.condition)).symm
    rw [← e₂]
    simp only [y₀, Category.assoc]
  let h : (TFK (R := R) F ⊗ A.A).left ⟶ (T ⊗ G).left := pullback.lift _ _ hcomm
  have h₁ : h ≫ (fst T G).left = (fst (TFK (R := R) F) A.A).left ≫ φ.left := pullback.lift_fst _ _ _
  have h₂ : h ≫ (snd T G).left = y₀ ≫ pullback.fst G.hom (jK R) := pullback.lift_snd _ _ _
  obtain ⟨t, ht⟩ := exists_sec_of_iso U.P.L.isLB A.isLB U.wA U.wA_gen y₀ h _ (snd T G).left ha h₂.symm k σ
  have key : U.PullG F φ k σ t := by
    intro Z rA y rG e₁ e₂ e₃ z JA JG hA hG
    obtain rfl : y = rA ≫ y₀ := by
      have := congrArg (· ≫ U.gen.inv.left) e₁
      simp only [Category.assoc, hi, Category.comp_id] at this
      exact this.symm
    obtain rfl : rG = rA ≫ h := by
      refine pullback.hom_ext (e₃.trans ?_) (e₂.trans ?_)
      · exact ((Category.assoc _ _ _).trans (congrArg (rA ≫ ·) h₁)).symm
      · exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (rA ≫ ·) h₂)).symm
    rw [sval_of (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) t rA z JA
        (fun _ => JA ((rA ≫ y₀) ≫ U.gen.hom.left)) (fun _ => congrArg JA e₁),
      sval_of σ (rA ≫ h) z JG (fun _ => JG ((rA ≫ y₀) ≫ pullback.fst G.hom (jK R))) (fun _ => congrArg JG e₂)]
    exact ht Z rA z _ _ (hG ((rA ≫ y₀) ≫ pullback.fst G.hom (jK R))) (hA ((rA ≫ y₀) ≫ U.gen.hom.left))
  refine ⟨t, key, fun t' key' => sec_eq fun j => sec_ext_val A.isLB (fun z JA hA => ?_) j⟩
  obtain ⟨JG, hG⟩ := exists_good_pt U.P.L.isLB z
  have e₁ : 𝟙 _ ≫ (snd (TFK (R := R) F) A.A).left = y₀ ≫ U.gen.hom.left := (Category.id_comp _).trans ha.symm
  have e₃ : h ≫ (fst T G).left = 𝟙 _ ≫ (fst (TFK (R := R) F) A.A).left ≫ φ.left := h₁.trans (Category.id_comp _).symm
  have := (key' _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG).trans (key _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG).symm
  rw [← Units.val_pow_eq_pow_val] at this
  exact (Units.mul_right_inj _).1 this

theorem existsUnique_pullB (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (f : ∀ α, SecBT D T k α) :
    ∃! s, PullB D F φ k f s := by
  have hc : ∀ (α : D.X) (i : Fin 4), DegPre.famφ D F α i = (φ ▷ D.P.A).left ≫ famφT D T α i := fun α i => by
    have u : φ ▷ D.P.A ≫ toUnit (T ⊗ D.P.A) = toUnit _ := toUnit_unique _ _
    have a₀ : snd (TF (R := R) F) D.P.A = φ ▷ D.P.A ≫ snd T D.P.A := (whiskerRight_snd _ _).symm
    have a₂ : ∀ c : 𝟙_ _ ⟶ D.P.A, toUnit (DegPre.BF D F) ≫ c = φ ▷ D.P.A ≫ toUnit (T ⊗ D.P.A) ≫ c := fun c => by
      rw [← Category.assoc, u]
    fin_cases i
    · exact congrArg (fun q => q.left) a₀
    · exact congrArg (fun q => q.left) ((congrArg₂ (· * ·) a₀ (a₂ (D.c α))).trans (MonObj.comp_mul _ _ _).symm)
    · exact congrArg (fun q => q.left) (a₂ (D.c α))
    · exact congrArg (fun q => q.left) (a₂ η[D.P.A])
  choose s hs using fun α => exists_pullSec D.P.isLB (φ ▷ D.P.A).left (hc α) (f α)
  have key : PullB D F φ k f s := fun α z J hJ => (hs α _ (𝟙 _) z J hJ).trans (by rw [Category.id_comp])
  exact ⟨s, key, fun s' key' => funext fun α => sec_eq fun j => sec_ext_val D.P.isLB
    (fun z J hJ => (key' α z J hJ).trans (key α z J hJ).symm) j⟩

theorem pullEx : (AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (T : Over (Spec (CommRingCat.of V))) (φ : TF (R := V) F ⟶ T) (k : ℕ), (∀ σ, ∃! t, U.PullG F φ k σ t) ∧ ∀ f, ∃! s, PullB D F φ k f s) :=
  fun _ _ _ _ _ D _ _ _ _ U F _ _ _ φ k => ⟨existsUnique_pullG U F φ k, existsUnique_pullB D F φ k⟩

end GlobalTheory.UU.PullSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfExpT
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.IntExp

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ f) z U a = (r.stalkMap z).hom (gs f (r z) U a) := by
  rw [gs_eq f (r z) U h, gs_eq (r ≫ f) z U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _).symm

theorem sval_comp {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) (J) (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem gs_scal_one {F : Type} [CommRing F] {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : Y ⟶ Spec (CommRingCat.of F)) :
    gs r z ⊤ (scal p (1 : F)) = 1 := by
  rw [gs_eq r z ⊤ trivial]
  simp only [scal, map_one]

theorem expF_of_expT : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (t) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f → U.PullG F (toUnit _) k σ t → PullB D F (toUnit _) k f s → U.ExpF F k t s := by
  intro R _ _ I D A G _ _ U F _ _ k σ f t s hE hG hB
  refine ⟨1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE, ?_, ?_⟩
  · intro Z rA y rG h₁ h₂ z JA JG hJA hJG
    rw [Fin.sum_univ_one]
    refine (hG Z rA y rG h₁ h₂ ?_ z JA JG hJA hJG).trans ?_
    · have e₁ : (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left = (snd (𝟙_ _) G).left ≫ G.hom := by
        have a := Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G)
        have b := Over.w (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) G)
        exact ((Category.comp_id _).symm.trans a).trans b.symm
      have e₂ : (toUnit (TF (R := R) F)).left = jFK (R := R) F ≫ jK R := by
        have a := Over.w (toUnit (TF (R := R) F))
        exact (Category.comp_id _).symm.trans a
      have e₃ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
        (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
      have e₄ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
      calc rG ≫ (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left
          = (rG ≫ (snd (𝟙_ _) G).left) ≫ G.hom := by rw [e₁]; exact (Category.assoc _ _ _).symm
        _ = y ≫ pullback.fst G.hom (jK R) ≫ G.hom := by rw [h₂]; exact Category.assoc _ _ _
        _ = y ≫ (U.gen.hom.left ≫ A.A.hom) ≫ jK R := by rw [e₄]; exact congrArg (y ≫ ·) pullback.condition
        _ = (rA ≫ (snd (TFK (R := R) F) A.A).left) ≫ A.A.hom ≫ jK R := by rw [h₁]; simp only [Category.assoc]
        _ = rA ≫ ((fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F) ≫ jK R := by rw [e₃]; simp only [Category.assoc]
        _ = _ := by rw [e₂]; exact congrArg (rA ≫ ·) (Category.assoc _ _ _)
    · exact ((congrArg (· * _) (gs_scal_one rA z _)).trans (one_mul _)).symm
  · intro α Z rF rB h z J hJ
    rw [Fin.sum_univ_one]
    refine Eq.trans ?_ ((congrArg (· * _) (gs_scal_one rF z _)).trans (one_mul _)).symm
    have e : rB = rF ≫ (toUnit (TF (R := R) F) ▷ D.P.A).left := by
      have w : (toUnit (TF (R := R) F) ▷ D.P.A).left ≫ (snd (𝟙_ _) D.P.A).left = (snd _ D.P.A).left :=
        congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := R) F)) D.P.A)
      have i : IsIso (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A).left := by
        rw [← leftUnitor_hom]; exact inferInstanceAs (IsIso ((Over.forget _).map (λ_ D.P.A).hom))
      rw [← cancel_mono (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A).left, Category.assoc, w, h]
    rw [e, sval_comp (f α) _ rF z J hJ, ← hB α (rF z) _ (fun ψ => hJ (rF ≫ ψ)), ← sval_comp (s α) _ rF z J hJ,
      Category.comp_id]

end GlobalTheory.UU.IntExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpTOfExpandsAt
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem expT_of_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : H0 U'.LG.L k) (σ₀ : H0 U.P.L.L k) (σ' : U.SecGT (𝟙_ _) k) (f) (f'), HEq σ σ₀ → SameG σ₀ σ' → SameB f f' → (∀ e, U'.ExpandsAt e k σ f) → U.ExpT (𝟙_ _) k σ' f' := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ σ' f f' hσ hG hB hE e
  obtain ⟨S, hS⟩ := ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_val U' e k σ f (hE e)
  refine ⟨S, fun Z x rG rB h1 h2 _ z JG J hJG hJ => ?_⟩
  obtain ⟨h₀, h₁⟩ := hS Z x z J hJ
  clear hS hE
  obtain ⟨-, hL, -, -, hgt, hw⟩ := hM
  cases U'
  dsimp only at hL hgt hw
  subst hL hgt
  cases hw
  cases hσ
  have eB : ∀ α, sval (f' α) rB z J = sval (f α) (x ≫ (U.gt e).pG.left) z J := fun α => by
    rw [hB α Z rB z J hJ, h2]
  refine ⟨fun α hα => (eB α).trans (h₀ α hα), ?_⟩
  have H := h₁ (JG (x ≫ (fstG I e G).left)) (hJG (x ≫ (fstG I e G).left))
  rw [hG Z rG z JG hJG, h1, Finset.sum_congr rfl fun α _ => congrArg (· * _) (eB α)]
  refine Eq.trans ?_ H
  rw [Units.val_pow_eq_pow_val, sval_of σ₀ _ z JG (fun _ => JG (x ≫ (fstG I e G).left)) (fun _ => by rw [Category.comp_id])]
  rfl

end GlobalTheory.UU
end

