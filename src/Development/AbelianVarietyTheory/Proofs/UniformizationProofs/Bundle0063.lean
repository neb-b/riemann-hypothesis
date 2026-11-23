module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductSupportInSubgroupTheta
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.MulSupp

section
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem sval_eq_zero (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J}
    (hJ : Good L z J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ((congrArg _ (map_zero _)).trans (map_zero _)))

theorem exists_sub_sum {N : Type} (a : LB.Sec (LB.LinComb L φ ε)) (p : N → LB.Sec (LB.LinComb L φ ε)) (s : Finset N) :
    ∃ d : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval a r z J - ∑ i ∈ s, sval (p i) r z J := by
  refine ⟨⟨fun j => a.f j - ∑ i ∈ s, (p i).f j, fun i j => ?_⟩, fun Z r z J hJ => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sub, map_sub, map_sum, map_sum, mul_sub, Finset.mul_sum, a.compat]
      exact congrArg _ (Finset.sum_congr rfl fun b _ => (p b).compat i j)
  · have hm := hJ.mem φ r
    refine (gs_eq r z _ hm _).trans ?_
    refine (congrArg _ (map_sub _ _ _)).trans ((map_sub _ _ _).trans (congrArg₂ (· - ·) (gs_eq r z _ hm _).symm ?_))
    refine (congrArg _ (map_sum _ _ _)).trans ((map_sum _ _ _).trans (Finset.sum_congr rfl fun b _ => ?_))
    exact (gs_eq r z _ hm _).symm
end

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

noncomputable def cubAt (α β : D.X) {Z : Scheme.{0}} (ψ : Z ⟶ D.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
    (ψ ≫ (lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) (𝟙 D.P.A))).left) z J

theorem val_pull_cub (α β : D.X) {Y : Over (Spec (CommRingCat.of R))} (p : Y ⟶ D.P.A) {Z : Scheme.{0}}
    (r : Z ⟶ Y.left) (z : Z) {J} (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) p)).left) r z J = cubAt D α β (r ≫ p.left) z J := by
  refine (val_pull hJ _ _ _).trans ?_
  have e : lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) p) =
      p ≫ lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) (𝟙 D.P.A)) := by
    simp only [comp_lift, comp_toUnit_assoc, Category.comp_id]
  rw [e, Over.comp_left, ← Category.assoc]
  rfl

theorem exists_prod (T : Over (Spec (CommRingCat.of R))) (k l : ℕ) (α β : D.X) (a : SecBT D T k α) (b : SecBT D T l β) :
    ∃ p : SecBT D T (k + l) (α + β), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval p r z J = sval a r z J * sval b r z J * (cubAt D α β (r ≫ (snd T D.P.A).left) z J).val := by
  obtain ⟨p, hp⟩ := exists_sec D.P.isLB (φ' := famφT D T (α + β)) (ε' := DegPre.famε (k + l)) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (Fintype.prod_sum_type _)
        (prod_cub (toUnit _ ≫ D.c α) (toUnit _ ≫ D.c β) (snd T D.P.A) h))).trans ?_
      have e₀ : ∀ u, padd D.P.A (snd T D.P.A) u = u * snd T D.P.A :=
        fun u => mul_comm (snd T D.P.A) u
      have e₁ : toUnit (T ⊗ D.P.A) ≫ D.c (α + β) = (toUnit _ ≫ D.c α) * (toUnit _ ≫ D.c β) := by
        rw [D.c_add]; exact MonObj.comp_mul _ _ _
      have e₂ : toUnit (T ⊗ D.P.A) ≫ η[D.P.A] = 1 := rfl
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, famφT, DegPre.famε, e₀, e₁, e₂, Matrix.cons_val]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec a b) (genSec (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) (snd T D.P.A))).left) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)))
  refine ⟨p, fun Z r z J hJ => (hp Z r z J hJ).trans ?_⟩
  exact (H1.SectionArithmetic.sval_mulSec _ _ r z hJ).trans (congrArg₂ (· * ·) (H1.SectionArithmetic.sval_mulSec _ _ r z hJ)
    ((sval_genSec _ _ r z hJ).trans (congrArg Units.val (val_pull_cub D α β _ r z hJ))))

variable {D} {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem val_coord_mul {e : ℕ} (g : GtCoord I D e G) (α β : D.X) {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G).left)
    (z : Z) {J} (hJ : Good D.P.L z J) :
    val (g.t (α + β)) x z J * cubAt D α β (x ≫ g.pG.left) z J = val (g.t α) x z J * val (g.t β) x z J := by
  have E := val_corr hJ (g.t_mul α β) x
  exact ((val_mul hJ _ _ _).trans (congrArg _ (val_pull_cub D α β g.pG x z hJ))).symm.trans (E.trans (val_mul hJ _ _ _))

theorem level {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G) (Λ : AddSubgroup D.X) (k l : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) (f) (f') (f'')
    (h : U.ExpT (𝟙_ _) k σ f) (h' : U.ExpT (𝟙_ _) l σ' f') (h'' : U.ExpT (𝟙_ _) (k + l) σ'' f'')
    (hm : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J →
      sval σ'' r z J = sval σ r z J * sval σ' r z J)
    (hf : ∀ α ∉ Λ, ∀ j, (f α).f j = 0) (hf' : ∀ α ∉ Λ, ∀ j, (f' α).f j = 0) (χ₀ : D.X) (hχ : χ₀ ∉ Λ) (e : ℕ)
    (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left)
    (hr : r ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (f'' χ₀) r z J = 0 := by
  classical
  obtain ⟨s, hs⟩ := h e
  obtain ⟨s', hs'⟩ := h' e
  obtain ⟨s'', hs''⟩ := h'' e
  have c₁ : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left),
      (x ≫ (lift (toUnit _) (fstG I e G)).left) ≫ (snd (𝟙_ _) G).left = x ≫ (fstG I e G).left := fun Z x =>
    (Category.assoc _ _ _).trans (congrArg (fun q => x ≫ q.left) (lift_snd (toUnit _) (fstG I e G)))
  have c₂ : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      r ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left →
      r ≫ (fst (𝟙_ _) D.P.A).left = (x ≫ (lift (toUnit _) (fstG I e G)).left) ≫ (fst (𝟙_ _) G).left := by
    intro Z x r hr
    have a₁ : fst (𝟙_ _) D.P.A = snd _ D.P.A ≫ toUnit _ := toUnit_unique _ _
    have a₂ : (U.gt e).pG ≫ toUnit _ = lift (toUnit _) (fstG I e G) ≫ fst (𝟙_ _) G := toUnit_unique _ _
    rw [a₁, Over.comp_left, ← Category.assoc, hr]
    exact (Category.assoc _ _ _).trans ((congrArg (fun q => x ≫ q.left) a₂).trans (Category.assoc _ _ _).symm)
  have ex : ∀ (g : D.X) (p : D.X × D.X), ∃ q : SecBT D (𝟙_ _) (k + l) g,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval q r z J = if p.1 + p.2 = g then
        sval (f p.1) r z J * sval (f' p.2) r z J * (cubAt D p.1 p.2 (r ≫ (snd _ D.P.A).left) z J).val else 0 := by
    intro g p
    by_cases hp : p.1 + p.2 = g
    · subst hp
      simpa only [if_true] using exists_prod D (𝟙_ _) k l p.1 p.2 (f p.1) (f' p.2)
    · exact ⟨H1.SectionArithmetic.secZero _, fun Z r z J hJ => by rw [if_neg hp]; exact sval_eq_zero _ (fun _ => rfl) r z hJ⟩
  choose q hq using ex
  choose d hd using fun g => exists_sub_sum (f'' g) (q g) (s ×ˢ s')
  let S : Finset D.X := s'' ∪ (s ×ˢ s').image (fun p => p.1 + p.2)
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  by_cases hS : χ₀ ∈ S
  swap
  · exact (hs'' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ).1 χ₀ fun h => hS (Finset.mem_union_left _ h)
  have H := sval_eq_zero_of_sum_mul_coord R I D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) (Fin 4) (famφT D (𝟙_ _))
    (DegPre.famε (k + l)) d S (fun Z x r hr z J hJ => by
      choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
      obtain ⟨-, E⟩ := hs Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      obtain ⟨-, E'⟩ := hs' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      obtain ⟨E₀, E''⟩ := hs'' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      rw [hm _ _ z JG hJG, pow_add, _root_.mul_mul_mul_comm, E, E', Finset.sum_mul_sum, ← Finset.sum_product'] at E''
      simp only [hd _ Z r z J hJ, hq _ _ Z r z J hJ, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [sub_eq_zero, ← Finset.sum_subset Finset.subset_union_left (fun g _ hg => by rw [E₀ g hg, zero_mul]), ← E'',
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun p hp => ?_
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq]
      rw [if_pos (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun p : D.X × D.X => p.1 + p.2) hp)), hr,
        _root_.mul_mul_mul_comm, ← Units.val_mul, ← val_coord_mul (U.gt e) p.1 p.2 x z hJ, Units.val_mul]
      ring) χ₀ hS Z x r hr z J hJ
  rw [hd χ₀ Z r z J hJ, Finset.sum_eq_zero, sub_zero] at H
  · exact H
  intro p _
  rw [hq χ₀ p Z r z J hJ]
  split_ifs with hp
  · by_cases h₁ : p.1 ∈ Λ
    · have h₂ : p.2 ∉ Λ := fun h₂ => hχ (hp ▸ Λ.add_mem h₁ h₂)
      rw [sval_eq_zero _ (hf' _ h₂) r z hJ, mul_zero, zero_mul]
    · rw [sval_eq_zero _ (hf _ h₁) r z hJ, zero_mul, zero_mul]
  · rfl

theorem main : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (k l : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) f f' f'', U.ExpT (𝟙_ _) k σ f → U.ExpT (𝟙_ _) l σ' f' → U.ExpT (𝟙_ _) (k + l) σ'' f'' → (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ'' r z J = sval σ r z J * sval σ' r z J) → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → (∀ α ∉ Λ, ∀ j, (f' α).f j = 0) → ∀ α ∉ Λ, ∀ j, (f'' α).f j = 0) := by
  intro V _ _ _ hV D A G _ _ U Λ k l σ σ' σ'' f f' f'' h h' h'' hm hf hf' χ₀ hχ
  have := hV.1
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of V)))
  have eV : V ≃+* Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of V)).symm.commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := isNoetherianRing_of_ringEquiv V eV
  have : Nontrivial Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := eV.symm.nontrivial
  have : IsLocalRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    IsLocalRing.of_surjective' eV.toRingHom eV.surjective
  refine sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A (fun a ha => ?_) _ D.P.L D.P.isLB
    (Fin 4) _ _ (f'' χ₀) (fun e => LiftTest.main V _ D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) _ D.P.L D.P.isLB _ _ _ (f'' χ₀)
      (level U Λ k l σ σ' σ'' f f' f'' h h' h'' hm hf hf' χ₀ hχ e))
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  intro hu
  have hu' : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) := hu
  have := hu'.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
  rw [Iso.inv_hom_id_apply] at this
  exact ha this

end GlobalTheory.MulSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiMulPsiOfAdditionFirstVariable
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory
namespace FirstSlot
variable {R : Type} [CommRing R] [IsDomain R]

theorem cT_add (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (a b : D.X) :
    cT D T (a + b) = cT D T a * cT D T b := by
  rw [cT, D.c_add]
  exact MonObj.comp_mul _ _ _

theorem comp_cT (D : DegPre R) {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (a : D.X) :
    ρ ≫ cT D T a = cT D T' a := by
  rw [cT, cT, ← Category.assoc, toUnit_unique (ρ ≫ toUnit T) (toUnit T')]

theorem kapV_one (D : DegPre R) (a b : D.X) {T : Over (Spec (CommRingCat.of R))} {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (x : T ⟶ D.P.A) :
    kapV D a b z J x 1 = (val D.sym (1 : T ⟶ D.P.A).left z J)⁻¹ * rigV D z J ^ 2 *
      cubV D.cub z J (cT D T a) (cT D T b) x := by
  have h := isCub_cubV D.cub (T := T) (z := z) (J := J) hJ
  rw [kapV, kap0, inv_one]
  simp only [h.face₃, _root_.mul_one, _root_.one_mul, inv_one]
  rfl

theorem compare (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (s₀ : ∀ α, SecBT D T₀ 1 α) (r : R) {n : ℕ}
    (s s' : Fin n → ∀ α, SecBT D T₀ 2 α) (hA : AddB D T₀ s₀ r s s') (hP : PsiRel D T₀ s₀) (a b mu : D.X)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (κ : T ⟶ TK R) (x : T ⟶ D.P.A) (z : T.left) (J)
    (hJ : Good D.P.L z J) [IsDomain (T.left.presheaf.stalk z)] (hr : gs (𝟙 _) z ⊤ (scal T.hom r) ≠ 0)
    (h0 : ∀ χ, sval (s₀ 0) (lift ρ (x * cT D T χ)).left z J ≠ 0) (C U : T.left.presheaf.stalk z)
    (hs : ∀ i, sval (s i (a + b + 2 • mu)) (lift ρ x).left z J =
      C * (sval (s i (a + b)) (lift ρ (x * cT D T mu)).left z J * U)) :
    (cubV D.cub z J (cT D T (a + mu)) (cT D T (b + mu)) x).val *
        ((val (D.psi (a + mu)) κ.left z J).val * (val (D.psi (b + mu)) κ.left z J).val) =
      C * (U * (cubV D.cub z J (cT D T a) (cT D T b) (x * cT D T mu)).val * (val (D.psi a) κ.left z J).val *
        (val (D.psi b) κ.left z J).val) := by
  have e₁ := (hA T ρ x 1 z J hJ).1 (a + mu) (b + mu) (a + b + 2 • mu) (a - b) (by rw [two_smul]; abel) (by abel)
  have e₂ := (hA T ρ (x * cT D T mu) 1 z J hJ).1 a b (a + b) (a - b) rfl rfl
  rw [kapV_one D _ _ hJ, inv_one, _root_.mul_one x, hP _ T ρ κ _ z J hJ, hP (b + mu) T ρ κ _ z J hJ] at e₁
  rw [kapV_one D _ _ hJ, inv_one, _root_.mul_one (x * cT D T mu), hP _ T ρ κ _ z J hJ, hP b T ρ κ _ z J hJ,
    _root_.mul_assoc x, _root_.mul_assoc x, ← cT_add, ← cT_add, add_comm mu a, add_comm mu b] at e₂
  have e₃ : ∑ i, sval (s i (a + b + 2 • mu)) (lift ρ x).left z J * sval (s' i (a - b)) (lift ρ 1).left z J =
      C * U * ∑ i, sval (s i (a + b)) (lift ρ (x * cT D T mu)).left z J * sval (s' i (a - b)) (lift ρ 1).left z J := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs i]; ring
  rw [e₁, e₂] at e₃
  have hne : gs (𝟙 _) z ⊤ (scal T.hom r) * ((val D.sym (1 : T ⟶ D.P.A).left z J)⁻¹ * rigV D z J ^ 2).val *
      (rigV D z J).val * (rigV D z J).val * sval (s₀ 0) (lift ρ (x * cT D T (a + mu))).left z J *
      sval (s₀ 0) (lift ρ (x * cT D T (b + mu))).left z J ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hr (Units.ne_zero _)) (Units.ne_zero _))
      (Units.ne_zero _)) (h0 _)) (h0 _)
  refine mul_left_cancel₀ hne ?_
  simp only [Units.val_mul] at e₃ ⊢
  linear_combination e₃

theorem gs_scal_ne_zero {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Y) {r : R}
    (hr : r ≠ 0) : gs (𝟙 _) z ⊤ (scal (q ≫ jK R) r) ≠ 0 := by
  have h2 : ((jK R).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) := by
    have e := congrArg (fun φ => φ.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    exact e.symm
  have h3 : scal (q ≫ jK R) r = scal q (algebraMap R (FractionRing R) r) := congrArg q.appTop.hom h2
  have hu : IsUnit (algebraMap R (FractionRing R) r) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
  rw [h3, gs_eq _ z ⊤ trivial]
  exact ((((hu.map _).map q.appTop.hom).map _).map _).ne_zero

theorem isIso_transl (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (χ : D.X) :
    IsIso (lift (fst T D.P.A) (snd T D.P.A * cT D (T ⊗ D.P.A) χ)) := by
  refine ⟨lift (fst T D.P.A) (snd T D.P.A * (cT D (T ⊗ D.P.A) χ)⁻¹), ?_, ?_⟩
  · ext
    · simp
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, lift_snd, comp_cT, mul_inv_cancel_right,
        Category.id_comp]
  · ext
    · simp
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, lift_snd, comp_cT, inv_mul_cancel_right, Category.id_comp]

end FirstSlot


open FirstSlot in
theorem psi_mul_psi_of_addition_first_variable : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (a b mu α : D.X), α = a + b → ∀ (c : F) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 2 α mu) (DegPre.deltaε 2))), (∀ i z J, Good D.P.L z J → sval (s i (α + 2 • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D F c ⊤) * (sval (s i α) (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val)) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → (val (Z := (TF (R := R) F).left) (D.psi (a + mu)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b + mu)) (jFK (R := R) F) z J).val = gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) * (val u (DegPre.zF D F).left z J * cubV D.cub z J (cT D _ a) (cT D _ b) (cT D _ mu) * val (Z := (TF (R := R) F).left) (D.psi (a)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b)) (jFK (R := R) F) z J).val := by
  intro R _ _ D F _ _ s₀ r n s s' hr hA hP h0 a b mu α hα c u hs z J hJ
  subst hα
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have hint : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  let κF : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  have zf : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have zs : DegPre.zF D F ≫ snd _ _ = 1 := lift_snd _ _
  have zκ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A ≫ κF).left = jFK (R := R) F := by
    rw [← Over.comp_left, ← Category.assoc, zf, Category.id_comp]; rfl
  have hJ' : Good D.P.L ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ)) := fun ψ => hJ _
  have hhom : (DegPre.BF D F).hom = (fst (TF (R := R) F) D.P.A ≫ κF).left ≫ jK R :=
    (Over.w (fst (TF (R := R) F) D.P.A ≫ κF)).symm
  have key := FirstSlot.compare D (TF (R := R) F) s₀ r s s' hA hP a b mu (DegPre.BF D F) (fst _ _) (fst _ _ ≫ κF)
    (snd _ _) ((DegPre.zF D F).left z) _ hJ' (by rw [hhom]; exact gs_scal_ne_zero _ _ hr)
    (fun χ => by
      have := isIso_transl D (TF (R := R) F) χ
      have : IsIso (lift (fst (TF (R := R) F) D.P.A) (snd _ _ * cT D (DegPre.BF D F) χ)).left :=
        (Over.forget _).map_isIso (lift (fst (TF (R := R) F) D.P.A) (snd _ _ * cT D (TF (R := R) F ⊗ D.P.A) χ))
      exact sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) h0 _ _ _ _ hJ')
    _ _ (fun i => by
      rw [lift_fst_snd]
      exact hs i _ _ hJ')
  have ψn : ∀ χ, ((DegPre.zF D F).left.stalkMap z).hom (val (D.psi χ) (fst (TF (R := R) F) D.P.A ≫ κF).left
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ))).val =
      (val (Z := (TF (R := R) F).left) (D.psi χ) (jFK (R := R) F) z J).val := fun χ => by
    rw [← zκ]
    exact ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 (D.psi χ)).symm
  have cn : ∀ x x' y : DegPre.BF D F ⟶ D.P.A, ((DegPre.zF D F).left.stalkMap z).hom (cubV D.cub
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ)) x x' y).val =
      (cubV D.cub z J (DegPre.zF D F ≫ x) (DegPre.zF D F ≫ x') (DegPre.zF D F ≫ y)).val := fun x x' y => by
    refine ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 D.cub.t).symm.trans ?_
    rw [← Over.comp_left, comp_lift, comp_lift]; rfl
  have un : ((DegPre.zF D F).left.stalkMap z).hom (val u (𝟙 _)
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ))).val =
      (val u (DegPre.zF D F).left z J).val := by
    refine ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 u).symm.trans ?_
    rw [Category.comp_id]
  have kn : ((DegPre.zF D F).left.stalkMap z).hom (gs (𝟙 _) ((DegPre.zF D F).left z) ⊤ (DegPre.constBF D F c ⊤)) =
      gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) := by
    refine (gs_comp_stalkMap (𝟙 _) (DegPre.zF D F).left z ⊤ trivial _).symm.trans ?_
    refine (gs_res ((DegPre.zF D F).left ≫ 𝟙 _) z (U := ⊤) (V := ⊤) le_top trivial _).trans ?_
    refine (gs_pull ((DegPre.zF D F).left ≫ 𝟙 _) (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_
    rw [Category.comp_id, ← Over.comp_left, zf]
    rfl
  have k2 := congrArg ((DegPre.zF D F).left.stalkMap z).hom key
  simp only [map_mul] at k2
  rw [ψn, ψn, ψn, ψn, cn, cn, un, kn, MonObj.comp_mul, zs, comp_cT, comp_cT, comp_cT, comp_cT, comp_cT,
    _root_.one_mul, (isCub_cubV D.cub (T := TF (R := R) F) (z := z) (J := J) hJ).face₃, Units.val_one,
    _root_.one_mul] at k2
  simp only [Units.val_mul]
  exact k2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIff
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem sval_eq_zero_of_local_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, d.f j = 0) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) : sval d r z J = 0 := by
  have e : gs r z (LB.wchart L φ (fun k => J (r ≫ φ k))) 0 = 0 := by
    rw [gs_eq r z _ (hJ.mem φ r), map_zero, map_zero]
  exact (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h _)).trans e

theorem appTop_field_point_injective (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] :
    Function.Injective (toUnit (TF (R := R) F)).left.appTop.hom := by
  have e : (toUnit (TF (R := R) F)).left =
      Spec.map (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
    have := Over.w (toUnit (TF (R := R) F))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.comp_id _).symm.trans this
  rw [e]
  have hi : Function.Injective ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R (FractionRing R))
  have n := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))
  have hb : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have hc := hi.comp hb
  intro a b hab
  apply hc
  have na := congrArg (fun q => q.hom a) n
  have nb := congrArg (fun q => q.hom b) n
  exact na.symm.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom hab).trans nb)

theorem pullB_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (s : Raw D F k), PullB D F (toUnit _) k f s → ∀ α, ((∃ j, (s α).f j ≠ 0) ↔ ∃ j, (f α).f j ≠ 0) := by
  intro R _ _ D F _ _ k f s h α
  have := D.P.smoothDim
  have : Smooth D.P.A.hom := SmoothOfRelativeDimension.smooth D.P.g _
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  have : IsAffine (TF (R := R) F).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of F)))
  rw [← not_iff_not]
  simp only [not_exists, not_not]
  constructor
  · intro hs
    refine sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A _ _ (toUnit (TF (R := R) F))
      (appTop_field_point_injective R F) _ D.P.L D.P.isLB _ _ _ (f α) fun z J hJ => ?_
    exact (h α z J hJ).symm.trans (sval_eq_zero_of_local_eq_zero (s α) hs _ z J hJ)
  · intro hf
    refine sec_eq_zero_of_sval_eq_zero_of_app_injective (𝟙 _) (fun U a b hab => hab) D.P.L D.P.isLB _ _ (s α)
      fun z J hJ => ?_
    exact (h α z J hJ).trans (sval_eq_zero_of_local_eq_zero (f α) hf _ z J hJ)

end GlobalTheory
end

