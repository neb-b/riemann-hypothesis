module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DiscriminantEqJacobianCompleteIntersectionDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discriminant_eq_jacobian_complete_intersection_dvr : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (n l d : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, x.P.A.hom y ≠ IsLocalRing.closedPoint O → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∃ (ev₀ : ∀ j, Matrix (Fin d) (Fin ((l - j * n) ^ x.P.g)) O) (Pm : Matrix (Fin d) (Fin d) O) (t₀ : O), (Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b 0 k).f (ch a))) = Pm * ev₀ 0 ∧ IsCx kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m ev₀) ∧ TorsSq kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m ev₀) t₀ ∧ Associated (Pm.det ^ 2) (∏ a, jac x s (z a) (ch a)) := by
  first | exact @GlobalTheory.DiscrJacGlobal.main | exact GlobalTheory.DiscrJacGlobal.main | (intros; apply GlobalTheory.DiscrJacGlobal.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSymmetricSquareRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SymRoot

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

def rigCls (c : Pic A.left) : Pic A.left := c - pull (1 : A ⟶ A).left c

theorem pull_rigCls (c : Pic A.left) (x : T ⟶ A) :
    pull x.left (rigCls c) = pull x.left c - pull (1 : T ⟶ A).left c := by
  rw [rigCls, map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_one]

theorem lam_rigCls (c : Pic A.left) (x y : T ⟶ A) : lam (rigCls c) x y = lam c x y := by
  simp only [lam, pull_rigCls]
  abel

theorem lam_diag [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen)
    (hs : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL) :
    lam (cls L hL) (𝟙 A) (𝟙 A) = 2 • rigCls (cls L hL) := by
  have h := lam_mul_left hL hΘ (𝟙 A) (𝟙 A)⁻¹ (𝟙 A)
  rw [mul_inv_cancel, lam_one_left] at h
  have e : lam (cls L hL) (𝟙 A)⁻¹ (𝟙 A) = -(2 • rigCls (cls L hL)) := by
    rw [lam, inv_mul_cancel, Hom.inv_def, Category.id_comp, hs, Over.id_left, pull_id, rigCls]
    abel
  rw [e] at h
  exact add_neg_eq_zero.1 h.symm

theorem exists_polAV_sqOf : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (L : LB c.A.left), c.Principal → SmoothOfRelativeDimension h c.A.hom → L.IsLB → LBIso (abelian₂ c.A L) c.P → LBIso L (L.pull (GrpObj.inv : c.A ⟶ c.A).left) → ∃ (P : Out.PolAV (Sp R)) (φ : P.A.left ⟶ c.A.left), SqOf P c (𝟙 _) φ := by
  intro laws h k o _ ζ R _ _ β c L ⟨ha, hk⟩ hdim hL hΛ hs
  have hA := c.ab
  have hd : c.diag.IsLB := pull_isLB c.isLB _
  have hp : IsProjBy c.A.hom :=
    (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ c.A c.diag hA hd ha R (𝟙 _) _ (𝟙 _) c.A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  have hΘ : ∃ t : LB.Gen (Theta c.A L), t.IsGen := CubeAffine.triv_theta_of_isProjBy laws R c.A hA hp L hL
  have s₁ : pull (GrpObj.inv : c.A ⟶ c.A).left (cls L hL) = cls L hL :=
    ((cls_eq_iff hL (pull_isLB hL _)).2 hs).symm
  have e₀ : cls c.P c.isLB = lam (cls L hL) (fst c.A c.A) (snd c.A c.A) :=
    ((cls_eq_iff (LB.isLB_linComb hL _ _) c.isLB).2 hΛ).symm.trans (cls_cube_two hL _ _ (LB.isLB_linComb hL _ _))
  obtain ⟨M, hM, e⟩ := cls_surj (rigCls (cls L hL))
  have e₁ : cls c.P c.isLB = lam (cls M hM) (fst c.A c.A) (snd c.A c.A) := by rw [e, lam_rigCls, e₀]
  have e₂ : pull (GrpObj.inv : c.A ⟶ c.A).left (cls M hM) = cls M hM := by
    rw [e, pull_rigCls, s₁, rigCls]
  have e₃ : cls c.diag hd = 2 • cls M hM := by
    refine (cls_pull c.isLB _ _).trans ?_
    rw [e₀, pull_lam, lift_fst, lift_snd, lam_diag hL hΘ s₁, e]
  have hr : Out.Rigidified c.A M := by
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ((cls_pull hM _ _).trans ?_)
    have e₄ : (η[c.A] : 𝟙_ _ ⟶ c.A) = 1 := by rw [Hom.one_def]; simp
    have := pull_rigCls (cls L hL) η[c.A]
    rw [← e₄, sub_self, ← e] at this
    exact this
  have hsym : Out.Sym c.A M := fun s => ⟨⊤, trivial, by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_
    rw [cls_linComb hM, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_comp, e₂, one_smul, neg_smul, add_neg_cancel]⟩
  have hamp : Out.RelAmple c.A M := by
    have f : IsFinite (𝟙 c.A : c.A ⟶ c.A).left := by rw [Over.id_left]; infer_instance
    refine (relAmple_finite_pow_iso _ c.A c.A (𝟙 _) M 2 two_pos hA hA hM f).2.1.1
      ((relAmple_finite_pow_iso _ c.A c.A (𝟙 _) _ 2 two_pos hA hA hd f).2.2.2 _ (isLB_lbPow hM 2) ?_ ha)
    exact (cls_eq_iff hd (isLB_lbPow hM 2)).1 (e₃.trans (cls_lbPow hM 2 _).symm)
  have hid : IsMonHom (Iso.refl c.A).hom := inferInstanceAs (IsMonHom (𝟙 c.A))
  refine ⟨{ A := c.A, isAb := hA, g := h, smoothDim := hdim, L := M, isLB := hM, rigid := hr, sym := hsym,
            ample := hamp, ktriv := ThetaExtend.kTriv_of_lam hM c.isLB e₁ hk }, 𝟙 _,
    (isGrpPullback_of_iso (Iso.refl c.A)).congr rfl rfl, rfl, 𝟙 _, ⟨by simp, by simp⟩, ?_⟩
  refine (cls_eq_iff (LB.isLB_linComb hM _ _) (pull_isLB c.isLB _)).1 ?_
  exact (cls_cube_two hM _ _ (LB.isLB_linComb hM _ _)).trans (e₁.symm.trans (pull_id _).symm)

end GlobalTheory.SymRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RelAmpleSubring
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.AmpleSubring

theorem relAmple_subring : ∀ (S : Type) [CommRing S] [IsLocalRing S] (R₀ : Subring S) [IsNoetherianRing R₀] (P : Out.PolAV (Sp S)) (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : P.A.left ⟶ A₀.left) (L₀ : LB A₀.left), IsAbelianScheme A₀ → IsProjOver A₀.hom → L₀.IsLB → IsGrpPullback P.A A₀ (spMap R₀.subtype) φ → LBIso P.L (L₀.pull φ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (π : A₁.left ⟶ A₀.left), IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π → Out.RelAmple A₁ (L₀.pull π) := by
  intro S _ _ R₀ _ P A₀ _ φ L₀ hA₀ hproj hL₀ hφ e
  have := hA₀.proper
  have := hA₀.smooth
  let x : R₀ →+* IsLocalRing.ResidueField S := (IsLocalRing.residue S).comp R₀.subtype
  let p : Ideal R₀ := RingHom.ker x
  have : p.IsPrime := RingHom.ker_isPrime x
  let g := algebraMap R₀ p.ResidueField
  let i : p.ResidueField →+* IsLocalRing.ResidueField S :=
    Ideal.ResidueField.lift p x le_rfl fun a ha => IsUnit.mk0 _ ha
  have hi : i.comp g = x := RingHom.ext fun a => Ideal.ResidueField.lift_algebraMap p x le_rfl
    (fun a ha => IsUnit.mk0 _ ha) a
  have hu : spMap (IsLocalRing.residue S) ≫ spMap R₀.subtype = spMap i ≫ spMap g := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi]
  have h₂ := IsPullback.of_hasPullback A₀.hom (spMap i ≫ spMap g)
  obtain ⟨r, hr, hA⟩ := GlobalTheory.T.relAmple_near_fibre_flat_projective R₀ A₀ L₀ inferInstance
    ((ProjSpace.isProjBy_iff_isProjOver _).2 hproj) hL₀ _ g (FibreAmple.residueField_fraction p)
    (FibreAmple.relAmple_of_fieldExtension hL₀ i (IsPullback.of_hasPullback A₀.hom (spMap g)) h₂
      (LB.isLB_pull hL₀ _) (GlobalTheory.lbIso_refl (LB.isLB_pull hL₀ _))
      (FibreAmple.relAmple_of_factor hL₀ hφ.1 h₂ _ hu P.isLB e P.ample))
  have hx : x r ≠ 0 := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
  obtain ⟨v, hv⟩ : IsUnit (r : S) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hx
  refine ⟨{v⁻¹.val}, fun R₁ h hF A₁ _ π hπ => ?_⟩
  have hu₁ : IsUnit (Subring.inclusion h r) :=
    IsUnit.of_mul_eq_one (⟨v⁻¹.val, hF (by simp)⟩ : R₁) (Subtype.ext (by
      change (r : S) * v⁻¹.val = 1
      rw [← hv, Units.mul_inv]))
  let D : (Spec (CommRingCat.of R₀)).Opens := PrimeSpectrum.basicOpen r
  have hrange : Set.range (spMap (Subring.inclusion h)) ⊆ Set.range D.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨_, fun hm => z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu₁)⟩, rfl⟩
  exact FibreAmple.relAmple_of_factor hL₀ (IsPullback.of_hasPullback A₀.hom D.ι) hπ.1
    (IsOpenImmersion.lift D.ι _ hrange) (IsOpenImmersion.lift_fac _ _ _) (LB.isLB_pull hL₀ _)
    (GlobalTheory.lbIso_refl (LB.isLB_pull hL₀ _)) hA

end GlobalTheory.AmpleSubring
end
end

