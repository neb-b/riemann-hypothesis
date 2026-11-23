module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPsiThetaExpansionPsiRelation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.PsiExists

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem cT_zero (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h := DVR.cPoint_add D T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem comp_famφT {T T₀ : Over (Spec (CommRingCat.of R))} (r : T ⟶ T₀ ⊗ D.P.A) (α : D.X) (k : Fin 4) :
    r.left ≫ famφT D T₀ α k = ![(r ≫ snd T₀ D.P.A).left, ((r ≫ snd T₀ D.P.A) * cT D T α).left, (cT D T α).left,
      (1 : T ⟶ D.P.A).left] k := by
  have c : r ≫ cT D _ α = cT D T α := by rw [← Category.assoc, comp_toUnit]
  fin_cases k
  · rfl
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul r (snd T₀ D.P.A) (cT D _ α)).trans (congrArg _ c))
  · exact congrArg (fun q => q.left) c
  · exact congrArg (fun q => q.left) (MonObj.comp_one (M := D.P.A) r)

theorem famφT_eq (T₀ : Over (Spec (CommRingCat.of R))) (α : D.X) :
    famφT D T₀ α = ![(snd T₀ D.P.A).left, (snd T₀ D.P.A * cT D _ α).left, (cT D _ α).left,
      (1 : T₀ ⊗ D.P.A ⟶ D.P.A).left] := rfl

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem exists_pullB {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (f : ∀ α, SecBT D T k α) :
    ∃ s : Raw D F k, PullB D F φ k f s := by
  have H : ∀ α, FormEq (Sum.elim (fun i => (φ ▷ D.P.A).left ≫ famφT D T α i)
      (fun e : PEmpty => (e.elim : (DegPre.BF D F).left ⟶ D.P.A.left))) (Sum.elim (DegPre.famε k) fun e => e.elim)
      (DegPre.famφ D F α) (DegPre.famε k) := by
    intro α U _ h
    have e : (fun i => (φ ▷ D.P.A).left ≫ famφT D T α i) = DegPre.famφ D F α := by
      funext i
      rw [comp_famφT, whiskerRight_snd]; rfl
    rw [e, Fintype.prod_sum_type]
    simp
  choose s hs using fun α => exists_sec D.P.isLB (H α)
    (pullMulSec (f α) (φ ▷ D.P.A).left (LB.oneGen D.P.L) (oneGen_isGen _))
  refine ⟨s, fun α z J hJ => ?_⟩
  refine (hs α _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ _ hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one, Category.id_comp]

theorem isIso_trF (χ : D.X) : IsIso (DegPre.trF D F χ) := by
  have key : ∀ a b : D.X, a + b = 0 → DegPre.trF D F a ≫ DegPre.trF D F b = 𝟙 _ := by
    intro a b hab
    have c : DegPre.trF D F a ≫ cT D _ b = cT D _ b := by rw [← Category.assoc, comp_toUnit]
    have e : DegPre.trF D F a ≫ (snd (TF (R := R) F) D.P.A * cT D _ b) = snd _ _ := by
      rw [MonObj.comp_mul, c, show DegPre.trF D F a ≫ snd _ _ = snd (TF (R := R) F) D.P.A * cT D _ a from lift_snd _ _,
        _root_.mul_assoc]
      have := (DVR.cPoint_add D (DegPre.BF D F) a b).symm
      rw [hab] at this
      rw [show cT D (DegPre.BF D F) a * cT D _ b = 1 from this.trans (cT_zero D _), _root_.mul_one]
    have e' : DegPre.trF D F a ≫ fst _ _ = fst _ _ := lift_fst _ _
    exact (comp_lift _ _ _).trans ((congrArg₂ lift e' e).trans lift_fst_snd)
  exact ⟨DegPre.trF D F (-χ), key _ _ (add_neg_cancel χ), key _ _ (neg_add_cancel χ)⟩

theorem exists_translate (χ : D.X) (s₀ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F 0) (DegPre.famε 1))) :
    ∃ h : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval h r z J = sval s₀ (r ≫ (DegPre.trF D F χ).left) z J *
          (val (D.psi χ) (r ≫ (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) z J *
            val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
              (r ≫ (DegPre.BF D F).hom) z J).val := by
  let κ : DegPre.BF D F ⟶ TK R := Over.homMk ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) F) D.P.A)))
  have H : FormEq (Sum.elim (fun i => (DegPre.trF D F χ).left ≫ DegPre.famφ D F 0 i)
      (Sum.elim (fun _ : PUnit => κ.left ≫ ptK (D.c χ)) (fun _ : PUnit => (DegPre.BF D F).hom ≫ eSec D.P.A)))
      (Sum.elim (DegPre.famε 1) (Sum.elim (fun _ => -1) (fun _ => 1))) (DegPre.famφ D F χ) (DegPre.famε 1) := by
    intro U _ h
    have e₁ : (fun i => (DegPre.trF D F χ).left ≫ DegPre.famφ D F 0 i) =
        ![(snd (TF (R := R) F) D.P.A * cT D _ χ).left, (snd (TF (R := R) F) D.P.A * cT D _ χ).left,
          (1 : DegPre.BF D F ⟶ D.P.A).left, (1 : DegPre.BF D F ⟶ D.P.A).left] := by
      funext i
      refine (comp_famφT D (DegPre.trF D F χ) 0 i).trans ?_
      rw [cT_zero, _root_.mul_one,
        show DegPre.trF D F χ ≫ snd _ _ = snd (TF (R := R) F) D.P.A * cT D _ χ from lift_snd _ _]
    have e₂ : κ.left ≫ ptK (D.c χ) = (cT D (DegPre.BF D F) χ).left :=
      congrArg (fun q => q.left) (show κ ≫ cT D _ χ = cT D _ χ by rw [← Category.assoc, comp_toUnit])
    have e₃ : (DegPre.BF D F).hom ≫ eSec D.P.A = (1 : DegPre.BF D F ⟶ D.P.A).left := rfl
    rw [e₁, e₂, e₃, show DegPre.famφ D F χ = _ from famφT_eq D (TF (R := R) F) χ, Fintype.prod_sum_type,
      Fintype.prod_sum_type]
    simp [Fin.prod_univ_four, DegPre.famε, _root_.mul_assoc]
  obtain ⟨h, hh⟩ := exists_sec D.P.isLB H (pullMulSec s₀ (DegPre.trF D F χ).left
    (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi χ) κ.left)
      (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (DegPre.BF D F).hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) _) (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)))
  refine ⟨h, fun Z r z J hJ => (hh Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ _ _ hJ).trans ?_)⟩
  exact congrArg (fun u : (Z.presheaf.stalk z)ˣ => sval s₀ (r ≫ (DegPre.trF D F χ).left) z J * u.val)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)))

def constVal {F : Type} [Field F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) : F →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)

theorem constVal_eq {F : Type} [Field F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (c : F) :
    constVal p z c = gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) := (gs_eq p z ⊤ trivial _).symm

theorem exists_ratio (h₁ : Laws) (h₂ : Laws2) (χ : D.X)
    (s t : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1))) (hs : ∃ j, s.f j ≠ 0) (ht : ∃ j, t.f j ≠ 0) :
    ∃ a : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval s r z J = constVal (r ≫ (fst (TF (R := R) F) D.P.A).left) z a.val * sval t r z J := by
  obtain ⟨b, hb⟩ := exists_basis_twist_field h₁ h₂ R D F 1 le_rfl χ
  have : Subsingleton (Fin (1 ^ D.P.g)) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  have key : ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1)), (∃ j, s.f j ≠ 0) →
      ∃ c : F, c ≠ 0 ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval s r z J = constVal (r ≫ (fst (TF (R := R) F) D.P.A).left) z c * sval (b i₀) r z J := by
    rintro s ⟨j, hj⟩
    obtain ⟨c, hc, -⟩ := hb s
    have hc' : ∀ j, s.f j = DegPre.constBF D F (c i₀) _ * (b i₀).f j := fun j =>
      (hc j).trans (Fintype.sum_subsingleton _ i₀)
    refine ⟨c i₀, fun h0 => hj ?_, fun Z r z J hJ => ?_⟩
    · rw [hc', h0, DegPre.constBF, map_zero, map_zero, map_zero, zero_mul]
    · rw [constVal_eq]
      exact (congrArg (gs r z _) (hc' _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·)
        ((gs_res r z le_top (hJ.mem _ r) _).trans (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _)) rfl))
  obtain ⟨c, hc0, hc⟩ := key s hs
  obtain ⟨d, hd0, hd⟩ := key t ht
  refine ⟨Units.mk0 (c / d) (div_ne_zero hc0 hd0), fun Z r z J hJ => ?_⟩
  rw [hc Z r z J hJ, hd Z r z J hJ, ← _root_.mul_assoc, ← map_mul, Units.val_mk0, div_mul_cancel₀ c hd0]

theorem exists_psi_of_section (h₁ : Laws) (h₂ : Laws2) (i : (TK R).left ⟶ Spec (CommRingCat.of F))
    (hi : i ≫ jFK (R := R) F = 𝟙 _) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (hf : ∀ α, ∃ j, (f α).f j ≠ 0) :
    ∃ ψ : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1)),
      (∀ χ, (ψ χ).IsGen) ∧ ∀ (χ : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ 𝟙_ _) (κ : T ⟶ TK R)
        (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval (f χ) (lift ρ y).left z J =
          (val (ψ χ) κ.left z J * rigV D z J).val * sval (f 0) (lift ρ (y * cT D T χ)).left z J := by
  obtain ⟨s, hs⟩ := exists_pullB D F (toUnit _) 1 f
  have hs0 := fun α => (pullB_ne_zero_iff R D F 1 f s hs α).2 (hf α)
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  choose h hh using fun χ => exists_translate D F χ (s 0)
  have hh0 : ∀ χ, ∃ j, (h χ).f j ≠ 0 := fun χ => by
    obtain ⟨J, hJ⟩ := exists_good_pt (Z := (DegPre.BF D F).left) D.P.isLB (genericPoint _)
    have := isIso_trF D F χ
    have : IsIso (DegPre.trF D F χ).left := inferInstanceAs (IsIso ((Over.forget _).map (DegPre.trF D F χ)))
    rw [exists_ne_zero_iff_sval_ne_zero _ hJ, hh χ _ _ _ J hJ, Category.id_comp]
    exact mul_ne_zero (sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s 0) (hs0 0) _ _ _ J hJ) (Units.ne_zero _)
  choose a ha using fun χ => exists_ratio D F h₁ h₂ χ (s χ) (h χ) (hs0 χ) (hh0 χ)
  let u : D.X → Γ((TK R).left, ⊤)ˣ := fun χ => Units.map (i.app ⊤).hom.toMonoidHom (unitOn (a χ))
  refine ⟨fun χ => GlobalTheory.UU.scaleGen (u χ) (D.psi χ), fun χ => GlobalTheory.UU.scaleGen_isGen _ (D.psi_gen χ), ?_⟩
  intro χ T ρ κ y z J hJ
  have hκ : (κ.left ≫ i) ≫ jFK (R := R) F = κ.left := by rw [Category.assoc, hi, Category.comp_id]
  let κ' : T ⟶ TF (R := R) F := Over.homMk (κ.left ≫ i)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hκ).trans (Over.w κ)))
  have hρ : κ' ≫ toUnit _ = ρ := toUnit_unique _ _
  have v₁ := pullB_values R D _ _ _ 1 f s hs χ T κ' y z J hJ
  have v₂ := pullB_values R D _ _ _ 1 f s hs 0 T κ' (y * cT D T χ) z J hJ
  rw [hρ] at v₁ v₂
  have a₁ : (lift κ' y).left ≫ (fst (TF (R := R) F) D.P.A).left = κ.left ≫ i :=
    congrArg (fun q => q.left) (lift_fst κ' y)
  have a₂ : (lift κ' y).left ≫ (DegPre.trF D F χ).left = (lift κ' (y * cT D T χ)).left := by
    refine congrArg (fun q => q.left) (?_ : lift κ' y ≫ DegPre.trF D F χ = _)
    refine (comp_lift _ _ _).trans (congrArg₂ lift (lift_fst _ _) ?_)
    refine (MonObj.comp_mul (lift κ' y) (snd _ D.P.A) (cT D _ χ)).trans ?_
    rw [lift_snd, ← Category.assoc, comp_toUnit]
  have a₃ : (lift κ' y).left ≫ (DegPre.BF D F).hom = T.hom := Over.w _
  have a₄ : (lift κ' y).left ≫ (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F = κ.left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jFK (R := R) F) a₁).trans hκ)
  have w₁ := ha χ _ (lift κ' y).left z J hJ
  have w₂ := hh χ _ (lift κ' y).left z J hJ
  rw [a₂, a₃, a₄] at w₂
  rw [a₁] at w₁
  have w₃ := GlobalTheory.UU.val_scaleGen (u χ) (D.psi χ) κ.left hJ
  have w₄ : (gm κ.left z ⊤ (u χ)).val = constVal (κ.left ≫ i) z (a χ).val :=
    (gs_unit κ.left z ⊤ trivial _).symm.trans ((gs_pull κ.left i z ⊤ trivial _).trans (constVal_eq _ _ _).symm)
  have alg : ∀ (A : Type) [CommRing A] (x₁ x₂ s₁ s₂ t c : A) (p q u v : Aˣ), s₁ = x₁ → s₂ = x₂ → s₁ = c * t →
      t = s₂ * (p * q).val → v = u * p → u.val = c → x₁ = (v * q).val * x₂ := by
    intro A _ x₁ x₂ s₁ s₂ t c p q u v e₁ e₂ e₃ e₄ e₅ e₆
    rw [← e₁, ← e₂, e₃, e₄, e₅, ← e₆]
    simp only [Units.val_mul]
    ring
  exact alg _ _ _ _ _ _ _ _ _ _ _ v₁ v₂ w₁ w₂ w₃ w₄

end GlobalTheory.PsiExists

namespace GlobalTheory

theorem exists_psi_psiRel : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), (∀ α, ∃ j, (f α).f j ≠ 0) → ∃ ψ h, PsiRel (setPsi D ψ h) (𝟙_ _) f := by
  intro h₁ h₂ R _ _ D f hf
  obtain ⟨ψ, h, H⟩ := PsiExists.exists_psi_of_section D (FractionRing R) h₁ h₂ (𝟙 _)
    ((Category.id_comp _).trans (Spec.map_id _)) f hf
  exact ⟨ψ, h, H⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.NormTheta

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem rigT_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigT A L ρ T k).IsGen := by
  intro i j
  refine unit_ext fun y hy => ?_
  have v : ∀ i : Fin 1 → L.ι, y ∈ LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i →
      gm (𝟙 T.left) y (LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i) ((rigT A L ρ T k).s i) =
        gm T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => i 0)) (ρ.s fun _ => i 0) ^ k := fun i hi =>
    (map_zpow _ _ _).trans (congrArg (· ^ k) (gm_rp₁ T.hom y _ _ (rigT_le A L i) hi _))
  have e := gen_trans (L := L) (φ := fun _ : PUnit.{1} => eSec A) (ε := fun _ => 1) hρ T.hom y
    (j := fun _ => i 0) (j' := fun _ => j 0) (rigT_le A L (T := T) i hy.1) (rigT_le A L (T := T) j hy.2)
  rw [trF, Fintype.prod_unique, zpow_one] at e
  refine ((gm_res (𝟙 _) y _ hy _).trans (v i hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L (fun _ : Fin 1 => T.hom ≫ eSec A) (fun _ => k) (𝟙 _) y i j hy.1 hy.2)
    ((gm_res (𝟙 _) y _ hy _).trans (v j hy.2)))).symm)
  rw [Fin.prod_univ_one, Category.id_comp, ← mul_zpow]
  exact congrArg (· ^ k) e

theorem ptSec_fst : (ptSecT A (1 : T ⟶ A)).left ≫ (fst T A).left = 𝟙 T.left := by
  rw [← Over.comp_left, ptSecT, lift_fst]; rfl

theorem one_left : (1 : T ⟶ A).left = T.hom ≫ eSec A := rfl

theorem ptSec_snd : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, ptSecT, lift_snd, one_left]

theorem ptSec_snd_pow (m : ℕ) : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A ^ m).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, MonObj.comp_pow, ptSecT, lift_snd, one_pow, one_left]

theorem exists_normalised (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a b c : ℤ)
    (hc : c = a - b)
    (α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])) (h₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b]), α.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left) (rigT A L ρ T c) := by
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ m).left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ptSec_snd, ptSec_snd_pow, hc]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (ptSecT A 1).left)) (rigT A L ρ T c)) (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ _)) (rigT_isGen hρ c)) _))
  refine ⟨α, hα, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, ptSec_fst, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

theorem exists_value (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ)
    (t : LB.Sec (LPow A L k T)) : ∃ c : Γ(T.left, ⊤), ∀ z J, Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) t (ptSecT A 1).left z J =
        gs (𝟙 _) z ⊤ c * (val (rigT A L ρ T k) (𝟙 _) z J).val := by
  obtain ⟨s, hs⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ f => by
      refine Eq.trans ?_ (Fintype.prod_empty _).symm
      simp only [Fintype.prod_sum_type, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr, ptSec_snd, zpow_neg,
        mul_inv_cancel])
    (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) t (ptSecT A 1).left
      (LB.invGen L _ _ (rigT A L ρ T k)) (DVR.invGen_isGen _ _ _ _ (rigT_isGen hρ k)))
  have le : (⊤ : T.left.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (T.left ⟶ A.left)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(T.left.presheaf.map (homOfLE le).op).hom (s.f PEmpty.elim), fun z J hJ => ?_⟩
  have e := (hs _ (𝟙 _) z J hJ).trans (sval_pullMulSec _ _ _ _ _ z hJ)
  rw [val_inv, Category.id_comp,
    sval_of s (𝟙 _) z J PEmpty.elim (fun k => k.elim)] at e
  exact (Units.inv_mul_cancel_right _ _).symm.trans
    (congrArg (· * _) ((gs_res (𝟙 _) z le trivial _).trans e).symm)

theorem sec_ext {Y : Scheme.{0}} {M : LB Y} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  congr
  exact funext h

end General

end GlobalTheory.NormTheta

namespace GlobalTheory


open NormTheta in
theorem existsUnique_thetaConst : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m : ℕ), Odd m → ∀ (th : SecA A F 1) (x : TFK (R := R) F ⟶ A.A), x ^ (m ^ 2) = 1 → (∃! q : SecA A F (m ^ 2) × F, ThC A ρ m th x q.1 q.2) := by
  intro hLL R _ _ _ A F _ _ ρ hρ m hm th x hx
  have hLaw : Laws := hLL.1
  have hL := A.isLB
  let T := TFK (R := R) F
  have : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hm.pos.ne'))
  obtain ⟨hex, huniq⟩ := hLaw.symLift _ A (m ^ 2) hm.pow hu T x hx
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ A m
    have e₁ : (snd T A.A).left ≫ (mulA A.A m).left = (snd T A.A ^ m).left := by
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
    obtain ⟨α₁, hα₁, -⟩ := exists_gen hL (φ' := ![(snd T A.A).left, (snd T A.A ^ m).left])
      (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
      (fun U _ f => by
        refine Finset.prod_congr rfl fun i _ => ?_
        fin_cases i
        · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow m 2).symm
        · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
      (LB.pullGen A.L ![𝟙 A.A.left, (mulA A.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd T A.A).left)
      (DVR.pullGen_isGen _ _ _ _ hα₀ _)
    obtain ⟨α, hα, hn⟩ := exists_normalised hL hρ m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) rfl α₁ hα₁
    obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT A.A T m) (snd T A.A ^ m) (lift_snd _ _)
      ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
    obtain ⟨V, hV, θ₀, hθ₀⟩ := hex p
    obtain ⟨h, hh⟩ := GlobalLift.exists_section (T := T) hV
    obtain ⟨θ, hθ⟩ := GlobalLift.exists_symLift_pull hL h hθ₀
    rw [← Category.assoc, hh, Category.id_comp] at hθ
    obtain ⟨t, ht⟩ := ThetaPtExist.exists_isTwistPull hL (translT A.A θ.pt) (translPt A.A θ.pt) (lift_snd _ _)
      ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) θ.φ θ.isGen s₁
    obtain ⟨c₀, hc₀⟩ := exists_value hL hρ _ t
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 c₀
    exact ⟨(t, c), α, s₁, θ, hα, hn, hs₁, hθ, ht, hc₀⟩
  · rintro ⟨t, c⟩ ⟨t', c'⟩ ⟨α, s₁, θ, hα, hn, hs₁, hθ, ht, hc⟩ ⟨α', s₁', θ', hα', hn', hs₁', hθ', ht', hc'⟩
    have ea := gen_unique hL (fst T A.A).left (ptSecT A.A 1).left ptSec_fst
      (CommPairing.surj_fst hLaw.globalFns A.isAb T) hα hα' (fun y J hJ => by
        have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
        rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
    obtain rfl : s₁ = s₁' := sec_ext (sec_ext_val hL fun y J hJ =>
      (ThetaLin.sval_of_isTwistPull A.A hs₁ _ y hJ).trans
        (Eq.trans (by rw [ea _ _ y J hJ]) (ThetaLin.sval_of_isTwistPull A.A hs₁' _ y hJ).symm))
    have eθ := huniq θ θ' hθ hθ'
    have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
    obtain rfl : t = t' := sec_ext (sec_ext_val hL fun y J hJ =>
      (ThetaLin.sval_of_isTwistPull A.A ht _ y hJ).trans
        (Eq.trans (by rw [val_corr hJ eθ, ept]) (ThetaLin.sval_of_isTwistPull A.A ht' _ y hJ).symm))
    refine Prod.ext rfl ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).1
      (fn_ext (V := ⊤) fun y _ => ?_))
    choose J hJ using fun χ : T.left ⟶ A.A.left => exists_chart hL (χ y)
    exact (Units.mul_left_inj _).1 ((hc y J hJ).symm.trans (hc' y J hJ))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionTranslateTorus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ShiftExp

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl)

theorem gs_scal {Y Z : Scheme.{0}} {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem shift (hG : GlobalFnsSt) (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W]
    (a : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G) (hx : U.TorPt a x) (e : ℕ) (Z : Scheme.{0})
    (y y' : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (TA R W ⊗ G).left)
    (h₁ : rG ≫ (snd _ G).left = y ≫ (fstG I e G).left)
    (h₂ : y' ≫ (fstG I e G).left = rG ≫ (translPt G x).left) :
    y' ≫ (U.gt e).pG.left = y ≫ (U.gt e).pG.left ∧ ∀ (χ : D.X) (z : Z) (J), Good D.P.L z J →
      (val ((U.gt e).t χ) y' z J).val =
        gs (𝟙 Z) z ⊤ (scal (R := W) (rG ≫ (fst (TA R W) G).left) (a (Multiplicative.ofAdd χ)).val) *
          (val ((U.gt e).t χ) y z J).val := by
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y ≫ (thickObj R I e G).hom)
  let yo : T ⟶ thickObj R I e G := Over.homMk y rfl
  have hb : rG ≫ (TA R W ⊗ G).hom = T.hom ≫ thick R I e := by
    rw [← Over.w (snd (TA R W) G), ← Category.assoc, h₁, Category.assoc, Over.w (fstG I e G)]
    exact (Category.assoc _ _ _).symm
  let ro : Over.mk (T.hom ≫ thick R I e) ⟶ TA R W ⊗ G := Over.homMk rG hb
  let x₀ : Over.mk (T.hom ≫ thick R I e) ⟶ G := ro ≫ fst _ _ ≫ x
  let xe : T ⟶ thickObj R I e G :=
    Over.homMk (pullback.lift x₀.left T.hom (Over.w x₀)) (pullback.lift_snd _ _ _)
  have hxe : xe.left ≫ pullback.fst G.hom (thick R I e) = x₀.left := pullback.lift_fst _ _ _
  have hm := (isGrpPullback_pullback G (thick R I e)).2 T xe yo x₀ (ro ≫ snd _ _) hxe.symm h₁
  have ht : ro ≫ translPt G x = x₀ * (ro ≫ snd _ _) := MonObj.comp_mul ro (fst _ _ ≫ x) (snd _ _)
  have hf : y' ≫ pullback.fst G.hom (thick R I e) = (xe * yo).left ≫ pullback.fst G.hom (thick R I e) :=
    h₂.trans ((congrArg (fun q => q.left) ht).trans hm)
  haveI : Mono (thick R I e) := by
    haveI : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hy : y' = (xe * yo).left := (cancel_mono (pullback.fst G.hom (thick R I e))).1 hf
  obtain ⟨p₁, p₂⟩ := hx e Z (rG ≫ (fst (TA R W) G).left) xe.left (hxe.trans (Category.assoc _ _ _).symm)
  have hone : GlobalTheory.TorusCoord.im (U.gt e) xe = 1 := by
    have : (ro ≫ fst _ _) ≫ (1 : TA R W ⟶ D.P.A) = 1 := MonObj.comp_one _
    exact (Over.OverMorphism.ext p₁).trans this
  subst hy
  refine ⟨?_, fun χ z J hJ => ?_⟩
  · have := GlobalTheory.TorusCoord.im_mul (U.gt e) xe yo
    rw [hone, _root_.one_mul] at this
    exact congrArg (fun q => q.left) this
  · have k := GlobalTheory.TorusCoord.val_t_mul_points (U.gt e) hG χ xe yo z J hJ
    have c : GlobalTheory.TorusCoord.cubeVal (U.gt e) χ z J xe yo = 1 := by
      unfold GlobalTheory.TorusCoord.cubeVal
      rw [hone]
      exact (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ).face₂ _ _
    rw [c, _root_.mul_one] at k
    exact (congrArg Units.val k).trans ((Units.val_mul _ _).trans (congrArg (· * _) (p₂ χ z J hJ)))

end GlobalTheory.UU.ShiftExp

theorem GlobalTheory.UU.expansion_translate_torus : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (W : Type) [CommRing W] [Algebra R W] (a : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G), U.TorPt a x → ∀ (k : ℕ) (σ : U.SecGT (TA R W) k) (f : ∀ α, SecBT D (TA R W) k α), U.ExpT (TA R W) k σ f → ∀ e : ℕ, ∃ s : Finset D.X, ∀ (Z : Scheme.{0}) (y y' : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (TA R W ⊗ G).left) (rB : Z ⟶ (TA R W ⊗ D.P.A).left), rG ≫ (snd _ G).left = y ≫ (fstG I e G).left → rB ≫ (snd _ D.P.A).left = y ≫ (U.gt e).pG.left → rB ≫ (fst _ D.P.A).left = rG ≫ (fst _ G).left → y' ≫ (fstG I e G).left = rG ≫ (translPt G x).left → ∀ (z : Z) (JG) (J), Good U.P.L.L z JG → Good D.P.L z J → (∀ α ∉ s, sval (twist a f α) rB z J = 0) ∧ (U.wv e y' z JG J).val ^ k * sval σ (rG ≫ (translT G x).left) z JG = ∑ α ∈ s, sval (twist a f α) rB z J * (val ((U.gt e).t α) y z J).val := by
  intro hG R _ _ I D A G _ _ U W _ _ a x hx k σ f hf e
  obtain ⟨s, hs⟩ := hf e
  refine ⟨s, fun Z y y' rG rB h₁ h₂ h₃ h₄ z JG J hJG hJ => ?_⟩
  obtain ⟨p₁, p₂⟩ := ShiftExp.shift hG U a x hx e Z y y' rG h₁ h₄
  have e₁ : (translT G x).left ≫ (snd (TA R W) G).left = (translPt G x).left :=
    congrArg (fun q => q.left) (lift_snd (fst (TA R W) G) (translPt G x))
  have e₂ : (translT G x).left ≫ (fst (TA R W) G).left = (fst (TA R W) G).left :=
    congrArg (fun q => q.left) (lift_fst (fst (TA R W) G) (translPt G x))
  obtain ⟨q₁, q₂⟩ := hs Z y' (rG ≫ (translT G x).left) rB (by rw [Category.assoc, e₁, h₄]) (h₂.trans p₁.symm)
    (by rw [Category.assoc, e₂, h₃]) z JG J hJG hJ
  have tw : ∀ α, sval (twist a f α) rB z J =
      gs (𝟙 Z) z ⊤ (scal (R := W) (rG ≫ (fst (TA R W) G).left) (a (Multiplicative.ofAdd α)).val) *
        sval (f α) rB z J := fun α => by
    rw [← h₃]
    exact (ShiftExp.sval_secScale _ _ rB z hJ).trans (congrArg (· * _) (ShiftExp.gs_scal _ rB z _))
  refine ⟨fun α hα => by rw [tw, q₁ α hα, mul_zero], q₂.trans (Finset.sum_congr rfl fun α _ => ?_)⟩
  rw [tw, p₂ α z J hJ]
  ring
end

