module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0084
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0085
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearFourierJacobiExpansionFamilyStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_fourierJacobi_expansion_family : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∃ ex : ∀ α : D.X, EA A (jFK (R := V) F) k →ₗ[F] WB D F k α, (∀ t, U.ExpF F k t.sec (fun α => (ex α t).sec)) ∧ (∀ t s, U.ExpF F k t s → ∀ α, s α = (ex α (SecMod.mk _ t)).sec) ∧ (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, (U.Supp F k α ↔ ex α ≠ 0)) := by
  first | exact @GlobalTheory.UU.ExpLinMap.exists_expansion_linear | exact GlobalTheory.UU.ExpLinMap.exists_expansion_linear | (intros; apply GlobalTheory.UU.ExpLinMap.exists_expansion_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDimStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expF_of_theta_degree_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → (∃ j, th.f j ≠ 0) ∧ U.ExpF (Kbar V) 1 th s₀ ∧ ∀ t s, U.ExpF (Kbar V) 1 t s → ∃ c : (Kbar V), ∀ α j, (s α).f j = DegPre.constBF D (Kbar V) c _ * (s₀ α).f j) := by
  first | exact @GlobalTheory.UU.OneDim.expF_one_dim | exact GlobalTheory.UU.OneDim.expF_one_dim | (intros; apply GlobalTheory.UU.OneDim.expF_one_dim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtCancelNonzeroScalar
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem expandsAt_cancel_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) [QuasiCompact G.hom] (r : R), r ≠ 0 → ∀ (σ₀ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ f : ∀ α, D.toPre.SecB k α), (∀ α, (∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j)) → (∀ j, (σ₀).f j = resTop _ (scal G.hom r) * (σ).f j) → (∀ e, U.ExpandsAt e k σ₀ f₀) → ∀ e, U.ExpandsAt e k σ f := by
  intro R _ _ I hR D A G _ _ _ U k _ r hr σ₀ σ f₀ f hf hσ hE
  have := hR.1
  exact expandsAt_cancel_of_ne_zero R I D A G U k r hr σ σ₀ f f₀ hσ hf hE

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteExponentBaseChangeField
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.FEDesc

theorem spec_appTop_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (Spec.map (CommRingCat.ofHom f)).appTop.hom := by
  have e : (Spec.map (CommRingCat.ofHom f)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1.comp hf).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1

theorem toUnit_injective (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Function.Injective (toUnit (TF (R := R) F)).left.appTop.hom := by
  have e₂ : (toUnit (TF (R := R) F)).left = jFK (R := R) F ≫ jK R := by
    have a := Over.w (toUnit (TF (R := R) F))
    exact (Category.comp_id _).symm.trans a
  rw [e₂]
  exact (spec_appTop_injective _ (algebraMap (FractionRing R) F).injective).comp
    (spec_appTop_injective _ (IsFractionRing.injective R (FractionRing R)))

theorem famFE_of_sum {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k n : ℕ) (c : Fin n → F) (s : Raw D F k) (t : Fin n → Raw D F k)
    (h : ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = ∑ i, gs r z ⊤ (scal (fst (TF (R := R) F) D.P.A).left (c i)) * sval (t i α) r z J)
    (ht : ∀ i, DegPre.FamFE D F k (t i)) : DegPre.FamFE D F k s := by
  intro mu α u hu hc
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  rw [h _ _ _ y J hJ, h _ _ _ y J hJ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (ht i mu α u hu hc) _ (𝟙 _) y J hJ, _root_.mul_assoc]
  congr 1
  have e : (DegPre.trF D F mu).left ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D.P.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D F mu ≫ fst (TF (R := R) F) D.P.A = _)
  have key : ∀ {Y : Scheme.{0}} (y : Y) (a : Y ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of F)) (x : F), a ≫ p = p →
      gs (𝟙 Y) y ⊤ (scal p x) = gs (𝟙 Y ≫ a) y ⊤ (scal p x) := by
    intro Y y a p x hap
    rw [← gs_pull (𝟙 Y) a y ⊤ trivial]
    conv_lhs => rw [← hap]
    rfl
  exact key y _ _ _ e

theorem fe_of_fe_kbar : GlobalFnsSt → AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ k : ℕ, U.FE (Kbar V) k → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F], U.FE F k := by
  intro hG V _ _ _ hV D A G _ _ U k hK F _ _ t s hE
  obtain ⟨n, c, σ, f, hT, -, hs⟩ := hE
  have P := PullSec.pullEx V hV D A G U
  choose tK htK using fun i => ((P (Kbar V) (𝟙_ _) (toUnit _) k).1 (σ i)).exists
  choose sK hsK using fun i => ((P (Kbar V) (𝟙_ _) (toUnit _) k).2 (f i)).exists
  choose sF hsF using fun i => ((P F (𝟙_ _) (toUnit _) k).2 (f i)).exists
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of V)))
  refine famFE_of_sum D F k n c s sF (fun α Z r z J hJ => ?_) fun i =>
    GlobalTheory.T.familyFunctionalEquation_field_change hG V D (𝟙_ _) k (f i) (Kbar V) F (toUnit _) (toUnit _) (sK i) (sF i) (toUnit_injective V _)
      (hsK i) (hsF i) (hK (tK i) (sK i)
        (IntExp.expF_of_expT V _ D A G U (Kbar V) k (σ i) (f i) (tK i) (sK i) (hT i) (htK i) (hsK i)))
  have w : (toUnit (TF (R := V) F) ▷ D.P.A).left ≫ (snd (𝟙_ _) D.P.A).left = (snd _ D.P.A).left :=
    congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := V) F)) D.P.A)
  rw [hs α Z r (r ≫ (toUnit (TF (R := V) F) ▷ D.P.A).left) (by rw [Category.assoc, w]) z J hJ]
  refine Finset.sum_congr rfl fun i _ => congrArg (_ * ·) ?_
  rw [IntExp.sval_comp (f i α) _ r z J hJ, ← hsF i α (r z) _ (fun ψ => hJ (r ≫ ψ)),
    ← IntExp.sval_comp (sF i α) _ r z J hJ, Category.comp_id]

end GlobalTheory.UU.FEDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericSectionBasis

section Calc

variable {F : Type} [CommRing F] {X Y Y' Z : Scheme.{0}} {n : ℕ}

def IsComb {M : LB Y} (p : Y ⟶ Sp F) (b : Fin n → LB.Sec M) (c : Fin n → F) (s : LB.Sec M) : Prop :=
  ∀ j, s.f j = ∑ i, resTop _ (scal p (c i)) * (b i).f j

def HasBasis (M : LB Y) (p : Y ⟶ Sp F) (n : ℕ) : Prop :=
  ∃ b : Fin n → LB.Sec M, ∀ s : LB.Sec M, ∃! c : Fin n → F, IsComb p b c s

theorem exists_comb {M : LB Y} (p : Y ⟶ Sp F) (b : Fin n → LB.Sec M) (c : Fin n → F) :
    ∃ s : LB.Sec M, IsComb p b c s :=
  ⟨⟨fun j => ∑ i, resTop _ (scal p (c i)) * (b i).f j, fun j j' => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (scal p (c i)) (b i)).compat j j'⟩, fun _ => rfl⟩

theorem gs_comb {M : LB Y} (p : Y ⟶ Sp F) (b : Fin n → LB.Sec M) (c : Fin n → F) (r : Z ⟶ Y) (z : Z) (j : M.ι)
    (hz : r z ∈ M.U j) :
    gs r z (M.U j) (∑ i, resTop _ (scal p (c i)) * (b i).f j) =
      ∑ i, cst (r ≫ p) z (c i) * gs r z (M.U j) ((b i).f j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [gs_eq r z _ hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← gs_eq r z _ hz, gs_mul r z _ hz, GlobalTheory.IndivisibleSection.gs_scal p r z _ hz]

theorem HasBasis.transfer {A : LB Y'} {B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (σ : Y' ⟶ Y) (τ : Y ⟶ Y')
    (h₁ : τ ≫ σ = 𝟙 Y) (p : Y ⟶ Sp F) (p' : Y' ⟶ Sp F) (hp : σ ≫ p = p')
    (u : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y') (z : Z), A.ι → B.ι → (Z.presheaf.stalk z)ˣ)
    (Rel : LB.Sec A → LB.Sec B → Prop)
    (hRel : ∀ s t, Rel s t → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (a : A.ι) (b : B.ι), r z ∈ A.U a →
      (r ≫ σ) z ∈ B.U b → gs r z (A.U a) (s.f a) = (u Z r z a b).val * gs (r ≫ σ) z (B.U b) (t.f b))
    (hl : ∀ t, ∃ s, Rel s t) (hr : ∀ s, ∃ t, Rel s t) (H : HasBasis B p n) : HasBasis A p' n := by
  obtain ⟨β, hβ⟩ := H
  choose β' hβ' using fun i => hl (β i)
  refine ⟨β', fun s => ?_⟩
  obtain ⟨t, ht⟩ := hr s
  have key : ∀ c, IsComb p' β' c s ↔ IsComb p β c t := fun c => by
    constructor
    · intro h j
      refine fn_ext fun y hy => ?_
      obtain ⟨a, ha⟩ := exists_chart hA (τ y)
      have hy' : (τ ≫ σ) y ∈ B.U j := by rw [h₁]; exact hy
      have e := hRel s t ht Y τ y a j ha hy'
      rw [h a, gs_comb p' β' c τ y a ha] at e
      simp only [fun i => hRel _ _ (hβ' i) Y τ y a j ha hy', h₁] at e
      rw [gs_comb p β c (𝟙 Y) y j hy, ← (u Y τ y a j).mul_right_inj, ← e, Finset.mul_sum, ← hp,
        ← Category.assoc, h₁]
      exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
    · intro h a
      refine fn_ext fun y hy => ?_
      obtain ⟨j, hj⟩ := exists_chart hB (σ y)
      have hy' : (𝟙 Y' ≫ σ) y ∈ B.U j := hj
      rw [hRel s t ht Y' (𝟙 Y') y a j hy hy', h j, gs_comb p β c _ y j hy', gs_comb p' β' c (𝟙 Y') y a hy,
        Finset.mul_sum, ← hp, Category.assoc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hRel _ _ (hβ' i) Y' (𝟙 Y') y a j hy hy']
      exact mul_left_comm _ _ _
  simp only [key]
  exact hβ t

theorem exists_inv_iso {A B : LB X} (w : LB.Iso A B) (hw : w.IsGen) : ∃ w' : LB.Iso B A, w'.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (a : A.ι) (b : B.ι), r z ∈ A.U a ⊓ B.U b →
      gm r z ((LB.div A B).U (a, b)) (w'.s (a, b)) = (gm r z ((LB.div B A).U (b, a)) (w.s (b, a)))⁻¹ := by
  have le : ∀ p : A.ι × B.ι, A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1 := fun p y hy => ⟨hy.2, hy.1⟩
  refine ⟨⟨fun p => (res (le p) (w.s (p.2, p.1)))⁻¹⟩, fun p q => unit_ext fun y hy => ?_,
    fun Z r z a b hz => (map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z (le (a, b)) hz _))⟩
  have hm : (𝟙 X : X ⟶ X) y ∈ B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1))) (hw (p.2, p.1) (q.2, q.1))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) y (p.2, p.1) (q.2, q.1) hm) (gm_res _ y _ hm _))))
  have v : ∀ p : A.ι × B.ι, y ∈ A.U p.1 ⊓ B.U p.2 → gm (𝟙 X) y (A.U p.1 ⊓ B.U p.2) (res (le p) (w.s (p.2, p.1)))⁻¹ =
      (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹ := fun p hp =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))
  refine ((gm_res _ y _ hy _).trans ((v p hy.1).trans (congrArg (·⁻¹) e'))).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div B A (𝟙 X) y p q hy)
    ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
  rw [mul_inv, mul_inv, inv_inv, mul_comm (gm (𝟙 X) y _ (A.g p.1 q.1))]
  rfl

theorem HasBasis.of_iso {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) {p : Y ⟶ Sp F}
    (H : HasBasis B p n) : HasBasis A p n := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw', e⟩ := exists_inv_iso w hw
  refine H.transfer hA hB (𝟙 Y) (𝟙 Y) (Category.id_comp _) p p (Category.id_comp _)
    (fun Z r z a b => (gm r z ((LB.div B A).U (b, a)) (w.s (b, a)))⁻¹) _ (fun _ _ h => h)
    (fun t => ⟨secOfIso t hw hA hB, fun Z r z a b ha hb => ?_⟩)
    (fun s => ⟨secOfIso s hw' hB hA, fun Z r z a b ha hb => ?_⟩)
  · rw [Category.comp_id] at hb ⊢
    exact GlobalTheory.GenericGenerated.gs_secOfIso w t hw hA hB a b r z ⟨ha, hb⟩
  · rw [Category.comp_id] at hb ⊢
    rw [GlobalTheory.GenericGenerated.gs_secOfIso w' s hw' hB hA b a r z ⟨hb, ha⟩, e Z r z a b ⟨ha, hb⟩, inv_inv,
      Units.inv_mul_cancel_left]

theorem exists_pull_gs {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = φ' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L φ' j →
      gs r z (LB.wchart L φ' j) (s'.f j) = gs (r ≫ h) z (LB.wchart L φ j) (s.f j) := by
  obtain ⟨s', hs'⟩ := GlobalTheory.IndivisibleSection.exists_pull_chart s h φ' e
  refine ⟨s', fun Z r z j hz => ?_⟩
  have le : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j := fun y hy => Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy k
    rw [← e] at this
    exact this
  rw [hs' j le]
  exact (gs_res r z le hz _).trans (gs_pull r h z _ (le hz) _)

theorem HasBasis.pull {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)}
    {ε : K → ℤ} (σ : Y' ⟶ Y) (τ : Y ⟶ Y') (h₁ : τ ≫ σ = 𝟙 Y) (h₂ : σ ≫ τ = 𝟙 Y') (e : ∀ k, σ ≫ φ k = φ' k)
    (p : Y ⟶ Sp F) (p' : Y' ⟶ Sp F) (hp : σ ≫ p = p') (H : HasBasis (LB.LinComb L φ ε) p n) :
    HasBasis (LB.LinComb L φ' ε) p' n := by
  have e' : ∀ k, τ ≫ φ' k = φ k := fun k => by rw [← e, ← Category.assoc, h₁, Category.id_comp]
  have mem : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (b : K → L.ι), (r ≫ σ) z ∈ LB.wchart L φ b →
      r z ∈ LB.wchart L φ' b := fun Z r z b hb => Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hb k
    rw [← e]
    exact this
  refine H.transfer (linComb_isLB L hL _ _) (linComb_isLB L hL _ _) σ τ h₁ p p' hp
    (fun Z r z a b => trF φ' ε r z a b) _ (fun _ _ h => h) (fun t => ?_) (fun s => ?_)
  · obtain ⟨s, hs⟩ := exists_pull_gs t σ φ' e
    exact ⟨s, fun Z r z a b ha hb => (sec_trans s r z ha (mem Z r z b hb)).trans
      (congrArg _ (hs Z r z b (mem Z r z b hb)))⟩
  · obtain ⟨t, ht⟩ := exists_pull_gs s τ φ e'
    refine ⟨t, fun Z r z a b ha hb => (sec_trans s r z ha (mem Z r z b hb)).trans (congrArg _ ?_)⟩
    refine Eq.trans ?_ (ht Z (r ≫ σ) z b hb).symm
    rw [Category.assoc, h₂, Category.comp_id]

end Calc

section Field

variable {F : Type} [Field F] (P : PolAV (Spec (CommRingCat.of F))) (k : ℕ)

theorem hasBasis_of_basis (q : Sp F ⟶ Sp F) (hq : q = 𝟙 _) {n : ℕ}
    (β : Fin n → LB.Sec (LPow P.A P.L k (Over.mk q)))
    (hli : LinearIndependent Γ((Over.mk q).left, ⊤) (fun i => (SecM.ofSec P.A (β i) : SecM P.A P.L k (Over.mk q))))
    (hsp : Submodule.span Γ((Over.mk q).left, ⊤)
      (Set.range fun i => (SecM.ofSec P.A (β i) : SecM P.A P.L k (Over.mk q))) = ⊤) :
    HasBasis (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => (k : ℤ))) P.A.hom n := by
  subst hq
  let u : P.A ⟶ Over.mk (𝟙 (Sp F)) := Over.homMk P.A.hom (Category.comp_id _)
  have hw : (snd (Over.mk (𝟙 (Sp F))) P.A).left ≫ P.A.hom = (fst (Over.mk (𝟙 (Sp F))) P.A).left :=
    (Over.w (snd (Over.mk (𝟙 (Sp F))) P.A)).trans
      ((Over.w (fst (Over.mk (𝟙 (Sp F))) P.A)).symm.trans (Category.comp_id _))
  have hu : snd (Over.mk (𝟙 (Sp F))) P.A ≫ u = fst (Over.mk (𝟙 (Sp F))) P.A := Over.OverMorphism.ext hw
  have e₁ : lift u (𝟙 P.A) ≫ snd (Over.mk (𝟙 (Sp F))) P.A = 𝟙 _ := lift_snd _ _
  have e₂ : snd (Over.mk (𝟙 (Sp F))) P.A ≫ lift u (𝟙 P.A) = 𝟙 _ := by
    rw [comp_lift, hu, Category.comp_id, lift_fst_snd]
  have e₃ : lift u (𝟙 P.A) ≫ fst (Over.mk (𝟙 (Sp F))) P.A = u := lift_fst _ _
  refine HasBasis.pull P.isLB (φ := fun _ : Fin 1 => (snd (Over.mk (𝟙 (Sp F))) P.A).left)
    (lift u (𝟙 P.A)).left (snd (Over.mk (𝟙 (Sp F))) P.A).left
    (congrArg CommaMorphism.left e₂) (congrArg CommaMorphism.left e₁) (fun _ => congrArg CommaMorphism.left e₁)
    (fst (Over.mk (𝟙 (Sp F))) P.A).left _ (congrArg CommaMorphism.left e₃) ⟨β, fun s => ?_⟩
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv
  have key : ∀ c : Fin n → F, IsComb (fst (Over.mk (𝟙 (Sp F))) P.A).left β c s ↔
      ∑ i, (show Γ((Over.mk (𝟙 (Sp F))).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) •
        (SecM.ofSec P.A (β i) : SecM P.A P.L k (Over.mk (𝟙 (Sp F)))) = SecM.ofSec P.A s := fun c => by
    rw [Subtype.ext_iff, Submodule.coe_sum, funext_iff]
    refine forall_congr' fun j => ?_
    rw [Finset.sum_apply]
    exact eq_comm
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
  choose c hc using fun i => bij.2 (r i)
  obtain rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) = r := funext hc
  refine ⟨c, (key c).2 hr, fun c' hc' => funext fun i => bij.1 ?_⟩
  exact Fintype.linearIndependent_iffₛ.1 hli _ _ (((key c').1 hc').trans hr.symm) i

theorem hasBasis_field (hS : SecBaseChangeSt) (hk : 1 ≤ k) :
    HasBasis (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => (k : ℤ))) P.A.hom (k ^ P.g) := by
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of F)) P k hk (IsLocalRing.closedPoint F)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  let t : Spec (CommRingCat.of F) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of F))) ⊤).left :=
    (Spec (CommRingCat.of F)).topIso.inv
  have ht : t ≫ (overRes (T := baseOver (Spec (CommRingCat.of F))) ⊤).hom = 𝟙 _ := by
    show (Spec (CommRingCat.of F)).topIso.inv ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of F)).topIso.inv_hom_id
  have pull : ∀ i, ∃ b' : LB.Sec (LPow P.A P.L k (baseAt t)),
      IsPullSec P.A P.L k (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) b' := fun i => by
    obtain ⟨s', hs'⟩ := GlobalTheory.IndivisibleSection.exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
    exact ⟨s', fun j => hs' j _⟩
  choose b' hb' using pull
  obtain ⟨hli, hsp⟩ := hb F t b' hb'
  exact hasBasis_of_basis P k _ ht b' hli hsp

end Field

theorem iso_pow {X X' Y : Scheme.{0}} {L : LB X} {M : LB X'}
    (g : Y ⟶ X) (gi : X ⟶ Y) (e₁ : gi ≫ g = 𝟙 X) (e₂ : g ≫ gi = 𝟙 Y) (p : Y ⟶ X')
    (H : LBIso (L.pull g) (M.pull p)) (k : ℤ) :
    LBIso (LB.LinComb M (K := Fin 1) (fun _ => p) (fun _ => k))
      (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k)) := by
  obtain ⟨w, hw⟩ : LBIso L (M.pull (gi ≫ p)) :=
    LBIso.chartPull (chartPullSec L g gi e₁)
      (chartPullSame M (fun _ : PUnit => gi ≫ p) (fun _ => p) (fun _ => 1) gi fun _ => rfl) H
  have H₂ := iso_linComb ((isGen_iff w).1 hw) (fun _ : Fin 1 => g) (fun _ => k)
  have ep : (fun _ : Fin 1 => g ≫ gi ≫ p) = fun _ => p := by
    funext _; rw [← Category.assoc, e₂, Category.id_comp]
  rw [ep] at H₂
  exact LBIso.symm H₂

theorem exists_secK_basis : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), 1 ≤ k → ∃ b : Fin (k ^ A.g) → U.SecK k, (∀ c : Fin (k ^ A.g) → FractionRing R, ∃ s : U.SecK k, (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j)) ∧ ∀ s : U.SecK k, ∃! c : Fin (k ^ A.g) → FractionRing R, (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j) := by
  intro hS R _ _ I D A G _ _ U k hk
  have e₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.inv_hom_id
  have e₂ : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.hom_inv_id
  have H₁ := (hasBasis_field A k hS hk).pull A.isLB (φ' := fun _ => U.gen.hom.left) U.gen.hom.left U.gen.inv.left
    e₁ e₂ (fun _ => Category.comp_id _) _ (pullback.snd G.hom (jK R)) (Over.w U.gen.hom)
  obtain ⟨b, hb⟩ := H₁.of_iso (linComb_isLB _ U.LG.isLB _ _) (linComb_isLB _ A.isLB _ _)
    (iso_pow U.gen.hom.left U.gen.inv.left e₁ e₂ (pullback.fst G.hom (jK R)) U.ext k)
  exact ⟨b, fun c => exists_comb _ b c, hb⟩

end GlobalTheory.GenericSectionBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MapUniq

variable {X X' : Scheme.{0}}

theorem hom_ext_of_gs {I : Type} (D : I → X.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (φ ψ : X' ⟶ X) (hm : ∀ i z, φ z ∈ D i → ψ z ∈ D i)
    (h : ∀ i z, φ z ∈ D i → ∀ a : Γ(X, D i), gs φ z _ a = gs ψ z _ a) : φ = ψ := by
  refine Scheme.hom_ext_of_forall _ _ fun z => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ z ∈ ⨆ i, D i by rw [hc]; trivial)
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hle⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open (show z ∈ (φ ⁻¹ᵁ D i : Set X') from hi) (φ ⁻¹ᵁ D i).isOpen
  have e₁ : V ≤ φ ⁻¹ᵁ D i := hle
  have e₂ : V ≤ ψ ⁻¹ᵁ D i := fun y hy => hm i y (e₁ hy)
  have e : φ.appLE (D i) V e₁ = ψ.appLE (D i) V e₂ := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => fn_ext fun y hy => ?_)
    have k : ∀ (χ : X' ⟶ X) (e : V ≤ χ ⁻¹ᵁ D i), gs (𝟙 X') y V ((χ.appLE (D i) V e).hom a) = gs χ y _ a :=
      fun χ e => ((gs_res (𝟙 X') y e hy _).trans (gs_pull (𝟙 X') χ y _ (e hy) a)).trans (by rw [Category.id_comp])
    rw [k, k]
    exact h i y (e₁ hy) a
  refine ⟨V, hzV, ?_⟩
  have hV' : IsAffineOpen V := hV
  rw [← cancel_epi hV'.isoSpec.inv, ← Category.assoc, ← Category.assoc, hV'.isoSpec_inv_ι,
    ← (hD i).SpecMap_appLE_fromSpec φ hV' e₁, ← (hD i).SpecMap_appLE_fromSpec ψ hV' e₂, e]

theorem gs_cst {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (φ : X' ⟶ X) (z : X') (W : X.Opens)
    (h : φ z ∈ W) (c : R) :
    gs φ z W (AbLaw.cst f W c) = gs (φ ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) :=
  (gs_res φ z le_top h _).trans (gs_pull φ f z ⊤ trivial _)

theorem hom_eq_of_pull_sections : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ ψ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)) (w' : LB.Iso H' (H.pull ψ)), H'.IsLB → φ ≫ f = ψ ≫ f → w.IsGen → w'.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (ψ) z ∈ (H).U k → z ∈ (H').U k' → gs (ψ) z _ ((s j).f k) = (Geo.Tor.gw (w') (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → φ = ψ := by
  intro R _ X f H n s hH hs X' H' s' φ ψ w w' hH' hf _ _ hφ hψ
  choose r hr hsurj using fun i => (hs.2 i).2
  have mem : ∀ (χ : X' ⟶ X) (u : LB.Iso H' (H.pull χ)),
      (∀ j z (k : H.ι) (k' : H'.ι), χ z ∈ H.U k → z ∈ H'.U k' →
        gs χ z _ ((s j).f k) = (Geo.Tor.gw u (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k')) →
      ∀ i z k', z ∈ H'.U k' → (χ z ∈ nonzeroLocus (s i) ↔ IsUnit (gs (𝟙 X') z _ ((s' i).f k'))) ∧
        (χ z ∈ nonzeroLocus (s i) → ∀ j, gs (𝟙 X') z _ ((s' j).f k') =
          gs χ z _ (r i j) * gs (𝟙 X') z _ ((s' i).f k')) := by
    intro χ u hu i z k' hk'
    obtain ⟨k, hk⟩ := exists_chart hH (χ z)
    refine ⟨?_, fun hz j => ?_⟩
    · rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i) χ z hk, hu i z k k' hk hk', Units.isUnit_units_mul]
    · have e := AmpleSpan.IsRatio.gs (s := s j) (t := s i) (r := r i j) (hr i j) χ z hz hk
      rw [hu i z k k' hk hk', hu j z k k' hk hk', mul_left_comm] at e
      exact (Units.mul_right_inj _).1 e
  have hm : ∀ i z, φ z ∈ nonzeroLocus (s i) → ψ z ∈ nonzeroLocus (s i) := fun i z hz => by
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    exact (mem ψ w' hψ i z k' hk').1.2 ((mem φ w hφ i z k' hk').1.1 hz)
  refine hom_ext_of_gs (fun i => nonzeroLocus (s i)) (fun i => (hs.2 i).1) hs.1 φ ψ hm fun i z hz a => ?_
  obtain ⟨k', hk'⟩ := exists_chart hH' z
  have hz' := hm i z hz
  have hrr : ∀ j, gs φ z _ (r i j) = gs ψ z _ (r i j) := fun j =>
    ((mem φ w hφ i z k' hk').1.1 hz).mul_right_cancel
      (((mem φ w hφ i z k' hk').2 hz j).symm.trans ((mem ψ w' hψ i z k' hk').2 hz' j))
  obtain ⟨p, rfl⟩ := hsurj i a
  induction p using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.eval₂Hom_C, gs_cst f φ z _ hz, gs_cst f ψ z _ hz', hf]
  | add p q hp hq => rw [map_add (f := _), gs_add φ z _ hz, gs_add ψ z _ hz', hp, hq]
  | mul_X p j hp => rw [map_mul, MvPolynomial.eval₂Hom_X', gs_mul φ z _ hz, gs_mul ψ z _ hz', hp, hrr]

end GlobalTheory.MapUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducesFrobeniusOnSectionsTranslationIffImageStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.inducesFrobeniusOnSections_translation_iff_image : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (x : TFK (R := R) F ⟶ A.A), IndAt U.toUnifPre F N p (translT A.A x) ↔ QkToAkU U.toUnifPre F N p x := by
  first | exact @GlobalTheory.UT.indAt_translT_iff | exact GlobalTheory.UT.indAt_translT_iff | (intros; apply GlobalTheory.UT.indAt_translT_iff <;> assumption)
end

