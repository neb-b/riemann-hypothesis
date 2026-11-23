module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageTrQ
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatTrans

section Pull

variable {X Y Z : Scheme.{0}}

theorem pbT_pbT (T : Z ⟶ Y) (S : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens} (h₁ : O₁ ≤ S ⁻¹ᵁ O₀)
    (h₂ : O₂ ≤ T ⁻¹ᵁ O₁) (s : Γ(X, O₀)) : pbT T (pbT S s O₁) O₂ = pbT (T ≫ S) s O₂ := by
  rw [GlobalTheory.KS.pbT_of_le S h₁, GlobalTheory.KS.pbT_of_le T h₂, GlobalTheory.KS.pbT_of_le (T ≫ S) (h₂.trans (T.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE T S O₀ O₁ O₂ h₁ h₂)

theorem pbT_id {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) : pbT (𝟙 Z) s O = rsT s O := by
  rw [GlobalTheory.KS.pbT_of_le (𝟙 Z) h, GlobalTheory.KS.rsT_of_le h]
  simp [Scheme.Hom.appLE]
  rfl

theorem pbT_pow (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (s : Γ(Y, O₀)) (k : ℕ) :
    pbT f (s ^ k) O = pbT f s O ^ k := by
  rw [GlobalTheory.KS.pbT_of_le f h, GlobalTheory.KS.pbT_of_le f h, map_pow]

end Pull

def conjF {Z : Scheme.{0}} (T S : Z ⟶ Z) (d : Fld Z) : Fld Z :=
  fun O f => pbT T (d (S ⁻¹ᵁ O) (pbT S f (S ⁻¹ᵁ O))) O

section Tr

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]

def tr (x : 𝟙_ (Over (Sp R)) ⟶ G) : G.left ⟶ G.left := (𝟙 G * (toUnit G ≫ x)).left

theorem tr_over (x : 𝟙_ (Over (Sp R)) ⟶ G) : (𝟙 G * (toUnit G ≫ x)) ≫ (𝟙 G * (toUnit G ≫ x⁻¹)) = 𝟙 G := by
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique ((𝟙 G * (toUnit G ≫ x)) ≫ toUnit G) (toUnit G),
    _root_.mul_assoc, ← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one, _root_.mul_one]

theorem tr_tr_inv (x : 𝟙_ (Over (Sp R)) ⟶ G) : tr G x ≫ tr G x⁻¹ = 𝟙 _ := by
  rw [tr, tr, ← Over.comp_left, tr_over]; rfl

theorem tr_inv_tr (x : 𝟙_ (Over (Sp R)) ⟶ G) : tr G x⁻¹ ≫ tr G x = 𝟙 _ := by
  have := tr_tr_inv G x⁻¹
  rwa [inv_inv] at this

theorem tr_hom (x : 𝟙_ (Over (Sp R)) ⟶ G) : tr G x ≫ G.hom = G.hom := by
  rw [tr]; exact (Over.w _)

end Tr

section Field

variable {Z : Scheme.{0}}

theorem rsT_natCast {O₀ O : Z.Opens} (h : O ≤ O₀) (m : ℕ) : rsT (m : Γ(Z, O₀)) O = m := by
  rw [GlobalTheory.KS.rsT_of_le h, map_natCast]

theorem rsT_ofNat {O₀ O : Z.Opens} (h : O ≤ O₀) (m : ℕ) [m.AtLeastTwo] :
    rsT (OfNat.ofNat m : Γ(Z, O₀)) O = OfNat.ofNat m := by
  rw [GlobalTheory.KS.rsT_of_le h, map_ofNat]

theorem rsT_pow {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) (m : ℕ) : rsT (s ^ m) O = rsT s O ^ m := by
  rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h, map_pow]

theorem op_rsT {R : Type} [CommRing R] (G : Over (Sp R)) {n : ℕ} (dd : Fin n → Fld G.left)
    (hdd : ∀ a, IsField ⊤ (dd a)) (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) {W : G.left.Opens} (d : Fld G.left)
    (hd : IsField W d) (p p' : Γ(G.left, W)) (k : ℕ) {O O' : G.left.Opens} (h : O' ≤ O) (hO : O ≤ W)
    (f : Γ(G.left, O)) : op G dd Θ u d p p' k O' (rsT f O') = rsT (op G dd Θ u d p p' k O f) O' := by
  have e1 : ∀ a (g : Γ(G.left, O)), dd a O' (rsT g O') = rsT (dd a O g) O' := fun a g => by
    rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h]; exact (hdd a).2.2 O O' h le_top g
  have e2 : ∀ g : Γ(G.left, O), d O' (rsT g O') = rsT (d O g) O' := fun g => by
    rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h]; exact hd.2.2 O O' h hO g
  simp only [op, GlobalTheory.KS.rsT_add, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_sum, e1, e2,
    GlobalTheory.KS.rsT_constFn _ h, GlobalTheory.KS.rsT_rsT hO h, rsT_natCast h, rsT_ofNat h, rsT_pow h]

end Field

section Conj

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem isLift_conjF (D : R → R) {T S : G.left ⟶ G.left} (hTS : T ≫ S = 𝟙 _) (hST : S ≫ T = 𝟙 _)
    (hT : T ≫ G.hom = G.hom) (hS : S ≫ G.hom = G.hom) {W : G.left.Opens} {d : Fld G.left} (hl : IsLift G D W d) :
    IsLift G D (T ⁻¹ᵁ W) (conjF T S d) := by
  have hpre : ∀ U : G.left.Opens, S ⁻¹ᵁ (T ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hST]; rfl
  have hpre' : ∀ U : G.left.Opens, T ⁻¹ᵁ (S ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hTS]; rfl
  have hSO : ∀ O, O ≤ T ⁻¹ᵁ W → S ⁻¹ᵁ O ≤ W := fun O hO => (S.preimage_mono hO).trans (hpre W).le
  have back : ∀ (O : G.left.Opens) (f : Γ(G.left, O)), pbT T (pbT S f (S ⁻¹ᵁ O)) O = f := fun O f => by
    rw [pbT_pbT T S le_rfl (hpre' O).ge, hTS, pbT_id le_rfl, GlobalTheory.KS.rsT_self]
  refine ⟨⟨fun O hO f f' => ?_, fun O hO f f' => ?_, fun O O' hle hO f => ?_⟩, fun O hO r => ?_⟩
  · simp only [conjF]
    rw [GlobalTheory.KS.pbT_add, hl.1.1 _ (hSO O hO), GlobalTheory.KS.pbT_add]
  · simp only [conjF]
    rw [GlobalTheory.KS.pbT_mul, hl.1.2.1 _ (hSO O hO), GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_mul, GlobalTheory.KS.pbT_mul, back, back]
  · simp only [conjF]
    have hS' : S ⁻¹ᵁ O' ≤ S ⁻¹ᵁ O := S.preimage_mono hle
    rw [← GlobalTheory.KS.rsT_of_le hle, ← GlobalTheory.KS.rsT_of_le hle, GlobalTheory.KS.pbT_rsT S hle le_rfl,
      ← GlobalTheory.KS.rsT_pbT S le_rfl hS', GlobalTheory.KS.rsT_of_le hS', hl.1.2.2 _ _ hS' (hSO O hO), ← GlobalTheory.KS.rsT_of_le hS',
      GlobalTheory.KS.pbT_rsT T hS' (hpre' O').ge, GlobalTheory.KS.rsT_pbT T (hpre' O).ge hle]
  · simp only [conjF]
    rw [GlobalTheory.KS.pbT_constFn _ S le_rfl, hS, hl.2 _ (hSO O hO), GlobalTheory.KS.pbT_constFn _ T (hpre' O).ge, hT]

end Conj

section OpConj

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem pbT_natCast {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (m : ℕ) :
    pbT f (m : Γ(Y, O₀)) O = m := by
  rw [GlobalTheory.KS.pbT_of_le f h, map_natCast]

theorem pbT_ofNat {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (m : ℕ)
    [m.AtLeastTwo] : pbT f (OfNat.ofNat m : Γ(Y, O₀)) O = OfNat.ofNat m := by
  rw [GlobalTheory.KS.pbT_of_le f h, map_ofNat]

theorem op_conjF {n : ℕ} (dd : Fin n → Fld G.left) {T S : G.left ⟶ G.left} (hTS : T ≫ S = 𝟙 _) (hST : S ≫ T = 𝟙 _)
    (hT : T ≫ G.hom = G.hom)
    (hdd : ∀ a (O O' : G.left.Opens), O' ≤ T ⁻¹ᵁ O → ∀ f : Γ(G.left, O), dd a O' (pbT T f O') = pbT T (dd a O f) O')
    (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) (d : Fld G.left) {W : G.left.Opens} (p p' : Γ(G.left, W)) (k : ℕ)
    {O : G.left.Opens} (hO : O ≤ T ⁻¹ᵁ W) (f : Γ(G.left, O)) :
    op G dd Θ u (conjF T S d) (pbT T p (T ⁻¹ᵁ W)) (pbT T p' (T ⁻¹ᵁ W)) k O f =
      pbT T (op G dd Θ u d p p' k (S ⁻¹ᵁ O) (pbT S f (S ⁻¹ᵁ O))) O := by
  have hpre : ∀ U : G.left.Opens, S ⁻¹ᵁ (T ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hST]; rfl
  have hpre' : ∀ U : G.left.Opens, T ⁻¹ᵁ (S ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hTS]; rfl
  have hOO : O ≤ T ⁻¹ᵁ (S ⁻¹ᵁ O) := (hpre' O).ge
  have hSO : S ⁻¹ᵁ O ≤ W := (S.preimage_mono hO).trans (hpre W).le
  have back : pbT T (pbT S f (S ⁻¹ᵁ O)) O = f := by
    rw [pbT_pbT T S le_rfl hOO, hTS, pbT_id le_rfl, GlobalTheory.KS.rsT_self]
  have e : ∀ a (X : Γ(G.left, S ⁻¹ᵁ O)), pbT T (dd a (S ⁻¹ᵁ O) X) O = dd a O (pbT T X O) :=
    fun a X => (hdd a _ _ hOO X).symm
  have ep : ∀ q : Γ(G.left, W), pbT T (rsT q (S ⁻¹ᵁ O)) O = rsT (pbT T q (T ⁻¹ᵁ W)) O := fun q => by
    rw [GlobalTheory.KS.pbT_rsT T hSO hOO, GlobalTheory.KS.rsT_pbT T le_rfl hO]
  simp only [op, conjF, GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_sub, GlobalTheory.KS.pbT_mul, GlobalTheory.KS.pbT_sum, e, ep, back,
    GlobalTheory.KS.pbT_constFn _ T hOO, hT, pbT_natCast T hOO, pbT_ofNat T hOO, pbT_pow T hOO]

end OpConj

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem tr_q (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) : tr Y.H x ≫ Y.q.left = Y.q.left ≫ tr Q.P.A (x ≫ Y.q) := by
  have := Y.q_linear.isMonHom
  have e : (𝟙 Y.H * (toUnit Y.H ≫ x)) ≫ Y.q = Y.q ≫ (𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id, ← Category.assoc, ← Category.assoc,
      toUnit_unique (Y.q ≫ toUnit Q.P.A) (toUnit Y.H), Category.assoc]
  exact congrArg CommaMorphism.left e

theorem preimage_tr_q (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (V : Q.P.A.left.Opens) :
    tr Y.H x ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V) = Y.q.left ⁻¹ᵁ (tr Q.P.A (x ≫ Y.q) ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, tr_q, Scheme.Hom.comp_preimage]

end Ray

end GlobalTheory.HeatTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveHodgeToOmegaSpanModMaximalStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_hodge_to_omega_span_mod_maximal :
    GlobalTheory.Published.AbelianHodgeDeRham →
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ),
      IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
      (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ I : Ideal R, I.IsMaximal → LinearMap.range ψ ⊔ I • (⊤ : Submodule R G.omega) = ⊤ :=
  @GlobalTheory.PtExt.psi_sup_smul_top_eq_top
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEqTauFromSignRelationFourTorsion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.PsiSignRel

open GlobalTheory.UT.SymFrame

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem act_zero' (o : D.OAct O) : o.onB.act (0 : O) = 1 := by
  have h := o.onB.map_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem act_add' (o : D.OAct O) (a c : O) : o.onB.act a * o.onB.act c = o.onB.act (a + c) :=
  (o.onB.map_add a c).symm

theorem act_comp' (o : D.OAct O) (a c : O) : o.onB.act a ≫ o.onB.act c = o.onB.act (c * a) :=
  (o.onB.map_mul c a).symm

theorem act_natCast' (o : D.OAct O) (n : ℕ) : o.onB.act (n : O) = 𝟙 D.P.A ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero', pow_zero]
  | succ n ih => rw [Nat.cast_succ, ← act_add', ih, o.onB.map_one, pow_succ]

theorem act_pow' (o : D.OAct O) (a : O) (n : ℕ) : o.onB.act a ^ n = o.onB.act ((n : O) * a) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, act_zero']
  | succ n ih => rw [pow_succ, ih, act_add', Nat.cast_succ, add_one_mul]

theorem prod_gam {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (x : T ⟶ A) {U : Type} [CommGroup U]
    (k : (T.left ⟶ A.left) → U) :
    ∏ i : Fin 4, k (x.left ≫ (![(𝟙 A ^ 5).left, (𝟙 A ^ 4).left, 𝟙 _, (1 : A ⟶ A).left] : Fin 4 → _) i) ^
      (![2, -3, -2, 3] : Fin 4 → ℤ) i =
      k (x ^ 5).left ^ 2 * (k (x ^ 4).left ^ 3)⁻¹ * (k x.left ^ 2)⁻¹ * k (1 : T ⟶ A).left ^ 3 := by
  rw [Fin.prod_univ_four]
  show k (x ≫ 𝟙 A ^ 5).left ^ (2 : ℤ) * k (x ≫ 𝟙 A ^ 4).left ^ (-3 : ℤ) * k (x ≫ 𝟙 A).left ^ (-2 : ℤ) *
    k (x ≫ 1).left ^ (3 : ℤ) = _
  rw [MonObj.comp_pow, MonObj.comp_pow, MonObj.comp_one, Category.comp_id, zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat,
    zpow_ofNat, zpow_ofNat]


set_option maxHeartbeats 1600000 in
theorem core_id (hG : GlobalFnsSt) (o : D.OAct O) (w : O) (u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w)) (hu : Normd u)
    (gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]))
    (hgam : Normd gam)
    (ra : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (o.onB.act (star (1 + w))) (o.onB.act (1 + w))) rosatiε))
    (hra : GlobalTheory.TorusExt.IsRos D.P.L (o.onB.act (star (1 + w))) (o.onB.act (1 + w)) ra)
    (rw' : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (o.onB.act (star w)) (o.onB.act w)) rosatiε))
    (hrw : GlobalTheory.TorusExt.IsRos D.P.L (o.onB.act (star w)) (o.onB.act w) rw')
    (hw : w + star w = 1) {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (z : T.left) {J} (hJ : Good D.P.L z J) :
    val u (b ^ 4).left z J * val₂ ra z J ((b ^ 4) ≫ o.onB.act (1 + w)) b ^ 2 * val gam (b ≫ o.onB.act (1 + w)).left z J =
      th D z J (b ^ 4 * b ^ 4) ((b ^ 4) ≫ o.onB.act (star w * w)) b ^ 2 * th D z J (b ^ 4) (b ^ 4) b ^ 2 *
        val gam b.left z J ^ 2 * val₂ rw' z J ((b ^ 4) ≫ o.onB.act w) b ^ 2 * val gam (b ≫ o.onB.act w).left z J := by
  have hm : ∀ t : O, IsMonHom (o.onB.act t) := o.onB.hom
  have Gu := (grep_gen (Y := D.P.A) u hu.1 (o.onB.act 4).left).congr (P' := fun _ _ h =>
      h (o.onB.act 4 * (o.onB.act 4 ≫ o.onB.act w)).left * (h (o.onB.act 4).left ^ 2)⁻¹ *
        (h (o.onB.act 4 ≫ o.onB.act w).left)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ 2)
    (fun _ _ h => GlobalTheory.PsiWZeroPull.prod_four _ _ h) (fun _ _ _ _ _ => rfl)
  have Gra := (grep_gen (Y := D.P.A) ra hra.1 (lift (o.onB.act 4 ≫ o.onB.act (1 + w)) (𝟙 D.P.A)).left).congr
    (fun _ _ h => prod_ros _ _ _ _ h) (fun _ _ _ _ _ => rfl)
  have Grw := (grep_gen (Y := D.P.A) rw' hrw.1 (lift (o.onB.act 4 ≫ o.onB.act w) (𝟙 D.P.A)).left).congr
    (fun _ _ h => prod_ros _ _ _ _ h) (fun _ _ _ _ _ => rfl)
  have Gga := (grep_gen (Y := D.P.A) gam hgam.1 (o.onB.act (1 + w)).left).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Ggw := (grep_gen (Y := D.P.A) gam hgam.1 (o.onB.act w).left).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Ggb := (grep_gen (Y := D.P.A) gam hgam.1 (Over.Hom.left (𝟙 D.P.A))).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Gt2 := grep_cub (D := D) (Y := D.P.A) (o.onB.act 4 * o.onB.act 4) (o.onB.act 4 ≫ o.onB.act (star w * w)) (𝟙 D.P.A)
  have Gt1 := grep_cub (D := D) (Y := D.P.A) (o.onB.act 4) (o.onB.act 4) (𝟙 D.P.A)
  have key := (((Gu.mul (Gra.pow 2)).mul Gga).mul (((((Gt2.pow 2).mul (Gt1.pow 2)).mul (Ggb.pow 2)).mul
    (Grw.pow 2)).mul Ggw).inv).triv hG (fun U _ h => by
      clear Gu Gra Grw Gga Ggw Ggb Gt2 Gt1
      have e1 : 𝟙 D.P.A = o.onB.act 1 := o.onB.map_one.symm
      have e0 : (1 : D.P.A ⟶ D.P.A) = o.onB.act 0 := (act_zero' o).symm
      have hsw : star w = 1 - w := eq_sub_of_add_eq' hw
      simp only [e1, e0, act_add', act_comp', act_pow', star_add, star_one, hsw]
      ring_nf
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
      abel) (fun y I hI => by
      clear Gu Gra Grw Gga Ggw Ggb Gt2 Gt1
      have C : IsCub (cubV D.cub (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      have o1 : ∀ t : O, (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left ≫ (o.onB.act t).left =
          (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left := fun t => by
        rw [← Over.comp_left, MonObj.one_comp]
      have l1 : ∀ t t' : O, (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left ≫
          (lift (o.onB.act t ≫ o.onB.act t') (𝟙 D.P.A)).left =
          (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) 1).left := fun t t' => by
        rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, MonObj.one_comp, MonObj.one_comp]
      beta_reduce
      rw [o1, l1, l1, o1, o1, Over.id_left, Category.comp_id, normd_one hu hI, normd_one hgam hI]
      have r1 := hra.val_origin hI
      have r2 := hrw.val_origin hI
      unfold val₂ at r1 r2
      rw [r1, r2]
      simp only [MonObj.comp_mul, MonObj.one_comp, Category.comp_id, _root_.mul_one, C.face, one_pow, inv_one, normd_one hgam hI]) T b z J hJ
  have c4 : b ≫ o.onB.act 4 = b ^ 4 := by
    have := act_natCast' o 4
    rw [Nat.cast_ofNat] at this
    rw [this, comp_id_pow]
  beta_reduce at key
  simp only [← Over.comp_left, comp_lift, ← Category.assoc, c4, MonObj.comp_mul, Category.comp_id] at key
  exact mul_inv_eq_one.1 key


set_option maxHeartbeats 800000 in
theorem sign_rel : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (O : Type) [CommRing O] [StarRing O] [Module O D.X] (o : D.OAct O) (w : O), w + star w = 1 → ∀ u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w), Normd u → ∀ gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]), Normd gam → ∀ p q r : QkPt D F 4, q.y = w • p.y → r.y = (1 + w) • p.y → GtAct o w p.g q.g → GtAct o (1 + w) p.g r.g → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ s s' s'' : ((TF (R := R) F).left.presheaf.stalk z)ˣ, s * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (p.g.s p.y) (𝟙 _) z J ^ 2 * val gam p.g.b.left z J → s' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (q.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (q.g.s q.y) (𝟙 _) z J ^ 2 * val gam q.g.b.left z J → s'' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (r.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (r.g.s r.y) (𝟙 _) z J ^ 2 * val gam r.g.b.left z J → s'' = s ^ 2 * s' → @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) * val u (cP D (TF (R := R) F) p.y).left z J = @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J := by
  intro R _ _ D F _ _ O _ _ _ o w hw u hu gam hgam p q r hq hr hgq hgr z J hJ s s' s'' hs hs' hs'' hss
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  have hb4 : cP D (TF (R := R) F) p.y = p.g.b ^ 4 := cPoint_y p
  obtain ⟨qb, qv⟩ := (GlobalTheory.TorusExt.gtAct_iff_val hG o w p.g q.g).1 hgq
  obtain ⟨rb, rv⟩ := (GlobalTheory.TorusExt.gtAct_iff_val hG o (1 + w) p.g r.g).1 hgr
  have eq1 := qv (w • p.y) z J hJ
  have eq2 := rv ((1 + w) • p.y) z J hJ
  have sm1 : star w • w • p.y = (star w * w) • p.y := smul_smul _ _ _
  have sm2 : star (1 + w) • (1 + w) • p.y = (p.y + p.y) + (star w * w) • p.y := by
    rw [smul_smul, show star (1 + w) * (1 + w) = 1 + 1 + star w * w by
      rw [star_add, star_one]; linear_combination hw, add_smul, add_smul, one_smul]
  have e3 : (1 + w) • p.y = p.y + w • p.y := by rw [add_smul, one_smul]
  rw [sm1, GlobalTheory.TorusExt.cPoint_smul o, hb4] at eq1
  rw [sm2, GlobalTheory.TorusExt.cPoint_smul o, hb4] at eq2
  have g1 := GlobalTheory.TorusExt.charVal_add p.g hJ p.y p.y
  have g2 := GlobalTheory.TorusExt.charVal_add p.g hJ (p.y + p.y) ((star w * w) • p.y)
  rw [cPoint_add, GlobalTheory.TorusExt.cPoint_smul o, hb4] at g2
  rw [hb4] at g1
  have cid := core_id hG o w u hu gam hgam (GlobalTheory.TorusExt.rosGen hG o (1 + w)) (GlobalTheory.TorusExt.rosGen_isRos hG o (1 + w))
    (GlobalTheory.TorusExt.rosGen hG o w) (GlobalTheory.TorusExt.rosGen_isRos hG o w) hw p.g.b z hJ
  have vτ : @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) =
      @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi ((1 + w) • p.y)) (jFK (R := R) F) z J) *
        (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi p.y) (jFK (R := R) F) z J))⁻¹ *
        (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (w • p.y)) (jFK (R := R) F) z J))⁻¹ *
        (rigV D (TF (R := R) F).hom z J)⁻¹ := by
    rw [e3]
    exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) ((val_inv _ _).trans
        (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans rfl))))
  have gq : val gam q.g.b.left z J = val gam (p.g.b ≫ o.onB.act w).left z J := by rw [qb]
  have gr : val gam r.g.b.left z J = val gam (p.g.b ≫ o.onB.act (1 + w)).left z J := by rw [rb]
  rw [hq, gq] at hs'
  rw [hr, gr] at hs''
  rw [vτ, hb4]
  simp only [id_eq] at hs hs' hs'' ⊢
  apply Additive.ofMul.injective
  have E := fun {a c : ((TF (R := R) F).left.presheaf.stalk z)ˣ} (e : a = c) => congrArg Additive.ofMul e
  have hs := E hs; have hs' := E hs'; have hs'' := E hs''; have hss := E hss
  have eq1 := E eq1; have eq2 := E eq2; have g1 := E g1; have g2 := E g2; have cid := E cid
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at hs hs' hs'' hss eq1 eq2 g1 g2 cid ⊢
  linear_combination (norm := module) hs'' - 2 • hs - hs' - hss + 2 • eq2 - 2 • eq1 + 2 • g2 + 2 • g1 + cid

end GlobalTheory.PsiSignRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackLineBundleAutomorphismEqConst
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullAutConst

theorem main : ∀ {A : Type} [CommRing A] (B' : Over (Sp A)) [GrpObj B'] {X : Scheme.{0}} (L : LB X) (π : B'.left ⟶ X), IsAbelianScheme B' → L.IsLB → ∀ w : LB.Iso (L.pull π) (L.pull π), w.IsGen → ∃ lam : Aˣ, ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (z : Z) (j : L.ι), π (x z) ∈ L.U j → gm x z _ (w.s (fun _ => j, fun _ => j)) = gm (x ≫ B'.hom) z ⊤ (unitOn lam) := by
  intro A _ B' _ X L π hB hL w hw
  have hP := (isGen_iff w).1 hw
  have hg : ∀ (j j' : L.ι) (x : B'.left), π x ∈ L.U j → π x ∈ L.U j' →
      gm (𝟙 B'.left) x _ ((L.pull π).g (fun _ => j) (fun _ => j')) = gm (𝟙 _ ≫ π) x _ (L.g j j') := by
    intro j j' x hj hj'
    have hp : (𝟙 B'.left : B'.left ⟶ B'.left) x ∈ (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    show gm _ x _ (∏ _k : PUnit, (res _ (pullU π _ (L.g j j'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ x _ hp _).trans (gm_pull _ π x (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)
  obtain ⟨u, hu⟩ := glue_unit (⊤ : B'.left.Opens)
    (fun j : L.ι => (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j)) (fun _ => le_top)
    (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (π x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, mem_pull.2 hj, mem_pull.2 hj⟩)
    (fun j => w.s (fun _ => j, fun _ => j)) (fun j j' x hx => by
      have hj : π x ∈ L.U j := mem_pull.1 hx.1.1
      have hj' : π x ∈ L.U j' := mem_pull.1 hx.2.1
      have e := hP _ (𝟙 _) x j j' (fun _ => j) (fun _ => j') hj hj' (mem_pull.2 hj) (mem_pull.2 hj')
      rw [hg j j' x hj hj', mul_inv_cancel] at e
      exact e.trans (_root_.one_mul _))
  let e₁ : Γ(Sp A, ⊤) ≃+* Γ(B'.left, ⊤) :=
    RingEquiv.ofBijective B'.hom.appTop.hom (GlobalTheory.globalFns_holds _ B' hB)
  let e₂ : A ≃+* Γ(Sp A, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  let e : A ≃+* Γ(B'.left, ⊤) := e₂.trans e₁
  refine ⟨Units.map e.symm.toMonoidHom u, fun Z x z j hj => ?_⟩
  have hl : pullU B'.hom ⊤ (unitOn (Units.map e.symm.toMonoidHom u)) = u :=
    Units.ext (e.apply_symm_apply u.val)
  have hm : x z ∈ (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j) := ⟨mem_pull.2 hj, mem_pull.2 hj⟩
  refine (congrArg (gm x z _) (hu j)).symm.trans ((gm_res x z _ hm _).trans ?_)
  exact (congrArg (gm x z ⊤) hl).symm.trans (gm_pull x B'.hom z ⊤ trivial _)

end GlobalTheory.PullAutConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatV

abbrev bo (R : Type) [CommRing R] (f : R) : (Sp R).affineOpens :=
  (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f)

abbrev resV (R : Type) [CommRing R] (f : R) : R →+* Γ(Sp R, (bo R f).1) :=
  ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

abbrev cst {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {O : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) : Γ(X, V) →+* Γ(Y, O) :=
  (π.appLE V O h).hom

def opV {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {n : ℕ} (dd : Fin n → Fld Y) (Θ : Matrix (Fin n) (Fin n) Γ(X, V))
    (u : Fin n → Γ(X, V)) (d : Fld Y) {W : Y.Opens} (p p' : Γ(Y, W)) (k : ℕ) (O : Y.Opens) (h : O ≤ π ⁻¹ᵁ V)
    (f : Γ(Y, O)) : Γ(Y, O) :=
  2 * (k : Γ(Y, O)) * d O f - ∑ a, ∑ b, cst π V h (Θ a b) * dd a O (dd b O f) +
    2 * ∑ a, cst π V h (u a) * dd a O f + (2 * (k : Γ(Y, O)) ^ 2 * rsT p O + 2 * (k : Γ(Y, O)) * rsT p' O) * f

end GlobalTheory.HeatV
end
end

