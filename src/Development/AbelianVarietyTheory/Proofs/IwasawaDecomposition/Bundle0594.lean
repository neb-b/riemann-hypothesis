module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0580
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Formalism.LocalToGlobal.GroupLattices.ClassLocalOfEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSquaresCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateTwoNsmulAssociatedPowFour
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiDoubleCoord

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel MonoidalCategory CartesianMonoidalCategory MonObj GrpObj

section
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem val_cub (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J : (Spec (CommRingCat.of (FractionRing R)) ⟶ D.P.A.left) → D.P.L.ι}
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t (𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.pt3 a a' b) ξ J =
      Units.map (cst ξ).toMonoidHom w := by
  have hp : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
    simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]
  rw [hp]
  refine val_int (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) ξ hJc D.cub.t _ fun k => ?_
  show (_ ≫ (psum _ _ _).left) ≫ _ = _
  rw [Category.assoc, Over.w, Over.w]; rfl

theorem val_sym (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (y : D.X) :
    ∃ w : Rˣ, val (LB.pullGen D.P.L _ _ D.sym (D.xK y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  rw [val_pull hJ]
  have hx : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.xK y = jK R ≫ (D.c y).left := by rw [Category.id_comp]; exact DVR.QForm.ptK_eq D y
  rw [hx]
  refine val_int ξ hJc D.sym _ fun k => ?_
  obtain ⟨q, hq⟩ : ∃ q : D.P.A ⟶ D.P.A, (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k = q.left := by
    fin_cases k
    · exact ⟨_, rfl⟩
    · exact ⟨𝟙 _, rfl⟩
  rw [hq, Category.assoc, Over.w q, Over.w]; rfl

theorem val_rig (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) :
    ∃ w : Rˣ, val D.rigK (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  unfold DegPre.rigK
  rw [val_pull hJ]
  have : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
  rw [this]
  exact val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]

end

theorem alg {G : Type} [CommGroup G] (A0 Ay Am A2 Vr C0 C1 S : G)
    (h1 : Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C0 = Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * (Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹))
    (h2 : Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C1 = A2 * Ay⁻¹ * Ay⁻¹ * Vr⁻¹ * (A0 * Am⁻¹ * Ay⁻¹ * Vr⁻¹))
    (h3 : Am * S = Ay) :
    A2 = C0 * C0 * C1 * Vr * Vr * Vr * S⁻¹ * Ay ^ 4 := by
  have hC0 := mul_left_cancel h1
  have hAm : Am = Ay * S⁻¹ := eq_mul_inv_of_mul_eq h3
  subst hC0 hAm
  have e : A2 = Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C1 * (Ay⁻¹ * Ay⁻¹ * Vr⁻¹ * (A0 * (Ay * S⁻¹)⁻¹ * Ay⁻¹ * Vr⁻¹))⁻¹ := by
    rw [h2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem val_cubP {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b))
      (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  obtain ⟨w, hw⟩ := val_cub D ξ hJc a a' b
  exact ⟨w, (val_pull hJ _ _ _).trans hw⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I)
    (y : D.toPre.X) (r s : R), PsiCoord D.toPre y r → PsiCoord D.toPre (2 • y) s → Associated s (r ^ 4) := by
  intro R _ _ _ I D y r s hr hs
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.toPre.P.isLB D.toPre.P.A.hom
  have b1 := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult 0 0 y) (𝟙 _)).trans (val_mul hJ _ _ _))
  have b2 := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult y (-y) y) (𝟙 _)).trans (val_mul hJ _ _ _))
  have ev := (val_mul hJ _ _ _).symm.trans (val_corr hJ (D.psi_even y) (𝟙 _))
  have vt : ∀ a b : D.toPre.X, val (D.toPre.tau a b) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = val (D.toPre.psi (a + b)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J *
      (val (D.toPre.psi a) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ * (val (D.toPre.psi b) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ * (val D.toPre.rigK (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ :=
    fun a b => GlobalTheory.PeriodBalance.val_tau D.toPre ξ hJ a b
  obtain ⟨w0, hw0⟩ := val_cubP D.toPre ξ hJ hJc 0 0 y
  obtain ⟨w1, hw1⟩ := val_cubP D.toPre ξ hJ hJc y (-y) y
  obtain ⟨w5, hw5⟩ := val_rig D.toPre ξ hJ hJc
  obtain ⟨w6, hw6⟩ := val_sym D.toPre ξ hJ hJc y
  rw [hw6] at ev
  rw [hw0, vt, vt, hw5] at b1
  rw [hw1, vt, vt, vt, hw5] at b2
  rw [add_zero, zero_add] at b1
  rw [add_neg_cancel, zero_add, neg_add_cancel, ← two_nsmul] at b2
  have key := alg _ _ _ _ _ _ _ _ b1 b2 ev
  obtain ⟨u1, g1⟩ : ∃ u : Rˣ, (val (D.toPre.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J).val = cst ξ (u * r) := val_psi D.toPre ξ hJ hJc y r hr
  obtain ⟨u2, g2⟩ : ∃ u : Rˣ, (val (D.toPre.psi (2 • y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J).val = cst ξ (u * s) := val_psi D.toPre ξ hJ hJc (2 • y) s hs
  obtain ⟨W, key2⟩ : ∃ W : Rˣ, val (D.toPre.psi (2 • y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J =
      Units.map (cst ξ).toMonoidHom W * (val (D.toPre.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J) ^ 4 :=
    ⟨w0 * w0 * w1 * w5 * w5 * w5 * w6⁻¹, by rw [key]; simp only [map_mul, map_inv]⟩
  have e : cst ξ (u2 * s) = cst ξ (W * (u1 * r) ^ 4) := by
    rw [← g2, key2, map_mul, map_pow, ← g1, Units.val_mul, Units.val_pow_eq_pow_val]; rfl
  have e2 := cst_injective ξ e
  refine ⟨u2 * (W * u1 ^ 4)⁻¹, ?_⟩
  have h3 : ((W * u1 ^ 4 : Rˣ) : R) * r ^ 4 = u2 * s := by push_cast; rw [e2]; ring
  rw [Units.val_mul, ← _root_.mul_assoc, _root_.mul_comm s, ← h3, _root_.mul_comm, ← _root_.mul_assoc, Units.inv_mul,
    _root_.one_mul]

end GlobalTheory.PsiDoubleCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace CarDim

section Pull

variable {O : Type} [CommRing O] {bar : O → O} {ψ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [AddCommGroup X₁] [Module O X₁] {m : ℕ}

theorem isCell_pull_equiv [Module.Finite O X] [Module.Finite O X₁] {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsCell bar ψ γ) (e : X ≃ₗ[O] X₁) : IsCell bar ψ fun i => pull e.toLinearMap (γ i) :=
  ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, (linearOn_pull_iff e.surjective).2 h.linear,
    IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩

def pullLin (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pullLin_apply (r : X →ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X₁) : pullLin r β = pull r β := rfl

theorem pullLin_injective {r : X →ₗ[O] X₁} (hr : Function.Surjective r) : Function.Injective (pullLin r) :=
  fun β β' h => LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    exact LinearMap.congr_fun₂ h a b

theorem genRank_pull {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (γ : Fin m → LinearMap.BilinForm ℤ X₁) :
    genRank (fun i => pull r (γ i)) = genRank γ := by
  unfold genRank
  have e : Submodule.span ℤ (Set.range fun i => pull r (γ i)) = (Submodule.span ℤ (Set.range γ)).map (pullLin r) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [e]
  exact (Submodule.equivMapOfInjective _ (pullLin_injective hr) _).finrank_eq.symm

theorem inRCone_pull_iff {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    {β : LinearMap.BilinForm ℤ X₁} : InRCone (fun i => pull r (γ i)) (pull r β) ↔ InRCone γ β := by
  refine exists_congr fun c => and_congr_right fun _ => ?_
  constructor
  · intro h
    refine LinearMap.ext₂ fun a b => ?_
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    have := LinearMap.congr_fun₂ h a b
    simpa [LinearMap.sum_apply] using this
  · intro h
    refine LinearMap.ext₂ fun a b => ?_
    have := LinearMap.congr_fun₂ h (r a) (r b)
    simpa [LinearMap.sum_apply] using this

end Pull

section Rad

variable {O : Type} [CommRing O] {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]

def orad (β : LinearMap.BilinForm ℤ X) : Submodule O X where
  carrier := {x | ∀ (a : O) (y : X), β (a • x) y = 0}
  add_mem' := by
    intro x x' hx hx' a y
    rw [smul_add, map_add (f := _), LinearMap.add_apply, hx a y, hx' a y, add_zero]
  zero_mem' := by
    intro a y
    rw [smul_zero, map_zero, LinearMap.zero_apply]
  smul_mem' := by
    intro c x hx a y
    rw [smul_smul]
    exact hx _ y

theorem mem_orad {β : LinearMap.BilinForm ℤ X} {x : X} : x ∈ orad (O := O) β ↔ ∀ (a : O) (y : X), β (a • x) y = 0 :=
  Iff.rfl

theorem orad_pull {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X₁) :
    orad (pull r β) = (orad β).comap r := by
  ext x
  simp only [Submodule.mem_comap, mem_orad, pull_apply, map_smul]
  constructor
  · intro h a y
    obtain ⟨y, rfl⟩ := hr y
    exact h a y
  · intro h a y
    exact h a (r y)

def qEquiv {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (N : Submodule O X₁) : (X ⧸ N.comap r) ≃ₗ[O] (X₁ ⧸ N) :=
  (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])).trans
    ((N.mkQ ∘ₗ r).quotKerEquivOfSurjective (N.mkQ_surjective.comp hr))

end Rad

section Def

variable {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O)

def cdimSet (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (N : Submodule O X) (β : LinearMap.BilinForm ℤ X) :
    Set ℕ :=
  {k | ∃ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (X ⧸ N)), IsCell bar ψ δ ∧ InRCone (fun i => pull N.mkQ (δ i)) β ∧
    genRank δ = k}

def cdimQ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (N : Submodule O X) (β : LinearMap.BilinForm ℤ X) : ℕ :=
  sInf (cdimSet bar ψ X N β)

variable {bar ψ}

theorem cdimSet_pull {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup X₁] [Module O X₁]
    [Module.Finite O X₁] {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X₁) :
    cdimSet bar ψ X (orad (pull r β)) (pull r β) = cdimSet bar ψ X₁ (orad β) β := by
  rw [orad_pull hr]
  set N := orad (O := O) β
  let e := qEquiv hr N
  have key : ∀ δ : LinearMap.BilinForm ℤ (X₁ ⧸ N),
      pull (N.comap r).mkQ (pull e.toLinearMap δ) = pull r (pull N.mkQ δ) := fun δ => rfl
  ext k
  constructor
  · rintro ⟨m, δ', h1, h2, rfl⟩
    refine ⟨m, fun i => pull e.symm.toLinearMap (δ' i), isCell_pull_equiv h1 e.symm, ?_,
      genRank_pull e.symm.surjective _⟩
    rw [← inRCone_pull_iff hr]
    convert h2 using 2 with i
    rw [← key, pull_pull_symm]
  · rintro ⟨m, δ, h1, h2, rfl⟩
    refine ⟨m, fun i => pull e.toLinearMap (δ i), isCell_pull_equiv h1 e, ?_, genRank_pull e.surjective _⟩
    simp only [key]
    exact (inRCone_pull_iff hr).2 h2

theorem zero_mem_cdimSet {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Subsingleton X] (N : Submodule O X)
    (β : LinearMap.BilinForm ℤ X) : 0 ∈ cdimSet bar ψ X N β := by
  haveI : Subsingleton (X ⧸ N) := ⟨fun a b => by
    induction a using Submodule.Quotient.induction_on
    induction b using Submodule.Quotient.induction_on
    rename_i a b
    rw [Subsingleton.elim a b]⟩
  refine ⟨0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun c _ => ?_, ?_⟩,
    ⟨Fin.elim0, fun i => i.elim0, ?_⟩, ?_⟩
  · rw [ψ.eval_of_subsingleton]
    simp
  · refine ⟨1, 0, one_pos, fun i => i.elim0, fun β' _ _ => ?_, fun β' _ _ _ => ⟨1, Fin.elim0, one_pos, ?_⟩⟩
    · simp [InvFun.evalZ, ψ.eval_of_subsingleton]
    · rw [Fin.sum_univ_zero, one_smul]
      exact LinearMap.ext₂ fun a b => by rw [Subsingleton.elim a 0]; simp
  · exact LinearMap.ext₂ fun a b => by rw [Subsingleton.elim a 0]; simp
  · simp [genRank]

end Def

section Fun

variable {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O)


open Classical in
def carFun : InvFun O where
  toFun n B := if h : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
      ∀ a b, B a b = β a b then (cdimQ bar ψ (Fin n → O) (orad h.choose) h.choose : ℝ) else 0
  inv n m r hr B := by
    obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
    have hrs : ∀ a, r (s a) = a := fun a => LinearMap.congr_fun hs a
    by_cases h : ∃ β : LinearMap.BilinForm ℤ (Fin m → O), β ∈ balForms bar (Fin m → O) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B a b = β a b
    · have h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
          ∀ a b, B (r a) (r b) = β a b :=
        ⟨pull r h.choose, pull_mem r h.choose_spec.1, fun y => h.choose_spec.2.1 _, fun a b => h.choose_spec.2.2 _ _⟩
      rw [dite_eq_left h, dite_eq_left h']
      have e : h'.choose = pull r h.choose := LinearMap.ext₂ fun a b => by
        have h1 := h'.choose_spec.2.2 a b
        have h2 := h.choose_spec.2.2 (r a) (r b)
        rw [pull_apply]
        exact_mod_cast h1.symm.trans h2
      rw [e]
      unfold cdimQ
      rw [cdimSet_pull hr]
    · have h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
          ∀ a b, B (r a) (r b) = β a b := by
        rintro ⟨β, h1, h2, h3⟩
        exact h ⟨pull s β, pull_mem s h1, fun y => h2 _, fun a b => by rw [pull_apply, ← h3, hrs, hrs]⟩
      rw [dite_eq_right h, dite_eq_right h']
  zero B := by
    split_ifs with h
    · have := Nat.sInf_eq_zero.2 (Or.inl (zero_mem_cdimSet (bar := bar) (ψ := ψ) (orad h.choose) h.choose))
      unfold cdimQ
      rw [this, Nat.cast_zero]
    · rfl

variable {bar ψ}

theorem evalZ_carFun {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y) :
    (carFun bar ψ).evalZ β = cdimQ bar ψ X (orad β) β := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.evalZ, (carFun bar ψ).eval_eq hs]
  dsimp only [carFun]
  split_ifs with h
  · have e : h.choose = pull s β := LinearMap.ext₂ fun a b => by
      have := h.choose_spec.2.2 a b
      rw [pull_apply]
      exact_mod_cast this.symm
    rw [e]
    unfold cdimQ
    rw [cdimSet_pull hs]
  · exact absurd ⟨pull s β, pull_mem s hβ, fun y => hp _, fun a b => rfl⟩ h

end Fun

end CarDim

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RangeInterCellOpenSubset
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.Overlap

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_fieldPoint {A : Type} [CommRing A] (y : Sp A) :
    ∃ (k : Type) (_ : Field k) (ψ : A →+* k), ∀ q : Sp k, spMap ψ q = y := by
  refine ⟨(show PrimeSpectrum A from y).asIdeal.ResidueField, inferInstance, algebraMap _ _, fun q => ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap _ (show PrimeSpectrum _ from q).asIdeal = _
  rw [show (show PrimeSpectrum _ from q).asIdeal = ⊥ from Ideal.eq_bot_of_prime _]
  exact Ideal.ker_algebraMap_residueField _

theorem inBlock_cellVec {T : Type} {m : T → ℕ} {S : Type} [CommRing S] {ι : Type} {c c' : Let m → ι → S}
    (h : InBlock c c') (w : Pm m) (x : CellVar m → S) : InBlock c (cellVec c' w x) := fun z =>
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h ⟨z.1, w z.1 i⟩)

theorem map_lform {ι : Type} {M k : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (D : ι → Fin (M + 1) → S) (ρ : Fin k → ι) (q : Fin (plN M k + 1)) :
    φ (lform D ρ q) = lform (fun z => φ ∘ D z) ρ q := by
  simp [lform, map_prod]

theorem range_inter_cellOpen_subset : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ b w (W : P.Opens), IsCellOpen p0 p (V b) (D b) w W → ∀ b' w', Set.range (h b' w') ∩ (W : Set P) ⊆ Set.range (h b w) := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hc hp b w W hW b' w'
  rintro _ ⟨⟨y, rfl⟩, hy⟩
  obtain ⟨k, _, ψ', hψ'⟩ := exists_fieldPoint y
  have hz : ∀ q : Sp k, (spMap ψ' ≫ h b' w') q = h b' w' y := fun q => by
    rw [Scheme.Hom.comp_apply, hψ']
  obtain ⟨φ, hφ, hne⟩ := (hW k (spMap ψ' ≫ h b' w')).1 (by
    rintro _ ⟨q, rfl⟩
    rw [hz]; exact hy)
  rw [Category.assoc, hp.base] at hφ
  have hφ' : spMap φ ≫ (V b).2.fromSpec =
      spMap (ψ'.comp (MvPolynomial.C : Γ(X, (V b').1) →+* CR m (V b'))) ≫ (V b').2.fromSpec := by
    rw [← hφ, cbase, ← Category.assoc, spMap_spMap]
  have hu : InBlock (fun z => φ ∘ c b z) (fun z => ψ' ∘ uvec (c b') w' z) := by
    have := inBlock_cellVec (hc.compat k b b' φ _ hφ') w' (ψ' ∘ MvPolynomial.X)
    convert this using 2 with z
    exact map_cellVec ψ' _ w' _ z
  have span_range_comp_eq_top : ∀ {A B : Type} [CommRing A] [CommRing B] {n : ℕ}
      (v : Fin (n + 1) → A), Ideal.span (Set.range v) = ⊤ → (ψ : A →+* B) →
      Ideal.span (Set.range (ψ ∘ v)) = ⊤ := by
    intro A B _ _ n v hv ψ
    rw [Set.range_comp, ← Ideal.map_span, hv, Ideal.map_top]
  have spMap_pt : ∀ {O A B : Type} [CommRing O] [CommRing A] [CommRing B] {n : ℕ}
      (c : O →+* A) (v : Fin (n + 1) → A) (hv : Ideal.span (Set.range v) = ⊤) (ψ : A →+* B),
      spMap ψ ≫ pt c v hv = pt (ψ.comp c) (ψ ∘ v) (span_range_comp_eq_top v hv ψ) := by
    intro O A B _ _ _ n c v hv ψ
    letI := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := O)
    refine (ProjPoint.SpecMap_ofHom _ _ _ ψ).trans ?_
    unfold pt
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  obtain ⟨x, d, hd, ht⟩ := GlobalTheory.T.exists_flagCell_of_nonvanishing_leading_minors T m k M _ _ _ w ((hc.inv b).map φ) hu (fun τ j hj => by
    obtain ⟨hv, e⟩ := hp.plk b' w' (stdEn τ j hj)
    have := hne τ j hj _ _ _ (by rw [Category.assoc, e, spMap_pt])
    rw [map_plk] at this
    simpa only [map_lform] using this)
  have hψ : ∀ z, (MvPolynomial.eval₂Hom φ x : CR m (V b) →+* k) ∘ uvec (c b) w z =
      cellVec (fun z => φ ∘ c b z) w x z := fun z => by
    refine (map_cellVec _ _ w _ z).trans ?_
    congr 1
    · funext z r; simp
    · funext r; simp
  have key := GlobalTheory.T.flagCell_point_eq_of_triangular_frames O K β X s T m M B V α c D P p0 p h hc hp k b b' w w' (MvPolynomial.eval₂Hom φ x) ψ' d
    (by rw [hφ, cbase, ← Category.assoc, spMap_spMap, MvPolynomial.eval₂Hom_comp_C]) hd
    (by simpa only [hψ] using ht)
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  exact ⟨spMap (MvPolynomial.eval₂Hom φ x : CR m (V b) →+* k) q, by
    rw [← hz q, ← key, Scheme.Hom.comp_apply]⟩

end GlobalTheory.FlagEmb.Overlap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesServedPlaceEqLocalOrbitPairs
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.KerOne

theorem stepZeroClasses_servedPlace_eq_localOrbitPairs_alt : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ cls0 : ((w.D Z).gat u v hg).comp → ((w.D Z).gat u v hg).P.Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls 0,
        (∀ (a a' : ((w.D Z).gat u v hg).comp) (L L' : ((w.D Z).gat u v hg).P.Tup), ((w.D Z).gat u v hg).P.IsLatTup L →
          ((w.D Z).gat u v hg).P.IsLatTup L' →
          (cls0 a L = cls0 a' L' ↔ a = a' ∧ ∃ γ : (((w.D Z).gat u v hg).lev a).Γ, L' = (((w.D Z).gat u v hg).lev a).smul γ L)) ∧
        ∀ x, ∃ a L, ((w.D Z).gat u v hg).P.IsLatTup L ∧ cls0 a L = x := by
  intro K B f T w _ _ _ Z t Wt nch _ Y _ _ O _ _ E _ u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  have e : ((w.D Z).mem u).C.cls 0 ≃ ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls 0 := TC.eCls0 w.I w.l u ((w.D Z).what₂.muAt v)
  obtain ⟨W, Qq, O', Kf, _, _, _, _, _, _, _, _, _, _, n', ι, σ, j, w0, hS, nV, r, m, lam0, dom, hk, I, ψ, e', hH, heq⟩ :=
    t.g.gat u v hg
  obtain ⟨c⟩ := Formalism.L2.G.TwTie0.class_local_of_eq (w.D Z) t.g.herm.lev0 u e hS nV r m lam0 dom hk I ψ e' hH ((w.D Z).gat u v hg) heq
  exact ⟨c.cls, c.cls_iff, c.cls_surj⟩

end GlobalTheory.Mem.Top.KerOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSquaresCorrespondStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_coord_squares_correspond' : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ β : D'.toPre.X, D'.toPre.c (2 • β) ≫ Φ.hom = D.toPre.c (xe (2 • β)) → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val ((U.gt e).t (xe (2 • β))) r z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ) * val ((U'.gt e).t (2 • β)) r z J' ^ 2 := by
  first | exact @GlobalTheory.torus_coord_squares_correspond | exact GlobalTheory.torus_coord_squares_correspond | (intros; apply GlobalTheory.torus_coord_squares_correspond <;> assumption)
end

