module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodBalance

variable {R : Type} [CommRing R] [IsDomain R]

def cst (ξ : Spec (CommRingCat.of (FractionRing R))) :
    R →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ :=
  (((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom).comp (algebraMap R (FractionRing R))

theorem cst_injective (ξ : Spec (CommRingCat.of (FractionRing R))) : Function.Injective (cst ξ) :=
  (RingHom.injective (((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)).comp
    (IsFractionRing.injective R (FractionRing R))

theorem cst_eq (ξ : Spec (CommRingCat.of (FractionRing R))) (r : R) :
    cst ξ r = ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom
      (((jK R).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  exact congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom hnat

variable [IsLocalRing R]

theorem unit_gm (ξ : Spec (CommRingCat.of (FractionRing R))) (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (closedPoint R : Spec (CommRingCat.of R)) ∈ U) (a : Γ(Spec (CommRingCat.of R), U)ˣ) :
    ∃ u : Rˣ, (gm (jK R) ξ U a).val = cst ξ u := by
  obtain rfl := DVR.eq_top_of_closedPoint_mem U hU
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom a, ?_⟩
  rw [gm_val _ ξ ⊤ trivial, cst_eq]
  refine congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom
    (congrArg ((jK R).app ⊤).hom ?_)
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) a.val).symm

theorem unit_gm' (ξ : Spec (CommRingCat.of (FractionRing R))) {X : Scheme.{0}} (p : Spec (CommRingCat.of R) ⟶ X)
    (U : X.Opens) (hU : p (closedPoint R) ∈ U) (a : Γ(X, U)ˣ) :
    ∃ u : Rˣ, (gm (jK R ≫ p) ξ U a).val = cst ξ u := by
  have h : p (jK R ξ) ∈ U := by
    have := DVR.eq_top_of_closedPoint_mem (p ⁻¹ᵁ U) hU
    have h2 : jK R ξ ∈ p ⁻¹ᵁ U := by rw [this]; trivial
    exact h2
  rw [← gm_pull (jK R) p ξ U h]
  exact unit_gm ξ _ hU _

theorem exists_good_integral (ξ : Spec (CommRingCat.of (FractionRing R))) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (s : X ⟶ Spec (CommRingCat.of R)) [IsSeparated s] :
    ∃ J, Good L ξ J ∧ ∀ p : Spec (CommRingCat.of R) ⟶ X, p ≫ s = 𝟙 _ →
      p (closedPoint R) ∈ L.U (J (jK R ≫ p)) := by
  haveI : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ X => exists_chart hL (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL ξ (K := {p : Spec (CommRingCat.of R) ⟶ X // p ≫ s = 𝟙 _})
    (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK R) h))
    (fun p => by
      have := DVR.eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)
      have h2 : jK R ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1) := by rw [this]; trivial
      exact h2)
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

theorem val_psi (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (χ : D.X) (r : R) (hr : PsiCoord D χ r) :
    ∃ u : Rˣ, (val (D.psi χ) (𝟙 _) ξ J).val = cst ξ (u * r) := by
  obtain ⟨j, hj, h, e⟩ := hr
  have hx : D.xK χ = jK R ≫ (D.c χ).left := DVR.QForm.ptK_eq D χ
  have hm : (𝟙 (Spec (CommRingCat.of (FractionRing R))) : _ ⟶ _) ξ ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j :=
    h (show ξ ∈ jK R ⁻¹ᵁ ⊤ from trivial)
  have t := gen_trans (D.psi_gen χ) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
    (hJ.mem (fun _ : PUnit => D.xK χ) (𝟙 _)) hm
  have h1 : (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
      (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j)).val = cst ξ r := by
    refine (gm_val _ ξ _ hm _).trans (Eq.trans ?_ (cst_eq ξ r).symm)
    have e' : ((jK R).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = _ := Eq.trans ?_ e
    · rw [e']
      exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of (FractionRing R))).presheaf (homOfLE h) ξ trivial _).symm
    · congr 1
  obtain ⟨u, hu⟩ := unit_gm' ξ (D.c χ).left (D.P.L.U (J (jK R ≫ (D.c χ).left)) ⊓ D.P.L.U (j PUnit.unit))
    ⟨hJc _ (Over.w _), hj trivial⟩ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit))
  have h2 : trF (L := D.P.L) (fun _ : PUnit => D.xK χ) (fun _ => -1) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
      (fun _ => J (𝟙 _ ≫ D.xK χ)) j = (gm (jK R ≫ (D.c χ).left) ξ _ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit)))⁻¹ := by
    rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp, hx]
  refine ⟨u⁻¹, (congrArg Units.val t).trans ?_⟩
  refine (Units.val_mul _ _).trans ?_
  rw [map_mul]
  refine congrArg₂ (· * ·) ?_ h1
  refine (congrArg Units.val h2).trans ?_
  rw [Units.inv_eq_of_mul_eq_one_left]
  rw [hu, ← map_mul, Units.inv_mul, map_one]

omit [IsLocalRing R] in
theorem val_tau (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J) (a b : D.X) :
    val (D.tau a b) (𝟙 _) ξ J = val (D.psi (a + b)) (𝟙 _) ξ J * (val (D.psi a) (𝟙 _) ξ J)⁻¹ *
      (val (D.psi b) (𝟙 _) ξ J)⁻¹ * (val D.rigK (𝟙 _) ξ J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem coord_balance {O : Type} [Ring O] [StarRing O] (D : DegPre R) [Module O D.X] (ρ : D.OAct O) (x : O)
    (a b : D.X) {r₁ r₂ r₃ s₁ s₂ s₃ : R} (h₁ : PsiCoord D (x • a + b) r₁) (h₂ : PsiCoord D (x • a) r₂)
    (h₃ : PsiCoord D b r₃) (k₁ : PsiCoord D (a + star x • b) s₁) (k₂ : PsiCoord D a s₂)
    (k₃ : PsiCoord D (star x • b) s₃) : ∃ u : Rˣ, u * (r₁ * s₂ * s₃) = s₁ * r₂ * r₃ := by
  haveI := ρ.onB.hom x
  haveI := ρ.onB.hom (star x)
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨w, hw, h₀⟩ := exists_ros GlobalTheory.globalFns_holds D.P.isAb D.P.isLB _ _ (ρ.onB.rosati x)
  have hc := ρ.tau_bal x w hw h₀ a b
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ hc (𝟙 _))
  have e1 := val_tau D ξ hJ (x • a) b
  have e2 := val_tau D ξ hJ a (star x • b)
  have e3 := val_pull hJ w (D.pt2 a b) (𝟙 _)
  have hp : 𝟙 _ ≫ D.pt2 a b = jK R ≫ (lift (D.c a) (D.c b)).left := by
    simp [DegPre.pt2, ← CartesianMonoidalCategory.comp_lift]
  obtain ⟨v, hv⟩ : ∃ v : Rˣ, (val w (jK R ≫ (lift (D.c a) (D.c b)).left) ξ J).val = cst ξ v := by
    refine unit_gm' ξ _ _ (Set.mem_iInter.2 fun k => ?_) _
    obtain ⟨q, hq⟩ : ∃ q : D.P.A ⊗ D.P.A ⟶ D.P.A, rosatiφ D.P.A (ρ.onB.act x) (ρ.onB.act (star x)) k = q.left := by
      fin_cases k <;> exact ⟨_, rfl⟩
    have := hJc ((lift (D.c a) (D.c b)).left ≫ rosatiφ D.P.A (ρ.onB.act x) (ρ.onB.act (star x)) k) (by
      rw [hq, Category.assoc, Over.w q, Over.w]; rfl)
    exact this
  have e3' := e3.trans (congrArg (fun q => val w q ξ J) hp)
  have e4 := (congrArg₂ (@HMul.hMul _ _ ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ instHMul)
    e1 e3').symm.trans (e.trans e2)
  obtain ⟨u₁, g₁⟩ := val_psi D ξ hJ hJc _ _ h₁
  obtain ⟨u₂, g₂⟩ := val_psi D ξ hJ hJc _ _ h₂
  obtain ⟨u₃, g₃⟩ := val_psi D ξ hJ hJc _ _ h₃
  obtain ⟨v₁, f₁⟩ := val_psi D ξ hJ hJc _ _ k₁
  obtain ⟨v₂, f₂⟩ := val_psi D ξ hJ hJc _ _ k₂
  obtain ⟨v₃, f₃⟩ := val_psi D ξ hJ hJc _ _ k₃
  have key : ∀ {G : Type} [CommGroup G] (A₁ A₂ A₃ B₁ B₂ B₃ Z W : G),
      A₁ * A₂⁻¹ * A₃⁻¹ * Z⁻¹ * W = B₁ * B₂⁻¹ * B₃⁻¹ * Z⁻¹ → W * A₁ * B₂ * B₃ = B₁ * A₂ * A₃ := by
    intro G _ A₁ A₂ A₃ B₁ B₂ B₃ Z W h
    have h' := congrArg Additive.ofMul h
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at h' ⊢
    rw [← sub_eq_zero] at h' ⊢
    refine Eq.trans ?_ h'
    abel
  have e5 := congrArg Units.val (key _ _ _ _ _ _ _ _ e4)
  have e6 : cst ξ (v * (u₁ * r₁) * (v₂ * s₂) * (v₃ * s₃)) = cst ξ ((v₁ * s₁) * (u₂ * r₂) * (u₃ * r₃)) := by
    rw [map_mul, map_mul, map_mul, map_mul (cst ξ) (_ * _) (_ * r₃), map_mul (cst ξ) (_ * s₁), ← hv, ← g₁, ← g₂,
      ← g₃, ← f₁, ← f₂, ← f₃]
    exact e5
  have e7 := cst_injective ξ e6
  refine ⟨(v₁ * u₂ * u₃)⁻¹ * (v * u₁ * v₂ * v₃), ?_⟩
  rw [Units.val_mul, mul_assoc, Units.inv_mul_eq_iff_eq_mul]
  push_cast
  linear_combination e7

theorem norm_unit {R C : Type} [CommRing R] [NormedField C] (f : R →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (u : Rˣ) :
    ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have h1 := hf u
  have h2 := hf (u⁻¹ : Rˣ)
  have h3 := norm_nonneg (f u)
  nlinarith

theorem betaAt_balanced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (t : SAB H (Sp R)) (U : PELUnif (maximalIdeal R) t) (C : Type) [NormedField C] [IsUltrametricDist C] (f : R →+* C) (p : ℕ), IsIntegrallyClosed R → (∀ a, ‖f a‖ ≤ 1) → (∀ χ r, PsiCoord U.D.toPre χ r → f r ≠ 0) → ∀ (x : 𝓞 E) a b, betaAt U.D.toPre f p (x • a) b = betaAt U.D.toPre f p a (H.bar x • b) := by
  intro E _ _ _ H R _ _ _ _ t U C _ _ f p hR hf hne x a b
  letI := H.starRing
  have hex : ∀ χ, ∃ r, PsiCoord U.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main R U.D hR χ).1).imp fun _ h => h.1
  have hv : ∀ χ, vPsiAt U.D.toPre f p χ = -Real.logb p ‖f (hex χ).choose‖ := fun χ => dif_pos (hex χ)
  have hn : ∀ χ, ‖f (hex χ).choose‖ ≠ 0 := fun χ => norm_ne_zero_iff.2 (hne χ _ (hex χ).choose_spec)
  obtain ⟨u, hu⟩ := coord_balance U.D.toPre U.oD x a b (hex (x • a + b)).choose_spec (hex (x • a)).choose_spec
    (hex b).choose_spec (hex (a + H.bar x • b)).choose_spec (hex a).choose_spec (hex (H.bar x • b)).choose_spec
  have h := congrArg (fun r => Real.logb p ‖f r‖) hu
  simp only [map_mul, norm_mul, norm_unit f hf u, one_mul] at h
  rw [Real.logb_mul (mul_ne_zero (hn _) (hn _)) (hn _), Real.logb_mul (mul_ne_zero (hn _) (hn _)) (hn _),
    Real.logb_mul (hn _) (hn _), Real.logb_mul (hn _) (hn _)] at h
  simp only [betaAt, hv]
  linarith

end GlobalTheory.PeriodBalance
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology GlobalTheory.TangentOrigin

namespace GlobalTheory.HolLieFrame

theorem differentiableAt_of_forms {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : ℕ} (W : V → Fin g → ℂ)
    (b₀ : V) (H : ∀ w : Fin g → ℂ, (∀ L : V → ((Fin g → ℂ) →L[ℂ] ℂ), DifferentiableAt ℂ L b₀ →
      DifferentiableAt ℂ (fun b => L b (W b)) b₀ → L b₀ w = 0) → w = 0) : DifferentiableAt ℂ W b₀ := by
  let M : Submodule ℂ (Module.Dual ℂ (Fin g → ℂ)) :=
    { carrier := {l | ∃ L : V → ((Fin g → ℂ) →L[ℂ] ℂ), DifferentiableAt ℂ L b₀ ∧
        DifferentiableAt ℂ (fun b => L b (W b)) b₀ ∧ ∀ w, L b₀ w = l w}
      add_mem' := by
        rintro l l' ⟨L, h1, h2, h3⟩ ⟨L', h1', h2', h3'⟩
        exact ⟨fun b => L b + L' b, h1.add h1', h2.add h2', fun w => by simp [h3, h3']⟩
      zero_mem' := ⟨fun _ => 0, differentiableAt_const _, by simp, by simp⟩
      smul_mem' := by
        rintro c l ⟨L, h1, h2, h3⟩
        exact ⟨fun b => c • L b, h1.const_smul c, h2.const_smul c, fun w => by simp [h3]⟩ }
  have hM : M = ⊤ := by
    have h0 : M.dualCoannihilator = ⊥ := by
      refine eq_bot_iff.2 fun w hw => H w fun L h1 h2 => ?_
      exact (Submodule.mem_dualCoannihilator w).1 hw (L b₀).toLinearMap ⟨L, h1, h2, fun _ => rfl⟩
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := M), h0, Submodule.dualAnnihilator_bot]
  have hj : ∀ j : Fin g, LinearMap.proj j ∈ M := fun j => hM ▸ Submodule.mem_top
  choose L h1 h2 h3 using hj
  let J : V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := fun b => ContinuousLinearMap.pi fun j => L j b
  have hJ : DifferentiableAt ℂ J b₀ :=
    (ContinuousLinearMap.piEquivL ℂ (Fin g → ℂ) (fun _ : Fin g => ℂ)).differentiableAt.comp b₀
      (differentiableAt_pi.2 h1)
  have hJ0 : IsUnit (J b₀) := by
    have : J b₀ = 1 := by
      ext1 w
      funext j
      exact h3 j w
    rw [this]; exact isUnit_one
  have hW : DifferentiableAt ℂ (fun b => J b (W b)) b₀ := differentiableAt_pi.2 h2
  refine ((hJ.inverse hJ0).clm_apply hW).congr_of_eventuallyEq ?_
  filter_upwards [hJ.continuousAt.eventually (Units.isOpen.mem_nhds hJ0)] with b hb
  have := congrArg (fun T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) => T (W b)) (Ring.inverse_mul_cancel _ hb)
  exact this.symm

theorem evalPt_appLE {A : Type} [CommRing A] {X Y : Scheme.{0}} (v : Sp A ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(Y, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V) (hU : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U) :
    evalPt v V hV ((φ.appLE U V e).hom f) = evalPt (v ≫ φ) U hU f := by
  simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (φ.appLE U V e), Scheme.Hom.appLE_comp_appLE]

theorem exists_fraction {A : Type} [CommRing A] {X : Scheme.{0}} (ψ : Sp A ⟶ X) (U : X.Opens) (f : Γ(X, U))
    (t₀ : A →+* ℂ) (h₀ : ⊤ ≤ (spMap t₀ ≫ ψ) ⁻¹ᵁ U) :
    ∃ r a : A, t₀ r ≠ 0 ∧ ∀ (C : Type) [CommRing C] (t : A →+* C), IsUnit (t r) →
      ∃ h : ⊤ ≤ (spMap t ≫ ψ) ⁻¹ᵁ U, evalPt (spMap t ≫ ψ) U h f * t r = t a := by
  have hY := isAffineOpen_top (Sp A)
  obtain ⟨s, hsU, hs⟩ := hY.exists_basicOpen_le (V := ψ ⁻¹ᵁ U)
    ⟨_, (top_le_preimage_iff_mem _ _).1 ((top_le_preimage_comp _ ψ U).1 h₀)⟩ trivial
  have hloc := hY.isLocalization_basicOpen s
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers s) ((ψ.appLE U _ hsU).hom f)
  have ha' : (ψ.appLE U _ hsU).hom f * resG _ ((Sp A).basicOpen_le s) (s ^ n) =
    resG _ ((Sp A).basicOpen_le s) a := ha
  obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2 s
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2 a
  have hs₀ : t₀ s ≠ 0 := by
    have := (top_le_preimage_basicOpen_iff _ _ _).1 ((top_le_preimage_iff_mem (spMap t₀) _).2 hs)
    rwa [valAt'_eq_evalPt _ _ le_rfl, evalPt_spMap] at this
  refine ⟨s ^ (n + 1), a * s, by rw [map_pow]; exact pow_ne_zero _ hs₀, fun C _ t ht => ?_⟩
  have hu : IsUnit (t s) := by
    rw [map_pow] at ht
    exact (isUnit_pow_iff n.succ_ne_zero).1 ht
  have hD : ⊤ ≤ spMap t ⁻¹ᵁ (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv s) := by
    rw [← evalPt_spMap t s] at hu
    have hu' := hu.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
    simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply] at hu'
    have := Scheme.basicOpen_appLE (spMap t) ⊤ ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of A)).inv s)
    rw [(Sp C).basicOpen_of_isUnit hu', top_inf_eq] at this
    exact this.le
  have h : ⊤ ≤ (spMap t ≫ ψ) ⁻¹ᵁ U := fun p hp => hsU (hD hp)
  refine ⟨h, ?_⟩
  have := congrArg (evalPt (spMap t) _ hD) ha'
  rw [map_mul, evalPt_appLE _ _ _ _ _ _ _ h, evalPt_res _ _ le_rfl, evalPt_res _ _ le_rfl, map_pow, evalPt_spMap,
    evalPt_spMap] at this
  rw [map_pow, pow_succ, ← _root_.mul_assoc, this, map_mul]

theorem exists_hol_snd {V R : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing R] {X : Scheme.{0}}
    (ψ : Sp (DualNumber R) ⟶ X) (ev : V → (R →+* ℂ)) (b₀ : V) (hev : ∀ c, DifferentiableAt ℂ (fun b => ev b c) b₀)
    (U : X.Opens) (f : Γ(X, U)) (h₀ : ⊤ ≤ (spMap (Chart.dualMapR (ev b₀)) ≫ ψ) ⁻¹ᵁ U) :
    ∃ F : V → ℂ, DifferentiableAt ℂ F b₀ ∧ ∀ᶠ b in 𝓝 b₀,
      ∃ h : ⊤ ≤ (spMap (Chart.dualMapR (ev b)) ≫ ψ) ⁻¹ᵁ U, (evalPt _ U h f).snd = F b := by
  have h₁ : ⊤ ≤ (spMap (fstC.comp (Chart.dualMapR (ev b₀))) ≫ ψ) ⁻¹ᵁ U := by
    have := (top_le_preimage_iff _ U).1 h₀
    rwa [← Category.assoc, ← Spec.map_comp] at this
  obtain ⟨r, a, hr, H⟩ := exists_fraction ψ U f _ h₁
  have hf : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).fst = ev b x.fst := fun b x => by simp [Chart.dualMapR]
  have hs : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).snd = ev b x.snd := fun b x => by simp [Chart.dualMapR]
  have hr' : ev b₀ r.fst ≠ 0 := (hf b₀ r) ▸ hr
  refine ⟨fun b => (ev b a.snd - ev b a.fst * (ev b r.fst)⁻¹ * ev b r.snd) * (ev b r.fst)⁻¹,
    ((hev a.snd).sub (((hev a.fst).mul ((hev r.fst).inv hr')).mul (hev r.snd))).mul ((hev r.fst).inv hr'), ?_⟩
  filter_upwards [(hev r.fst).continuousAt.eventually_ne hr'] with b hb
  obtain ⟨h, e⟩ := H _ (Chart.dualMapR (ev b)) (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [hf]; exact hb.isUnit))
  refine ⟨h, ?_⟩
  have e1 := congrArg TrivSqZeroExt.fst e
  have e2 := congrArg TrivSqZeroExt.snd e
  rw [TrivSqZeroExt.fst_mul, hf, hf] at e1
  rw [DualNumber.snd_mul, hf, hs, hs] at e2
  rw [← e1, ← e2]
  field_simp
  ring

theorem differentiableAt_ev {V R : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing R] {X : Scheme.{0}}
    {B : Set V} {y : V → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) (j : Sp R ⟶ X) [IsOpenImmersion j] (ev : V → (R →+* ℂ))
    (h : ∀ b ∈ B, y b = spMap (ev b) ≫ j) {b₀ : V} (hb : b₀ ∈ B) (c : R) :
    DifferentiableAt ℂ (fun b => ev b c) b₀ := by
  have hle : ⊤ ≤ j ⁻¹ᵁ (j ''ᵁ ⊤) := (j.preimage_image_eq ⊤).ge
  have h₀ : ⊤ ≤ y b₀ ⁻¹ᵁ (j ''ᵁ ⊤) := by
    rw [h b₀ hb]
    exact fun p _ => hle (Set.mem_univ _)
  refine (LocalLift.hol_differentiableAt hy hb h₀
    ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))).congr_of_eventuallyEq ?_
  filter_upwards [LocalLift.hol_eventually_mem hy hb h₀] with b hb'
  rw [h b hb'.1, ← valAt'_appLE _ j _ ⊤ hle _ le_rfl, valAt'_eq_evalPt _ _ le_rfl, ← evalPt_spMap (ev b) c,
    ← CommRingCat.comp_apply (j.appIso ⊤).inv, Scheme.Hom.appIso_inv_appLE]
  simp

theorem differentiableAt_fderiv {m g : ℕ} {X : Scheme.{0}} {B : Set (Fin m → ℂ)}
    {e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (he : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2)) {b₀ : Fin m → ℂ} (hb : b₀ ∈ B)
    (U : X.Opens) (f : Γ(X, U)) (h₀ : ⊤ ≤ e b₀ 0 ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => fderiv ℂ (fun z => valAt' (e b z) U f) 0) b₀ := by
  have h1 := SCV.analyticOnNhd_of_differentiableOn (he U f).1 (he U f).2 (b₀, 0) ⟨⟨hb, trivial⟩, h₀⟩
  have h2 := ContDiffAt.fderiv (𝕜 := ℂ) (f := fun b z => valAt' (e b z) U f) (g := fun _ => 0) (x₀ := b₀) (m := 1)
    (n := 2) h1.contDiffAt contDiffAt_const le_rfl
  exact h2.differentiableAt one_ne_zero

section Fibre

open GlobalTheory.GrpTangent

variable {G : Over (Sp ℂ)} [GrpObj G] {X : Scheme.{0}} {ψ : G.left ⟶ X} {g : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)}

end Fibre

end GlobalTheory.HolLieFrame

namespace GlobalTheory

open HolLieFrame
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemHolSubIff
section
noncomputable section

namespace GlobalTheory.CuspProduct

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem mem_holSub_iff {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    (P : FDSec X) : P ∈ holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)


open Classical in
theorem rdU_mul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f g : Rul Xo c) : rdU U (f * g) = rdU U f * rdU U g := by
  funext k x
  show (if h : x ∈ (U.X k).dom then toC (evR Xo c (f * g) (U.un k ⟨x, h⟩)) else 0) =
    (if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) *
      (if h : x ∈ (U.X k).dom then toC (evR Xo c g (U.un k ⟨x, h⟩)) else 0)
  split_ifs with h
  · exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)
  · simp

theorem laU_add {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (hn : Even n)
    (hn' : Even n') (k : U.Comp) : laU U (a + a') (n + n') k = laU U a n k + laU U a' n' k := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨m', rfl⟩ := hn'
  have h1 : (m + m) / 2 = m := by omega
  have h2 : (m' + m') / 2 = m' := by omega
  have h3 : (m + m + (m' + m')) / 2 = m + m' := by omega
  funext τ j
  simp only [laU, Pi.add_apply, h1, h2, h3]
  split_ifs <;> push_cast <;> ring

theorem cuspMul_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ)
    (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.CuspMul Xo c U := by
  intro E _ _ _ H Dw l Xo c r U a a' n n' f g hd hd' hf hg
  rw [mem_cusp] at hf hg ⊢
  refine ⟨mulC_mem_sec Xo c a a' n n' hf.1 hg.1, fun σ hσ => ?_⟩
  show rdU (U σ) (f * g) ∈ holSub (U σ).X (laU (U σ) (a + a') (n + n'))
  rw [rdU_mul, mem_holSub_iff]
  intro k
  rw [laU_add (U σ) a a' n n' hd.2 hd'.2 k]
  exact (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((mem_holSub_iff _ _ _).1 (hf.2 σ hσ) k) _
    ((mem_holSub_iff _ _ _).1 (hg.2 σ hσ) k).1

end GlobalTheory.CuspProduct
end
end

