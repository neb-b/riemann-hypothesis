module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2384
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbacksDifferByUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Trait.bijective_appTop {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) :
    Function.Bijective T.G.hom.appTop.hom := by
  have hd : IsDiscreteValuationRing W := T.cdvr.1
  have := T.U.smooth
  have := T.U.separated
  have := C.semi.quasiCompact
  have : QuasiCompact T.G.hom := MorphismProperty.of_isPullback (P := @QuasiCompact) T.cart.1 this
  exact GlobalFunctionsDvrGeneric.bij_of_generic T.G
    (GlobalFunctionsDvrPowers.bijective_of_iso T.U.gen (GlobalTheory.allSixLaws.1.globalFns _ T.A.A T.A.isAb))

theorem Trait.exists_unit_scal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (c : Γ(T.G.left, ⊤)ˣ) :
    ∃ v : Wˣ, scal T.G.hom (v : W) = c.val := by
  let e : W ≃+* Γ(T.G.left, ⊤) := RingEquiv.ofBijective
    (T.G.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom)
    (T.bijective_appTop.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv))
  exact ⟨Units.map e.symm.toMonoidHom c, e.apply_symm_apply c.val⟩

theorem Trait.carries_mulPull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    u.IsGen →
    ∀ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    uG.IsGen → ∀ (b : W) (σ' : H0 T.U.LG.L 1) (σ : SecK C.P.L.L T.β 1), T.Carries b σ' σ →
    ∀ (σ₂ : SecK C.P.L.L T.β (m ^ 2)) (σ'' : H0 T.U.LG.L (m ^ 2)),
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
      sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) →
    ∃ v : Wˣ, T.Carries (b * v) σ'' σ₂ := by
  intro R _ _ _ _ D C W _ _ _ T m u hu uG huG b σ' σ hcar σ₂ σ'' h₂ h''
  have hm := GlobalTheory.ZH.TorsFrame.mulA_comm T.cart m
  obtain ⟨a, ha, hP⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_gen_move C.P.L.isLB T.U.LG.isLB T.ℓ ((isGen_iff _).1 T.ℓ_gen)
    (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![𝟙 T.G.left, (mulA T.G m).left]
    ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)] T.β (fun k => by
      fin_cases k
      · exact (Category.id_comp _).trans (Category.comp_id _).symm
      · exact hm) u hu
  obtain ⟨c, hc⟩ := GlobalTheory.ZM.Coord.exists_global_unit (DVR.linComb_isLB _ T.U.LG.isLB _ _) ha huG
  obtain ⟨v, hv⟩ := T.exists_unit_scal c
  refine ⟨v, fun Z r z J J' hJ hJ' => ?_⟩
  have e₁ : (r ≫ T.β) ≫ (mulA C.G m).left = (r ≫ (mulA T.G m).left) ≫ T.β := by
    rw [Category.assoc, Category.assoc, hm]
  have hp : val u (r ≫ T.β) z J = (gw T.ℓ r z (J (r ≫ T.β)) (J' r) ^ (m ^ 2) *
      (gw T.ℓ (r ≫ (mulA T.G m).left) z (J ((r ≫ (mulA T.G m).left) ≫ T.β)) (J' (r ≫ (mulA T.G m).left)))⁻¹) *
      val a r z J' := by
    refine (hP Z r z _ _ (fun k => ?_) (fun k => hJ' (r ≫ _))).trans ?_
    · fin_cases k
      · exact hJ ((r ≫ T.β) ≫ 𝟙 _)
      · have := hJ ((r ≫ T.β) ≫ (mulA C.G m).left)
        exact (congrArg (fun q => q z ∈ C.P.L.L.U (J ((r ≫ T.β) ≫ (mulA C.G m).left))) e₁).mp this
    · refine congrArg (· * val a r z J') ?_
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, e₁, zpow_natCast, zpow_neg, pow_one]
  have hq : val a r z J' = gm r z ⊤ c * val uG r z J' := by
    have hm' := hJ'.mem ![𝟙 T.G.left, (mulA T.G m).left] r
    exact (congrArg (gm r z _) (hc _)).trans ((map_mul _ _ _).trans (congrArg (· * val uG r z J') (gm_res r z _ hm' _)))
  have hs : gs (r ≫ (mulA T.G m).left) z ⊤ (scal T.G.hom b) = gs r z ⊤ (scal T.G.hom b) := by
    refine (gs_pull r (mulA T.G m).left z ⊤ trivial _).symm.trans (congrArg (gs r z ⊤) ?_)
    show ((mulA T.G m).left ≫ T.G.hom).appTop.hom _ = _
    rw [Over.w]; rfl
  have hbv : gs r z ⊤ (scal T.G.hom (b * v)) = gs r z ⊤ (scal T.G.hom b) * (gm r z ⊤ c).val := by
    rw [← gs_unit r z ⊤ trivial, ← hv, ← gs_mul r z ⊤ trivial, scal, scal, scal, map_mul, map_mul]
  rw [h₂ Z r z J hJ, h'' Z r z J' hJ', hcar Z _ z J J' hJ hJ', hp, hq, hs, hbv, Category.comp_id, pow_one]
  generalize gw T.ℓ (r ≫ (mulA T.G m).left) z _ _ = g
  simp only [Units.val_mul]
  linear_combination (gs r z ⊤ (scal T.G.hom b) * (gm r z ⊤ c).val * (gw T.ℓ r z (J (r ≫ T.β)) (J' r) ^ (m ^ 2)).val *
    (val uG r z J').val * sval σ' (r ≫ (mulA T.G m).left) z J') * g.inv_mul

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCancelValuesMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.LamCancel

theorem lam_cancel : ∀ (SA SB SC : Scheme.{0}) (A : Over SA) [GrpObj A] [IsCommMonObj A] (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (MA : LB A.left) (MB : LB B.left) (MC : LB C.left), MA.IsLB → MB.IsLB → MC.IsLB → ∀ (m₁ : (G2 A).left ⟶ (G2 B).left) (m₂ : (G2 B).left ⟶ (G2 C).left) (m : (G2 A).left ⟶ (G2 C).left), m₁ ≫ m₂ = m → ∀ (w₂ : LB.Iso (abelian₂ B MB) ((abelian₂ C MC).pull m₂)), w₂.IsGen → ∀ (w : LB.Iso (abelian₂ A MA) ((abelian₂ C MC).pull m)), w.IsGen → ∃ w₁ : LB.Iso (abelian₂ A MA) ((abelian₂ B MB).pull m₁), w₁.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 A).left) (z : Z) JA JB JC, Good MA z JA → Good MB z JB → Good MC z JC → lamVal w p z JC JA = lamVal w₁ p z JB JA * lamVal w₂ (p ≫ m₁) z JC JB := by
  intro SA SB SC A _ _ B _ _ C _ _ MA MB MC hA hB hC m₁ m₂ m hm w₂ h₂ w hw
  subst hm
  have lA : (abelian₂ A MA).IsLB := DVR.linComb_isLB _ hA _ _
  have lB : (abelian₂ B MB).IsLB := DVR.linComb_isLB _ hB _ _
  have lC : (abelian₂ C MC).IsLB := DVR.linComb_isLB _ hC _ _
  have p₂ := (isGen_iff _).1 h₂
  have pw := (isGen_iff _).1 hw
  obtain ⟨w₁, T⟩ := Geo.Tor.exists_cancel lC w₂ w p₂ pw lB lA
  refine ⟨w₁, (isGen_iff _).2 (T.pgen_cancel lC p₂ pw), fun Z p z JA JB JC gA gB gC => ?_⟩
  have t := T Z p z (fun k => JC (((p ≫ m₁) ≫ m₂) ≫ (psum C (x2 C) k.down).left))
    (fun k => JB ((p ≫ m₁) ≫ (psum B (x2 B) k.down).left)) (fun k => JA (p ≫ (psum A (x2 A) k.down).left))
    (Set.mem_iInter.2 fun k => gC (((p ≫ m₁) ≫ m₂) ≫ (psum C (x2 C) k.down).left))
    (Set.mem_iInter.2 fun k => gB ((p ≫ m₁) ≫ (psum B (x2 B) k.down).left))
    (Set.mem_iInter.2 fun k => gA (p ≫ (psum A (x2 A) k.down).left))
  refine Eq.trans ?_ (t.trans ((mul_comm _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · show Geo.Tor.gw w p z (fun k => JC (p ≫ (m₁ ≫ m₂) ≫ (psum C (x2 C) k.down).left))
      (fun k => JA (p ≫ (psum A (x2 A) k.down).left)) = _
    simp only [Category.assoc]
  · show _ = Geo.Tor.gw w₁ p z (fun k => JB (p ≫ m₁ ≫ (psum B (x2 B) k.down).left))
      (fun k => JA (p ≫ (psum A (x2 A) k.down).left))
    simp only [Category.assoc]
  · show _ = Geo.Tor.gw w₂ (p ≫ m₁) z (fun k => JC ((p ≫ m₁) ≫ m₂ ≫ (psum C (x2 C) k.down).left))
      (fun k => JB ((p ≫ m₁) ≫ (psum B (x2 B) k.down).left))
    simp only [Category.assoc]

end GlobalTheory.LamCancel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCompValuesMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.LamComp


open GlobalTheory.HalfBC GlobalTheory.PrimCocycle in
theorem lam_comp : ∀ (SA SB SC : Scheme.{0}) (A : Over SA) [GrpObj A] [IsCommMonObj A] (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (MA : LB A.left) (MB : LB B.left) (MC : LB C.left), MA.IsLB → MB.IsLB → MC.IsLB → ∀ (m₁ : (G2 A).left ⟶ (G2 B).left) (m₂ : (G2 B).left ⟶ (G2 C).left) (m : (G2 A).left ⟶ (G2 C).left), m₁ ≫ m₂ = m → ∀ (w₂ : LB.Iso (abelian₂ B MB) ((abelian₂ C MC).pull m₂)), w₂.IsGen → ∀ (w₁ : LB.Iso (abelian₂ A MA) ((abelian₂ B MB).pull m₁)), w₁.IsGen → ∃ w : LB.Iso (abelian₂ A MA) ((abelian₂ C MC).pull m), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 A).left) (z : Z) JA JB JC, Good MA z JA → Good MB z JB → Good MC z JC → lamVal w p z JC JA = lamVal w₁ p z JB JA * lamVal w₂ (p ≫ m₁) z JC JB := by
  intro SA SB SC A _ _ B _ _ C _ _ MA MB MC hA hB hC m₁ m₂ m hm w₂ h₂ w₁ h₁
  subst hm
  have lA : (abelian₂ A MA).IsLB := DVR.linComb_isLB _ hA _ _
  have lB : (abelian₂ B MB).IsLB := DVR.linComb_isLB _ hB _ _
  have lC : (abelian₂ C MC).IsLB := DVR.linComb_isLB _ hC _ _
  have p₂ := (isGen_iff _).1 h₂
  have p₁ := (isGen_iff _).1 h₁
  obtain ⟨w, T⟩ := exists_comp lB w₂ w₁ p₂ p₁ lC lA
  refine ⟨w, (isGen_iff _).2 (T.pgen_comp lB p₂ p₁), fun Z p z JA JB JC gA gB gC => ?_⟩
  have t := T Z p z (fun k => JC ((p ≫ m₁ ≫ m₂) ≫ lamφ C k))
    (fun k => JB ((p ≫ m₁) ≫ lamφ B k)) (fun k => JA (p ≫ lamφ A k))
    (Set.mem_iInter.2 fun k => gC ((p ≫ m₁ ≫ m₂) ≫ lamφ C k))
    (Set.mem_iInter.2 fun k => gB ((p ≫ m₁) ≫ lamφ B k))
    (Set.mem_iInter.2 fun k => gA (p ≫ lamφ A k))
  rw [mul_comm]
  show Geo.Tor.gw w p z (fun k => JC (p ≫ (m₁ ≫ m₂) ≫ lamφ C k)) (fun k => JA (p ≫ lamφ A k)) =
    Geo.Tor.gw w₂ (p ≫ m₁) z (fun k => JC ((p ≫ m₁) ≫ m₂ ≫ lamφ C k)) (fun k => JB ((p ≫ m₁) ≫ lamφ B k)) *
    Geo.Tor.gw w₁ p z (fun k => JB (p ≫ m₁ ≫ lamφ B k)) (fun k => JA (p ≫ lamφ A k))
  simp only [Category.assoc] at t ⊢
  exact t

end GlobalTheory.LamComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoValueOneZeroFirstFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

open GlobalTheory.PolDeg GlobalTheory.LamRigid GlobalTheory.LamBiext

noncomputable section

namespace GlobalTheory.MumRigidZero

theorem comp_one_pt {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]

theorem one_comp_hom {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : X ⟶ M) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem lift_comp_left {S : Scheme.{0}} {B₀ B : Over S} (a b : B₀ ⟶ B) {T : Over S} (p q : T ⟶ B₀) :
    (lift p q).left ≫ (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : B₀ ⊗ B₀ ⟶ B ⊗ B).left =
      (lift (p ≫ a) (q ≫ b)).left := by
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]

theorem lamVal_one_left : ∀ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B] (M₀ : LB B₀.left) (M : LB B.left), M₀.IsLB → M.IsLB → IsAbelianScheme B₀ → ∀ (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b] (w : LB.Iso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left)), w.IsGen → (∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1) → ∀ (T : Over S) (y : T ⟶ B₀) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) y).left z J J' = 1 := by
  intro S B₀ B _ _ _ _ M₀ M hM₀ hM hB₀ a b _ _ w hw hn T y z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hL' : (abelian₂ B₀ M₀).IsLB := DVR.linComb_isLB _ hM₀ _ _
  let β₂ := (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left
  let φ1 : Fin 1 → (B₀.left ⟶ (G2 B₀).left) := fun _ => (lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left
  let ε1 : Fin 1 → ℤ := fun _ => 1
  have fe' : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B₀) φ1) (flatε lamε ε1) := fun U _ h => by
    rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
    show 1 = (∏ i, h ((lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left ≫ lamφ B₀ i) ^ lamε i) ^ (1 : ℤ)
    rw [prod_lam, _root_.one_mul (𝟙 B₀)]
    apply Additive.ofMul.injective
    simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have fe : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => φ1 k ≫ β₂) (flatε lamε ε1) :=
    fun U _ h => by
      rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
      show 1 = (∏ i, h (((lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ)
      rw [lift_comp_left, prod_lam, one_comp_hom a, Category.id_comp, _root_.one_mul b]
      apply Additive.ofMul.injective
      simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel
  obtain ⟨g', hg', hv'⟩ := exists_gen hM₀ fe' (LB.oneGen M₀) (oneGen_isGen _)
  obtain ⟨g, hg, hv⟩ := exists_gen hM fe (LB.oneGen M) (oneGen_isGen _)
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ B₀.left) (z₀ : Z) J₀, Good M₀ z₀ J₀ →
      val (L := abelian₂ B₀ M₀) (nest M₀ (lamφ B₀) lamε φ1 ε1 g') r z₀ (ind B₀ J₀) = 1 := fun r z₀ J₀ hJ₀ => by
    refine (val_nest hg' r (good_ind hJ₀) hJ₀).trans ?_
    simp only [adj_ind hM₀ hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    exact (hv' _ r z₀ J₀ hJ₀).trans (val_one r)
  have Ft : ∀ {Z : Scheme.{0}} (r : Z ⟶ B₀.left) (z₀ : Z) J₀, Good M z₀ J₀ →
      val (L := abelian₂ B M) (nest M (lamφ B) lamε (fun k => φ1 k ≫ β₂) ε1 g) r z₀ (ind B J₀) = 1 :=
    fun r z₀ J₀ hJ₀ => by
      refine (val_nest hg r (good_ind hJ₀) hJ₀).trans ?_
      simp only [adj_ind hM hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
      exact (hv _ r z₀ J₀ hJ₀).trans (val_one r)
  have Fp : ∀ {T₀ : Over S} (c : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.ι)
      (J₀' : (T₀.left ⟶ B₀.left) → M₀.ι),
      pw w φ1 ε1 c.left z₀ (fun k => ind B J₀ (c.left ≫ φ1 k ≫ β₂)) (fun k => ind B₀ J₀' (c.left ≫ φ1 k)) =
        lamVal w (lift (1 : T₀ ⟶ B₀) c).left z₀ J₀ J₀' := by
    intro T₀ c z₀ J₀ J₀'
    rw [pw_eq, Fin.prod_univ_one]
    show lamVal w (c ≫ lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left z₀ J₀ J₀' ^ (1 : ℤ) = _
    rw [comp_lift, comp_one_pt, Category.comp_id, zpow_one]
  have he : (1 : 𝟙_ (Over S) ⟶ B₀).left ≫ B₀.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over S) ⟶ B₀)
  have E := rigid_pw w hw hL hL' φ1 ε1 (nest_isGen hg') (nest_isGen hg) B₀.hom _ he (hG _ _ hB₀).2
    (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM₀ y₀
      refine ⟨ind B J₁, ind B₀ J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
      rw [Ft _ y₀ J₁ hJ₁, Fp (1 : 𝟙_ (Over S) ⟶ B₀), Fa _ y₀ J₁' hJ₁', hn (𝟙_ (Over S)) y₀ J₁ J₁' hJ₁ hJ₁',
        _root_.mul_one])
    T.left y.left z (ind B J) (ind B₀ J') (good_ind hJ) (good_ind hJ')
  rw [Ft _ z J hJ, Fp y, Fa _ z J' hJ', _root_.mul_one] at E
  exact E.symm

end GlobalTheory.MumRigidZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoEqRosatiGeneratorMulComparison
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

theorem lam_eq_ros_mul_cmp : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R) (inc : D₀.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D₀.P.A) [IsMonHom inc] [IsMonHom pr] (ea fa ea' : D'.P.A ⟶ D'.P.A) [IsMonHom ea] [IsMonHom fa] [IsMonHom ea'], pr ≫ inc = ea → ∀ (w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ fa) : G2 D₀.P.A ⟶ G2 D'.P.A).left)), w.IsGen → (∀ (T : Over (Sp R)) (y : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι) (J' : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D'.P.L z J → Good D₀.P.L z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ D₀.P.A) y).left z J J' = 1) → ∀ (ur : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A ea ea') rosatiε)), ur.IsGen → (∀ (T : Over (Sp R)) (y : T ⟶ D'.P.A) (z : T.left) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val ur (lift (1 : T ⟶ D'.P.A) y).left z J = 1) → ∀ (χ' : D'.X) (χ : D₀.X) (q : 𝟙_ (Over (Sp R)) ⟶ D'.P.A), D₀.c χ ≫ inc ≫ fa = q → D'.c χ' = q ≫ ea' → ∀ (u : LB.Gen (CmpLB D' D₀ pr χ' χ)), Nrm u → ∀ (T : Over (Sp R)) (x : T ⟶ D'.P.A) (z : T.left) (J : (T.left ⟶ (D'.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) → (JN D' D₀).ι), Good (JN D' D₀) z J → GlobalTheory.PolDeg.lamVal w (lift (x ≫ pr) (toUnit T ≫ D₀.c χ)).left z (rl J) (rr J) = val ur (lift x (toUnit T ≫ q)).left z (rl J) * val u x.left z J := by
  intro R _ _ D₀ D' inc pr _ _ ea fa ea' _ _ _ hea w hw hw1 ur hur hur1 χ' χ q hq hq' u hu T x z J hJ
  have hN : (JN D' D₀).IsLB := jn_isLB D' D₀
  have h₁ := isPart_inl D'.P.L D₀.P.L
  have h₂ := isPart_inr D'.P.L D₀.P.L
  obtain ⟨t, ht, htv⟩ := exists_gen_of_iso h₁ h₂ w hw
  let m : D'.P.A.left ⟶ (G2 D₀.P.A).left := (lift pr (toUnit _ ≫ D₀.c χ)).left
  let n : D'.P.A.left ⟶ (G2 D'.P.A).left := (lift (𝟙 _) (toUnit _ ≫ q)).left
  let t₁ := LB.pullGen _ _ _ t m
  let t₂ := LB.mulGen _ _ _ _ _ (h₁.gen (LB.pullGen _ _ _ ur n)) u
  have hG := GlobalTheory.globalFns_holds
  have key := gen_unique' hN (u := t₁) (u' := t₂) ?fe D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (DVR.pullGen_isGen _ _ _ _ ht m) (DVR.mulGen_isGen _ _ _ _ _ _ _ (h₁.gen_isGen (DVR.pullGen_isGen _ _ _ _ hur n)) hu.1)
    ?ev T.left x.left z J hJ
  · have e₁ : x.left ≫ m = (lift (x ≫ pr) (toUnit T ≫ D₀.c χ)).left := by
      rw [← Over.comp_left, comp_lift, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit T)]
    have e₂ : x.left ≫ n = (lift x (toUnit T ≫ q)).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit T)]
    rw [val_pull hJ, htv _ _ z J hJ, val_mul hJ, h₁.val_gen _ _ z hJ, val_pull (h₁.good hJ), e₁, e₂] at key
    exact key
  case fe =>
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have mβ : m ≫ (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ fa)).left =
        (lift ea (toUnit _ ≫ q)).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, hea, Category.assoc, hq]
    have A1 : ∏ a₁ : ULift (Finset (Fin 2)), h (m ≫ (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ fa)).left ≫
        (psum D'.P.A (x2 D'.P.A) a₁.down).left ≫ coprod.inl) ^ ((-1 : ℤ) ^ (2 - a₁.down.card)) =
        h ((ea * (toUnit _ ≫ q)).left ≫ coprod.inl) * (h (ea.left ≫ coprod.inl))⁻¹ *
          (h ((toUnit _ ≫ q).left ≫ coprod.inl))⁻¹ * h ((1 : D'.P.A ⟶ D'.P.A).left ≫ coprod.inl) := by
      refine (Finset.prod_congr rfl fun k _ => ?_).trans
        (GlobalTheory.PrimCocycle.prod_lam ea (toUnit _ ≫ q) (fun g => h (g ≫ coprod.inl)))
      rw [← Category.assoc, ← Category.assoc, mβ]
    have A2 : ∏ a₂ : ULift (Finset (Fin 2)), h (m ≫ (psum D₀.P.A (x2 D₀.P.A) a₂.down).left ≫ coprod.inr) ^
        (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((pr * (toUnit _ ≫ D₀.c χ)).left ≫ coprod.inr) * (h (pr.left ≫ coprod.inr))⁻¹ *
          (h ((toUnit _ ≫ D₀.c χ).left ≫ coprod.inr))⁻¹ * h ((1 : D'.P.A ⟶ D₀.P.A).left ≫ coprod.inr))⁻¹ := by
      rw [← GlobalTheory.PrimCocycle.prod_lam pr (toUnit _ ≫ D₀.c χ) (fun g => h (g ≫ coprod.inr)), ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    have A3 := prod_ros ea ea' (𝟙 D'.P.A) (toUnit _ ≫ q) (fun g => h (g ≫ coprod.inl))
    beta_reduce at A3
    rw [A1, A2, A3, Fin.prod_univ_four, Fin.prod_univ_four]
    clear * - h hq'
    have pm : ∀ {X Y : Over (Sp R)} [GrpObj Y] (a b : X ⟶ Y), padd Y a b = a * b := fun _ _ => rfl
    simp only [DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, pm, ← Hom.one_def, hq', Category.id_comp,
      Category.assoc]
    simp only [zpow_one, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  case ev =>
    intro y I hI
    have o₀ : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have o' : (1 : 𝟙_ (Over (Sp R)) ⟶ D'.P.A) = η[D'.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have e₁ : eSec D'.P.A ≫ m = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) (toUnit _ ≫ D₀.c χ)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, IsMonHom.one_hom, ← Category.assoc,
        toUnit_unique (η[D'.P.A] ≫ toUnit _) (toUnit _), o₀]
    have e₂ : eSec D'.P.A ≫ n = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D'.P.A) (toUnit _ ≫ q)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D'.P.A] ≫ toUnit _) (toUnit _), o']
    rw [val_pull hI, htv _ _ y I hI, val_mul hI, h₁.val_gen _ _ y hI, val_pull (h₁.good hI), e₁, e₂]
    have a := hw1 (𝟙_ _) (toUnit _ ≫ D₀.c χ) y (rl I) (rr I) (h₁.good hI) (h₂.good hI)
    have b := hur1 (𝟙_ _) (toUnit _ ≫ q) y (rl I) (h₁.good hI)
    have c := hu.2 _ (𝟙 _) y I hI
    rw [Category.id_comp] at c
    rw [show isoVal w (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) (toUnit _ ≫ D₀.c χ)).left y (rl I) (rr I) = 1 from a, b, c,
      _root_.one_mul]

end GlobalTheory.Mum.Two
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenSumMapFlatSurjectiveQuasiCompact
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Desc

theorem irreducibleSpace_fibre_pullback (S : Scheme.{0}) (G' : Over S) [GrpObj G'] (hG : IsSemiAbelian G') {T : Scheme.{0}} (p : T ⟶ S)
    (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ T) :
    IrreducibleSpace (pullback ((Over.pullback p).obj G').hom t : Scheme.{0}) := by
  have : Smooth G'.hom := hG.smooth
  have : GeometricallyConnected G'.hom := hG.geomConnected
  have hc : ConnectedSpace (pullback (pullback.snd G'.hom p) t : Scheme.{0}) :=
    GeometricallyConnected.geometrically_connectedSpace (f := G'.hom) (t ≫ p) _ _
      ((IsPullback.of_hasPullback (pullback.snd G'.hom p) t).paste_horiz (IsPullback.of_hasPullback G'.hom p))
  have hs : Smooth (pullback.snd (pullback.snd G'.hom p) t) := inferInstance
  exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace K _ (pullback.snd (pullback.snd G'.hom p) t) hs hc

theorem isPullback_embL {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}
    (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    IsPullback (embL N p hp) (toS N p hp) (pullback.fst G.hom p) N.u := by
  have t : IsPullback (pullback.snd N.U.hom (pullback.fst π π ≫ π)) (toS N p hp ≫ pullback.fst N.U.hom π) (p ≫ π) N.U.hom := by
    rw [toS, pullback.lift_fst, hp]; exact (IsPullback.of_hasPullback _ _).flip
  have s : IsPullback (pullback.snd N.U.hom (pullback.fst π π ≫ π)) (toS N p hp) p (pullback.snd N.U.hom π) :=
    IsPullback.of_bot t (by rw [toS, pullback.lift_snd]) (IsPullback.of_hasPullback N.U.hom π).flip
  refine IsPullback.of_right ?_ (by rw [embL, pullback.lift_fst]) (IsPullback.of_hasPullback G.hom p).flip
  rw [embL, pullback.lift_snd, N.u_over]; exact s

theorem isOpenImmersion_embL {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}
    (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : IsOpenImmersion (embL N p hp) := by
  have := N.isOpen
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_embL N p hp).flip this

theorem sum_flat_surjective_quasiCompact : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', ∀ (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π), Flat (Desc.sum N p hp).left ∧ Surjective (Desc.sum N p hp).left ∧ QuasiCompact (Desc.sum N p hp).left := by
  intro R _ _ _ _ S π _ hπ _ G' _ _ hG N p hp
  have : Smooth G'.hom := hG.smooth
  have : IsSeparated G'.hom := hG.separated
  have : QuasiCompact N.U.hom := N.quasiCompact
  have ho : IsOpenImmersion (emb N p hp).left := isOpenImmersion_embL N p hp
  have hfl : Flat ((Over.pullback p).obj G').hom := by
    change Flat (pullback.snd G'.hom p); infer_instance
  refine ⟨_root_.GlobalTheory.Mum.FlatMul.main _ _ _ _ ho hfl, _root_.GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres _ _ _ _ ho (_root_.GlobalTheory.Mum.Desc.surjective_UT_hom R S π hπ G' N) (irreducibleSpace_fibre_pullback S G' hG p), ?_⟩
  have : QuasiCompact (UT N ⊗ UT N).hom := by
    change QuasiCompact (pullback.fst (UT N).hom (UT N).hom ≫ (UT N).hom)
    have h1 : QuasiCompact (UT N).hom := by
      change QuasiCompact (pullback.snd N.U.hom (pullback.fst π π ≫ π)); infer_instance
    have h2 : QuasiCompact (pullback.fst (UT N).hom (UT N).hom) := inferInstance
    infer_instance
  have : QuasiSeparated ((Over.pullback p).obj G').hom := by
    change QuasiSeparated (pullback.snd G'.hom p); infer_instance
  have hw : (Desc.sum N p hp).left ≫ ((Over.pullback p).obj G').hom = (UT N ⊗ UT N).hom := Over.w _
  have : QuasiCompact ((Desc.sum N p hp).left ≫ ((Over.pullback p).obj G').hom) := by rw [hw]; infer_instance
  exact QuasiCompact.of_comp _ (((Over.pullback p).obj G').hom)
end GlobalTheory.Mum.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMap
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem evA_subst_and_map : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], (∀ (τ : Type) [Finite τ] (φ : MvPowerSeries τ k →ₐ[k] A), (∀ t, IsNilpotent (φ (X t))) → ∀ a : σ → MvPowerSeries τ k, (∀ i, constantCoeff (a i) = 0) → ∀ (y : σ → A) (hy : ∀ i, IsNilpotent (y i)), (∀ i, φ (a i) = y i) → ∀ f : MvPowerSeries σ k, φ (subst a f) = evA k y hy f) ∧ ∀ (B : Type) [CommRing B] [Algebra k B] (g : A →ₐ[k] B) (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (y : σ → B) (hy : ∀ i, IsNilpotent (y i)), (∀ i, g (x i) = y i) → ∀ f : MvPowerSeries σ k, g (evA k x hx f) = evA k y hy f := by
  intro k _ σ _ A _ _
  refine ⟨?_, ?_⟩
  · intro τ _ φ _ a ha y hy hφa f
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    have key : evA k y hy = φ.comp (substAlgHom hs) := by
      refine _root_.GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent k σ A _ _ (fun i => ?_) (fun i => ?_)
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A y hy i]; exact hy i
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A y hy i, AlgHom.comp_apply, coe_substAlgHom, subst_X hs, hφa]
    rw [key, AlgHom.comp_apply, coe_substAlgHom]
  · intro B _ _ g x hx y hy hg f
    have key : evA k y hy = g.comp (evA k x hx) := by
      refine _root_.GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent k σ B _ _ (fun i => ?_) (fun i => ?_)
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ B y hy i]; exact hy i
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ B y hy i, AlgHom.comp_apply, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A x hx i, hg]
    rw [key, AlgHom.comp_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackAddAndPrimeSmulIdStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedExtensionPullback_add_and_prime_smul_id : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G H : PDivGroup p R), (∀ f g : G ⟶ H, rigExtMap (f + g) = rigExtMap f + rigExtMap g) ∧ rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 := by
  first | exact @GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id | exact GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id | (intros; apply GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id <;> assumption)
end

