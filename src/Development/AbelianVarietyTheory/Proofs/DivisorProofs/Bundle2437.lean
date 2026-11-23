module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVRingOnNear
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc

theorem USetup.exists_polAV_ringOn_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∀ (U₀ : X.M.Z.Opens) (u₀ : Sp (ratHull (X.M.ringOn U₀)) ⟶ Xo.XF cf), IsAffineOpen U₀ → w₀ ∈ U₀ → spMap (ratHull (X.M.ringOn U₀)).val.toRingHom ≫ u₀ = X.uΩ → ∃ (U₁ : X.M.Z.Opens) (h : X.M.ringOn U₀ ≤ X.M.ringOn U₁) (P₁ : PolAV (Sp (X.M.ringOn U₁))), U₁ ≤ U₀ ∧ IsAffineOpen U₁ ∧ w₀ ∈ U₁ ∧ UOver Xo cf P₁ (toRat (X.M.ringOn U₁)) (spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u₀) :=
  fun E _ _ _ H Dw _ l Xo cf C X w₀ hw U₀ u₀ hU hwU _ =>
    LocSpread.exists_uOver_ringOn E H Dw l Xo cf C X U₀ u₀ w₀ hU hwU hw

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionNonvanishingClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ExtNZ

theorem exists_sec_nz : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ t : SAB H (Sp R), Nonempty (PELUnif (IsLocalRing.maximalIdeal R) t) → ∃ σ : SecAt t.G t.PP.L (𝟙 (Sp R)), NZ t.G t.PP.L (𝟙 (Sp R)) σ := by
  intro E _ _ _ H R _ _ _ hB t ⟨P⟩
  haveI := t.comm
  haveI : GeometricallyConnected t.G.hom := t.semi.geomConnected
  haveI : IsNoetherianRing R := hB.1.1
  have hLaws := GlobalTheory.abelianSchemeLaws_all

  obtain ⟨th, hth, -⟩ := GlobalTheory.PsiRing.exists_basis_fibNZ hLaws.2.secTwist R P.D.toPre
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : P.D.toPre.SecB 1 0, ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good P.D.toPre.P.L z J →
      sval th r z J = sval f₀ (r ≫ (snd (𝟙_ _) P.D.toPre.P.A).left) z J := by
    refine GlobalTheory.PsiExpansion.exists_sec_of_retract P.D.toPre.P.isLB _ _
      (GlobalTheory.PsiExpansion.snd_lift_unit P.D.toPre.P.A) (fun i => ?_) th
    fin_cases i
    · exact congrArg CommaMorphism.left (lift_snd (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A))
    · refine congrArg CommaMorphism.left (show lift (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A) ≫
        padd P.D.toPre.P.A (snd _ _) (toUnit _ ≫ P.D.toPre.c 0) = padd P.D.toPre.P.A (𝟙 _) (toUnit _ ≫ P.D.toPre.c 0) from ?_)
      simp only [padd, ← Category.assoc, comp_lift, lift_snd, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A) ≫ toUnit _ ≫ P.D.toPre.c 0 = toUnit _ ≫ P.D.toPre.c 0 from ?_)
      rw [← Category.assoc, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A) ≫ toUnit _ ≫ η[P.D.toPre.P.A] = toUnit _ ≫ η[P.D.toPre.P.A] from ?_)
      rw [← Category.assoc, comp_toUnit]
  obtain ⟨z₀, hz₀, hn₀⟩ := hth (IsLocalRing.closedPoint R)
  have hx : P.D.toPre.P.A.hom ((snd (𝟙_ (Over (Sp R))) P.D.toPre.P.A).left z₀) = IsLocalRing.closedPoint R :=
    (congrArg (fun q => q z₀) (Over.w (snd (𝟙_ (Over (Sp R))) P.D.toPre.P.A))).trans hz₀
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' P.D.toPre.P.isLB z₀
  have hu : IsUnit (sval th (𝟙 _) z₀ J) := (isUnit_sval_iff th (𝟙 _) z₀ hJ).2 hn₀
  rw [hf₀ _ _ z₀ J hJ, Category.id_comp] at hu
  have hxn := (isUnit_sval_iff f₀ _ z₀ hJ).1 hu

  obtain ⟨σ, fam, hfam0, hσ, hmem, -⟩ := GlobalTheory.ThetaUnit.exists_theta hLaws.1.globalFns hLaws.1.secBaseChange
    le_rfl P.U f₀ ⟨_, hx, hxn⟩
  have key : ∃ σ : H0 P.U.LG.L 1, ∃ g, t.G.hom g = IsLocalRing.closedPoint R ∧ g ∈ nonzeroLocus σ :=
    ⟨σ, GlobalTheory.ThetaUnit.exists_mem_nonzeroLocus le_rfl P.U.toUnifPre (hσ 0)
      (by rw [hfam0]; exact ⟨_, hx, hxn⟩) hmem⟩
  rw [P.bundle] at key
  obtain ⟨σ, g, hg, hn⟩ := key
  refine ⟨GlobalTheory.TorRef.upSec t.G σ, GlobalTheory.Ex.OnModel.toBase t.G g, ?_, ?_⟩
  · have a : GlobalTheory.Ex.OnModel.toBase t.G ≫ (fst (Over.mk (𝟙 (Sp R))) t.G).left = t.G.hom := by
      rw [GlobalTheory.Ex.OnModel.toBase, ← Over.comp_left, lift_fst]; rfl
    rw [← Scheme.Hom.comp_apply, a]
    exact hg
  · refine GlobalTheory.Ex.OnModel.mem_nonzeroLocus_pullTo σ _ _ ?_
    rw [← Scheme.Hom.comp_apply, GlobalTheory.Ex.OnModel.toBase_snd]
    exact hn

end GlobalTheory.UMin.ExtNZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPoincareKernelComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.KerPoincare

open GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem lift_mul_lift {T : Over S} (u v u' v' : T ⟶ A) : lift u v * lift u' v' = lift (u * u') (v * v') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp, lift_fst, lift_fst, lift_fst]
  · rw [MonObj.mul_comp, lift_snd, lift_snd, lift_snd]

theorem one_eq_lift {T : Over S} : (1 : T ⟶ A ⊗ A) = lift (1 : T ⟶ A) 1 := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.one_comp, lift_fst]
  · rw [MonObj.one_comp, lift_snd]

theorem lam_diag (p : Pic (A ⊗ A).left)
    (hmul : ∀ {T : Over S} (X X' Y : T ⟶ A ⊗ A), lam p (X * X') Y = lam p X Y + lam p X' Y)
    (r₁ : ∀ {T : Over S} (v : T ⟶ A), pull (lift (1 : T ⟶ A) v).left p = 0)
    (r₂ : ∀ {T : Over S} (u : T ⟶ A), pull (lift u (1 : T ⟶ A)).left p = 0)
    {T : Over S} (a b : T ⟶ A) :
    lam (pull (lift (𝟙 A) (𝟙 A)).left p) a b = pull (lift a b).left p + pull (lift b a).left p := by
  rw [lam_pull, comp_lift, comp_lift]
  simp only [Category.comp_id]
  have ha : lift a a = lift a (1 : T ⟶ A) * lift 1 a := by rw [lift_mul_lift, _root_.mul_one, _root_.one_mul]
  have hb : lift b b = lift b (1 : T ⟶ A) * lift 1 b := by rw [lift_mul_lift, _root_.mul_one, _root_.one_mul]
  have hmul' : ∀ (X Y Y' : T ⟶ A ⊗ A), lam p X (Y * Y') = lam p X Y + lam p X Y' := fun X Y Y' ↦ by
    rw [lam_comm, hmul, lam_comm, lam_comm p Y']
  rw [ha, hb, hmul, hmul', hmul']
  simp only [lam, lift_mul_lift, one_eq_lift, _root_.mul_one, _root_.one_mul, r₁, r₂]
  abel

end GlobalTheory.KerPoincare

namespace GlobalTheory.KerPoincare

open GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_pow_eq_one_of_kernel : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ))
      (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q →
    Submodule.span ℝ (Set.range Q) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Q.range) →
    (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) →
    ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A,
      (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) →
      ∃ k : ℕ, 0 < k ∧ x ^ k = 1 := by
  intro A _ _ g hA hsm P hP hr₁ hr₂ hsym hamp e La _ Q EF he _ _ _ _ x hx
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  obtain ⟨Λ, hd, hf, hk⟩ := GlobalTheory.ExpKernel.kernel_isFullLattice (Sp ℂ) A g hA hsm (𝟙 _) e he
  obtain ⟨L₀, u₀, -⟩ := GlobalTheory.exists_holUnif_of_isExp A g e Λ he hd hf hk
  obtain ⟨u, Hm, χ, -, hAH⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ _ hL
  have pos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ hL hamp g u Hm χ hAH.1 hAH.2.1 hAH.2.2
  obtain ⟨PP, ψ, ρ, N, hN, hψ, hρ, h₁, h₂, h₃⟩ := GlobalTheory.PosAHIsog.exists_isog_principal_lam g A hA _ u Hm χ hL
    (GlobalTheory.TorusRM.isAH_of_isFactorAH hAH pos)
  refine ⟨N * N, Nat.mul_pos hN hN,
    GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial A hA _ hL PP ψ ρ N hψ hρ h₁ h₂ h₃ _ x ?_⟩
  have hG : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme ℂ (A ⊗ A) hG P hP
  have r₁ : ∀ {T : Over (Sp ℂ)} (v : T ⟶ A), pull (lift (1 : T ⟶ A) v).left (cls P hP) = 0 := fun {T} v ↦ by
    have hv : lift (1 : T ⟶ A) v = v ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    rw [hv, Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _),
      (cls_eq_zero_iff (pull_isLB hP _)).2 hr₁, map_zero]
  have r₂ : ∀ {T : Over (Sp ℂ)} (v : T ⟶ A), pull (lift v (1 : T ⟶ A)).left (cls P hP) = 0 := fun {T} v ↦ by
    have hv : lift v (1 : T ⟶ A) = v ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    rw [hv, Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _),
      (cls_eq_zero_iff (pull_isLB hP _)).2 hr₂, map_zero]
  have e₀ : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) := by
    rw [← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_iff hP (pull_isLB hP _)).2 hsym
  have hsymm : ∀ {T : Over (Sp ℂ)} (u v : T ⟶ A),
      pull (lift u v).left (cls P hP) = pull (lift v u).left (cls P hP) := fun {T} u v ↦ by
    conv_lhs => rw [e₀]
    rw [← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  have hxA : pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left (cls P hP) = 0 := by
    rw [← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_zero_iff _).2 hx
  refine (cls_eq_zero_iff (pull_isLB (LB.isLB_linComb hL _ _) _)).1
    ((GlobalTheory.RealMult.Elliptic.cls_pull_lam hL _ _ _).trans ?_)
  rw [cls_pull hP _ hL,
    lam_diag (cls P hP) (fun X X' Y ↦ lam_mul_left hP hΘ X X' Y) r₁ r₂, hsymm, hxA, add_zero]

end GlobalTheory.KerPoincare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreimageOfLocalPreimagesInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem imgLoc_app_res {X Y : Scheme.{0}} (a : Y ⟶ X) {U U' : X.Opens} (i : U' ⟶ U)
    (j : a ⁻¹ᵁ U' ⟶ a ⁻¹ᵁ U) (y : Γ(X, U)) :
    (Y.presheaf.map j.op).hom ((a.app U).hom y) = (a.app U').hom ((X.presheaf.map i.op).hom y) := by
  have hj : j = (TopologicalSpace.Opens.map a.base).map i := Subsingleton.elim _ _
  subst hj
  have e := a.naturality i.op
  have := congrArg (fun f => f.hom y) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

theorem imgLoc_exists {X Y : Scheme.{0}} (a : Y ⟶ X) (hinj : ∀ U : X.Opens, Function.Injective (a.app U).hom)
    (V : X.Opens) {B : Type} (W : B → X.Opens) (hV : V ≤ ⨆ b, W b) (x : Γ(Y, a ⁻¹ᵁ V))
    (hx : ∀ b, ∃ y : Γ(X, V ⊓ W b), (a.app (V ⊓ W b)).hom y =
      (Y.presheaf.map (homOfLE (extLI_preimage_mono a (inf_le_left : V ⊓ W b ≤ V))).op).hom x) :
    ∃ y : Γ(X, V), (a.app V).hom y = x := by
  choose y hy using hx
  have hcov : V ≤ ⨆ b, V ⊓ W b := by
    calc V ≤ V ⊓ ⨆ b, W b := le_inf le_rfl hV
      _ = ⨆ b, V ⊓ W b := inf_iSup_eq _ _
  have key : ∀ b (U' : X.Opens) (i : U' ⟶ V ⊓ W b), (a.app U').hom ((X.presheaf.map i.op).hom (y b)) =
      (Y.presheaf.map (homOfLE (extLI_preimage_mono a (i.le.trans inf_le_left))).op).hom x := by
    intro b U' i
    rw [← imgLoc_app_res a i (homOfLE (extLI_preimage_mono a i.le)), hy b, extLI_res_res]
  have compat : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun b => V ⊓ W b) y := by
    intro b c
    apply hinj
    exact (key b _ _).trans (key c _ _).symm
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun b => V ⊓ W b) V
    (fun b => homOfLE inf_le_left) hcov y compat
  have hcovY : a ⁻¹ᵁ V ≤ ⨆ b, a ⁻¹ᵁ (V ⊓ W b) := by
    intro z hz
    obtain ⟨b, hb⟩ := (TopologicalSpace.Opens.mem_iSup).1 (hcov hz)
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨b, hb⟩
  have hs' : ∀ b, (X.presheaf.map (homOfLE inf_le_left : V ⊓ W b ⟶ V).op).hom s = y b := hs
  refine ⟨s, ?_⟩
  refine Y.sheaf.eq_of_locally_eq' (fun b => a ⁻¹ᵁ (V ⊓ W b)) (a ⁻¹ᵁ V)
    (fun b => homOfLE (extLI_preimage_mono a inf_le_left)) hcovY _ _ (fun b => ?_)
  have h2 := imgLoc_app_res a (homOfLE inf_le_left : V ⊓ W b ⟶ V)
    (homOfLE (extLI_preimage_mono a inf_le_left)) s
  rw [hs' b, hy b] at h2
  exact h2

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveWithCotangentOfDualHeightOne
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem exists_primitive_dUnit_eq : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H],
    (∀ φ ∈ augIdeal K (CartierDual K H), φ ^ p = 0) →
    ∀ w : Cot K H, ∃ b : H, cobOne K H b = 0 ∧ dUnit (R := K) b = w := by
  intro p _ K H _ _ _ _ _ _ hnil w
  have hgen := _root_.GlobalTheory.HeightOneDual.adjoin_primitive_eq_top p K (CartierDual K H) hnil
  set e := CartierDual.bidual K H
  have hH : Algebra.adjoin K {b : H | cobOne K H b = 0} = ⊤ := by
    let f : CartierDual K (CartierDual K H) →ₐ[K] H :=
      ((e.symm : CartierDual K (CartierDual K H) →ₐc[K] H) : CartierDual K (CartierDual K H) →ₐ[K] H)
    have himg : f '' {φ | cobOne K (CartierDual K (CartierDual K H)) φ = 0} ⊆
        {b : H | cobOne K H b = 0} := by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [Set.mem_setOf_eq] at hφ ⊢
      show cobOne K H ((e.symm : CartierDual K (CartierDual K H) →ₐc[K] H) φ) = 0
      rw [← pullTwo_cobOne, hφ, map_zero]
    rw [eq_top_iff]
    intro x _
    refine Algebra.adjoin_mono himg ?_
    rw [Algebra.adjoin_image]
    refine ⟨e x, ?_, ?_⟩
    · rw [hgen]; trivial
    · exact e.symm_apply_apply x
  let P : Submodule K H := LinearMap.ker (cobOne K H)
  let S : Submodule K (Cot K H) := P.map (AugCot.d (counitAlgHom K H))
  have hS : ∀ a ∈ Algebra.adjoin K {b : H | cobOne K H b = 0}, dUnit (R := K) a ∈ S := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.mem_map_of_mem (p := P) hx
    | algebraMap r => rw [dUnit, AugCot.d_algebraMap]; exact S.zero_mem
    | add x y _ _ hx hy => rw [dUnit, map_add (f := _)]; exact S.add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [dUnit, AugCot.d_mul]
      exact S.add_mem (S.smul_mem _ hy) (S.smul_mem _ hx)
  obtain ⟨a, rfl⟩ := AugCot.d_surjective (counitAlgHom K H) w
  obtain ⟨b, hb, hbd⟩ := hS a (by rw [hH]; trivial)
  exact ⟨b, hb, hbd⟩

end GlobalTheory.PDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationMumfordBundleAlgClosu
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PrincipalBaseChange

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A] {f : S' ⟶ S}

theorem lift_comp_sq (w : pullback.fst A.hom f ≫ A.hom = ((Over.pullback f).obj A).hom ≫ f)
    {X : Over S'} (a b : X ⟶ (Over.pullback f).obj A) :
    (lift a b).left ≫ (lift (pushPt w (fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)))
        (pushPt w (snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)))).left =
      (lift (pushPt w a) (pushPt w b)).left := by
  apply pullback.hom_ext
  · change _ ≫ _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst]
    show (lift a b).left ≫ ((fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)).left ≫ pullback.fst A.hom f) = a.left ≫ pullback.fst A.hom f
    rw [← Category.assoc, ← Over.comp_left, lift_fst]
  · change _ ≫ _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd]
    show (lift a b).left ≫ ((snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)).left ≫ pullback.fst A.hom f) = b.left ≫ pullback.fst A.hom f
    rw [← Category.assoc, ← Over.comp_left, lift_snd]

theorem lift_comp_sq' (w : pullback.fst A.hom f ≫ A.hom = ((Over.pullback f).obj A).hom ≫ f)
    {X : Over S'} {Y : Over S} (U : Over.mk (X.hom ≫ f) ⟶ Y) (a b : X ⟶ (Over.pullback f).obj A) (c d : Y ⟶ A)
    (ha : pushPt w a = U ≫ c) (hb : pushPt w b = U ≫ d) :
    (lift a b).left ≫ (lift (pushPt w (fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)))
        (pushPt w (snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)))).left =
      U.left ≫ (lift c d).left := by
  rw [lift_comp_sq, ← Over.comp_left, comp_lift, ha, hb]

end GlobalTheory.PrincipalBaseChange

namespace GlobalTheory.PrincipalBaseChange

theorem exists_principal_algClosure : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∃ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB ∧ Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) ∧ Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L := by
  intro K _ _ A _ _ hA PP hP hs hb ha hk Ω _ _ _ κ hκ
  set f := spMap (algebraMap K Ω) with hf
  set AΩ := (Over.pullback f).obj A with hAΩ
  have h := isGrpPullback_pullback A f
  have w := h.1.w
  obtain rfl := GlobalTheory.LamPull.isSquare_unique hκ (GlobalTheory.LamPull.exists_isSquare w)
  have hAΩab : IsAbelianScheme AΩ := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hP' := pull_isLB hP (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left
  have pmul : ∀ {T : Over (Sp Ω)} (x y : T ⟶ AΩ), pushPt w (x * y) = pushPt w x * pushPt w y :=
    fun x y => map_mul (pushHom h _) x y
  refine GlobalTheory.PrincipalOfPairing.exists_principal Ω AΩ hAΩab _ hP' ?_ ?_ ?_ ?_
  · obtain ⟨u, hu⟩ := hs
    refine gen_chartPull (chartPullLinComb PP _ _ _ _ (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left fun k => ?_) u hu
    fin_cases k
    · exact lift_comp_sq' w _ (snd AΩ AΩ) (fst AΩ AΩ) (snd A A) (fst A A) (lift_snd _ _).symm (lift_fst _ _).symm
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · obtain ⟨u, hu⟩ := hb
    let U3 : Over.mk ((AΩ ⊗ (AΩ ⊗ AΩ)).hom ≫ f) ⟶ A ⊗ (A ⊗ A) :=
      lift (pushPt w (fst AΩ (AΩ ⊗ AΩ)))
        (lift (pushPt w (snd AΩ (AΩ ⊗ AΩ) ≫ fst AΩ AΩ)) (pushPt w (snd AΩ (AΩ ⊗ AΩ) ≫ snd AΩ AΩ)))
    refine gen_chartPull (chartPullLinComb PP _ _ _ _ U3.left fun k => ?_) u hu
    fin_cases k
    · refine lift_comp_sq' w U3 _ _ _ _ ?_ (by simp [U3])
      rw [comp_mul, pmul]
      simp [U3]
    · exact lift_comp_sq' w U3 _ _ _ _ (by simp [U3]) (by simp [U3])
    · have e1 : snd AΩ (AΩ ⊗ AΩ) = lift (snd AΩ (AΩ ⊗ AΩ) ≫ fst AΩ AΩ) (snd AΩ (AΩ ⊗ AΩ) ≫ snd AΩ AΩ) := by simp
      have e2 : snd A (A ⊗ A) = lift (snd A (A ⊗ A) ≫ fst A A) (snd A (A ⊗ A) ≫ snd A A) := by simp
      show (snd AΩ (AΩ ⊗ AΩ)).left ≫ _ = U3.left ≫ (snd A (A ⊗ A)).left
      rw [e1, e2]
      exact lift_comp_sq' w U3 _ _ _ _ (by simp [U3]) (by simp [U3])
  · have e : (lift (𝟙 AΩ) (𝟙 AΩ)).left ≫ (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left =
        pullback.fst A.hom f ≫ (lift (𝟙 A) (𝟙 A)).left := by
      rw [lift_comp_sq' w (pushPt w (𝟙 AΩ)) _ _ (𝟙 A) (𝟙 A) (by simp) (by simp)]
      simp [pushPt]
    refine GlobalTheory.AmpleLocalBase.relAmple_baseChange h.1 (pull_isLB hP _) (pull_isLB hP' _) ?_ ha
    refine LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _)
      (GlobalTheory.Mum.lbIso_pull_pull_comp hP _ _) ?_
    rw [e]
    exact (GlobalTheory.Mum.lbIso_pull_pull_comp hP _ _).symm
  · intro T x ⟨t, ht⟩
    let T₀ : Over (Sp K) := Over.mk (T.hom ≫ f)
    let x₀ : T₀ ⟶ A := pushPt w x
    let sT : Over.mk ((AΩ ⊗ T).hom ≫ f) ⟶ T₀ := Over.homMk (snd AΩ T).left (by
      show (snd AΩ T).left ≫ T.hom ≫ f = (AΩ ⊗ T).hom ≫ f
      rw [← Category.assoc, Over.w (snd AΩ T)])
    let V0 : Over.mk ((AΩ ⊗ T).hom ≫ f) ⟶ A ⊗ T₀ := lift (pushPt w (fst AΩ T)) sT
    have e : (lift (snd AΩ T ≫ x) (fst AΩ T)).left ≫ (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left =
        V0.left ≫ (lift (snd A T₀ ≫ x₀) (fst A T₀)).left := by
      refine lift_comp_sq' w V0 _ _ _ _ ?_ (by simp [V0])
      rw [lift_snd_assoc]
      exact Over.OverMorphism.ext (by simp [pushPt, sT, x₀])
    have hV : IsIso V0.left := by
      have e3 : V0.left = (pullbackLeftPullbackSndIso A.hom f T.hom).hom := by
        apply pullback.hom_ext
        · change V0.left ≫ pullback.fst A.hom (T.hom ≫ f) =
            (pullbackLeftPullbackSndIso A.hom f T.hom).hom ≫ pullback.fst A.hom (T.hom ≫ f)
          rw [pullbackLeftPullbackSndIso_hom_fst]
          change V0.left ≫ (fst A T₀).left = _
          rw [← Over.comp_left, lift_fst]
          rfl
        · change V0.left ≫ pullback.snd A.hom (T.hom ≫ f) =
            (pullbackLeftPullbackSndIso A.hom f T.hom).hom ≫ pullback.snd A.hom (T.hom ≫ f)
          rw [pullbackLeftPullbackSndIso_hom_snd]
          change V0.left ≫ (snd A T₀).left = _
          rw [← Over.comp_left, lift_snd]
          rfl
      rw [e3]
      infer_instance
    have g1 := (exists_gen_pull_pull_iff hP _ _).1 ⟨t, ht⟩
    rw [e] at g1
    obtain ⟨t1, ht1⟩ := g1
    obtain ⟨t2, ht2⟩ := gen_chartPull (chartPullPull (PP.pull (V0.left ≫ (lift (snd A T₀ ≫ x₀) (fst A T₀)).left))
      (inv V0.left)) t1 ht1
    have g3 := (exists_gen_pull_pull_iff hP _ (inv V0.left)).1 ⟨t2, ht2⟩
    rw [IsIso.inv_hom_id_assoc] at g3
    have hx0 : x₀ = toUnit T₀ ≫ η[A] := hk T₀ x₀ g3
    have e1 : pushPt w (toUnit T ≫ η[AΩ]) = toUnit T₀ ≫ η[A] := by
      rw [← Hom.one_def, ← Hom.one_def]
      exact map_one (pushHom h T)
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · change x₀.left = (pushPt w (toUnit T ≫ η[AΩ])).left
      rw [hx0, e1]
    · rw [Over.w x, Over.w (toUnit T ≫ η[AΩ])]

end GlobalTheory.PrincipalBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegArcDataAtUniformiserStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullDeg_arcData_at_uniformiser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V) (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) (ϖ : T.V) (hϖ : Irreducible ϖ) (hX : Nontrivial D.toPre.X) (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ GlobalTheory.TraitArc.beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) (hLie : GlobalTheory.TraitArc.LieCl D oD Dm β b) (hTate : GlobalTheory.TraitArc.TateCl D oD hϖ Dm β b hdiv pA pM) (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp T.V ⟶ Y.X), Y.HasArcData (GlobalTheory.TraitArc.arc D oD hϖ β b hX hw hdiv pA pM hLie hTate) (maximalIdeal T.V) (RingHom.id T.V) ϖ y → ∃ (t : SAB H (Sp T.V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), Nonempty (IsPullDeg (RingHom.id T.V) D.toPre P.D.toPre) := by
  first | exact @GlobalTheory.TraitArcMatch.exists_isPullDeg_arc | exact GlobalTheory.TraitArcMatch.exists_isPullDeg_arc | (intros; apply GlobalTheory.TraitArcMatch.exists_isPullDeg_arc <;> assumption)
end

