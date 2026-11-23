module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesSiegelLevelStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullDegIdOfCommonFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ

namespace GlobalTheory.FieldDescent

open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.GenSpread

variable {K Ω : Type} [Field K] [Field Ω] {l : K →+* Ω} {D₁ D₂ : DegPre K} {D : DegPre Ω}

theorem lbIso_of_common_pull (h₁ : IsPullDeg l D₁ D) (h₂ : IsPullDeg l D₂ D) {Φ : D₂.P.A.left ⟶ D₁.P.A.left}
    (hΦ : proj h₂ ≫ Φ = proj h₁) : LBIso D₂.P.L (D₁.P.L.pull Φ) := by
  have e : pullback.fst D₂.P.A.hom (specOf l) = h₂.e.inv.left ≫ proj h₂ := by
    rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    exact (Category.id_comp _).symm
  have e' : pullback.fst D₂.P.A.hom (specOf l) ≫ Φ = h₂.e.inv.left ≫ proj h₁ :=
    (congrArg (· ≫ Φ) e).trans ((Category.assoc _ _ _).trans (congrArg (h₂.e.inv.left ≫ ·) hΦ))
  exact PolIsoDescent.lbIso_descend globalFns_holds (specOf l) D₂.P.A D₂.P.isAb D₂.P.isLB (pull_isLB D₁.P.isLB Φ)
    (LBIso.trans (pull_isLB D₂.P.isLB _) (pull_isLB D.P.isLB _) (pull_isLB (pull_isLB D₁.P.isLB _) _)
      (lbIso_pull_of_lbIso ⟨h₂.w, h₂.w_gen⟩ h₂.e.inv.left e).symm
      (LBIso.trans (pull_isLB D.P.isLB _) (pull_isLB D₁.P.isLB _) (pull_isLB (pull_isLB D₁.P.isLB _) _)
        (lbIso_pull_of_lbIso ⟨h₁.w, h₁.w_gen⟩ h₂.e.inv.left e') (lbIso_pull_pull D₁.P.isLB _ rfl)))

theorem om_eq (h₁ : IsPullDeg l D₁ D) {ψ : D.P.A.left ⟶ D₁.P.A.left} (v : LB.Iso D.P.L (D₁.P.L.pull ψ))
    (hψ : ψ = proj h₁) (gv : PGen v)
    (pv : PMaps v (K := PUnit) (fun _ => eSec D.P.A) (fun _ => eSec D₁.P.A) (fun _ => 1) D.rig D₁.rig (spMap l))
    {Z : Scheme.{0}} (z : Z) (J J') (q : Z ⟶ D.P.A.left) : om v z J J' q = om h₁.w z J J' q := by
  subst hψ
  rw [iso_unique_of_rig globalFns_holds D.P.A D.P.isAb D.P.isLB D₁.P.isLB ((isGen_iff v).2 gv) h₁.w_gen
    ((maps_iff v _ (fun _ => eSec D₁.P.A) _ D.rig D₁.rig (specOf l) _
      (rigPull_le (proj h₁) (specOf l) h₁.he D₁.P.L) (fun _ => rfl)).2 pv) h₁.w_rig]

end GlobalTheory.FieldDescent


open GlobalTheory.PsiEvenPull (proj) in
theorem GlobalTheory.nonempty_isPullDeg_id_of_common_pull : ∀ (K Ω : Type) [Field K] [Field Ω] (l : K →+* Ω) (D₁ D₂ : DegPre K) (D : DegPre Ω) (h₁ : IsPullDeg l D₁ D) (h₂ : IsPullDeg l D₂ D) (φ : D₂.P.A ≅ D₁.P.A), IsMonHom φ.hom → h₂.e.hom.left ≫ pullback.fst D₂.P.A.hom (specOf l) ≫ φ.hom.left = h₁.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf l) → Nonempty (IsPullDeg (RingHom.id K) D₁ D₂) := by
  intro K Ω _ _ l D₁ D₂ D h₁ h₂ φ hm hφ
  have hΦ : proj h₂ ≫ φ.hom.left = proj h₁ := (Category.assoc _ _ _).trans hφ
  have hs : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id (CommRingCat.of K)
  have gp : IsGrpPullback D₂.P.A D₁.P.A (spMap (RingHom.id K)) φ.hom.left :=
    (Geo.Tor.isGrpPullback_of_iso φ).congr hs.symm rfl
  have he : eSec D₂.P.A ≫ φ.hom.left = spMap (RingHom.id K) ≫ eSec D₁.P.A := (cubeMapOf gp).e_comm
  obtain ⟨w, gw', rw'⟩ := Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap (RingHom.id K)) D₁.P.A D₂.P.A φ.hom.left he
    ⟨D₁.P.L, D₁.rig, D₁.P.isLB, D₁.rig_gen⟩ ⟨D₂.P.L, D₂.rig, D₂.P.isLB, D₂.rig_gen⟩
    (FieldDescent.lbIso_of_common_pull h₁ h₂ hΦ)
  have pw' := (isGen_iff w).1 gw'
  have p₂ := (isGen_iff h₂.w).1 h₂.w_gen
  have r₀ := (maps_iff w _ (fun _ => eSec D₁.P.A) _ D₂.rig D₁.rig (spMap (RingHom.id K)) _
    (rigPull_le φ.hom.left (spMap (RingHom.id K)) he D₁.P.L) (fun _ => rfl)).1 rw'
  obtain ⟨v, T⟩ := exists_comp D₂.P.isLB w h₂.w pw' p₂ D₁.P.isLB D.P.isLB
  have r₂ := T.pmaps_comp D₂.P.isLB (fun _ => h₂.he) r₀ (FieldPull.pmaps_rig h₂)
  rw [← spMap_comp] at r₂
  have hom := fun {Z : Scheme.{0}} (z : Z) J J' q =>
    FieldDescent.om_eq h₁ v hΦ (T.pgen_comp D₂.P.isLB pw' p₂) r₂ z J J' q
  obtain ⟨f₁, f₂⟩ := PolIsoDescent.flat_surjective (spMap l)
  have : Epi (spMap l) := Flat.epi_of_flat_of_surjective _
  let xe : D₂.X ≃+ D₁.X := h₂.xe.symm.trans h₁.xe
  have hxe : ∀ y, xe (h₂.xe y) = h₁.xe y := fun y => congrArg h₁.xe (h₂.xe.symm_apply_apply y)
  have hc : ∀ x, (D₂.c x).left ≫ φ.hom.left = spMap (RingHom.id K) ≫ (D₁.c (xe x)).left := fun x => by
    obtain ⟨y, rfl⟩ := h₂.xe.surjective x
    rw [hxe, hs]
    refine Eq.trans ?_ (Category.id_comp _).symm
    refine (cancel_epi (spMap l)).1 ((Category.assoc _ _ _).symm.trans ?_)
    exact (congrArg (· ≫ φ.hom.left) (h₂.c_pr y).symm).trans ((Category.assoc _ _ _).trans
      ((congrArg ((D.c y).left ≫ ·) hΦ).trans (h₁.c_pr y)))
  have si : jK K ≫ spMap (RingHom.id K) = genMap (RingHom.id K).injective ≫ jK K :=
    (Category.id_comp _).symm.trans (fracMap_sq (RingHom.id K).injective)
  have si' : genMap (RingHom.id K).injective ≫ jK K = jK K :=
    si.symm.trans ((congrArg (jK K ≫ ·) hs).trans (Category.comp_id _))
  have sl := fracMap_sq l.injective
  obtain ⟨hD, -⟩ := FieldPull.exists_isPullDeg_of_val (RingHom.id K) D₁ D₂ gp w pw' r₀ xe hc
    (fun x z J₁ J₂ hJ₁ hJ₂ => by
      obtain ⟨y, rfl⟩ := h₂.xe.surjective x
      have hx : D₂.xK (h₂.xe y) ≫ φ.hom.left = genMap (RingHom.id K).injective ≫ D₁.xK (xe (h₂.xe y)) := by
        show (jK K ≫ (D₂.c _).left) ≫ _ = _ ≫ jK K ≫ (D₁.c _).left
        rw [Category.assoc, hc, ← Category.assoc, si, Category.assoc]
      obtain ⟨a, ha, va⟩ := exists_down_om gw' D₁.P.isLB D₂.P.isLB (K := PUnit) (φ' := fun _ => D₂.xK (h₂.xe y))
        (genMap (RingHom.id K).injective) (fun _ => hx) (D₁.psi (xe (h₂.xe y))) (D₁.psi_gen _)
      obtain ⟨k₁, k₂⟩ := PolIsoDescent.flat_surjective (F := FractionRing Ω) (C := FractionRing K) (genMap l.injective)
      have ea := PsiEvenPull.val_eq_of_app_injective D₂.P.isLB (fun _ _ _ => rfl) (genMap l.injective)
        (fun U => FunDescent.app_injective (genMap l.injective) U) ha (D₂.psi_gen (h₂.xe y)) (fun u I₂ hI₂ => by
          obtain ⟨I₁, hI₁⟩ := DegPull.exists_good' D₁.P.isLB u
          obtain ⟨I, hI⟩ := DegPull.exists_good' D.P.isLB u
          have v₂ := psi_val h₂ _ _ sl hI₂ hI y
          have v₁ := psi_val h₁ (genMap l.injective ≫ genMap (RingHom.id K).injective) _
            (sl.trans ((congrArg (_ ≫ ·) si'.symm).trans (Category.assoc _ _ _).symm)) hI₁ hI y
          have v₀ := va _ (genMap l.injective) u I₁ I₂ hI₁ hI₂
          have hq : genMap l.injective ≫ D₂.xK (h₂.xe y) = (𝟙 _ ≫ D.xK y) ≫ proj h₂ := by
            show _ ≫ jK K ≫ (D₂.c _).left = (𝟙 _ ≫ jK Ω ≫ (D.c y).left) ≫ _
            rw [← Category.assoc, ← sl]
            simp only [Category.assoc]
            exact congrArg (fun q => 𝟙 _ ≫ jK Ω ≫ q) (h₂.c_pr y).symm
          have t : om v u I₁ I (𝟙 _ ≫ D.xK y) =
              om w u I₁ I₂ ((𝟙 _ ≫ D.xK y) ≫ proj h₂) * om h₂.w u I₂ I (𝟙 _ ≫ D.xK y) := by
            rw [om, om, om, Category.assoc (𝟙 _ ≫ D.xK y)]
            exact T _ _ u _ _ _ (hI₁ ((𝟙 _ ≫ D.xK y) ≫ proj h₂ ≫ φ.hom.left)) (hI₂ ((𝟙 _ ≫ D.xK y) ≫ proj h₂)) (hI _)
          rw [Fintype.prod_unique, zpow_neg_one, hq, hxe, v₁, ← hom, t, mul_inv, _root_.mul_assoc] at v₀
          exact (mul_left_cancel v₀).symm.trans v₂.symm) _ (𝟙 _) z J₂ hJ₂
      have v₀ := va _ (𝟙 _) z J₁ J₂ hJ₁ hJ₂
      rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp, ea] at v₀
      exact v₀)
  exact ⟨hD⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfIsNilpotent
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup

theorem omega_baseChange_bijective_of_isNilpotent : ∀ (p : ℕ) [Fact p.Prime] (R R' : Type) [CommRing R]
    [CommRing R'] [Algebra R R'], IsNilpotent (p : R) → ∀ G : PDivGroup p R,
    Function.Bijective (PDiv.liftSemi (G.toBase R').omega) := by
  intro p _ R R' _ _ _ hnil G
  obtain ⟨N, hN⟩ := hnil
  have hN' : (p : R') ^ N = 0 := by
    rw [← map_natCast (algebraMap R R'), ← map_pow, hN, map_zero]
  have hL := omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl
  have hL' := omegaLevel_bijective_of_pow_eq_zero p R' N hN' (G.baseChange R') N le_rfl
  have hg := PDiv.liftSemi_toBaseChange_cot_bijective R R' (G.A N)
  let e : R' ⊗[R] G.omega ≃ₗ[R'] R' ⊗[R] Cot R (G.A N) :=
    LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofBijective (G.omegaLevel N) hL)
  have hcomp : ((G.baseChange R').omegaLevel N).comp (PDiv.liftSemi (G.toBase R').omega) =
      (PDiv.liftSemi (toBaseChange R R' (G.A N)).cot).comp e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, PDiv.liftSemi_tmul, map_smul, e,
      LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
    rfl
  refine Function.Bijective.of_comp_left ?_ hL'.injective
  change Function.Bijective (((G.baseChange R').omegaLevel N).comp (PDiv.liftSemi (G.toBase R').omega))
  rw [hcomp]
  exact hg.comp e.bijective

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverPullbackMapLeftCompPullbackFstScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.Mum

theorem over_pullback_map_left_comp_pullbackFst_scheme {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (g : X ⟶ Y) :
    ((Over.pullback f).map g).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ g.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupCocycleMemCobRangeOfDiagonalSumZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem lift_counit_pullTwo {R D D' : Type} [CommRing R] [CommRing D] [Bialgebra R D] [CommRing D']
    [Bialgebra R D'] (f : D →ₐc[R] D') (c : D ⊗[R] D) :
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R D') (Bialgebra.counitAlgHom R D')
        (fun _ _ ↦ Commute.all _ _) (pullbackTwo f c) =
      Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R D) (Bialgebra.counitAlgHom R D)
        (fun _ _ ↦ Commute.all _ _) c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [pullbackTwo]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem diagSum_one (R D : Type) [CommRing R] [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) :
    diagSum R D m 1 = (m : D) := by
  rw [Algebra.TensorProduct.one_def, diagSum_tmul]
  simp

theorem cocycle_mem_range_cob_of_diagSum_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
      ∀ (G : PDivGroup p R) (z : G.cocycles), diagSum R (G.A N) (p ^ N) (z.1 N) = 0 →
        z ∈ LinearMap.range G.cob := by
  intro p _ R _ N hp G z hz
  have hq : ((p ^ N : ℕ) : R) = 0 := by rw [Nat.cast_pow, hp]
  let ε : ∀ n, G.A n ⊗[R] G.A n →ₐ[R] R := fun n =>
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R (G.A n)) (Bialgebra.counitAlgHom R (G.A n))
      (fun _ _ ↦ Commute.all _ _)
  have hr : ∀ n, ε n (z.1 n) = ε 0 (z.1 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [← ih, ← (z.2 n).2]; exact (lift_counit_pullTwo _ _).symm
  let o : G.funs := ⟨fun _ => 1, fun n => map_one (G.res n)⟩
  let z' : G.cocycles := z + ε 0 (z.1 0) • G.cob o
  have hz' : ∀ n, z'.1 n = z.1 n - ε 0 (z.1 0) • (1 : G.A n ⊗[R] G.A n) := by
    intro n
    change z.1 n + ε 0 (z.1 0) • cobOne R (G.A n) 1 = _
    rw [cobOne_apply, Bialgebra.comul_one, ← Algebra.TensorProduct.one_def, sub_self, zero_sub, smul_neg,
      sub_eq_add_neg]
  have h0 : ∀ n, ε n (z'.1 n) = 0 := by
    intro n
    rw [hz', map_sub, map_smul, map_one, hr, smul_eq_mul, _root_.mul_one, sub_self]
  have hmem : z' ∈ LinearMap.range G.cob := by
    refine cocycle_mem_range_cob_of_pullback_mulBy_pow p R G N z'
      (fun n => diagSum R (G.A n) (p ^ N) (z'.1 n)) (fun n => ?_) (fun n => ?_) ?_
    · rw [diagSum_pullTwo, (z'.2 n).2]
    · rw [cobOne_diagSum_eq p R G n (p ^ N) hq _ (z'.2 n).1]
      have := h0 n
      simp only [ε] at this
      rw [this, zero_smul, sub_zero]
    · change diagSum R (G.A N) (p ^ N) (z'.1 N) = 0
      rw [hz', map_sub, map_smul, hz, diagSum_one, ← map_natCast (algebraMap R (G.A N)), hq, map_zero,
        smul_zero, sub_zero]
  have : z = z' - ε 0 (z.1 0) • G.cob o := by simp [z']
  rw [this]
  exact Submodule.sub_mem _ hmem (Submodule.smul_mem _ _ ⟨o, rfl⟩)

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairUOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

abbrev sqR (N : Near π G) : Over (Sp R) :=
  Over.mk ((Desc.UT N ⊗ Desc.UT N).hom ≫ pullback.fst π π ≫ π)

def fstU (N : Near π G) : sqR N ⟶ N.U :=
  Over.homMk ((fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (fst (Desc.UT N) (Desc.UT N)))))))

def sndU (N : Near π G) : sqR N ⟶ N.U :=
  Over.homMk ((snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (snd (Desc.UT N) (Desc.UT N)))))))

def pairU (N : Near π G) : (Desc.UT N ⊗ Desc.UT N).left ⟶ (N.U ⊗ N.U).left :=
  (lift (fstU N) (sndU N)).left

abbrev VT (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) : (Desc.UT N ⊗ Desc.UT N).left.Opens :=
  pairU N ⁻¹ᵁ V

theorem pairU_over (N : Near π G) :
    pairU N ≫ (N.U ⊗ N.U).hom = (Desc.UT N ⊗ Desc.UT N).hom ≫ pullback.fst π π ≫ π :=
  Over.w (lift (fstU N) (sndU N))

def mT (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) : (VT N V).toScheme ⟶ (Desc.UT N).left :=
  pullback.lift ((pairU N ∣_ V) ≫ m) ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) (by
    have e : (pairU N ∣_ V) ≫ V.ι = (VT N V).ι ≫ pairU N := morphismRestrict_ι _ _
    refine (Category.assoc _ _ _).trans ?_
    rw [hm, ← Category.assoc, e, Category.assoc, pairU_over, Category.assoc])

variable [GrpObj G]

def trip (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N ⟶ (Over.pullback p).obj G :=
  (snd _ _ ≫ Desc.emb N p hp)⁻¹ * (fst _ _ ≫ Desc.sum N p hp)

def Pk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Over (pullback π π) :=
  Over.mk (pullback.snd (Desc.emb N p hp).left (trip N p hp).left ≫ ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom)

def dP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Pk N p hp ⟶ Desc.UT N :=
  Over.homMk (pullback.fst _ _) (by
    show pullback.fst _ _ ≫ (Desc.UT N).hom = pullback.snd _ _ ≫ _
    rw [← Over.w (Desc.emb N p hp), ← Category.assoc, pullback.condition, Category.assoc, Over.w (trip N p hp)])

def abP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ Desc.UT N ⊗ Desc.UT N :=
  Over.homMk (pullback.snd _ _ ≫ (fst (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)).left)
    ((Category.assoc _ _ _).trans (congrArg (pullback.snd _ _ ≫ ·) (Over.w (fst (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)))))

def cP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Pk N p hp ⟶ Desc.UT N :=
  Over.homMk (pullback.snd _ _ ≫ (snd (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)).left)
    ((Category.assoc _ _ _).trans (congrArg (pullback.snd _ _ ≫ ·) (Over.w (snd (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)))))

def cdP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ Desc.UT N ⊗ Desc.UT N :=
  lift (cP N p hp) (dP N p hp)

def Wk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (V : (N.U ⊗ N.U).left.Opens) :
    (Pk N p hp).left.Opens :=
  (abP N p hp).left ⁻¹ᵁ VT N V ⊓ (cdP N p hp).left ⁻¹ᵁ VT N V

def q3 (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N :=
  Over.homMk (pullback.snd _ _) rfl

theorem abP_eq (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    abP N p hp = q3 N p hp ≫ fst _ _ := Over.OverMorphism.ext rfl

theorem indicatorIdempotent_eq_add_sum (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    cP N p hp = q3 N p hp ≫ snd _ _ := Over.OverMorphism.ext rfl

theorem dP_emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    dP N p hp ≫ Desc.emb N p hp = q3 N p hp ≫ trip N p hp := Over.OverMorphism.ext pullback.condition

theorem abP_sum (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    abP N p hp ≫ Desc.sum N p hp = cdP N p hp ≫ Desc.sum N p hp := by
  have e4 : cdP N p hp ≫ Desc.sum N p hp = (cP N p hp ≫ Desc.emb N p hp) * (dP N p hp ≫ Desc.emb N p hp) := by
    rw [cdP, Desc.sum, comp_mul, ← Category.assoc, lift_fst, ← Category.assoc, lift_snd]
  rw [e4, dP_emb, trip, comp_mul, GrpObj.comp_inv, indicatorIdempotent_eq_add_sum, abP_eq]
  simp only [Category.assoc]
  exact (mul_inv_cancel_left _ _).symm

theorem exists_lift (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (Z : Scheme.{0})
    (g g' : Z ⟶ (Desc.UT N ⊗ Desc.UT N).left) (h : g ≫ (Desc.sum N p hp).left = g' ≫ (Desc.sum N p hp).left) :
    ∃ z : Z ⟶ (Pk N p hp).left, z ≫ (abP N p hp).left = g ∧ z ≫ (cdP N p hp).left = g' := by
  let FinalForm : Over (pullback π π) := Over.mk (g ≫ (Desc.UT N ⊗ Desc.UT N).hom)
  have hw : g' ≫ (Desc.UT N ⊗ Desc.UT N).hom = g ≫ (Desc.UT N ⊗ Desc.UT N).hom := by
    rw [← Over.w (Desc.sum N p hp), ← Category.assoc, ← h, Category.assoc]
  let a : FinalForm ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk g rfl
  let b : FinalForm ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk g' hw
  have hab : a ≫ Desc.sum N p hp = b ≫ Desc.sum N p hp := Over.OverMorphism.ext h
  let t : FinalForm ⟶ (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N := lift a (b ≫ fst _ _)
  have ht : (b ≫ snd _ _) ≫ Desc.emb N p hp = t ≫ trip N p hp := by
    rw [trip, comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_snd, ← Category.assoc t, lift_fst, hab, Desc.sum,
      comp_mul]
    simp only [Category.assoc]
    exact (inv_mul_cancel_left _ _).symm
  let zo : FinalForm ⟶ Pk N p hp := Over.homMk (pullback.lift (b ≫ snd _ _).left t.left (congrArg Over.Hom.left ht))
    (by show pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ _ = _
        rw [← Category.assoc, pullback.lift_snd]; exact Over.w t)
  have h1 : zo ≫ abP N p hp = a := by rw [abP_eq, ← Category.assoc]; exact (congrArg (· ≫ fst _ _)
    (Over.OverMorphism.ext (pullback.lift_snd _ _ _) : zo ≫ q3 N p hp = t)).trans (lift_fst _ _)
  have h2 : zo ≫ cdP N p hp = b := by
    have hc : zo ≫ cP N p hp = b ≫ fst _ _ := by
      rw [indicatorIdempotent_eq_add_sum, ← Category.assoc]; exact (congrArg (· ≫ snd _ _)
        (Over.OverMorphism.ext (pullback.lift_snd _ _ _) : zo ≫ q3 N p hp = t)).trans (lift_snd _ _)
    have hd : zo ≫ dP N p hp = b ≫ snd _ _ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    rw [cdP, comp_lift, hc, hd]
    exact (lift_comp_fst_snd b)
  exact ⟨zo.left, congrArg Over.Hom.left h1, congrArg Over.Hom.left h2⟩

end GlobalTheory.Mum.DescKP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationFunctionCellEqMinIntegralComb
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem polFn_cell_eq_min_integral : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, r ≤ g → ∀ μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b₀ x y = b₀ y x) → (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) → ∃ (ι : ℕ) (L : Finset ((Fin 8 → Fin r → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ c)) ∧ ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ c) := by
  classical
  intro g φ hφ W hW N _ hN3 hε r hr μ hμ b₀ hsym hpos hmin
  obtain ⟨p, m, γ, hcone, hcov⟩ := _root_.GlobalTheory.Poinc.Cells.exists_finite_cones g φ hφ W hW N hN3 r hr μ hμ b₀ hsym hpos hmin
  obtain ⟨Nℓ, ℓ, hNℓ, hℓ⟩ := polFn_eq_min_linear g φ hφ r hr p m γ hcone
  choose D ν hD hν using fun i : Fin p => _root_.GlobalTheory.Poinc.linForm_eq_sum_qW_lifts W hW N hN3 hε r μ hμ (ℓ i)
  obtain ⟨E, hDE⟩ : ∃ E : Fin p → ℕ, ∀ i, D i * E i = ∏ j, D j :=
    ⟨fun i => ∏ j ∈ Finset.univ.erase i, D j, fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)⟩
  have hDp : 0 < ∏ j, D j := Finset.prod_pos (fun j _ => hD j)
  refine ⟨Nℓ * ∏ j, D j, Finset.univ.image (fun i c => (N : ℤ) * (E i : ℤ) * ν i c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hNℓ.ne' hDp.ne')
  intro b' hs hp hm
  obtain ⟨i0, k, cf, hk, hkb⟩ := hcov b' hs hp hm
  obtain ⟨hle, i1, heq⟩ := hℓ b' hs hp ⟨i0, k, cf, hk, hkb⟩
  have key : ∀ i, ∑ c, ((((N : ℤ) * (E i : ℤ) * ν i c : ℤ)) : ℝ) * ((qW W b' (μ c) : ℤ) : ℝ)
      = ((N : ℝ) * (E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := by
    intro i
    have h' : (((∑ c, ν i c * qW W b' (μ c) : ℤ)) : ℝ) = (((D i : ℤ) * ℓ i b' : ℤ) : ℝ) := by
      rw [hν i b' hs]
    push_cast at h' ⊢
    calc ∑ c, (N : ℝ) * (E i : ℝ) * (ν i c : ℝ) * (qW W b' (μ c) : ℝ)
        = (N : ℝ) * (E i : ℝ) * ∑ c, (ν i c : ℝ) * (qW W b' (μ c) : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun c _ => ?_); ring
      _ = _ := by rw [h']; ring
  have hι : ∀ i, ((Nℓ * ∏ j, D j : ℕ) : ℝ) * (N : ℝ)
      = ((N : ℝ) * (E i : ℝ) * (D i : ℝ)) * (Nℓ : ℝ) := by
    intro i; rw [← hDE i]; push_cast; ring
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hν'
    have hc : (0 : ℝ) ≤ (N : ℝ) * (E i : ℝ) * (D i : ℝ) := by positivity
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * (N : ℝ) * φ.evalZ b'
        = ((N : ℝ) * (E i : ℝ) * (D i : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i]; ring
      _ ≤ ((N : ℝ) * (E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := mul_le_mul_of_nonneg_left (hle i) hc
      _ = _ := (key i).symm
  · refine ⟨_, Finset.mem_image.mpr ⟨i1, Finset.mem_univ _, rfl⟩, ?_⟩
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * (N : ℝ) * φ.evalZ b'
        = ((N : ℝ) * (E i1 : ℝ) * (D i1 : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i1]; ring
      _ = ((N : ℝ) * (E i1 : ℝ) * (D i1 : ℝ)) * ((ℓ i1 b' : ℤ) : ℝ) := by rw [heq]
      _ = _ := (key i1).symm

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveBundleEqTranslateAmpleNoetherianLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_bundle_eq_translate_ample_noetherian_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  first | exact @GlobalTheory.PrimitiveAmpleLocal.exists_section_translate | exact GlobalTheory.PrimitiveAmpleLocal.exists_section_translate | (intros; apply GlobalTheory.PrimitiveAmpleLocal.exists_section_translate <;> assumption)
end

