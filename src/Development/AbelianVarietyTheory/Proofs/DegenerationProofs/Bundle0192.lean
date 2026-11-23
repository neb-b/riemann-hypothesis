module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyAbelianSchemeProjectiveClosure
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusPointsLevelWeightsFromOrthogonalLabels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseFactsHasGeoExistsClos
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem baseFacts_hasGeo_exists_clos : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Big → ρ.HasU → S.Over₀ M U₀ → S.IsEE M U₀ EE → BaseFacts S M U₀ EE ∧ ρ.HasGeo ∧ ∃ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), ex.core.HasTests ∧ ex.core.Indep ∧ ex.core.Fib ∧ ex.core.HasCharts := by
  intro hL hT o Ω _ _ _ _ S ρ M U₀ EE hB hU hO hE
  have hTests : S.HasTests := by
    intro p _ y hy
    obtain ⟨_, _, τ, _⟩ := hU p y hy ∅
    exact ⟨τ⟩
  have hF : BaseFacts S M U₀ EE := baseFacts_of_isEE o Ω S M U₀ EE hTests hO hE
  have hG : ρ.HasGeo := _root_.GlobalTheory.ZH.GeoExist.hasGeo_of_hasU hL hT o Ω S ρ hB hU
  obtain ⟨Q⟩ := _root_.GlobalTheory.ZH.nonempty_clos hL o Ω S ρ M U₀ EE hF
  obtain ⟨ex⟩ := _root_.GlobalTheory.ZH.ClosureLifting.nonempty_ext hL o Ω S ρ M U₀ EE hF Q
  obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.ZH.Clos.Ext.hasTests_and_indep hL o Ω S ρ M U₀ EE hF Q ex hB hG
  have h₃ : ex.core.Fib := _root_.GlobalTheory.ZJ.Core.fib_of_indep ex.core h₂
  exact ⟨hF, hG, Q, ex, h₁, h₂, h₃, _root_.GlobalTheory.ZH.GradedCharts.hasCharts hL o Ω S ρ M U₀ EE hF Q ex hB hG h₃⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullTorsionIsometryOfTateIsoQ
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel

theorem weilIs_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : WeilIs G L k x₀ y₀ c) : WeilIs G' L' k x y c := by
  subst hg
  exact (GlobalTheory.weilIs_grpPullback_of_comm' S S' G G' f φ L L' hL hL' hp hw T k x y x₀ y₀ c ex ey).2 h

theorem exists_fullI_of_tateIsoQ : GlobalTheory.UT.LL → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (I' : TateIsoQ D M.P.D.toPre M.P.oD C), ∃ I : FullI o, I.ζ = I'.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j (I'.ev j x) z := by
  intro hLL E _ _ _ H D C _ o M I'
  let := H.starRing
  have : IsAlgClosed C := o.closed
  obtain ⟨hadm, hcz⟩ := M.admissible_base_of_complete_dvr
  have : CharZero M.W := hcz
  have hall := GlobalTheory.TestFibre.laws_all hLL.1 hLL.2.1
  have hT : M.P.TorsionIso := _root_.GlobalTheory.UT.torsionIso_of_pelUnif hLL hall.2.1 hall.2.2.1 hall.2.2.2.1 hall.2.2.2.2 E H M.W
    (IsLocalRing.maximalIdeal M.W) hadm M.t M.P
  have hTw := _root_.GlobalTheory.LevelCompat.qkToAkU_level hLL M.W (IsLocalRing.maximalIdeal M.W) hadm M.P.D M.P.A M.t.G M.t.semi M.P.U C
  have hT' := fun (k : ℕ) (hk : 1 ≤ k) => hT C k hk
  choose f hfA hfB hfC hfD hfE hfF using hT'
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) (jFK (R := M.W) C)
    (by simp)

  have gA : ∀ (n : ℕ) (hn : 0 < n) a, M.P.ToA C n (I'.ev n a) (f n hn (I'.ev n a)) := fun n hn a => (hfA n hn _ _).2 rfl
  have gAdd : ∀ (n : ℕ) (hn : 0 < n) a b, f n hn (I'.ev n (a + b)) = f n hn (I'.ev n a) * f n hn (I'.ev n b) :=
    fun n hn a b => hfD n hn _ _ _ (I'.add n hn a b)
  have gLin : ∀ (n : ℕ) (hn : 0 < n) (c : 𝓞 E) a, f n hn (I'.ev n (c • a)) = f n hn (I'.ev n a) ≫ M.P.oA.act c :=
    fun n hn c a => hfE n hn c _ _ (I'.lin n hn c a)
  have gEq : ∀ (n : ℕ) (hn : 0 < n) a b, f n hn (I'.ev n a) = f n hn (I'.ev n b) ↔ ∃ e, a = b + n • e :=
    fun n hn a b => (hfC n hn _ _).trans (I'.ker n hn a b)
  have gZero : ∀ (n : ℕ) (hn : 0 < n), f n hn (I'.ev n 0) = 1 := by
    intro n hn
    have h0 := gAdd n hn 0 0
    rw [add_zero] at h0
    exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
  have gNsmul : ∀ (n : ℕ) (hn : 0 < n) a (m : ℕ), f n hn (I'.ev n (m • a)) = f n hn (I'.ev n a) ^ m := by
    intro n hn a m
    induction m with
    | zero => rw [zero_smul, gZero, pow_zero]
    | succ m ih => rw [succ_nsmul, gAdd, ih, pow_succ]
  have gPow : ∀ (n : ℕ) (hn : 0 < n) a, f n hn (I'.ev n a) ^ n = 1 := by
    intro n hn a
    rw [← gNsmul, ← gZero n hn]
    exact (gEq n hn _ _).2 ⟨a, by rw [zero_add]⟩
  have gOnto : ∀ (n : ℕ) (hn : 0 < n) x, x ^ n = 1 → ∃ a, f n hn (I'.ev n a) = x := by
    intro n hn x hx
    obtain ⟨p, rfl⟩ := hfB n hn x hx
    obtain ⟨a, ha⟩ := I'.onto n hn p
    exact ⟨a, (hfC n hn _ _).2 ha⟩
  have gTower : ∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m) a,
      f (n * m) (Nat.mul_pos hn hm) (I'.ev (n * m) a) ^ m = f n hn (I'.ev n a) := by
    intro n m hn hm a
    obtain ⟨q, hqy, hqg, hqe⟩ := I'.tower n m hn hm a
    have h1 := (hTw n m (n * m) hn hm rfl q (I'.ev (n * m) a) (f (n * m) (Nat.mul_pos hn hm) (I'.ev (n * m) a))).2
      hqy hqg (gA (n * m) (Nat.mul_pos hn hm) a)
    rw [(hfA n hn q _).1 h1]
    exact (hfC n hn _ _).2 hqe
  have gWeil : ∀ (n : ℕ) (hn : 0 < n) a b, WeilIs M.P.A.A M.P.A.L n (f n hn (I'.ev n a)) (f n hn (I'.ev n b))
      (unitOn (I'.ζ n ^ D.EF a b)) := fun n hn a b => (hfF n hn _ _ _).1 (I'.isom n hn a b)

  have hL : ∀ y, (e.symm y).left ≫ M.φ = y.left := fun y => by rw [← he, e.apply_symm_apply]
  have hComm : ∀ y (c : 𝓞 E), e.symm (y ≫ M.P.oA.act c) = e.symm y ≫ o.oa.act c := by
    intro y c
    apply e.injective
    rw [e.apply_symm_apply]
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, M.act c, ← Category.assoc, hL]
  obtain ⟨ev, hev⟩ : ∃ ev : ℕ → D.La → (baseOver (Sp C) ⟶ o.P.A),
      ∀ n a, ev n a = if hn : 0 < n then e.symm (f n hn (I'.ev n a)) else o.I.ev n a := ⟨_, fun _ _ => rfl⟩
  refine ⟨{ ζ := I'.ζ, ζ_prim := I'.ζ_prim, ζ_pow := I'.ζ_pow, ev := ev, add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }, rfl, ?_⟩
  · intro n a b
    by_cases hn : 0 < n
    · rw [hev, hev, hev, dite_eq_left hn, dite_eq_left hn, dite_eq_left hn, gAdd, map_mul]
    · rw [hev, hev, hev, dite_eq_right hn, dite_eq_right hn, dite_eq_right hn]
      exact o.I.add n a b
  · intro n c a
    by_cases hn : 0 < n
    · rw [hev, hev, dite_eq_left hn, dite_eq_left hn, gLin, hComm]
    · rw [hev, hev, dite_eq_right hn, dite_eq_right hn]
      exact o.I.lin n c a
  · intro n hn a
    rw [hev, dite_eq_left hn, map_eq_one_iff _ e.symm.injective, ← gZero n hn, gEq]
    simp only [zero_add]
  · intro n hn x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := gOnto n hn (e x) (by rw [← map_pow, hx, map_one])
      exact ⟨a, by rw [hev, dite_eq_left hn, ha, e.symm_apply_apply]⟩
    · rintro ⟨a, rfl⟩
      rw [hev, dite_eq_left hn, ← map_pow, gPow, map_one]
  · intro n m hn hm a
    rw [hev, hev, dite_eq_left (Nat.mul_pos hn hm), dite_eq_left hn, ← map_pow, gTower n m hn hm]
  · intro n hn a b
    rw [hev, hev, dite_eq_left hn, dite_eq_left hn]
    exact weilIs_push M.P.A.isLB o.P.isLB M.cart M.lb (baseOver (Sp C)) (jFK (R := M.W) C)
      (by simp) n _ _ _ _ _ (hL _).symm (hL _).symm (gWeil n hn a b)
  · intro j hj x
    refine ⟨f j hj (I'.ev j x), ?_, gA j hj x⟩
    change _ = (ev j x).left ≫ M.φ
    rw [hev, dite_eq_left hj, hL]

end GlobalTheory.Relabel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralBasisCombinationOfIntegralFamilyStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_basis_combination_of_integral_family : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → c ≠ 0 → ∀ Φ : Fam u.D.toPre (PadicAlgCl p) S.N, NuGe u.D Q (PadicAlgCl p) v S.N Φ 0 → ∃ (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N), (∀ j, ‖c * b j‖ ≤ 1) ∧ IsComb u.A s b σ ∧ u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ := by
  first | exact @GlobalTheory.TestFibre.exists_isComb_expands_of_nuGe_zero | exact GlobalTheory.TestFibre.exists_isComb_expands_of_nuGe_zero | (intros; apply GlobalTheory.TestFibre.exists_isComb_expands_of_nuGe_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelPadicPrincipallyPolarised
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem finiteDimensional_of_finite_of_isFractionRing (V K W L : Type) [CommRing V] [IsDomain V] [Field K]
    [Algebra V K] [IsFractionRing V K] [CommRing W] [IsDomain W] [Field L] [Algebra V W] [Algebra W L] [Algebra K L]
    [IsFractionRing W L] [Module.Finite V W]
    (e : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K)) :
    FiniteDimensional K L := by
  letI : Algebra V L := ((algebraMap W L).comp (algebraMap V W)).toAlgebra
  haveI : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' e
  haveI : FaithfulSMul V W := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have h : Function.Injective ((algebraMap W L).comp (algebraMap V W)) := by
      rw [e]; exact (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    exact Function.Injective.of_comp (f := algebraMap W L) h
  exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)

theorem exists_ringHom_integralClosure (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (W L : Type) [CommRing W] [IsDomain W] [Field L]
    [Algebra (integralClosure ℤ_[p] K) W] [Algebra W L] [Algebra K L] [IsFractionRing W L]
    [Module.Finite (integralClosure ℤ_[p] K) W]
    (e : (algebraMap W L).comp (algebraMap (integralClosure ℤ_[p] K) W) =
      (algebraMap K L).comp (algebraMap (integralClosure ℤ_[p] K) K)) :
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧
      ∃ (τ : L →+* K') (f : W →+* integralClosure ℤ_[p] K'),
        τ.comp (algebraMap K L) = (IntermediateField.inclusion h).toRingHom ∧
        τ.comp (algebraMap W L) = (algebraMap (integralClosure ℤ_[p] K') K').comp f := by
  haveI := finiteDimensional_of_finite_of_isFractionRing _ K W L e
  let σ : L →ₐ[K] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let K' : IntermediateField ℚ_[p] (PadicAlgCl p) := σ.fieldRange.restrictScalars ℚ_[p]
  have h : K ≤ K' := fun x hx => ⟨algebraMap K L ⟨x, hx⟩, σ.commutes _⟩
  let τ : L →+* K' := σ.toRingHom.codRestrict K' fun x => ⟨x, rfl⟩
  have hτ : τ.comp (algebraMap K L) = (IntermediateField.inclusion h).toRingHom :=
    RingHom.ext fun x => Subtype.ext (σ.commutes x)
  have hK' : FiniteDimensional ℚ_[p] K' := by
    letI : Algebra ℚ_[p] L := ((algebraMap K L).comp (algebraMap ℚ_[p] K)).toAlgebra
    haveI : IsScalarTower ℚ_[p] K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ℚ_[p] L := Module.Finite.trans K L
    let τ' : L →ₐ[ℚ_[p]] K' := { τ with commutes' := fun x => Subtype.ext (σ.commutes (algebraMap ℚ_[p] K x)) }
    refine Module.Finite.of_surjective τ'.toLinearMap ?_
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  have hint : ∀ w : W, IsIntegral ℤ_[p] (τ (algebraMap W L w)) := fun w => by
    have h₁ : (algebraMap (integralClosure ℤ_[p] K) W).IsIntegralElem w := Algebra.IsIntegral.isIntegral w
    letI alg : Algebra (integralClosure ℤ_[p] K) K' :=
      ((IntermediateField.inclusion h).toRingHom.comp (algebraMap (integralClosure ℤ_[p] K) K)).toAlgebra
    haveI tower : IsScalarTower ℤ_[p] (integralClosure ℤ_[p] K) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h₂ := h₁.map (τ.comp (algebraMap W L))
    rw [RingHom.comp_assoc, e, ← RingHom.comp_assoc, hτ] at h₂
    change IsIntegral (integralClosure ℤ_[p] K) (τ (algebraMap W L w)) at h₂
    exact @isIntegral_trans _ _ _ _ _ _ alg _ _ tower _ _ h₂
  exact ⟨K', h, hK', τ, (τ.comp (algebraMap W L)).codRestrict _ hint, hτ, RingHom.ext fun _ => rfl⟩

theorem exists_semiAbelian_model_padic_polAV : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (P : Out.PolAV (Sp K)), ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧ ∃ (G : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G), IsSemiAbelian G ∧ ∃ φ : pullback G.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶ P.A.left, IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G) P.A (spMap (IntermediateField.inclusion h).toRingHom) φ := by
  intro p _ K _ P
  haveI := GlobalTheory.DiscEval.isAdicComplete_integralClosure K
  obtain ⟨W, L, _, _, _, _, _, _, _, _, e, hfin, -, -, G, _, ⟨i, hi⟩, hG⟩ :=
    _root_.GlobalTheory.SemiPol.potModel_semiAbelian (integralClosure ℤ_[p] K) K (GlobalTheory.DiscEval.finite_residueField_integralClosure K) P
  obtain ⟨K', h, hK', τ, f, hτ, hf⟩ := exists_ringHom_integralClosure p K W L e
  refine ⟨K', h, hK', (Over.pullback (spMap f)).obj G, inferInstance, IsSemiAbelian.pullback _ G hG, ?_⟩
  exact GlobalTheory.SplitReduction.exists_isGrpPullback_of_square hf hτ G P.A
    (((isGrpPullback_of_iso i).comp (isGrpPullback_pullback P.A (spMap (algebraMap K L)))).congr
      (Category.id_comp _) rfl)

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionIsometryUniformisedModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData.ModelTate

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_level_down {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) (n m : ℕ) (p : QkPt D F (n * m)) :
    ∃ q : QkPt D F n, q.y = p.y ∧ GtPtF.IsNsmul m p.g q.g :=
  ⟨TorusExt.qkMk hB p.y (m • p.g) (by rw [← mul_nsmul', TorusExt.qk_nsmul hB p]), rfl,
    (TorusExt.isNsmul_iff_eq _ _ _).2 rfl⟩

theorem weilIs_of_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : WeilIs G' L' k x y c) : WeilIs G L k x₀ y₀ c := by
  subst hg
  exact (weilIs_grpPullback_of_comm' _ _ _ _ _ _ _ _ hL hL' hp hw T k x y x₀ y₀ c ex ey).1 h

theorem exists_tateIsoQ_of_model : GlobalTheory.UT.LL → BrGtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (N' : NumD C) (_ : NumOf M.P.D.toPre C N'), ∃ I : TateIsoQ D M.P.D.toPre M.P.oD C, I.ζ = o.I.ζ ∧ ∀ k, 0 < k → ∀ x p' (z : TFK (R := M.W) C ⟶ M.P.A.A), QkPt.Equiv _ C (I.ev k x) p' → z.left = (o.I.ev k x).left ≫ M.φ → M.P.ToA C k p' z := by
  intro hL _ E _ _ _ H D C _ o M _ _
  letI := H.starRing
  have := o.closed
  have := o.P.isAb.comm
  have hB := M.P.D.tau_bimult
  obtain ⟨hA, h0⟩ := M.admissible_base_of_complete_dvr
  obtain ⟨-, l₁, l₂, l₃, l₄⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  have hT := GlobalTheory.UT.torsionIso_of_pelUnif hL l₁ l₂ l₃ l₄ E H M.W _ hA M.t M.P
  choose f f₁ f₂ f₃ f₄ f₅ f₆ using hT C
  have hg : jFK (R := M.W) C = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := (Category.id_comp _).symm
  obtain ⟨e, he⟩ : ∃ e : (baseOver (Sp C) ⟶ o.P.A) ≃* (TFK (R := M.W) C ⟶ M.P.A.A), ∀ x, (e x).left = x.left ≫ M.φ :=
    LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) _ hg
  have eact : ∀ c x, e (x ≫ o.oa.act c) = e x ≫ M.P.oA.act c := fun c x => Over.OverMorphism.ext (by
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, M.act, Category.assoc])
  have tors : ∀ n (hn : 0 < n) p, f n hn p ^ n = 1 := fun n hn p => by
    obtain ⟨w, hw⟩ := M.P.U.ext
    exact ((f₁ n hn p _).2 rfl w hw).1
  have hev : ∀ n a, ∃ p : QkPt M.P.D.toPre C n, ∀ hn : 0 < n, f n hn p = e (o.I.ev n a) := fun n a => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨TorusExt.qkZero hB C 0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨p, hp⟩ := f₂ n hn (e (o.I.ev n a)) (by rw [← map_pow, (o.I.onto n hn _).2 ⟨a, rfl⟩, map_one])
      exact ⟨p, fun _ => hp⟩
  choose ev evp using hev
  refine ⟨{ ζ := o.I.ζ, ζ_prim := o.I.ζ_prim, ζ_pow := o.I.ζ_pow, ev := ev
            add := fun n hn a b => ?_, lin := fun n hn c a => ?_, ker := fun n hn a b => ?_,
            onto := fun n hn p => ?_, tower := fun n m hn hm a => ?_, isom := fun n hn a b => ?_ },
    rfl, fun k hk x p' z h hz => ?_⟩
  · exact (TorusExt.qkAdd_iff hB _ _ _).2 ((f₃ n hn _ _).1 (by
      rw [f₄ n hn _ _ _ (TorusExt.qkAdd_qkAdd hB _ _), evp, evp, evp, o.I.add, map_mul]))
  · obtain ⟨p, hp⟩ := qkAct_exists hL.1.globalFns hB M.P.oD c (ev n a)
    have h₁ := f₅ n hn _ _ _ hp
    obtain ⟨q, q₁, q₂, q₃⟩ := hp
    refine ⟨q, q₁, q₂, TorusExt.equiv_trans hB q₃ ((f₃ n hn _ _).1 ?_)⟩
    rw [h₁, evp, evp, o.I.lin, eact]
  · rw [← f₃ n hn, evp, evp, e.injective.eq_iff]
    have h₁ : o.I.ev n a = o.I.ev n b * o.I.ev n (a - b) := by rw [← o.I.add, add_sub_cancel]
    rw [h₁, mul_eq_left, o.I.ker n hn]
    exact exists_congr fun c => sub_eq_iff_eq_add'
  · obtain ⟨a, ha⟩ := (o.I.onto n hn (e.symm (f n hn p))).1 (by rw [← map_pow, tors, map_one])
    exact ⟨a, (f₃ n hn _ _).1 (by rw [evp, ha, MulEquiv.apply_symm_apply])⟩
  · obtain ⟨q, q₁, q₂⟩ := exists_level_down hB n m (ev (n * m) a)
    have hN := Nat.mul_pos hn hm
    have h := (GlobalTheory.LevelCompat.qkToAkU_level hL M.W _ hA M.P.D M.P.A M.t.G M.t.semi M.P.U C n m _ hn hm rfl q
      (ev (n * m) a) _).2 q₁ q₂ ((f₁ _ hN _ _).2 rfl)
    refine ⟨q, q₁, q₂, (f₃ n hn _ _).1 ?_⟩
    rw [← (f₁ n hn _ _).1 h, evp, evp, ← map_pow, o.I.tower n m hn hm]
  · refine (f₆ n hn _ _ _).2 ?_
    rw [evp, evp]
    exact weilIs_of_pull M.P.A.isLB o.P.isLB M.cart M.lb (baseOver (Sp C)) _ hg n _ _ _ _ _ (he _) (he _)
      (o.I.isom n hn a b)
  · refine (f₁ k hk _ _).2 ?_
    rw [← (f₃ k hk _ _).2 h]
    exact (Over.OverMorphism.ext (hz.trans (he _).symm)).trans (evp k x hk).symm

end GlobalTheory.ModelData.ModelTate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusPointsLevelWeightsFromOrthogonalLabelsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusPoints_level_weights_from_orthogonal_labels : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∀ t : S.perp l.yy.ker, ∃ (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (q : QkPt u.D.toPre (PadicAlgCl p) S.N), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) S.N q (x (S.r • (t : S.Gam))) ∧ ∀ β, (τ (Multiplicative.ofAdd β) : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζN) ^ (l.wt β t).val := by
  first | exact @GlobalTheory.TestFibre.torus_points_level_weights | exact GlobalTheory.TestFibre.torus_points_level_weights | (intros; apply GlobalTheory.TestFibre.torus_points_level_weights <;> assumption)
end

