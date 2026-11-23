module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyWeightSectionProducts
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CuspMulUnit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pow_mem_secZ' {ex : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex) (n : ℕ) :
    f ^ n ∈ GlobalTheory.AllWt.secZ Xo c (n • ex) := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AllWt.one_mem_secZ
  | succ n ih => rw [pow_succ, succ_nsmul]; exact GlobalTheory.AllWt.mul_mem_secZ ih hf

theorem eq_of_mem_secZ {e e' : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c e)
    (hf' : f ∈ GlobalTheory.AllWt.secZ Xo c e') (h0 : f ≠ 0) : e = e' := by
  classical
  by_contra hne
  apply h0
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  funext p y
  let u0 : (c.F)ˣ := Units.mk0 2 two_ne_zero
  let t : Ix Dw → (p.R)ˣ := Pi.mulSingle i (Units.map (algebraMap c.F p.R : c.F →* p.R) u0)
  have hw : ∀ d : Ix Dw → ℤ, ((∏ j, t j ^ d j : (p.R)ˣ) : p.R) = algebraMap c.F p.R ((2 : c.F) ^ d i) := by
    intro d
    rw [Finset.prod_eq_single i]
    · simp only [t, Pi.mulSingle_eq_same, ← map_zpow, Units.coe_map, MonoidHom.coe_coe, Units.val_zpow_eq_zpow_val,
        u0, Units.val_mk0]
    · intro j _ hj
      simp [t, Pi.mulSingle_eq_of_ne hj]
    · simp
  obtain ⟨y', hy'⟩ := GlobalTheory.SecSeparation.exists_frBor y t
  have e1 := hf.2 p t y y' hy'
  have e2 := hf'.2 p t y y' hy'
  rw [hw] at e1 e2
  have hne2 : (2 : c.F) ^ e i - (2 : c.F) ^ e' i ≠ 0 := by
    intro h
    apply hi
    have h1 : algebraMap ℚ c.F ((2 : ℚ) ^ e i) = algebraMap ℚ c.F ((2 : ℚ) ^ e' i) := by
      rw [map_zpow₀, map_zpow₀, map_ofNat]
      exact sub_eq_zero.1 h
    exact zpow_right_injective₀ (by norm_num) (by norm_num) ((algebraMap ℚ c.F).injective h1)
  have hu : IsUnit (algebraMap c.F p.R ((2 : c.F) ^ e i - (2 : c.F) ^ e' i)) := (IsUnit.mk0 _ hne2).map _
  show f p y = 0
  refine hu.mul_right_eq_zero.1 ?_
  rw [map_sub, sub_mul, ← e1, ← e2, sub_self]

end GlobalTheory.CuspMulUnit

namespace GlobalTheory.CuspMulUnit

theorem fj_mul_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (hE : 1 < Module.finrank ℚ E / 2) {la la' : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P Q : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : P ∈ X.SS la) (hQ : X.IsSec la' Q) (ξ : Fin r → E) (hξ : X.IsIso ξ) (x) (hx : x ∈ X.dom) :
    X.fj (la + la') ξ 0 (P * Q) x = 0 := by
  have hPs := hP.1.1
  have hm := ReciprocityTheory.ChartRestriction.G.FD.coefficientConvolution_holds (E := E) r X la la' P Q hPs hQ (GlobalTheory.CuspFrom.isModerate _ hE hPs)
    (GlobalTheory.CuspFrom.isModerate _ hE hQ) ξ hξ x hx 0
  have hz : ∀ ν, X.fj la ξ ν P x * X.fj la' ξ (0 - ν) Q x = 0 := by
    intro ν
    by_cases h1 : X.fj la ξ ν P x = 0
    · rw [h1, zero_mul]
    by_cases h2 : X.fj la' ξ (0 - ν) Q x = 0
    · rw [h2, mul_zero]
    exfalso
    have a1 := GlobalTheory.CuspFrom.freqNonneg _ hE hPs ξ hξ ν x hx h1
    have a2 := GlobalTheory.CuspFrom.freqNonneg _ hE hQ ξ hξ (0 - ν) x hx h2
    have hν : ν = 0 := funext fun τ => le_antisymm (by have := a2 τ; simp at this; exact this) (a1 τ)
    subst hν
    exact h1 (hP.2 ξ hξ x hx)
  simp only [hz] at hm
  exact hm.unique hasSum_zero


end GlobalTheory.CuspMulUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeSpecAlgebraProd
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency false in
theorem exists_baseChange_spAlg_prod (R D : Type) [CommRing R] [CommRing D] [Algebra R D]
    (B : Over (Sp R)) [GrpObj B] (g : ℕ) :
    IsAbelianScheme B → SmoothOfRelativeDimension g B.hom →
      ∃ (B' : Over (Sp D)) (_ : GrpObj B') (π : B'.left ⟶ B.left)
        (q : B'.left ⟶ (SpAlg R D ⊗ B).left),
        IsGrpPullback B' B (spMap (algebraMap R D)) π ∧ IsAbelianScheme B' ∧
          SmoothOfRelativeDimension g B'.hom ∧ IsIso q ∧
          q ≫ (fst (SpAlg R D) B).left = B'.hom ∧ q ≫ (snd (SpAlg R D) B).left = π := by
  intro hA hg
  let f := spMap (algebraMap R D)
  refine ⟨(Over.pullback f).obj B, inferInstance, Limits.pullback.fst B.hom f,
    (Limits.pullbackSymmetry B.hom f).hom,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B f,
    GlobalTheory.isAbelianScheme_pullback_obj f B hA,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (CategoryTheory.IsPullback.of_hasPullback B.hom f) hg,
    inferInstance, Limits.pullbackSymmetry_hom_comp_fst B.hom f,
    Limits.pullbackSymmetry_hom_comp_snd B.hom f⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyOfPullbackFiniteSurjective
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem exists_fam_of_pull : ∀ (S : Scheme.{0}) (A U U' : Over S) [GrpObj A] [IsLocallyNoetherian U.left],
    IsAbelianScheme A → ∀ (p : U' ⟶ U), IsFinite p.left → Surjective p.left → ∀ (N' : LB (A ⊗ U').left)
    (h : Fam A N') (c : Pic (A ⊗ U).left), GlobalTheory.CechPic.pull (A ◁ p).left c = cls N' h.isLB →
    ∃ M : LB (A ⊗ U).left, Fam A M ∧ Same A M N' p (𝟙 U') := by
  intro S A U U' _ _ hA p hfin hsurj N' h c hc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (u : Y ⟶ U'), evc hL a (u ≫ p) = evc h.isLB a u := by
    intro Y a u
    have e : lift a (u ≫ p) = lift a u ≫ (A ◁ p) := by ext <;> simp
    rw [evc, e, Over.comp_left, pull_comp, hc]
    rfl
  obtain ⟨M, hM, hMc⟩ := cls_surj (cls L hL - CechPic.pull (snd A U).left (evc hL (1 : U ⟶ A) (𝟙 U)))
  have form : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ U), evc hM a t = evc hL a t - evc hL (1 : Y ⟶ A) t := by
    intro Y a t
    rw [evc, hMc, map_sub, ← pull_comp, ← Over.comp_left, lift_snd, pull_evc, MonObj.comp_one, Category.comp_id]
    rfl
  have keyM : ∀ (Y : Over S) (a : Y ⟶ A) (u : Y ⟶ U'), evc hM a (u ≫ p) = evc h.isLB a u := by
    intro Y a u
    rw [form, key, key, h.add.evc_one h.isLB, sub_zero]
  refine ⟨M, ⟨hM, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A U hA M hM ((triv_ev_iff hM _ _).2 (by rw [form, sub_self])) ?_⟩, ?_⟩
  · intro K _ _ s t
    haveI := hfin
    haveI := hsurj
    obtain ⟨b, hb⟩ := exists_lift_pt p.left t.left
    let t' : Over.mk s ⟶ U' := Over.homMk b (by
      rw [← Over.w p, ← Category.assoc, hb, Over.w t])
    have ht : t = t' ≫ p := Over.OverMorphism.ext hb.symm
    rw [ht]
    refine (isAdditive_iff (pull_isLB hM _)).2 fun Y a a' y ↦ ?_
    have e : ∀ a₀ : Y ⟶ A, evc (pull_isLB hM _) a₀ y = evc h.isLB a₀ (y ≫ t') := fun a₀ ↦ by
      rw [evc_ev hM, lift_fst, lift_snd_assoc, ← Category.assoc, keyM]
    rw [e, e, e]
    exact (isAdditive_iff h.isLB).1 h.add _ _ _ _
  · rw [same_iff hM h.isLB, Category.comp_id]
    exact keyM _ _ _

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumFieldOfCoeffTendstoZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

theorem exists_adic_sum_of_finsets {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {Ix : Type} (c : Ix → R) (S : ℕ → Finset Ix) (hmono : Monotone S)
    (hS : ∀ n i, i ∉ S n → c i ∈ I ^ n) :
    ∃ a : R, ∀ n, ∀ T : Finset Ix, S n ⊆ T → a - ∑ i ∈ T, c i ∈ I ^ n := by
  classical
  have key : ∀ n, ∀ T : Finset Ix, S n ⊆ T → ∑ i ∈ T, c i - ∑ i ∈ S n, c i ∈ I ^ n := by
    intro n T hT
    rw [← Finset.sum_sdiff hT, add_sub_cancel_right]
    exact Ideal.sum_mem _ fun i hi => hS n i (Finset.mem_sdiff.mp hi).2
  have hsm : ∀ n, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    simp
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance
    (f := fun n => ∑ i ∈ S n, c i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm, ← neg_mem_iff, neg_sub]
      exact key m _ (hmono hmn))
  refine ⟨a, fun n T hT => ?_⟩
  have h1 := ha n
  rw [SModEq.sub_mem, hsm] at h1
  have h2 := key n T hT
  have h3 := Ideal.add_mem _ h1 h2
  rw [← neg_mem_iff]
  convert h3 using 1
  ring

theorem exists_sumI_of_coeff {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {E : Type} [AddCommGroup E] [Module R E] {Jx : Type} [Fintype Jx] (g : Jx → E)
    {Ix : Type} (c : Ix → Jx → R) (h : ∀ n : ℕ, {i | ¬ ∀ k, c i k ∈ I ^ n}.Finite) :
    ∃ s : E, GlobalTheory.UT.SumI I (fun i => ∑ k, c i k • g k) s := by
  classical
  have hmono : Monotone (fun n => (h n).toFinset) := by
    intro m n hmn i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun hk => hi fun k => Ideal.pow_le_pow_right hmn (hk k)
  have hS : ∀ k n i, i ∉ (h n).toFinset → c i k ∈ I ^ n := by
    intro k n i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hi
    exact hi k
  choose a ha using fun k =>
    exists_adic_sum_of_finsets I (fun i => c i k) (fun n => (h n).toFinset) hmono (hS k)
  have hg : ∀ k, g k ∈ Submodule.span R (Set.range g) := fun k =>
    Submodule.subset_span ⟨k, rfl⟩
  refine ⟨∑ k, a k • g k, Submodule.span R (Set.range g),
    Submodule.fg_span (Set.finite_range g),
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k),
    fun i => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k),
    fun n => ⟨(h n).toFinset, fun T hT => ?_⟩⟩
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [← Finset.sum_smul, ← sub_smul]
  exact Submodule.smul_mem_smul (ha k n T hT) (hg k)

theorem exists_sumF_of_coeff : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (Jx : Type) [Fintype Jx] (g : Jx → F) (Ix : Type) (c : Ix → Jx → R), (∀ n : ℕ, {i | ¬ ∀ k, c i k ∈ maximalIdeal R ^ n}.Finite) → ∃ s : F, GlobalTheory.UT.SumF (maximalIdeal R) F (fun i => ∑ k, algebraMap (FractionRing R) F (algebraMap R _ (c i k)) * g k) s := by
  intro R _ _ _ _ hc F _ _ Jx _ g Ix c h
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  obtain ⟨s, hs⟩ := exists_sumI_of_coeff (maximalIdeal R) g c h
  refine ⟨s, ?_⟩
  have e : (fun i => ∑ k, algebraMap (FractionRing R) F (algebraMap R _ (c i k)) * g k)
      = fun i => ∑ k, c i k • g k := by
    funext i
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Algebra.smul_def]
    rfl
  rw [e]
  exact hs

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleProjectiveThetaModelOverModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.SegreModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem hasDiv_left {A B : Type} {a : A → Ω} {b : B → Ω} (h : M.HasDiv fun p : A × B => a p.1 * b p.2) :
    M.HasDiv a := fun z => by
  obtain ⟨i, h0, hi⟩ := h z
  refine ⟨i.1, left_ne_zero_of_mul h0, fun j => ?_⟩
  have := hi (j, i.2)
  rwa [mul_div_mul_right _ _ (right_ne_zero_of_mul h0)] at this

theorem hasDiv_right {A B : Type} {a : A → Ω} {b : B → Ω} (h : M.HasDiv fun p : A × B => a p.1 * b p.2) :
    M.HasDiv b := fun z => by
  obtain ⟨i, h0, hi⟩ := h z
  refine ⟨i.2, right_ne_zero_of_mul h0, fun j => ?_⟩
  have := hi (i.1, j)
  rwa [mul_div_mul_left _ _ (left_ne_zero_of_mul h0)] at this

theorem hasDiv_of_prod {K : Type} [Fintype K] {J : K → Type} {t : ∀ k, J k → Ω}
    (h : M.HasDiv fun i : ∀ k, J k => ∏ k, t k (i k)) (k : K) : M.HasDiv (t k) := fun z => by
  obtain ⟨i, h0, hi⟩ := h z
  have hne := Finset.prod_ne_zero_iff.1 h0
  refine ⟨i k, hne k (Finset.mem_univ _), fun j => ?_⟩
  have := hi (Function.update i k j)
  have e : ∏ l ∈ Finset.univ.erase k, t l (Function.update i k j l) = ∏ l ∈ Finset.univ.erase k, t l (i l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have h1 : ∏ l ∈ Finset.univ.erase k, t l (i l) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => hne l (Finset.mem_univ _)
  simp only at this
  rwa [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ (fun l => t l (i l)) (Finset.mem_univ k),
    e, Function.update_self, mul_div_mul_right _ _ h1] at this

theorem subfield_eq_top {J : Type} {c : J → Ω} (h : M.IsCl c) (F : Subfield Ω)
    (ho : Set.range (algebraMap o Ω) ⊆ F) (hc : ∀ i j, c i ≠ 0 → c j / c i ∈ F) : F = ⊤ := by
  obtain ⟨i, hi, -⟩ := h.1 (genericPoint M.Z)
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi
  have hne : (U : Set M.Z).Nonempty := ⟨genericPoint M.Z, hD ▸ RatModel.div_genericPoint hi⟩
  have hle : ∀ x ∈ M.ringOn U, x ∈ F := by
    intro x hx
    rw [hR] at hx
    induction hx using Algebra.adjoin_induction with
    | mem _ h' => obtain ⟨j, rfl⟩ := h'; exact hc i j hi
    | algebraMap r => exact ho ⟨r, rfl⟩
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  refine top_unique fun x _ => ?_
  obtain ⟨a, b, -, rfl⟩ := RatModel.exists_eq_div hU hne x
  exact div_mem (hle _ ((RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩))
    (hle _ ((RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))

theorem finite_of_eq_top (F : Subfield Ω) (h : F = ⊤) : Module.Finite F Ω :=
  Module.Finite.of_surjective (Algebra.linearMap F Ω) fun x => ⟨⟨x, h ▸ trivial⟩, rfl⟩

end GlobalTheory.Poinc.SegreModel

theorem GlobalTheory.Poinc.exists_admissible_projective_theta_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ∀ M₁ : RatModel o Ω, IsProjOver M₁.s → ∀ (K : Type) [Finite K] (Jk : K → Type) [∀ k, Finite (Jk k)] (t : ∀ k, Jk k → Ω), (∀ k j, t k j ≠ 0) → ∃ (Y : RatModel o Ω) (πY : Y.Z ⟶ M₁.Z) (U₀ : Y.Z.Opens) (EE : Y.Lat S.J) (_ : ZHOut ρ Y U₀ EE), M₁.IsHom Y (AlgHom.id o Ω) πY ∧ IsProper πY ∧ S.admitted Y U₀ ∧ S.IsEE Y U₀ EE ∧ ∀ k, Nonempty (Jk k) → Y.HasDiv (t k) := by
  intro o Ω _ _ _ _ S ρ hBig M₁ hM₁ K _ Jk _ t ht
  obtain ⟨n, c, hc⟩ := RatModel.exists_isCl_of_isProjOver hM₁
  have hN2 := S.N_ge
  haveI hN0 : NeZero S.N := ⟨by omega⟩
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by omega)⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  haveI : Finite (AddSubgroup S.Gam) :=
    Finite.of_injective (fun H : AddSubgroup S.Gam => (H : Set S.Gam)) SetLike.coe_injective
  haveI : ∀ T₀ : AddSubgroup S.Gam, Finite (T₀ →+ ZMod S.N) := fun T₀ =>
    Finite.of_injective (fun f : T₀ →+ ZMod S.N => (f : T₀ → ZMod S.N)) DFunLike.coe_injective
  let K₁ := {k : K // Nonempty (Jk k)}
  let K₂ := {d : Σ T : AddSubgroup S.Gam, (T →+ ZMod S.N) // S.FF d.1 d.2 ≠ 0}
  letI : Fintype K₁ := Fintype.ofFinite _
  letI : Fintype K₂ := Fintype.ofFinite _
  let J₂ : K₂ → Type := fun d => S.J × (d.1.1 → ZMod ((S.r * S.N) ^ 2))
  let B := (∀ k : K₁, Jk k.1) × (∀ d : K₂, J₂ d)
  let b : B → Ω := fun p => (∏ k : K₁, t k.1 (p.1 k)) * ∏ d : K₂, S.FF d.1.1 d.1.2 (p.2 d)
  haveI : Finite B := inferInstance
  letI : Fintype (Fin (n + 1) × B) := Fintype.ofFinite _
  obtain ⟨p₀, hp₀⟩ : ∃ p, b p ≠ 0 := by
    choose κ hκ using fun d : K₂ => Function.ne_iff.1 d.2
    exact ⟨(fun k => k.2.some, κ), mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => ht _ _)
      (Finset.prod_ne_zero_iff.2 fun d _ => hκ d)⟩
  obtain ⟨i₀, hi₀, -⟩ := hc.1 (genericPoint M₁.Z)
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  obtain ⟨Y, U₀, EE, hO, hD, hE, ⟨FinalForm⟩⟩ := GlobalTheory.zhSt_holds o Ω S ρ hBig (Fin (n + 1) × B) (fun p => c p.1 * b p.2)
    ⟨(i₀, p₀), mul_ne_zero hi₀ hp₀⟩ (by
      refine SegreModel.finite_of_eq_top _ (SegreModel.subfield_eq_top hc _
        (Set.subset_union_left.trans Subfield.subset_closure) fun i j _ =>
        Subfield.subset_closure (Or.inr ⟨(x₀, i, p₀), (x₀, j, p₀), ?_⟩))
      rw [mul_div_mul_left _ _ hx₀, mul_div_mul_right _ _ hp₀])
  have hb : Y.HasDiv b := SegreModel.hasDiv_right hD
  have h1 := SegreModel.hasDiv_left (a := fun q : ∀ k : K₁, Jk k.1 => ∏ k : K₁, t k.1 (q k))
    (b := fun q : ∀ d : K₂, J₂ d => ∏ d : K₂, S.FF d.1.1 d.1.2 (q d)) hb
  have h2 := SegreModel.hasDiv_right (a := fun q : ∀ k : K₁, Jk k.1 => ∏ k : K₁, t k.1 (q k))
    (b := fun q : ∀ d : K₂, J₂ d => ∏ d : K₂, S.FF d.1.1 d.1.2 (q d)) hb
  obtain ⟨π, hπ⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id o Ω) (SegreModel.hasDiv_left hD)
  refine ⟨Y, π, U₀, EE, FinalForm, hπ, ?_, ⟨hO, fun T c' _ h => ?_⟩, hE, fun k hk => ?_⟩
  · haveI := M₁.sep
    haveI : IsProper (π ≫ M₁.s) := by
      rw [hπ.inducedModelMorphism_comp_structureMap]
      obtain ⟨m, j, hj, hs⟩ := hO.proj
      rw [← hs]
      have := isProper_str o m
      infer_instance
    exact IsProper.of_comp π M₁.s
  · exact SegreModel.hasDiv_of_prod (t := fun d : K₂ => S.FF d.1.1 d.1.2) h2 ⟨⟨T, c'⟩, h⟩
  · exact SegreModel.hasDiv_of_prod (t := fun k : K₁ => t k.1) h1 ⟨k, hk⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusFlatLocalBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.AmplePt

theorem exists_affine_nonzeroLocus_of_square : (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (M₀ : LB G.left), M₀.IsLB → ∀ s₀ : M₀.Sec, IsAffineOpen (nonzeroLocus s₀) → (∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ (R' : Type) (_ : CommRing R') (ρ : R →+* R'), ρ.Flat ∧ ∃ x' : ↥(pullback G.hom (spMap ρ)), pullback.fst G.hom (spMap ρ) x' = y ∧ ∃ n, 1 ≤ n ∧ ∃ s : (lbPow (M₀.pull (pullback.fst G.hom (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  intro H R _ _ _ G _ hG hab M₀ hM s₀ hV hy₀ y
  obtain ⟨z, hz1, hz2, hz3⟩ := _root_.GlobalTheory.ShearMeet.exists_fst_mul_mem R G hG (nonzeroLocus s₀) hy₀ y
  obtain ⟨hd, hn, hic, hfl, hinj⟩ := _root_.GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular R G.left G.hom hG.smooth ((snd G G).left z)
  let R' : Type := G.left.presheaf.stalk ((snd G G).left z)
  let ρ : R →+* R' := (Spec.preimage (G.left.fromSpecStalk ((snd G G).left z) ≫ G.hom)).hom
  have hc : G.left.fromSpecStalk ((snd G G).left z) ≫ G.hom = spMap ρ := (Spec.map_preimage _).symm
  obtain ⟨a, Φ, hpb, hΦ1, hΦ2, hΦ3⟩ := _root_.GlobalTheory.TransBaseChange.exists_section_translate R R' ρ G (G.left.fromSpecStalk ((snd G G).left z)) hc
  obtain ⟨x', hx'⟩ : ∃ x', Φ x' = z := by
    obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (snd G G).left)
      (g := G.left.fromSpecStalk ((snd G G).left z)) z (closedPoint R') Scheme.fromSpecStalk_closedPoint.symm
    refine ⟨hpb.isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw1]
  have e1 : pullback.fst G.hom (spMap ρ) x' = (fst G G).left z := by
    rw [← hΦ1, Scheme.Hom.comp_apply, hx']
  have e2 : ((𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a)).left ≫ pullback.fst G.hom (spMap ρ)) x' =
      (fst G G * snd G G).left z := by rw [hΦ2, Scheme.Hom.comp_apply, hx']
  have e3 : ((𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a⁻¹)).left ≫ pullback.fst G.hom (spMap ρ)) x' =
      (fst G G * (snd G G)⁻¹).left z := by rw [hΦ3, Scheme.Hom.comp_apply, hx']
  have hsemi' : IsSemiAbelian ((Over.pullback (spMap ρ)).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := hd; haveI := hn; haveI := hic
  have hab' := GlobalTheory.T.isAbelianScheme_genericFibre_injective_domain_map R R' ρ hinj G hab
  obtain ⟨t, ht⟩ := H R' ((Over.pullback (spMap ρ)).obj G) hsemi' hab'
    (M₀.pull (pullback.fst G.hom (spMap ρ))) (LB.isLB_pull hM _) a
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_sq_nonzeroLocus_of_translate_generator _ _ (pullback.fst G.hom (spMap ρ)) M₀ hM s₀ _ _ ⟨t, ht⟩
  haveI : IsAffineHom (pullback.fst G.hom (spMap ρ)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom (spMap ρ)).flip inferInstance
  have hW : IsAffineOpen (pullback.fst G.hom (spMap ρ) ⁻¹ᵁ nonzeroLocus s₀) := hV.preimage _
  have hL := _root_.GlobalTheory.TransAff.isAffineOpen_translates R' ((Over.pullback (spMap ρ)).obj G) hsemi'.separated a _ hW
  refine ⟨R', inferInstance, ρ, hfl, x', e1.trans hz1, 2, by norm_num, s, ?_, ?_⟩
  · rw [hs]
    exact ⟨(Scheme.Hom.mem_preimage _).2 (e2 ▸ hz2), (Scheme.Hom.mem_preimage _).2 (e3 ▸ hz3)⟩
  · rw [hs, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]; exact hL

end GlobalTheory.AmplePt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantTuplePrescribedMemberLinearFormStatement
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_tuple_prescribed_member_linearForm : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a₀ : Fin m → X), IsCone bar φ γ → NoEquivRays O γ → (∀ x, x ≠ 0 → ∃ j, 0 < γ j x x) → Supports bar φ d γ a₀ → ∀ (s : ℕ) (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ), PosW W → ∀ N₁ : ℕ, 3 ≤ N₁ → ∀ lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ j, 0 ≤ lam (γ j)) → ∀ μ : Fin (s + 1) → X, ∃ (D D' l : ℕ) (a : Fin l × Fin (s + 1) → X) (i₀ : Fin l), 1 ≤ D ∧ 1 ≤ D' ∧ (∀ u, a (i₀, u) = μ u) ∧ Dominant bar φ (D * d) N₁ W γ a ∧ ∀ β ∈ balForms bar X, lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + D' * lam β := by
  first | exact @GlobalTheory.Poinc.DomTuple.exists_dominant | exact GlobalTheory.Poinc.DomTuple.exists_dominant | (intros; apply GlobalTheory.Poinc.DomTuple.exists_dominant <;> assumption)
end

