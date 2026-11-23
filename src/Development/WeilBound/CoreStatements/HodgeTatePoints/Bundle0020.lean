module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0010
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegular
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLFiniteExt
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace PositivityTheory.HtPt.Mb.LFiniteExt.ChartFinite

theorem mem_regAt_genPt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (h : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨s, hs⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [genMap]
  rw [e]
  erw [Category.id_comp]
  exact hs

theorem exists_eq_div_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type}
    [Finite κ] {x : κ → Ω} (M : PModel o x) {c : κ} (hc : x c ≠ 0) (a : Ω) :
    ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v := by
  have hp : InChart M.ξ x c ⟨genPt M.ξ, specializes_rfl⟩ :=
    ⟨hc, fun c' => mem_regAt_genPt M.tie.gen _⟩
  obtain ⟨u, hu, v, hv, -, e⟩ :=
    ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hp).2 a).1 (mem_regAt_genPt M.tie.gen a)
  exact ⟨u, hu, v, hv, e⟩

theorem finite_integralClosure_chRing {o : Type} [CommRing o] [Algebra.EssFiniteType ℤ o] {Ω : Type}
    [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω']
    [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ)
    (hc : x c ≠ 0) :
    Module.Finite (chRing o (fun k => algebraMap Ω Ω' (x k)) c)
      (integralClosure (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω') := by
  let φ : Ω →ₐ[o] Ω' := IsScalarTower.toAlgHom o Ω Ω'
  have hφ : Function.Injective φ := φ.toRingHom.injective
  have hmap : (chRing o x c).map φ = chRing o (fun k => algebraMap Ω Ω' (x k)) c := by
    simp only [chRing]
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    congr 2
    ext j
    simp [φ]
  let e : chRing o x c ≃ₐ[o] chRing o (fun k => algebraMap Ω Ω' (x k)) c :=
    ((chRing o x c).equivMapOfInjective φ hφ).trans (Subalgebra.equivOfEq _ _ hmap)
  have he : ∀ a, ((e a : chRing o (fun k => algebraMap Ω Ω' (x k)) c) : Ω') =
      algebraMap Ω Ω' (a : Ω) := fun a => rfl
  haveI : Algebra.FiniteType o (chRing o (fun k => algebraMap Ω Ω' (x k)) c) := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩
  haveI : Algebra.EssFiniteType o (chRing o (fun k => algebraMap Ω Ω' (x k)) c) :=
    Algebra.EssFiniteType.of_finiteType _ _
  haveI : Algebra.EssFiniteType ℤ (chRing o (fun k => algebraMap Ω Ω' (x k)) c) :=
    Algebra.EssFiniteType.comp ℤ o _
  letI : Algebra (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω :=
    ((chRing o x c).val.toRingHom.comp e.symm.toRingEquiv.toRingHom).toAlgebra
  have hmapΩ : ∀ a : chRing o x c,
      algebraMap (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω (e a) = (a : Ω) := by
    intro a
    change ((e.symm (e a) : chRing o x c) : Ω) = a
    rw [AlgEquiv.symm_apply_apply]
  haveI : IsScalarTower (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω Ω' :=
    IsScalarTower.of_algebraMap_eq fun a => by
      obtain ⟨b, rfl⟩ := e.surjective a
      rw [hmapΩ]
      exact he b
  haveI : FaithfulSMul (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h => by
      obtain ⟨a, rfl⟩ := e.surjective a
      obtain ⟨b, rfl⟩ := e.surjective b
      rw [hmapΩ, hmapΩ] at h
      rw [Subtype.ext h]
  haveI : IsFractionRing (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω :=
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨u, hu, v, hv, rfl⟩ := exists_eq_div_chRing M hc z
      exact ⟨e ⟨u, hu⟩, e ⟨v, hv⟩, by rw [hmapΩ, hmapΩ]⟩
  exact PositivityTheory.HtPt.Mb.fin_closure _ Ω Ω'

end PositivityTheory.HtPt.Mb.LFiniteExt.ChartFinite


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.finite_ext : ∀ {o : Type} [CommRing o] [Algebra.EssFiniteType ℤ o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → Module.Finite (chRing o (fun k => algebraMap Ω Ω' (x k)) c) (integralClosure (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω') :=
  @PositivityTheory.HtPt.Mb.LFiniteExt.ChartFinite.finite_integralClosure_chRing
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLFracExt
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace PositivityTheory.HtPt.Mb.LFracExt.FracExt

def genCpt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Cpt ξ :=
  ⟨genPt ξ, specializes_rfl⟩

theorem mem_regAt_genCpt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ)
    (a : Ω) : a ∈ regAt ξ (genCpt ξ) := by
  obtain ⟨s, hs⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (genCpt ξ).2 = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [genMap, e]
  exact hs

theorem exists_frac {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    (M : PModel o x) {c : κ} (hc : x c ≠ 0) (a : Ω) :
    ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v := by
  have hp : InChart M.ξ x c (genCpt M.ξ) := ⟨hc, fun _ => mem_regAt_genCpt M.tie.gen _⟩
  obtain ⟨u, hu, v, hv, -, e⟩ := ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hp).2 a).1 (mem_regAt_genCpt M.tie.gen a)
  exact ⟨u, hu, v, hv, e⟩

theorem algebraMap_mem_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ) {a : Ω}
    (ha : a ∈ chRing o x c) : algebraMap Ω Ω' a ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c := by
  induction ha using Algebra.adjoin_induction with
  | mem a h =>
    obtain ⟨j, rfl⟩ := h
    rw [map_div₀]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ r
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem exists_integral_div : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω']
    [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → ∀ a : Ω', ∃ b v : Ω',
      IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) b ∧
        v ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c ∧ v ≠ 0 ∧ a = b / v := by
  intro o _ Ω _ _ κ _ x M Ω' _ _ _ _ _ c hc a
  haveI : IsFractionRing (chRing o x c) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨u, hu, v, hv, e⟩ := exists_frac M hc z
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, e⟩
  have halg : IsAlgebraic (chRing o x c) a := by
    haveI : Algebra.IsAlgebraic (chRing o x c) Ω' :=
      (IsFractionRing.comap_isAlgebraic_iff (A := chRing o x c) (K := Ω) (C := Ω')).2 inferInstance
    exact Algebra.IsAlgebraic.isAlgebraic a
  obtain ⟨y, hy0, hi⟩ := halg.exists_integral_multiple
  have hy0' : (y : Ω) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hv : algebraMap Ω Ω' (y : Ω) ≠ 0 := (map_ne_zero _).2 hy0'
  let φ : chRing o x c →+* chRing o (fun k => algebraMap Ω Ω' (x k)) c :=
    ((algebraMap Ω Ω').comp (chRing o x c).val.toRingHom).codRestrict _
      fun r => algebraMap_mem_chRing x Ω' c r.2
  have hb := IsIntegral.map_of_comp_eq φ (RingHom.id Ω') (by ext r; rfl) hi
  refine ⟨y • a, algebraMap Ω Ω' (y : Ω), hb, algebraMap_mem_chRing x Ω' c y.2, hv, ?_⟩
  have e : y • a = algebraMap Ω Ω' (y : Ω) * a := by
    rw [Algebra.smul_def]; rfl
  rw [e, mul_div_cancel_left₀ _ hv]

end PositivityTheory.HtPt.Mb.LFracExt.FracExt


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.frac_ext : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → ∀ a : Ω', ∃ b v : Ω', IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) b ∧ v ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c ∧ v ≠ 0 ∧ a = b / v :=
  @PositivityTheory.HtPt.Mb.LFracExt.FracExt.exists_integral_div
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLMorph
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LMorph.ChMorph

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem hom_eq_of_points {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    (hgen : IsCptGen ξ') (hall : ∀ q : X', genPt ξ' ⤳ q) {i : Ω →+* Ω'} {f g : X' ⟶ X}
    (hf : Dominates ξ' ξ f i) (hg : Dominates ξ' ξ g i) (hb : ∀ q, f q = g q) : f = g := by
  have hbase : f.base = g.base := by
    ext q
    exact hb q
  refine Scheme.Hom.ext hbase fun U => ?_
  ext s
  refine TopCat.Presheaf.section_ext X'.sheaf _ _ _ fun q hq => ?_
  have hqg : g q ∈ U := hq
  have hqf : f q ∈ U := by rw [hb q]; exact hqg
  have hpf : genPt ξ ⤳ f q := RegAtDom.map_genPt hf ▸ (hall q).map f.continuous
  have hpg : genPt ξ ⤳ g q := RegAtDom.map_genPt hg ▸ (hall q).map g.continuous
  have key : ∀ (a b : X) (_ : a = b) (ha : genPt ξ ⤳ a) (hb : genPt ξ ⤳ b) (h1 : a ∈ U) (h2 : b ∈ U),
      genMap ξ ⟨a, ha⟩ ((X.presheaf.germ U a h1).hom s) = genMap ξ ⟨b, hb⟩ ((X.presheaf.germ U b h2).hom s) := by
    rintro a _ rfl ha hb h1 h2
    rfl
  apply hgen.inj ⟨q, hall q⟩
  have e1 := RegAtDom.genMap_stalkMap hf q (hall q) hpf ((X.presheaf.germ U (f q) hqf).hom s)
  have e2 := RegAtDom.genMap_stalkMap hg q (hall q) hpg ((X.presheaf.germ U (g q) hqg).hom s)
  rw [Scheme.Hom.germ_stalkMap_apply] at e1 e2
  have e3 := key _ _ (hb q) hpf hpg hqf hqg
  rw [← e3, ← e1] at e2
  refine (congrArg (genMap ξ' ⟨q, hall q⟩) ?_).trans e2.symm
  exact TopCat.Presheaf.germ_res_apply X'.presheaf _ q hqg _

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  {o' : Type} [CommRing o'] [Algebra o' Ω'] {κ' : Type} {y : κ' → Ω'}

theorem specializes_of_dominates (M : PModel o x) (M' : PModel o' y) {i : Ω →+* Ω'} {f g : M'.X ⟶ M.X}
    (hf : Dominates M'.ξ M.ξ f i) (hg : Dominates M'.ξ M.ξ g i) (q : M'.X) : g q ⤳ f q := by
  let p' : Cpt M'.ξ := ⟨q, M'.all q⟩
  obtain ⟨h1, fa, -⟩ := RegAtDom.regAt_dominates M.X Ω M.ξ M'.X Ω' M'.ξ f i hf p'
  obtain ⟨h2, ga, gb⟩ := RegAtDom.regAt_dominates M.X Ω M.ξ M'.X Ω' M'.ξ g i hg p'
  replace gb := gb M'.tie.gen
  obtain ⟨c, hc0, hc⟩ := M.tie.cover ⟨f q, h1⟩
  obtain ⟨c', hc'0, hc'⟩ := M.tie.cover ⟨g q, h2⟩
  have hu : unitAt M.ξ ⟨g q, h2⟩ (x c / x c') := by
    refine gb _ (hc' c) ⟨?_, ga _ (hc' c), ?_⟩
    · exact (map_ne_zero i).2 (div_ne_zero hc0 hc'0)
    · rw [← map_inv₀, inv_div]
      exact fa _ (hc c')
  have hin : InChart M.ξ x c ⟨g q, h2⟩ := by
    refine ⟨hc0, fun j => ?_⟩
    have : x j / x c = x j / x c' * (x c / x c')⁻¹ := by
      field_simp
    rw [this]
    exact mul_mem (hc' j) hu.2.2
  refine specializes_iff_forall_open.2 fun V hV hq => ?_
  obtain ⟨a, ha, hau, hU⟩ := PositivityTheory.HtPt.Ma.basic o Ω κ x M c ⟨f q, h1⟩ ⟨V, hV⟩ ⟨hc0, hc⟩ hq
  have hag : a ∈ regAt M.ξ ⟨g q, h2⟩ := (M.tie.ring c hc0 a).1 ha _ hin
  refine hU ⟨g q, h2⟩ hin (gb a hag ⟨(map_ne_zero i).2 hau.1, fa a hau.2.1, ?_⟩)
  rw [← map_inv₀]
  exact fa _ hau.2.2

theorem existsUnique_dominates :
    ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x)
      (o' : Type) [CommRing o'] (Ω' : Type) [Field Ω'] [Algebra o' Ω'] (κ' : Type) [Finite κ'] (y : κ' → Ω')
      (M' : PModel o' y) (i : Ω →+* Ω'), (∀ p', p' ∈ ctrSet o x i M'.ξ) →
      ∃! f : M'.X ⟶ M.X, Dominates M'.ξ M.ξ f i := by
  intro o _ Ω _ _ κ _ x M o' _ Ω' _ _ κ' _ y M' i h
  obtain ⟨f, hf, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map M.X Ω M.ξ o κ x M'.X Ω' M'.ξ i M.tie M'.tie.gen M'.all
    (fun r p' => by
      obtain ⟨c, -, H⟩ := h p'
      exact H _ (Subalgebra.algebraMap_mem _ r))
    (fun p' => by
      obtain ⟨c, hc, H⟩ := h p'
      refine ⟨c, (map_ne_zero i).2 hc, fun c' => ?_⟩
      rw [← map_div₀]
      exact H _ (Algebra.subset_adjoin ⟨c', rfl⟩))
  refine ⟨f, hf, fun g hg => ?_⟩
  exact hom_eq_of_points M'.tie.gen M'.all hg hf fun q =>
    ((specializes_of_dominates M M' hf hg q).antisymm (specializes_of_dominates M M' hg hf q)).eq

end PositivityTheory.HtPt.Mb.LMorph.ChMorph


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.morph : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (o' : Type) [CommRing o'] (Ω' : Type) [Field Ω'] [Algebra o' Ω'] (κ' : Type) [Finite κ'] (y : κ' → Ω') (M' : PModel o' y) (i : Ω →+* Ω'), (∀ p', p' ∈ ctrSet o x i M'.ξ) → ∃! f : M'.X ⟶ M.X, Dominates M'.ξ M.ξ f i :=
  @PositivityTheory.HtPt.Mb.LMorph.ChMorph.existsUnique_dominates
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLNormChart
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LNormChart.ChNorm

theorem mem_of_isIntegral_of_inv_mem {Ω : Type} [Field Ω] (R : Subring Ω) {v : Ω} (hv : IsIntegral R v)
    (hv0 : v ≠ 0) (hu : v⁻¹ ∈ R) : v ∈ R := by
  obtain ⟨p, hp, hpv⟩ := hv
  have huv : v * v⁻¹ = 1 := mul_inv_cancel₀ hv0
  have key : ∀ i m : ℕ, i ≤ m → v ^ i * v⁻¹ ^ m = v⁻¹ ^ (m - i) := by
    intro i m him
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le him
    rw [pow_add, ← mul_assoc, ← mul_pow, huv, one_pow, one_mul, Nat.add_sub_cancel_left]
  rw [hp.as_sum] at hpv
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow] at hpv
  generalize p.natDegree = n at hpv
  cases n with
  | zero => simp at hpv
  | succ m =>
    have h2 := congrArg (· * v⁻¹ ^ m) hpv
    simp only [add_mul, Finset.sum_mul, zero_mul] at h2
    rw [pow_succ, mul_comm (v ^ m) v, mul_assoc, key m m le_rfl, Nat.sub_self, pow_zero, mul_one] at h2
    have e : v = -∑ i ∈ Finset.range (m + 1), algebraMap R Ω (p.coeff i) * v⁻¹ ^ (m - i) := by
      rw [eq_neg_iff_add_eq_zero, ← h2]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [mul_assoc, key i m (by simp at hi; omega)]
    rw [e]
    refine neg_mem (sum_mem fun i _ => mul_mem ?_ (pow_mem hu _))
    exact (p.coeff i).2

end PositivityTheory.HtPt.Mb.LNormChart.ChNorm

namespace PositivityTheory.HtPt.Mb.LNormChart.ChNorm

theorem chRing_join_iff {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    {d n : ℕ} (z : κ ⊕ Fin n → Ω) (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (hc : x c ≠ 0) (a : Ω) :
    a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔
      a ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) := by
  have hd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have hrat : ∀ q : κ × (κ ⊕ Fin n), joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) =
      x q.1 / x c * (z q.2 / x c ^ d) := by
    intro q
    simp only [joinCo, RingHom.id_apply, hz c]
    exact mul_div_mul_comm _ _ _ _
  have hT : chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) =
      Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨q, rfl⟩
      dsimp only
      rw [hrat]
      exact mul_mem (Algebra.subset_adjoin (Or.inl ⟨q.1, rfl⟩)) (Algebra.subset_adjoin (Or.inr ⟨q.2, rfl⟩))
    · apply Algebra.adjoin_le
      rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
      · have h1 : joinCo (RingHom.id Ω) x z (j, Sum.inl c) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈
            chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
          Algebra.subset_adjoin (Set.mem_range_self (j, Sum.inl c))
        rw [hrat, hz c, div_self hd, mul_one] at h1
        exact h1
      · have h1 : joinCo (RingHom.id Ω) x z (c, k) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈
            chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
          Algebra.subset_adjoin (Set.mem_range_self (c, k))
        rw [hrat, div_self hc, one_mul] at h1
        exact h1
  rw [hT]

end PositivityTheory.HtPt.Mb.LNormChart.ChNorm

namespace PositivityTheory.HtPt.Mb.LNormChart.ChNorm

theorem joinCo_div {Ω : Type} [Field Ω] {κ : Type} (x : κ → Ω) {d n : ℕ} (z : κ ⊕ Fin n → Ω)
    (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (q : κ × (κ ⊕ Fin n)) :
    joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) = x q.1 / x c * (z q.2 / x c ^ d) := by
  simp only [joinCo, RingHom.id_apply, hz c]
  exact mul_div_mul_comm _ _ _ _

theorem join_chart_normalisation : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (d n : ℕ) (z : κ ⊕ Fin n → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x z)), (∀ c, z (Sum.inl c) = x c ^ d) → (∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d)) → ∀ c, x c ≠ 0 → (∀ a : Ω, a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔ IsIntegral (chRing o x c) a) ∧ ∀ p' : Cpt M'.ξ, (∀ j, x j / x c ∈ regAt M'.ξ p') → InChart M'.ξ (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) p' := by
  intro o _ Ω _ _ κ _ x d n z M' hz hspan c hc
  have hd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have hyS : ∀ k, IsIntegral (chRing o x c) (z k / x c ^ d) := fun k =>
    (hspan c hc _).2 (Submodule.subset_span ⟨k, rfl⟩)
  have hxS : ∀ j, x j / x c ∈ chRing o x c := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  refine ⟨fun a => ?_, fun p' hp' => ?_⟩
  · rw [chRing_join_iff x z hz c hc a]
    constructor
    · intro ha
      have hle : Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) ≤
          (integralClosure (chRing o x c) Ω).restrictScalars o := by
        apply Algebra.adjoin_le
        rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2
            (isIntegral_algebraMap (x := (⟨_, hxS j⟩ : chRing o x c))))
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2 (hyS k))
      exact (mem_integralClosure_iff _ _).1 ((Subalgebra.mem_restrictScalars o).1 (hle ha))
    · intro ha
      have hSle : chRing o x c ≤
          Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) :=
        Algebra.adjoin_mono Set.subset_union_left
      refine Submodule.span_induction
        (p := fun b _ => b ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)))
        ?_ ?_ ?_ ?_ ((hspan c hc a).1 ha)
      · rintro _ ⟨k, rfl⟩
        exact Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩)
      · exact zero_mem _
      · intro a b _ _ ha hb
        exact add_mem ha hb
      · intro s b _ hb
        rw [Subalgebra.smul_def]
        exact mul_mem (hSle s.2) hb
  · obtain ⟨hctr, l, hl⟩ :=
      PositivityTheory.HtPt.Mb.join_charts o Ω κ (κ ⊕ Fin n) x Ω (RingHom.id Ω) z M' (fun _ => rfl) p'
    obtain ⟨c', -, hc'⟩ := hctr
    have ho : ∀ r : o, algebraMap o Ω r ∈ regAt M'.ξ p' := fun r =>
      hc' _ (Subalgebra.algebraMap_mem _ r)
    have hSle : ∀ a ∈ chRing o x c, a ∈ regAt M'.ξ p' := by
      intro a ha
      have h1 : a ∈ (chRing o x c).toSubring := ha
      rw [chRing, Algebra.adjoin_eq_ring_closure] at h1
      exact (Subring.closure_le.2 (Set.union_subset (by rintro _ ⟨r, rfl⟩; exact ho r)
        (by rintro _ ⟨j, rfl⟩; exact hp' j))) h1
    let φ : chRing o x c →+* regAt M'.ξ p' :=
      { toFun := fun s => ⟨s, hSle s s.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hvint : IsIntegral (regAt M'.ξ p') (z l / x c ^ d) :=
      IsIntegral.map_of_comp_eq φ (RingHom.id Ω) (by ext; rfl) (hyS l)
    obtain ⟨hzl, hzr⟩ := hl
    have hv : z l / x c ^ d ∈ regAt M'.ξ p' :=
      mem_of_isIntegral_of_inv_mem _ hvint (div_ne_zero hzl hd) (by rw [inv_div, ← hz c]; exact hzr _)
    have hy : ∀ k, z k / x c ^ d ∈ regAt M'.ξ p' := fun k => by
      have e : z k / x c ^ d = z k / z l * (z l / x c ^ d) := by field_simp
      rw [e]
      exact mul_mem (hzr k) hv
    refine ⟨?_, fun q => ?_⟩
    · simp only [joinCo, RingHom.id_apply, hz c]
      exact mul_ne_zero hc hd
    · rw [joinCo_div x z hz c q]
      exact mul_mem (hp' q.1) (hy q.2)

end PositivityTheory.HtPt.Mb.LNormChart.ChNorm


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.norm_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (d n : ℕ) (z : κ ⊕ Fin n → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x z)), (∀ c, z (Sum.inl c) = x c ^ d) → (∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d)) → ∀ c, x c ≠ 0 → (∀ a : Ω, a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔ IsIntegral (chRing o x c) a) ∧ ∀ p' : Cpt M'.ξ, (∀ j, x j / x c ∈ regAt M'.ξ p') → InChart M'.ξ (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) p' :=
  @PositivityTheory.HtPt.Mb.LNormChart.ChNorm.join_chart_normalisation
end

