module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0029
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0025
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0028
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0023
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0016
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0052
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmooth
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Twpdiv

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FinrankDualEqOfProjective
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Ge

theorem finrank_dual_eq_of_projective (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] : finrank A (Module.Dual A M) = finrank A M := by
  classical
  haveI := Module.finitePresentation_of_projective A M
  let S := nonZeroDivisors A
  let F := Localization S
  let f := LocalizedModule.mkLinearMap S M
  let g := Algebra.linearMap A F
  have e1 : finrank A (Module.Dual A M) = finrank A (LocalizedModule S M →ₗ[F] F) :=
    (IsLocalizedModule.finrank_eq S (IsLocalizedModule.mapExtendScalars S f g F) le_rfl).symm
  rw [e1, ← IsLocalization.finrank_eq F S le_rfl, Subspace.dual_finrank_eq,
    IsLocalization.finrank_eq F S le_rfl, IsLocalizedModule.finrank_eq S f le_rfl]

theorem ringOfIntegers_mem_range (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] {E : Type} [Field E] [NumberField E] (σ : E →+* K) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A K).range := by
  have h1 : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have h2 : IsIntegral A (σ (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨y, hy⟩

def qLin {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {p R N : ℕ} {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
    (D : HTChart A K c p R N Ω) (σ : E →+* K) : (Fin N → A) →ₗ[A] Ω where
  toFun := D.q σ
  map_add' x y := by simp [HTChart.q, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [HTChart.q, Finset.smul_sum, mul_smul]

theorem chart_sequence : ChartSequence := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D κ m hκ htest hproj'
  have hκR : κ ∣ (p : A) ^ R := dvd_trans (dvd_mul_right κ _) hκ
  have h1 := PositivityTheory.HtPt.Gc.chart_ii A K E c hc p R N Ω D κ hκR hproj' htest
  refine ⟨h1, ?_⟩
  intro σ d d' hd hd' hP1 hP2
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hint : ∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range :=
    fun σ a => ringOfIntegers_mem_range A K σ a
  obtain ⟨⟨i, hi⟩, -, hr⟩ :=
    PositivityTheory.HtPt.Ga.dual_map A K hinj E c hc p R N Ω D κ σ d m hint hd hκ h1.2 hP2
  obtain ⟨-, -, hsurj⟩ := PositivityTheory.HtPt.Ga.q_surj A K hinj E c hc p R N Ω D κ σ m (hint σ) hκ h1.2
  have hcz := PositivityTheory.HtPt.Gd.chart_comp_zero A K E c hc p R N Ω D κ σ d d' m i hκ hd hd' h1.2
    hP1 hP2 htest hi
  refine ⟨i, hi, hr i hi, ?_, hsurj⟩
  intro x
  constructor
  · rintro ⟨y, hy, hxy⟩
    by_cases hu : IsUnit (p : A)
    · obtain ⟨u, hu⟩ := hu
      refine ⟨0, (↑u⁻¹ : A) ^ m • x, ?_⟩
      rw [map_zero, zero_add, smul_smul, ← mul_pow, ← hu, Units.mul_inv, one_pow, one_smul]
    · haveI : Module.Finite A (D.omHT σ) := Module.Finite.iff_fg.mpr (PositivityTheory.HtPt.Gd.omHT_fg D σ)
      haveI : Module.Finite A (D.omHT (σ.comp c.toRingHom)) :=
        Module.Finite.iff_fg.mpr (PositivityTheory.HtPt.Gd.omHT_fg D _)
      let q' : (Fin N → A) →ₗ[A] D.omHT σ :=
        (qLin D σ).codRestrict (D.omHT σ) (PositivityTheory.HtPt.Ga.q_mem D σ)
      have hrank : finrank A (Module.Dual A (D.omHT (σ.comp c.toRingHom))) +
          finrank A (D.omHT σ) = N := by
        rw [finrank_dual_eq_of_projective A K (D.omHT (σ.comp c.toRingHom)), add_comm]
        exact PositivityTheory.HtPt.Gb.chart_rank A K E c hc p R N Ω D κ σ d d' hu hκR hd hd' hP1 hP2 htest
      obtain ⟨rr, hrr⟩ := hr i hi
      obtain ⟨w, x', hx⟩ := PositivityTheory.HtPt.Gd.split_exact A
        (Module.Dual A (D.omHT (σ.comp c.toRingHom))) (D.omHT σ) N ((p : A) ^ m) i rr q' hrank hrr
        (fun z => by
          obtain ⟨x0, y', hy', h⟩ := hsurj z.1 z.2
          exact ⟨x0, ⟨y', hy'⟩, Subtype.ext h⟩)
        (fun w => by
          obtain ⟨y0, hy0, h0⟩ := hcz w
          exact ⟨⟨y0, hy0⟩, Subtype.ext h0⟩)
        x ⟨⟨y, hy⟩, Subtype.ext hxy⟩
      exact ⟨w, x', hx⟩
  · rintro ⟨w, x', rfl⟩
    obtain ⟨y0, hy0, h0⟩ := hcz w
    refine ⟨y0 + D.q σ x', (D.omHT σ).add_mem hy0 (PositivityTheory.HtPt.Ga.q_mem D σ x'), ?_⟩
    have hq : ∀ z, D.q σ z = qLin D σ z := fun _ => rfl
    rw [hq, map_add (f := _), map_smul, ← hq, ← hq, h0, smul_add]
    all_goals rfl

end PositivityTheory.HtPt.Ge
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenRing
section
noncomputable section

namespace PositivityTheory.HtPt.Hcptgen

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem aeval_scale {σ K R A : Type} [Fintype K] [CommRing R] [CommRing A] [Algebra R A] (w : σ → K → ℕ)
    (c : K → A) (z : σ → A) {f : MvPolynomial σ R} {d : K → ℕ} (hf : IsWeightedHomogeneous w f d) :
    aeval (fun p => (∏ k, c k ^ w p k) * z p) f = (∏ k, c k ^ d k) * aeval z f := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, mul_add]
  | monomial m r hm =>
    rw [aeval_monomial, aeval_monomial, ← hm]
    have e : (∏ k, c k ^ (Finsupp.weight w m) k) = m.prod fun p n => (∏ k, c k ^ w p k) ^ n := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow,
        ← pow_mul, mul_comm]
      exact Finset.prod_comm
    rw [e]
    simp only [mul_pow, Finsupp.prod_mul]
    ring

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K] {J : K → Type}

theorem ratio_eq [DecidableEq K] (y : (Σ k, J k) → Ω) (s : ∀ k, J k) (hs : mseg y s ≠ 0) (k : K) (i : J k) :
    y ⟨k, i⟩ / y ⟨k, s k⟩ = mseg y (Function.update s k i) / mseg y s := by
  have hk : y ⟨k, s k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
  rw [div_eq_div_iff hk hs]
  unfold mseg
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
    Function.update_self]
  have e : ∏ j ∈ Finset.univ.erase k, y ⟨j, Function.update s k i j⟩ = ∏ j ∈ Finset.univ.erase k, y ⟨j, s j⟩ :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [e]
  ring


open GroundTheory.Heights₂.Heights.NumbersDVR in
theorem chartRing_mseg (y : (Σ k, J k) → Ω) (s : ∀ k, J k) (hs : mseg y s ≠ 0) :
    chartRing o (mseg y) s = Algebra.adjoin o (Set.range fun j => mseg y j / mseg y s) := by
  classical
  refine le_antisymm (fun u hu => ?_) (Algebra.adjoin_le ?_)
  · have hk : ∀ k, y ⟨k, s k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
    obtain ⟨n, U, hU, hv⟩ := GenericProjClosureDivisor.chart_form (O := o) (Φ := Ω) y (Pi.basisFun Ω (Fin 0))
      (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 s hs hu
    let c : Option (Option K) → Ω := fun b => b.elim 1 fun b' => b'.elim 1 fun k => y ⟨k, s k⟩
    let z : (Σ b, bundleIdx (bundleIdx J 0) 0 b) → Ω := fun p =>
      pairProjCoord y (Pi.basisFun Ω (Fin 0)) (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 p / c p.1
    have hc : ∀ b, c b ≠ 0 := by
      rintro (_ | _ | k)
      · exact one_ne_zero
      · exact one_ne_zero
      · exact hk k
    have h := aeval_scale _ c z hU
    have e1 : (fun p => (∏ b, c b ^ blockWeight (bundleIdx (bundleIdx J 0) 0) p b) * z p) =
        pairProjCoord y (Pi.basisFun Ω (Fin 0)) (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 := by
      funext p
      have : ∏ b, c b ^ blockWeight (bundleIdx (bundleIdx J 0) 0) p b = c p.1 := by
        rw [Finset.prod_eq_single p.1]
        · simp [blockWeight]
        · intro b _ hb
          simp [blockWeight, Pi.single_eq_of_ne hb]
        · simp
      rw [this]
      exact mul_div_cancel₀ _ (hc _)
    have e2 : ∏ b, c b ^ GenericProjClosureDivisor.vdeg (fun _ : K => n) b = segreVec y s ^ n := by
      simp [Fintype.prod_option, c, GenericProjClosureDivisor.vdeg, segreVec, Finset.prod_pow]
    rw [e1, e2, hv, Algebra.algebraMap_self_apply, mul_comm] at h
    have hu' : u = aeval z U := mul_left_cancel₀ (pow_ne_zero n hs) h
    have hz : aeval z U ∈ Algebra.adjoin o (Set.range z) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨U, rfl⟩
    rw [hu']
    refine Algebra.adjoin_mono ?_ hz
    rintro _ ⟨⟨_ | _ | k, i⟩, rfl⟩
    · exact Fin.elim0 i
    · exact Fin.elim0 i
    · exact ⟨Function.update s k i, (ratio_eq y s hs k i).symm⟩
  · rintro _ ⟨j, rfl⟩
    exact div_mem_chartRing _ _ _

end PositivityTheory.HtPt.Hcptgen
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieB
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ChartDer

noncomputable section

namespace PositivityTheory.HtPt.Htat.Lie

theorem mul_left_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec := by
  intro S G _ U hU C _ y u hu v w hv hw φ ψ χ hφ hψ hχ hs ev ew
  have hv' : LieEx.zsec y ≫ (v : LieEx.ob y C ⟶ G) = 1 := (LieEx.isTanAt_iff y G v).1 hv
  have hw' : LieEx.zsec y ≫ (w : LieEx.ob y C ⟶ G) = 1 := (LieEx.isTanAt_iff y G w).1 hw
  have z : ∀ t : LieEx.ob y C ⟶ G, LieEx.zsec y ≫ t = 1 → LieEx.hom y (0 : C →ₗ[C] C) ≫ t = 1 := fun t ht => by
    rw [LieEx.hom_zero, Category.assoc, ht, MonObj.comp_one]
  obtain ⟨t, ht⟩ : ∃ t : LieEx.ob y (C × C) ⟶ G, t = (LieEx.hom y (LinearMap.inl C C C) ≫ (v : LieEx.ob y C ⟶ G)) *
    (LieEx.hom y (LinearMap.inr C C C) ≫ (w : LieEx.ob y C ⟶ G)) := ⟨_, rfl⟩
  have hz : LieEx.zsec y ≫ t = 1 := by
    rw [ht, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, LieEx.zsec_hom, LieEx.zsec_hom, hv', hw',
      _root_.mul_one]
  have h1 : LieEx.hom y (LinearMap.fst C C C) ≫ t = v := by
    simp only [ht, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.fst_comp_inl,
      LinearMap.fst_comp_inr, LieEx.hom_id, Category.id_comp, z w hw', _root_.mul_one]
  have h2 : LieEx.hom y (LinearMap.snd C C C) ≫ t = w := by
    simp only [ht, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.snd_comp_inl,
      LinearMap.snd_comp_inr, LieEx.hom_id, Category.id_comp, z v hv', _root_.one_mul]
  have h3 : LieEx.hom y (LinearMap.fst C C C + LinearMap.snd C C C) ≫ t = v * w := by
    simp only [ht, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.add_comp,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr,
      add_zero, zero_add, LieEx.hom_id, Category.id_comp]
  have hzl : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom C C (C × C)).toRingHom) ≫ t.left =
      spMap u ≫ hU.fromSpec := (congrArg CommaMorphism.left hz).trans hu
  have hle : ⊤ ≤ t.left ⁻¹ᵁ U := by
    intro p _
    obtain ⟨q, rfl⟩ := LieVB.surj_fst (T := C) (M := C × C) p
    have e : t.left (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom C C (C × C)).toRingHom) q) =
        hU.fromSpec (spMap u q) := congrArg (fun f : Sp C ⟶ G.left => f q) hzl
    show t.left _ ∈ U
    rw [e]
    exact hU.range_fromSpec.subset (Set.mem_range_self _)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Γ(G.left, U) →+* TrivSqZeroExt C (C × C), spMap Φ ≫ hU.fromSpec = t.left :=
    ⟨_, TanMul.ringOf_spec (A := TrivSqZeroExt C (C × C)) hU t.left hle⟩
  have key : ∀ (l : C × C →ₗ[C] C), (LieEx.hom y l ≫ t).left =
      spMap ((TrivSqZeroExt.map l).toRingHom.comp Φ) ≫ hU.fromSpec := fun l => by
    rw [spMap_comp, Category.assoc, hΦ]
    rfl
  have e1 := TanMul.ring_inj hU (ev.symm.trans ((congrArg CommaMorphism.left h1).symm.trans (key _)))
  have e2 := TanMul.ring_inj hU (ew.symm.trans ((congrArg CommaMorphism.left h2).symm.trans (key _)))
  have e3 : χ = (TrivSqZeroExt.map (LinearMap.fst C C C + LinearMap.snd C C C)).toRingHom.comp Φ := by
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    · rw [hχ, ← hφ, e1]
      simp
    · rw [hs, e1, e2]
      simp
  rw [e3]
  exact (congrArg CommaMorphism.left h3).symm.trans (key _)

theorem exists_lieModel {S : Scheme.{0}} (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (v : Γ(G.left, U) →+* C)
    (h1 : (1 : Over.mk y ⟶ G).left = spMap v ≫ hU.fromSpec)
    {E : Type} [AddCommGroup E] [Module C E] (δ : E → Γ(G.left, U) → C)
    (hadd : ∀ e a b, δ e (a + b) = δ e a + δ e b)
    (hmul : ∀ e a b, δ e (a * b) = v a * δ e b + v b * δ e a)
    (hker : ∀ e b, δ e ((G.hom.appLE V U hUV).hom b) = 0)
    (hEadd : ∀ e e' a, δ (e + e') a = δ e a + δ e' a)
    (hEsmul : ∀ (c : C) e a, δ (c • e) a = c * δ e a)
    (hinj : ∀ e e', (∀ a, δ e a = δ e' a) → e = e')
    (hsurj : ∀ δ' : Γ(G.left, U) → C, (∀ a b, δ' (a + b) = δ' a + δ' b) →
      (∀ a b, δ' (a * b) = v a * δ' b + v b * δ' a) →
      (∀ b, δ' ((G.hom.appLE V U hUV).hom b) = 0) → ∃ e, ∀ a, δ e a = δ' a) :
    ∃ M : LieModel G y E, ∀ e, ∃ φ : Γ(G.left, U) →+* DualNumber C,
      (∀ a, (φ a).fst = v a) ∧ (∀ a, (φ a).snd = δ e a) ∧ (M.pt e).left = spMap φ ≫ hU.fromSpec := by
  obtain ⟨c1, c2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.TanChart.tan_iff_der S G U V hU hV hUV C y v h1
  let φ : E → (Γ(G.left, U) →+* DualNumber C) := fun e => dualOf v (δ e) (hadd e) (hmul e)
  have φfst : ∀ e a, (φ e a).fst = v a := fun e a => dualOf_fst ..
  have φsnd : ∀ e a, (φ e a).snd = δ e a := fun e a => dualOf_snd ..
  have ex : ∀ e, ∃ t : epsAt y ⟶ G, IsTanAt G y t ∧ t.left = spMap (φ e) ≫ hU.fromSpec :=
    fun e => c1 (φ e) (φfst e) fun b => by rw [φsnd, hker]
  choose pt ptan pleft using ex
  have spinj : ∀ ψ ψ' : Γ(G.left, U) →+* DualNumber C,
      spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec → ψ = ψ' := fun ψ ψ' h => by
    have h2 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h)
    simpa using congrArg CommRingCat.Hom.hom h2
  refine ⟨{ pt := pt, tan := ptan, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun e => ⟨φ e, φfst e, φsnd e, pleft e⟩⟩
  · intro e e' h
    have h2 := spinj _ _ (by rw [← pleft, ← pleft, h] : spMap (φ e) ≫ hU.fromSpec = spMap (φ e') ≫ hU.fromSpec)
    exact hinj _ _ fun a => by rw [← φsnd, h2, φsnd]
  · intro t ht
    obtain ⟨ψ, f1, f2, f3⟩ := c2 t ht
    obtain ⟨e, he⟩ := hsurj (fun a => (ψ a).snd) (fun a b => by simp)
      (fun a b => by
        simp only [map_mul, TrivSqZeroExt.snd_mul, f1]
        simp [mul_comm, add_comm]) f2
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    have h2 : φ e = ψ := RingHom.ext fun a => TrivSqZeroExt.ext (by rw [φfst, f1]) (by rw [φsnd, he])
    rw [pleft, f3, h2]
  · intro e e'
    refine Over.OverMorphism.ext ?_
    rw [mul_left_eq S G U hU C y v h1 (pt e) (pt e') (ptan e) (ptan e') (φ e) (φ e') (φ (e + e'))
      (φfst e) (φfst e') (φfst _) (fun a => by rw [φsnd, φsnd, φsnd, hEadd]) (pleft e) (pleft e'), pleft]
  · intro c e
    have h2 : φ (c • e) = (epsMul c).comp (φ e) := RingHom.ext fun a => TrivSqZeroExt.ext
      (by simp [epsMul, φfst]) (by simp [epsMul, φsnd, hEsmul])
    rw [pleft, pleft, h2, spMap_comp, Category.assoc]

theorem lieChart_of_smooth_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Sp R ⟶ S) (f : R) (U : G.left.Opens) (V : S.Opens)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V), RingHom.Smooth (G.hom.appLE V U hUV).hom →
  ∀ u : Γ(G.left, U) →+* Localization.Away f,
    (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec → LieChart G x f := by
  intro S G _ R _ x f U V hU hV hUV hsm u h1
  obtain ⟨P, i1, i2, i3, i4, i5, i6, d, dadd, dmul, dker, hP⟩ :=
    exists_diffModule (G.hom.appLE V U hUV).hom hsm f u
  have hunit : ∀ (C : Type) [CommRing C] [Algebra R C] (κ : Localization.Away f →+* C),
      κ.comp (algebraMap R (Localization.Away f)) = algebraMap R C →
      (1 : Over.mk (spMap (algebraMap R C) ≫ x) ⟶ G).left = spMap (κ.comp u) ≫ hU.fromSpec := by
    intro C _ _ κ hκ
    rw [one_left] at h1 ⊢
    simp only [Over.mk_hom] at h1 ⊢
    have e : spMap (algebraMap R C) = spMap κ ≫ spMap (algebraMap R (Localization.Away f)) := by
      rw [← spMap_comp, hκ]
    have h3 : ((spMap κ ≫ spMap (algebraMap R (Localization.Away f))) ≫ x) ≫ η[G].left =
        spMap κ ≫ (spMap (algebraMap R (Localization.Away f)) ≫ x) ≫ η[G].left := by
      simp only [Category.assoc]
    rw [e, h3, h1, spMap_comp κ u]
    exact (Category.assoc _ _ _).symm
  have key : ∀ (C : Type) [CommRing C] [Algebra R C] (hC : IsUnit (algebraMap R C f)),
      ∃ M : LieModel G (spMap (algebraMap R C) ≫ x) (P →ₗ[R] C), ∀ w,
        ∃ φ : Γ(G.left, U) →+* DualNumber C,
          (∀ a, (φ a).fst = ((IsLocalization.Away.lift f hC).comp u) a) ∧ (∀ a, (φ a).snd = w (d a)) ∧
          (M.pt w).left = spMap φ ≫ hU.fromSpec := by
    intro C _ _ hC
    have hκ := IsLocalization.Away.lift_comp (S := Localization.Away f) f hC
    obtain ⟨l1, l2, l3⟩ := hP C _ hκ
    exact exists_lieModel (E := P →ₗ[R] C) G U V hU hV hUV C _ _ (hunit C _ hκ)
      (fun (w : P →ₗ[R] C) a => w (d a))
      (fun w a b => by simp [dadd]) (fun w a b => by simp only [dmul, map_add (f := _), l1, RingHom.comp_apply])
      (fun w b => by simp [dker]) (fun w w' a => rfl) (fun c w a => by simp) l2 l3
  refine ⟨P, i1, i2, i3, i4, i5, i6, fun C _ _ hC => (key C hC).choose, ?_⟩
  intro C C' _ _ _ _ hC hC' c w
  obtain ⟨φ, f1, f2, f3⟩ := (key C hC).choose_spec w
  obtain ⟨φ', g1, g2, g3⟩ := (key C' hC').choose_spec (c.toLinearMap ∘ₗ w)
  have hc : c.toRingHom.comp (IsLocalization.Away.lift (S := Localization.Away f) f hC) =
      IsLocalization.Away.lift (S := Localization.Away f) f hC' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
    rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]
    exact c.comp_algebraMap
  have h2 : φ' = (dualMap c.toRingHom).comp φ := RingHom.ext fun a => TrivSqZeroExt.ext
    (by
      simp only [g1, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, f1]
      exact (RingHom.congr_fun hc (u a)).symm)
    (by
      simp only [g2, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, f2]
      rfl)
  rw [g3, f3, h2, spMap_comp, Category.assoc]

end PositivityTheory.HtPt.Htat.Lie
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.LevMapLev
section
noncomputable section

namespace PositivityTheory.HtPt.Gi

open TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT Coalgebra Bialgebra
  PositivityTheory.HtPt.Twpdiv

def levMap {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) : LevGrp La p n →* LevGrp La p n :=
  AddMonoidHom.toMultiplicative (Submodule.mapQ _ _ φ.toIntLinearMap (by
    rintro _ ⟨b, rfl⟩
    exact ⟨φ b, (map_nsmul φ _ b).symm⟩)).toAddMonoidHom

theorem levMap_lev {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) (a : La) :
    levMap p n φ (lev p n a) = lev p n (φ a) := rfl

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {La : Type} [AddCommGroup La] [Module.Free ℤ La]
  [Module.Finite ℤ La] {L : Type} [AddCommGroup L] [Module O L] {X : OrdTower p O La L} {G : PDivGroup p O}
  (e : ∀ n, G.A n ≃ₐ[O] X.A n) {τ : La →+ G.Tate}

def evG (n : ℕ) (t : LevGrp La p n) : G.A n →ₐ[O] O := (evalAt (X.A n) t).comp (e n).toAlgHom

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) : evG e n t g = (e n g).1 t := rfl

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem sepG (n : ℕ) : Sep (evG e n) := fun _ _ h => (e n).injective (Subtype.ext (funext h))

variable {e}

omit [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_lev (hre : X.Realises G e τ) (n : ℕ) (a : La) : evG e n (lev p n a) = (τ a).pt n :=
  AlgHom.ext fun g => (hre.pt a n g).symm

omit [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_one (hre : X.Realises G e τ) (n : ℕ) (g : G.A n) : evG e n 1 g = counit (R := O) g := by
  rw [← lev_zero, evG_lev hre, map_zero]
  rfl

omit [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_mul (hre : X.Realises G e τ) (n : ℕ) (s t : LevGrp La p n) (g : G.A n) :
    pair (evG e n s) (evG e n t) (comul (R := O) g) = evG e n (s * t) g := by
  obtain ⟨a, rfl⟩ := lev_surjective p n s
  obtain ⟨b, rfl⟩ := lev_surjective p n t
  rw [← lev_add, evG_lev hre, evG_lev hre, evG_lev hre, map_add (f := _)]
  exact (AlgHom.convMul_apply ((τ a).conv n) ((τ b).conv n) g).symm

def pullA {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) : G.A n →ₐ[O] G.A n :=
  Ord.liftTo (evG e n) (sepG e n) (fun t => evG e n (levMap p n φ t)) fun g =>
    ⟨(e n).symm ⟨fun t => (e n g).1 (levMap p n φ t), (h n (e n g).1 _ fun _ => rfl).1 (e n g).2⟩, fun t => by
      rw [evG_apply, AlgEquiv.apply_symm_apply]; rfl⟩

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_pullA {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) (t : LevGrp La p n) :
    (evG e n t).comp (pullA (e := e) h n) = evG e n (levMap p n φ t) := Ord.ev_liftTo _ _ _ _ t

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_pullA' {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) (t : LevGrp La p n) (g : G.A n) :
    evG e n t (pullA (e := e) h n g) = evG e n (levMap p n φ t) g := DFunLike.congr_fun (evG_pullA h n t) g

def pullB (hre : X.Realises G e τ) {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) :
    G.A n →ₐc[O] G.A n :=
  BialgHom.ofAlgHom (pullA (e := e) h n)
    (AlgHom.ext fun g => by
      change counit (R := O) (pullA (e := e) h n g) = counit (R := O) g
      rw [← evG_one hre, ← evG_one hre, evG_pullA', map_one])
    (AlgHom.ext fun g => (sepG e n).pair (sepG e n) _ _ fun z => by
      change pair _ _ (Algebra.TensorProduct.map _ _ (comul (R := O) g)) =
        pair _ _ (comul (R := O) (pullA (e := e) h n g))
      rw [pair_map, evG_pullA, evG_pullA, evG_mul hre, evG_mul hre, evG_pullA', map_mul])

def endG (hre : X.Realises G e τ) {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) : G ⟶ G where
  app := pullB hre h
  comm n := BialgHom.ext fun g => sepG e n _ _ fun t => by
    obtain ⟨a, rfl⟩ := lev_surjective p n t
    change (e n (G.res n (pullA (e := e) h (n + 1) g))).1 _ = evG e n _ (pullA (e := e) h n (G.res n g))
    rw [hre.res, evG_pullA', levMap_lev, evG_apply, hre.res, ← evG_apply, evG_pullA', levMap_lev, map_nsmul,
      evG_apply]

end PositivityTheory.HtPt.Gi

end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem PositivityTheory.HtPt.Gi.tower_end : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), (∀ (φ : La →+ La) (dφ : L →ₗ[O] L), X.Acts φ dφ → ∃ f : G ⟶ G, (∀ a, tateMap G G O f (τ a) = τ (φ a)) ∧ ∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) ∧ ∀ (H : PDivGroup p O) (f f' : G ⟶ H), (∀ a, tateMap G H O f (τ a) = tateMap G H O f' (τ a)) → f = f' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ La _ _ _ L _ _ X G e τ hre
  refine ⟨fun φ dφ h => ⟨PositivityTheory.HtPt.Gi.endG hre h, fun a => TateOver.ext (funext fun n => AlgHom.ext fun g => ?_),
    fun n g a => PositivityTheory.HtPt.Gi.evG_pullA' h n _ g⟩, fun H f f' hf =>
      PDivGroup.Hom.ext (funext fun n => BialgHom.ext fun g =>
        PositivityTheory.HtPt.Gi.sepG e n _ _ fun t => ?_)⟩
  · rw [tateMap_pt, ← PositivityTheory.HtPt.Gi.evG_lev hre, ← PositivityTheory.HtPt.Gi.evG_lev hre]
    exact PositivityTheory.HtPt.Gi.evG_pullA' h n _ g
  · obtain ⟨a, rfl⟩ := PositivityTheory.HtPt.Twpdiv.lev_surjective p n t
    rw [PositivityTheory.HtPt.Gi.evG_lev hre, ← tateMap_pt, ← tateMap_pt, hf]
end

