module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2428
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2333
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2400
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSigmaStableSummandFromLiftedEigenCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory.HTSummand


set_option maxHeartbeats 800000 in
theorem summand_of_liftedCoords : ∀ {C : Type} [CommRing C] (I : Ideal C), I ^ 2 = ⊥ →
  ∀ {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (a : ℕ) (χ : Fin a → A →+* C) (π : Module.End C H), π * π = π → (∀ c, σ c * π = π * σ c) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F →
  ∀ (n : ℕ) (κ : Fin n → Fin a) (ℓ : Fin n → H →ₗ[C] C ⧸ I) (y : Fin n → H),
    (∀ k c x, ℓ k (σ c x) = Ideal.Quotient.mk I (χ (κ k) c) * ℓ k x) →
    (∀ x ∈ LinearMap.range π, x ∈ F ↔ ∀ k, ℓ k x = 0) →
    (∀ k, y k ∈ LinearMap.range π) → (∀ j k, ℓ j (y k) = if j = k then 1 else 0) →
  ∃ G₀ M₀ : Submodule C H, G₀ ⊓ M₀ = ⊥ ∧ G₀ ⊔ M₀ = LinearMap.range π ∧ (∀ c, ∀ x ∈ G₀, σ c x ∈ G₀) ∧
    G₀ ⊔ I • LinearMap.range π = F ⊓ LinearMap.range π ∧
    ∀ d ∈ LinearMap.range π, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G₀) ∧ d - ∑ i, w i ∈ G₀ := by
  intro C _ I hI A _ H _ _ σ hproj a χ π hπ hσπ F hIF n κ ℓ y hℓ hF hy hδ
  have hl : ∀ k, ∃ l : H →ₗ[C] C, (∀ c x, l (σ c x) = χ (κ k) c * l x) ∧
      ∀ x, Ideal.Quotient.mk I (l x) = ℓ k x :=
    fun k => GlobalTheory.T.exists_equivariantLift_functional_quotient_projective I σ hproj (χ (κ k)) (ℓ k) (hℓ k)
  choose l hlσ hlℓ using hl
  have hII : ∀ u v : C, u ∈ I → v ∈ I → u * v = 0 := by
    intro u v hu hv
    have h := Ideal.mul_mem_mul hu hv
    rw [← sq, hI] at h
    simpa using h
  have hσQ : ∀ c, ∀ x ∈ LinearMap.range π, σ c x ∈ LinearMap.range π := by
    rintro c _ ⟨z, rfl⟩
    refine ⟨σ c z, ?_⟩
    show (π * σ c) z = (σ c * π) z
    rw [hσπ]
  let e : Fin n → Fin n → C := fun j m => l j (y m) - if j = m then 1 else 0
  have he : ∀ j m, e j m ∈ I := by
    intro j m
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [e, map_sub, hlℓ, hδ]
    split_ifs <;> simp
  let x : Fin n → H := fun k => y k - ∑ m, e m k • y m
  have hxQ : ∀ k, x k ∈ LinearMap.range π := fun k =>
    Submodule.sub_mem _ (hy k) (Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hy m))
  have hlx : ∀ j k, l j (x k) = if j = k then 1 else 0 := by
    intro j k
    have h1 : ∀ m, e m k * l j (y m) = if j = m then e m k else 0 := by
      intro m
      have h0 := hII _ _ (he m k) (he j m)
      rw [show l j (y m) = e j m + (if j = m then 1 else 0) by simp [e], mul_add, h0]
      split_ifs <;> simp
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [x, map_sub, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_ite_eq]
    simp [e]
  let G₀ : Submodule C H := LinearMap.range π ⊓ ⨅ k, LinearMap.ker (l k)
  have hG : ∀ z, z ∈ G₀ ↔ z ∈ LinearMap.range π ∧ ∀ k, l k z = 0 := by
    intro z
    simp only [G₀, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  have key : ∀ q ∈ LinearMap.range π, q - ∑ k, l k q • x k ∈ G₀ := by
    intro q hq
    refine (hG _).2 ⟨Submodule.sub_mem _ hq (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (hxQ k)), fun j => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hlx]
  refine ⟨G₀, Submodule.span C (Set.range x), ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro z ⟨hzG, hzM⟩
    rw [Submodule.mem_bot]
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hzM
    have hc : ∀ j, c j = 0 := fun j => by
      have h := ((hG _).1 hzG).2 j
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, hlx] using h
    simp [hc]
  · refine le_antisymm (sup_le inf_le_left
      (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hxQ k))) ?_
    intro q hq
    rw [← sub_add_cancel q (∑ k, l k q • x k)]
    exact Submodule.add_mem_sup (key q hq) (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · intro c z hz
    rw [hG] at hz ⊢
    exact ⟨hσQ c z hz.1, fun k => by rw [hlσ, hz.2, mul_zero]⟩
  · apply le_antisymm
    · refine sup_le ?_ (le_inf ((Submodule.smul_mono le_rfl le_top).trans hIF)
        Submodule.smul_le_right)
      intro z hz
      rw [hG] at hz
      exact ⟨(hF z hz.1).2 (fun k => by rw [← hlℓ, hz.2 k, map_zero]), hz.1⟩
    · rintro z ⟨hzF, hzQ⟩
      have hlI : ∀ k, l k z ∈ I := fun k => by
        rw [← Ideal.Quotient.eq_zero_iff_mem, hlℓ]
        exact (hF z hzQ).1 hzF k
      rw [← sub_add_cancel z (∑ k, l k z • x k)]
      exact Submodule.add_mem_sup (key z hzQ) (Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem_smul (hlI k) (hxQ k))
  · intro d hd
    have hv : ∀ c k, σ c (x k) - χ (κ k) c • x k ∈ G₀ := by
      intro c k
      refine (hG _).2 ⟨Submodule.sub_mem _ (hσQ c _ (hxQ k)) (Submodule.smul_mem _ _ (hxQ k)),
        fun j => ?_⟩
      rw [map_sub, hlσ, map_smul, hlx, smul_eq_mul]
      split_ifs with h
      · subst h; ring
      · simp
    refine ⟨fun i => ∑ k ∈ Finset.univ.filter (fun k => κ k = i), l k d • x k, ?_, ?_⟩
    · intro i c
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]
      apply Submodule.sum_mem
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [← hk.2, smul_comm, ← smul_sub]
      exact Submodule.smul_mem _ _ (hv c k)
    · rw [Finset.sum_fiberwise]
      exact key d hd

end GlobalTheory.HTSummand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothWeightIntegralCombination
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.CombW

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}

theorem firstChernFormOfWeight_eq_hessianForm_chart {L : LB X.X} (ψ : Weight X.str σ L) (hψ : ψ.IsCInf) (c : AlgChart X.str σ X.dim)
    {y : CxPts X.str σ} (hy : y ∈ c.e.source) :
    c1W ψ ⟨(c, y), hy⟩ = GlobalTheory.ChernTop.matForm X.dim (c.hess ψ (pick ψ.isLB y) y) := by
  have hd := hψ.contDiffAt c hy (mem_pick ψ.isLB y)
  change ofValues _ = kappa • ∑ a, GlobalTheory.ChernTop.rowForm a _
  simp only [ofValues, GlobalTheory.ChernTop.rowForm, Fintype.linearCombination_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact congrArg (kappa * ·) (GlobalTheory.CurveDens.cHess_apply_eq_ddbar (contDiffAt_ofReal_comp hd) a b).symm

theorem firstChernFormOfWeight_tensor {A B : LB X.X} (ψ : Weight X.str σ A) (φ : Weight X.str σ B) (hψ : ψ.IsCInf) (hφ : φ.IsCInf) :
    c1W (ψ.tens φ) = c1W ψ + c1W φ := by
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have ha := mem_pick ψ.isLB y
  have hb := mem_pick φ.isLB y
  show c1W (ψ.tens φ) ⟨(c, y), hy⟩ = c1W ψ ⟨(c, y), hy⟩ + c1W φ ⟨(c, y), hy⟩
  rw [firstChernFormOfWeight_eq_hessianForm_chart _ (hψ.tens hφ) c hy, firstChernFormOfWeight_eq_hessianForm_chart _ hψ c hy, firstChernFormOfWeight_eq_hessianForm_chart _ hφ c hy,
    c.hess_eq (hψ.tens hφ) hy (i := (pick ψ.isLB y, pick φ.isLB y)) (mem_ptsIn_inf.2 ⟨ha, hb⟩) (mem_pick _ y),
    GlobalTheory.FlatMass.hess_tens hψ hφ hy ha hb, map_add]

theorem firstChernFormOfWeight_dual {B : LB X.X} (φ : Weight X.str σ B) (hφ : φ.IsCInf) :
    c1W φ.dual = -c1W φ := by
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have hb := mem_pick φ.isLB y
  show c1W φ.dual ⟨(c, y), hy⟩ = -c1W φ ⟨(c, y), hy⟩
  rw [firstChernFormOfWeight_eq_hessianForm_chart _ hφ.dual c hy, firstChernFormOfWeight_eq_hessianForm_chart _ hφ c hy,
    c.hess_eq hφ.dual hy (i := (pick φ.isLB y : B.ι)) hb (mem_pick _ y),
    GlobalTheory.FlatMass.hess_dual hφ hy hb, map_neg]

theorem firstChernFormOfWeight_trivial_zero : c1W (Weight.ofFun (p := X.str) (σ := σ) fun _ => 0) = 0 := by
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have h0 : (Weight.ofFun (p := X.str) (σ := σ) fun _ => (0:ℝ)).IsCInf := Weight.isCInf_ofFun (cInfAt_const 0)
  show c1W _ ⟨(c, y), hy⟩ = 0
  rw [firstChernFormOfWeight_eq_hessianForm_chart _ h0 c hy]
  have e : c.hess (Weight.ofFun (p := X.str) (σ := σ) fun _ => (0:ℝ)) (pick (Weight.ofFun (p := X.str) (σ := σ) fun _ => (0:ℝ)).isLB y) y = 0 :=
    GlobalTheory.FlatMass.cHess_zero _
  rw [e, map_zero]

def combSub (X : Var F) (σ : F →+* ℂ) : AddSubgroup (X.Dv × ((atlas X σ).Pt → Ev X.dim)) where
  carrier := {x | ∃ (L' : LB X.X) (r' : L'.ι → X.Fnˣ) (ψ' : Weight X.str σ L'),
    Presents x.1 L' r' ∧ ψ'.IsCInf ∧ c1W ψ' = x.2}
  zero_mem' := ⟨LB.triv X.X, fun _ => 1, Weight.ofFun fun _ => 0, presents_zero,
    Weight.isCInf_ofFun (cInfAt_const 0), firstChernFormOfWeight_trivial_zero⟩
  add_mem' := by
    rintro ⟨D, w⟩ ⟨E, u⟩ ⟨L, r, ψ, h1, h2, h3⟩ ⟨M, r', φ, h1', h2', h3'⟩
    exact ⟨_, _, ψ.tens φ, h1.tens h1', h2.tens h2', by rw [firstChernFormOfWeight_tensor _ _ h2 h2', h3, h3']; rfl⟩
  neg_mem' := by
    rintro ⟨D, w⟩ ⟨L, r, ψ, h1, h2, h3⟩
    have hdual : Presents (-D) (CechPic.dual L) (fun i => (r i)⁻¹) := by
      refine ⟨CechPic.isLB_dual h1.isLB, fun i j hij => ?_, fun i x hx => (h1.isEqn i x hx).neg⟩
      change (↑((r i)⁻¹) : X.Fn) =
        fnOf (L.U i ⊓ L.U j) hij ↑((L.g i j)⁻¹) * ↑((r j)⁻¹)
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_units_inv,
        h1.isRatSec i j hij, mul_inv]
    exact ⟨_, _, ψ.dual, hdual, h2.dual, by rw [firstChernFormOfWeight_dual _ h2, h3]; rfl⟩

end GlobalTheory.ChernCalc.CombW

open GlobalTheory.ChernCalc.CombW in
theorem GlobalTheory.ChernCalc.exists_comb_smoothWeight : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ c : κ → ℤ, ∃ (L' : LB X.X) (r' : L'.ι → X.Fnˣ) (ψ' : Weight X.str σ L'), Presents (∑ a, c a • Δ a) L' r' ∧ ψ'.IsCInf ∧ c1W ψ' = ∑ a, (c a : ℂ) • c1W (ψ a) := by
  intro F _ σ X κ _ Δ L r ψ h c
  have hm : (∑ a, c a • ((Δ a, c1W (ψ a)) : X.Dv × ((atlas X σ).Pt → Ev X.dim))) ∈ combSub X σ :=
    AddSubgroup.sum_mem _ fun a _ => AddSubgroup.zsmul_mem _ (show ((Δ a, c1W (ψ a)) : X.Dv × ((atlas X σ).Pt → Ev X.dim)) ∈ combSub X σ from ⟨L a, r a, ψ a, (h a).1, (h a).2, rfl⟩) _
  obtain ⟨L', r', ψ', h1, h2, h3⟩ := hm
  refine ⟨L', r', ψ', ?_, h2, ?_⟩
  · simpa [Prod.fst_sum] using h1
  · rw [h3, Prod.snd_sum]
    simp only [Prod.smul_snd]
    exact Finset.sum_congr rfl fun a _ => (Int.cast_smul_eq_zsmul ℂ (c a) _).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareDecompositionFiniteExtensionAmpleBun
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecFinite

theorem sqDec_of_finite_extension : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), SqDec ((Over.pullback (spMap (algebraMap K K'))).obj A) (L.pull (pullback.fst A.hom (spMap (algebraMap K K')))) (M.pull (pullback.fst A.hom (spMap (algebraMap K K')))) := by
  intro K _ _ A _ hA L M hL hM aL aM sL sM
  obtain ⟨k₀, A₀, _, π, L₀, M₀, hfg, hA₀, hπ, hL₀, hM₀, aL₀, aM₀, sL₀, sM₀, eL, eM⟩ :=
    _root_.GlobalTheory.AbFGSpread.spread_to_fg_subfield K A hA L M hL hM aL aM sL sM
  obtain ⟨σ⟩ := _root_.GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg K k₀ hfg
  obtain ⟨hC, aLC, sLC⟩ := _root_.GlobalTheory.FieldBaseChange.abelian_ample_symm_baseChange k₀ ℂ σ A₀ hA₀ L₀ hL₀ aL₀ sL₀
  obtain ⟨-, aMC, sMC⟩ := _root_.GlobalTheory.FieldBaseChange.abelian_ample_symm_baseChange k₀ ℂ σ A₀ hA₀ M₀ hM₀ aM₀ sM₀
  have hsq := _root_.GlobalTheory.SqDecC.sqDec_complex ((Over.pullback (spMap σ)).obj A₀) hC _ _ (pull_isLB hL₀ _) (pull_isLB hM₀ _) aLC aMC sLC sMC
  obtain ⟨k₁, _, _, _, hsq₁⟩ := _root_.GlobalTheory.SqDecFinite.main k₀ ℂ σ A₀ hA₀ L₀ M₀ hL₀ hM₀ hsq
  obtain ⟨K', _, _, _, e, he⟩ := _root_.GlobalTheory.exists_finite_ext_compat_of_finite k₀ K k₁
  exact ⟨K', inferInstance, inferInstance, inferInstance,
    _root_.GlobalTheory.SqDecTransport.transport k₀ K k₁ K' (algebraMap k₀ K) (algebraMap k₀ k₁) (algebraMap K K') e he.symm A₀ A π hπ L₀ M₀ L M hL₀ hM₀ hL hM eL eM hsq₁⟩

end GlobalTheory.SqDecFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricPolarisationFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetricPolarisation_finiteExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ IsGrpPullback P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) := by
  first | exact @GlobalTheory.PolDeg.exists_symmetric_pol | exact GlobalTheory.PolDeg.exists_symmetric_pol | (intros; apply GlobalTheory.PolDeg.exists_symmetric_pol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorDataBiextensionPeriods
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem tens_lam_core : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W), ∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb D.toPre.P.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  intro R _ _ I D D' r W T
  obtain ⟨v, hv, hvv⟩ := _root_.GlobalTheory.Mum.exists_transIso_linComb (L := D.toPre.P.L) (L' := D'.toPre.P.L) (tensφ T.pr) (tensε W) T.w T.w_gen
    D.toPre.P.isLB D'.toPre.P.isLB
    (fun K : ULift.{0} (Finset (Fin 2)) => (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left)
    (fun K => (-1 : ℤ) ^ (2 - K.down.card))
  obtain ⟨c, hc, hcv⟩ := _root_.GlobalTheory.Mum.cube_step (⟨D.toPre.P.L, D.toPre.rig, D.toPre.P.isLB, D.toPre.rig_gen⟩ : RigLB D.toPre.P.A)
    D.toPre.cub W T.pr T.pr_hom
  obtain ⟨u, hu, huv⟩ := GlobalTheory.T.exists_lineBundleIso_comp_linCombGenerator (A := abelian₂ D'.toPre.P.A D'.toPre.P.L) _ _
    (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1)
      (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2)
    (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) D.toPre.P.isLB (LB.isLB_linComb D'.toPre.P.isLB _ _) v hv c hc
  refine ⟨u, hu, fun a b z J J' hJ hJ' => ?_⟩
  have e1 := hvv _ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' hJ hJ'
  have e2 := hcv (TK R) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)) z J hJ
  rw [huv _ _ z J _ (hJ'.mem _ _) hJ, e2]
  refine (_root_.GlobalTheory.Mum.Tens.tau_periods R I D D' W T a b z J J' hJ hJ').trans ?_
  exact congrArg (· * _) (congrArg (· * _) e1.symm)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsNonvanishingFiniteSet
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt

theorem exists_tens_sec_finite_subset_nonzeroLocus : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsAmb q → ∀ (M : HermLB q) (S : Set Y), S.Finite →
      ∃ (A : HermLB q) (s : (M.tens A).B.Sec) (u : A.B.Sec), S ⊆ nonzeroLocus s ∧ S ⊆ nonzeroLocus u := by
  intro k _ Y q hq M S hS
  have := hq.isNoetherian
  obtain ⟨N, j, hj, e⟩ := hq.isProjOver
  let A₀ : HermLB q := (ProjSpace.hermitianTwistingSheaf k N).pull j e
  have hA : IsAmpleLB A₀.B := by
    dsimp [A₀, HermLB.pull, ProjSpace.hermitianTwistingSheaf, HermLB.fs]
    exact (isAmple_projective_O_one k N).pull_of_isClosedImmersion j
  obtain ⟨n, h₁, h₂⟩ := (tendsto_natCast_atTop_atTop.eventually
    ((hA.eventually_exists_finite_subset_nonzeroLocus M.isLB hS).and
      (hA.eventually_exists_finite_subset_nonzeroLocus (LB.isLB_triv Y) hS))).exists
  obtain ⟨s, hs⟩ := h₁ (CechPic.tens M.B (lbPow A₀.B n)) (isLB_tens M.isLB (isLB_lbPow A₀.isLB n)) (by
    rw [cls_tens M.isLB (isLB_lbPow A₀.isLB n), cls_lbPow A₀.isLB, natCast_zsmul])
  obtain ⟨u, hu⟩ := h₂ (lbPow A₀.B n) (isLB_lbPow A₀.isLB n) (by
    rw [cls_lbPow A₀.isLB, cls_triv, zero_add, natCast_zsmul])
  exact ⟨A₀.pow n, s, u, hs, hu⟩

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorsionPointOfComponentTuple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_pow {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (h : TensFacts W φ e wv)
    {v' : N'.Gt} {vs : Fin r → N.Gt} (hv : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := _root_.GlobalTheory.Mum.TensTor.gtRelV_io F N N' W φ e wv h 0
    have e0 : ∀ j, e 0 j = 0 := fun j => by
      have := h.2.2.1 0 0 j
      rw [add_zero] at this
      exact (add_eq_left.1 this.symm)
    simp only [e0, NumD.io_zero] at h0
    rw [pow_zero, pow_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact _root_.GlobalTheory.Mum.TensTor.gtRelV_mul F N N' W φ e wv h _ _ _ _ ih hv

theorem exists_ptRel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ) (ps : Fin r → QkPt D.toPre F k), ∃ p' : QkPt D'.toPre F k, PtRel T ν ν' p' ps := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' k ps
  have B := GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult F N ν
  have B' := GlobalTheory.Ex.GtValues.points_correspond R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  have hT := _root_.GlobalTheory.Mum.TensTor.tensFacts_holds R hR D D' W T F N N' ν ν'
  choose qs hqs using fun i => ((B.2.2.2.2 k).1 (ps i)).exists
  obtain ⟨v', hv'⟩ := _root_.GlobalTheory.Mum.TensTor.VExist.gtRelV_exists F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT fun j => (qs j).1.2
  obtain ⟨y', hy'⟩ := hT.2.2.2.1.2 fun i => (qs i).1.1.toAdd
  have hk : v' ^ k = N'.io y' := by
    refine _root_.GlobalTheory.Mum.TensTor.gtRelV_unique F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT _ _ (fun j => N.io (chi T ν ν' y' j))
      ?_ (_root_.GlobalTheory.Mum.TensTor.gtRelV_io F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT y')
    have hp := gtRelV_pow hT hv' k
    have e : ((fun j => (qs j).1.2) ^ k : Fin r → N.Gt) = fun j => N.io (chi T ν ν' y' j) := by
      funext j
      rw [Pi.pow_apply, hy']
      exact (qs j).2
    rwa [e] at hp
  let q' : N'.QT k := ⟨(Multiplicative.ofAdd y', v'), hk⟩
  obtain ⟨p', hp'⟩ := (B'.2.2.2.2 k).2.1 q'
  exact ⟨p', q', qs, hp', hqs, fun i => congrFun hy' i, hv'⟩

end GlobalTheory.Mum.TensTor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTrivialisationPowerLatticePointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorTrivialisation_powerLattice_points : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (A' : Over (Spec (CommRingCat.of R))) [GrpObj A'] (L' : LB A'.left), L'.IsLB → ∀ (pr : Fin r → (A' ⟶ D.P.A)) (w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))), w.IsGen → ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A') (y : Fin r → D.X), (∀ i, x ≫ pr i = D.c (y i)) → ∃ ψ : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => ptK x) (fun _ => -1)), ψ.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good D.P.L z J → Good L' z J' → val ψ (𝟙 _) z J' = gm (ptK x) z _ (w.s (fun k => J (ptK x ≫ tensφ pr k), J' (ptK x))) * ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J ^ W i j := by
  first | exact @GlobalTheory.Mum.tensPsi_exists | exact GlobalTheory.Mum.tensPsi_exists | (intros; apply GlobalTheory.Mum.tensPsi_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_thList : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x), Odd m → (m : K) ≠ 0 → N = m ^ (4 * g) → PolFib G L g x → ∃ (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c := by
  intro S G _ _ L ρ hL hρ g m N K _ _ x θ hm hmK hN hP
  subst hN
  obtain ⟨pt, hinj, hpt, hall⟩ := _root_.GlobalTheory.UMin.TorsList.exists_torsion_list S G L g m K x hmK hP
  have hex : ∀ a, ∃ c : K, ThG G L ρ m θ (pt a) (GlobalTheory.ZH.fn c) := by
    intro a
    exact _root_.GlobalTheory.UMin.exists_thG_of_polFib S G L ρ hL hρ g m K x θ (pt a) hm hmK hP (hpt a)
  choose c hc using hex
  exact ⟨pt, c, hinj, hc, hall⟩

end GlobalTheory.UMin
end

