module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorLiftEquivariant
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead.LiftEquiv

theorem map_rowAct_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (M : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R) :
    MvPolynomial.map φ (rowAct R M f) = rowAct S (M.map φ) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp, map_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [rowAct, map_sum, Matrix.map_apply]

theorem rowAct_detPol_eq {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    rowAct R M (detPol R n) = MvPolynomial.C M.det * detPol R n := by
  unfold detPol
  rw [AlgHom.map_det, RingHom.map_det (MvPolynomial.C : R →+* MvPolynomial (Fin n × Fin n) R), ← Matrix.det_mul]
  congr 1
  ext1 a s
  simp [rowAct, Matrix.mul_apply]

theorem rowAct_liftPol_eq {K C : Type} [CommRing K] [CommRing C] {n : ℕ} (e0 : K →+* C) (k : ℕ)
    (M : Matrix (Fin n) (Fin n) K) (f : MvPolynomial (Fin n × Fin n) K) :
    rowAct C (M.map e0) (liftPol e0 k f) = (e0 M.det) ^ k • liftPol e0 k (rowAct K M f) := by
  unfold liftPol
  have hd : (M.map e0).det = e0 M.det := (RingHom.map_det e0 M).symm
  rw [map_mul, map_pow, rowAct_detPol_eq, map_rowAct_eq, mul_pow, smul_eq_C_mul, map_pow, mul_assoc, hd]

theorem grp_tprod_eq (C : Type) [CommRing C] {ι : Type} (n : ℕ) (lamW : ι → ℕ → ℕ) (g : ι → GL (Fin n) C)
    (y : ∀ τ, dualWeyl C n n (res n (lamW τ))) :
    grp C n lamW g (PiTensorProduct.tprod C y) =
      PiTensorProduct.tprod C (fun τ => Formalism.UG.dualWeylRep C n n (res n (lamW τ)) (g τ) (y τ)) :=
  PiTensorProduct.map_tprod _ _

theorem scalar_eq {K C : Type} [Field K] [Field C] (e0 : K →+* C) {n : ℕ} (lam : DomWeight n) (k : ℕ) (c : ℤ)
    (h : ∀ hn : 0 < n, (k : ℤ) = lam.w ⟨n - 1, by omega⟩ + c) (g : GL (Fin n) K) :
    e0 (detPow K n (inside₂ K n g) lam.detShift) =
      ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map e0 g) ^ c : Cˣ) : C) *
        e0 ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ^ k := by
  have h1 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ((g : Matrix (Fin n) (Fin n) K).det)⁻¹ := by
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have h2 : ((inside₂ K n g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ((g : Matrix (Fin n) (Fin n) K).det)⁻¹ := by
    rw [← h1]; exact Matrix.det_transpose _
  have h3 : ((Matrix.GeneralLinearGroup.map e0 g : GL (Fin n) C) : Matrix (Fin n) (Fin n) C).det =
      e0 (g : Matrix (Fin n) (Fin n) K).det := (RingHom.map_det e0 _).symm
  have h0 : e0 (g : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    rw [map_ne_zero]; exact g.det_ne_zero
  simp only [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, h1, h2, h3, map_zpow₀, map_inv₀]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have he : lam.detShift = k - c := by
      rw [h hn]; simp [DomWeight.detShift, hn]
    rw [he, inv_zpow', inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ h0]
    congr 1
    ring

theorem phi_equivariant : ∀ (K C : Type) [Field K] [Field C] (e0 : K →+* C) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (Φ : VV K lam →ₛₗ[e0] NablaT C n lamW), Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ (g : ι → GL (Fin n) K) (v : VV K lam), Φ (rhoK lam (invTrK g) v) = lamG C n lamW c (fun τ => Matrix.GeneralLinearGroup.map e0 (g τ)) (Φ v) := by
  intro K C _ _ e0 ι _ _ n lam lamW c Φ hS hΦ g v
  obtain ⟨v, hv⟩ := v
  induction hv using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨x, hx, rfl⟩ := hP
    let M : ι → Matrix (Fin n) (Fin n) K := fun τ => ((g τ)⁻¹ : GL (Fin n) K)
    have hx' : ∀ τ, rowAct K (M τ) (x τ) ∈ nablaSq K n (lam τ) := fun τ =>
      Formalism.GradedWeylDivisibility.dualWeylRowStable K n n _ _ _ (hx τ)
    let w : VV K lam := ⟨Formalism.L2.DIV.ten fun τ => rowAct K (M τ) (x τ),
      Submodule.subset_span ⟨_, hx', rfl⟩⟩
    obtain ⟨y, hy, hyv⟩ := hΦ x ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩⟩ hx rfl
    obtain ⟨y', hy', hyw⟩ := hΦ _ w hx' rfl
    have hr : rhoK lam (invTrK g) ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩⟩ = detTwK lam (invTrK g) • w := by
      apply Subtype.ext
      show detTwK lam (invTrK g) • trAct (invTrK g) (∏ τ, blockEmb K τ (x τ)) =
        detTwK lam (invTrK g) • ∏ τ, blockEmb K τ (rowAct K (M τ) (x τ))
      congr 1
      rw [map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      exact (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n M).1 τ (x τ)
    have hg : (fun τ => Formalism.UG.dualWeylRep C n n (res n (lamW τ)) (Matrix.GeneralLinearGroup.map e0 (g τ)) (y τ)) =
        fun τ => (e0 (M τ).det) ^ (lamW τ (n - 1)) • y' τ := by
      funext τ
      apply Subtype.ext
      show rowAct C (((Matrix.GeneralLinearGroup.map e0 (g τ))⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) (y τ) =
        (e0 (M τ).det) ^ (lamW τ (n - 1)) • (y' τ : MvPolynomial (Fin n × Fin n) C)
      rw [hy, hy', ← map_inv]
      exact rowAct_liftPol_eq e0 _ (M τ) (x τ)
    rw [hr, LinearMap.map_smulₛₗ, hyw, hyv, lamG_apply, grp_tprod_eq, hg, MultilinearMap.map_smul_univ, smul_smul]
    congr 1
    rw [detTwK, map_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact scalar_eq e0 (lam τ) _ (c τ) (fun hn => hS τ ⟨n - 1, by omega⟩) (g τ)
  | zero =>
    show Φ (rhoK lam (invTrK g) 0) = lamG C n lamW c _ (Φ 0)
    simp only [map_zero]
  | add a b ha hb iha ihb =>
    show Φ (rhoK lam (invTrK g) (⟨a, ha⟩ + ⟨b, hb⟩)) = lamG C n lamW c _ (Φ (⟨a, ha⟩ + ⟨b, hb⟩))
    simp only [map_add (f := _)]
    rw [iha, ihb]
  | smul r a ha iha =>
    show Φ (rhoK lam (invTrK g) (r • ⟨a, ha⟩)) = lamG C n lamW c _ (Φ (r • ⟨a, ha⟩))
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, iha]

end GlobalTheory.FrameRead.LiftEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionWeightProjector
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem wComp_monomial_eq_ite {σ R M : Type} [CommSemiring R] [AddCommMonoid M] [DecidableEq M] (w : σ → M) (n : M) (d : σ →₀ ℕ) (c : R) :
    weightedHomogeneousComponent w n (monomial d c) = if Finsupp.weight w d = n then monomial d c else 0 := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_monomial]
  by_cases h : Finsupp.weight w d = n <;> by_cases hd : d = m
  · subst hd; simp [h]
  · simp [h, hd, coeff_monomial]
  · subst hd; simp [h]
  · simp [h, hd]

theorem wComp_mul_of_weight_zero {σ R M : Type} [CommSemiring R] [AddCommMonoid M] (w : σ → M) (n : M) (P Q : MvPolynomial σ R)
    (hQ : IsWeightedHomogeneous w Q 0) :
    weightedHomogeneousComponent w n (P * Q) = weightedHomogeneousComponent w n P * Q := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hq : AddMonoidAlgebra.coeff Q x.2 = 0
    · simp [hq]
    · have h2 := hQ hq
      have hm : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have e : Finsupp.weight w x.1 = n := by rw [← h, ← hm, map_add (f := _), h2, add_zero]
      rw [if_pos e]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hq : AddMonoidAlgebra.coeff Q x.2 = 0
    · simp [hq]
    · have h2 := hQ hq
      have hm : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have e : Finsupp.weight w x.1 ≠ n := by rw [← hm, map_add (f := _), h2, add_zero] at h; exact h
      rw [if_neg e, zero_mul]

theorem blockRed_eq_rename_map (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ f = rename (fun v => ((τ, v) : BVar N ι)) (map (Ideal.Quotient.mk (Ideal.span {ϖ})) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [blockRed, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p v hp => rw [map_mul, hp]; simp [blockRed]

theorem weight_blockW_mapDomain_self (N : ℕ) {ι : Type} [DecidableEq ι] (τ : ι) (d : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (blockW N τ) (Finsupp.mapDomain (fun v => ((τ, v) : BVar N ι)) d) = Finsupp.weight (rowW N N) d := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • blockW N τ i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp [blockW, rowW]

theorem weight_blockW_mapDomain_of_ne (N : ℕ) {ι : Type} [DecidableEq ι] {τ σ : ι} (h : σ ≠ τ) (d : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (blockW N τ) (Finsupp.mapDomain (fun v => ((σ, v) : BVar N ι)) d) = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • blockW N τ i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp [blockW, h]

end GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem blockRed_wComp_rowW (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (ϖ : O) (τ : ι) (v : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ (weightedHomogeneousComponent (rowW N N) v f) =
      weightedHomogeneousComponent (blockW N τ) v (blockRed O N ϖ τ f) := by
  classical
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [weightedHomogeneousComponent_apply, map_sum, map_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [blockRed_eq_rename_map, map_monomial, rename_monomial]
  rw [wComp_monomial_eq_ite, weight_blockW_mapDomain_self]

theorem blockRed_isWeightedHomogeneous_zero (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (ϖ : O) {τ σ : ι} (h : σ ≠ τ)
    (f : MvPolynomial (Fin N × Fin N) O) : IsWeightedHomogeneous (blockW N τ) (blockRed O N ϖ σ f) 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [blockRed_eq_rename_map, f.as_sum, map_sum, map_sum, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [mem_weightedHomogeneousSubmodule, map_monomial, rename_monomial]
  exact isWeightedHomogeneous_monomial _ _ _ (weight_blockW_mapDomain_of_ne N h d)

theorem redT_tprod_prod_blockRed (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O)
    (x : ∀ τ, dualWeyl O N N (res N (mu τ))) :
    redT O N mu ϖ (PiTensorProduct.tprod O x) = ∏ σ, blockRed O N ϖ σ (x σ) := by
  simp [redT]

theorem redT_isProj : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (τ : ι) (v : Fin N → ℕ) (a : Module.End O (NablaT O N mu)), IsProj O N mu τ v a → ∀ y : NablaT O N mu, redT O N mu ϖ (a y) = weightedHomogeneousComponent (blockW N τ) v (redT O N mu ϖ y) := by
  intro O _ N ι _ _ mu ϖ τ v a ha y
  have key : (redT O N mu ϖ).comp a =
      ((weightedHomogeneousComponent (blockW N τ) v).restrictScalars O).comp (redT O N mu ϖ) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    let yy : dualWeyl O N N (res N (mu τ)) := rowProj O N (res N (mu τ)) v (x τ)
    have hQ : IsWeightedHomogeneous (blockW N τ) (∏ σ ∈ ({τ}ᶜ : Finset ι), blockRed O N ϖ σ (x σ)) 0 := by
      have := IsWeightedHomogeneous.prod ({τ}ᶜ : Finset ι) (fun σ => blockRed O N ϖ σ (x σ)) (fun _ => (0 : Fin N → ℕ))
        (fun σ hσ => blockRed_isWeightedHomogeneous_zero O N ϖ (by simpa using hσ) (x σ))
      simpa using this
    rw [ha x yy rfl, redT_tprod_prod_blockRed, redT_tprod_prod_blockRed, Fintype.prod_eq_mul_prod_compl τ, Fintype.prod_eq_mul_prod_compl τ,
      Function.update_self, wComp_mul_of_weight_zero _ _ _ _ hQ]
    congr 1
    · show blockRed O N ϖ τ (weightedHomogeneousComponent (rowW N N) v (x τ : MvPolynomial (Fin N × Fin N) O)) = _
      exact blockRed_wComp_rowW O N ϖ τ v _
    · refine Finset.prod_congr rfl fun σ hσ => ?_
      rw [Function.update_of_ne (by simpa using hσ)]
  exact LinearMap.congr_fun key y

end GlobalTheory.HighWtEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveMapToAbelian
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjExpandRational

theorem evaluates_of_unif' {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (hu : R.LUnif) : fw.Evaluates := by
  intro i σ hσ hV
  refine fw.ev i σ hσ hV ?_
  by_contra hne
  have h0 := fw.ev0 i σ hσ hV hne
  have hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0 := fun x => by
    by_contra hx
    have h1 : LinearIndependent D.what₂.LL (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 hx
    have h2 := ((hu i σ).1 1 _ h1).ne_zero 0
    rw [h0] at h2
    exact h2 rfl
  refine hne ⟨0, fun f => ?_⟩
  have hf : f = 0 := (fw.e i).injective (Subtype.ext ((hx _).trans (hx _).symm))
  subst hf
  refine Eq.trans ?_ (GlobalTheory.phiC_zero_rule T hV (wtA (κ i))).symm
  rw [LinearMap.zero_apply, map_zero]
  rfl

end GlobalTheory.ConjExpandRational
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnrT
section
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspRep.ParLawsT

theorem eventually_unrT : ∀ (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hT : UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (π : CG E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w), (locParT hT π h).unr := by
  intro hF hT E Ω _ _ _ _ _ _ a π
  induction π using Quotient.inductionOn with | _ π =>
  filter_upwards [LocSph.locComp_spherical E a π] with w hw A h
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨v, h0, hv⟩ := hw σ hσ
  obtain ⟨ah, hah, H⟩ := isRecT_locRecT hT h
  have e : locParT hT (Quotient.mk _ π) h = locRecT hT h (cls (ParLaws.toRep σ)) := by
    have h1 : CG.IsLoc (Quotient.mk _ π : CG E a) w (Quotient.mk _ σ) := hσ
    unfold locParT
    rw [CG.IsLoc.unique E a _ w _ _ h1.loc h1]
    rfl
  rw [e]
  refine (GlobalTheory.RecT.isSpherical_iff_unr_of_lawsT E Ω A w h ah hah _ ((GlobalTheory.RecT.lawsT_iff ah hah _).2 H) _).1 ?_
  refine fixed_ne_bot_of_equiv (equivRep (ParLaws.toRep σ)) ((Submodule.ne_bot_iff _).2 ⟨v, fun x => ?_, h0⟩)
  obtain ⟨x, hx⟩ := x
  rw [SphCompletion.KO_completion] at hx
  obtain ⟨g, rfl⟩ := hx
  exact (hv g).trans (one_smul _ _).symm

end GlobalTheory.CuspRep.ParLawsT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicThetaReadsCurveThetaFunction
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact.ReadEx

theorem exists_vac_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∃ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), e0 ≠ 0 ∧ ∃ f₀, Reads ψ θ hS hT cc δ r e0 f₀ := _root_.GlobalTheory.VacRead.exists_vac_reads

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a}
  {hT : T.rank = d} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

theorem reads_zero : Reads ψ θ hS hT cc δ r 0 0 :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩

theorem reads_sum {k : ℕ} (G : Fin k → VC D a d → ℂ) (f : Fin k → WO S T → ℂ)
    (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) : Reads ψ θ hS hT cc δ r (∑ i, G i) (∑ i, f i) := by
  have key : ∀ s : Finset (Fin k), Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (reads_zero : Reads ψ θ hS hT cc δ r 0 0)
    · intro i s hi ih
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (h i).add ih
  exact key Finset.univ

theorem exists_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G ∈ TT D (tor0 D cc δ) a d, ∃ f, Reads ψ θ hS hT cc δ r G f := by
  intro D ψ θ S T a d hS hT cc δ r hP G hG
  obtain ⟨e0, he0, hne, f₀, hf₀⟩ := exists_vac_reads ψ θ S T hS hT cc δ r hP
  obtain ⟨k, c, z, rfl⟩ := GlobalTheory.ThetaSpan.theta_span D cc δ hP.crv a d e0 he0 hne G hG
  refine ⟨∑ i, c i • (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) •
    heisO ψ S T (finPt hS hT r (z i)) f₀), reads_sum _ _ fun i => ?_⟩
  have h := ((_root_.GlobalTheory.NormExact.heisO_finPt_reads ψ θ S T hS hT cc δ r hP e0 f₀ hf₀ (z i)).smul
    (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)))).smul (c i)
  convert h using 2
  ext x
  simp [Formalism.MainNotions.StandardLatticesGL3.Wd]

end GlobalTheory.NormExact.ReadEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintani
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW.BumpShintani

theorem map_comp_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := by
  ext i j; rfl

theorem pInf_tl {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ)) :
    GeneralLinearGroup.map (pInf E) (GlobalTheory.JSW.tl ϖ l) = 1 := by
  unfold GlobalTheory.JSW.tl
  rw [map_list_prod]
  apply List.prod_eq_one
  intro x hx
  simp only [List.map_map, List.mem_map] at hx
  obtain ⟨w, _, rfl⟩ := hx
  simp

theorem loc_tl {E : Type} [Field E] [NumberField E] {a : ℕ} (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ)) (v : HeightOneSpectrum (𝓞 E)) (hv : v ∉ l.support) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l) = 1 := by
  unfold GlobalTheory.JSW.tl
  rw [map_list_prod]
  apply List.prod_eq_one
  intro x hx
  simp only [List.map_map, List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  have hne : v ≠ w := fun h => hv (h ▸ (Finset.mem_toList.1 hw))
  simp only [Function.comp_apply, map_comp_eq, pFin_finGL]
  exact pLoc_locGL_of_ne hne _

theorem exists_bump_shintani : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) ∧ ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, F (g * finGL E (m + 1) (locGL E (m + 1) w k)) = F g) ∧ ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w) := by
  intro E _ _ _ m S hcond
  obtain ⟨b, hb1, hbN, hbC, hbU, hbS⟩ := GlobalTheory.T.exists_adelic_whittaker_equivariant_bump_mirabolic E m S
  refine ⟨b, hb1, hbN, hbC, ?_⟩
  intro π α hSat
  obtain ⟨φ, hφV, hφK, hφx⟩ := GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero E m S hcond π α hSat
  obtain ⟨F, hFV, hFb, hFU, hFinv, hFeig⟩ := GlobalTheory.T.kirillov_semilocal_smooth_bump E m S b hbN hbC hbU hbS π φ hφV hφx
  refine ⟨F, hFV, hFU, ?_, ?_⟩
  · intro w hw k hk g
    refine hFinv _ (pInf_finGL _) ?_ ?_ g
    · intro w' hw'
      have hne : w' ≠ w := fun h => hw (h ▸ hw')
      rw [map_comp_eq, pFin_finGL]
      exact pLoc_locGL_of_ne hne _
    · intro g'
      exact congrArg (fun ψ : Sm E (m + 1) => ψ.1 g') (hφK w hw k hk)
  · intro ϖ hϖ l hl p hp
    have hC := GlobalTheory.T.whittaker_mul_torus_iterated_factorisation E (m + 1) S hcond π α hSat φ hφV hφK ϖ hϖ l hl
    have hS : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l) = 1 :=
      fun w hw => loc_tl ϖ l w (fun h => hl w h hw)
    rw [hFeig _ _ (pInf_tl ϖ l) hS hC p hp.1, hFb p hp, mul_comm]

end GlobalTheory.JSW.BumpShintani
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocalStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_witt_model_local : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∃ ι, M.IsLinW B.ψ t b c ι := by
  first | exact @GlobalTheory.LinWSplit.exists_isLinW_at | exact GlobalTheory.LinWSplit.exists_isLinW_at | (intros; apply GlobalTheory.LinWSplit.exists_isLinW_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweHighestWeightSupStableLeStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeHighestWeight_sup_stable_le : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, KStable act N → KStable act N' → ∀ μ : Ix p q → ℚ, (N ⊔ N') ⊓ hwSub act μ ≤ (N ⊓ hwSub act μ) ⊔ (N' ⊓ hwSub act μ) := by
  first | exact @GlobalTheory.HoweR.hw_sup_le | exact GlobalTheory.HoweR.hw_sup_le | (intros; apply GlobalTheory.HoweR.hw_sup_le <;> assumption)
end

