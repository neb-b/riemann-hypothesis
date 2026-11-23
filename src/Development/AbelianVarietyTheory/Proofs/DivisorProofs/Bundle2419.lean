module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPullbackHolomorphicZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataPeriodDiagonalMemMaxIdealMulGene
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DataPos

variable {V : Type} [CommRing V] [IsDomain V]

theorem lamPts_generic (D : DegPre V) (a b : D.X) (k : Fin 4) :
    lamPts (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b) k = jK V ≫ lamPts (D.c a) (D.c b) k := by
  have e : (toUnit (TK V)).left = jK V := GlobalTheory.Mum.UnitValuedLeadingSection.toUnit_TK_left V
  fin_cases k
  · show ((toUnit (TK V) ≫ D.c a) * (toUnit (TK V) ≫ D.c b)).left = jK V ≫ (D.c a * D.c b).left
    rw [← MonObj.comp_mul, Over.comp_left, e]
  · show (toUnit (TK V) ≫ D.c a).left = jK V ≫ (D.c a).left
    rw [Over.comp_left, e]
  · show (toUnit (TK V) ≫ D.c b).left = jK V ≫ (D.c b).left
    rw [Over.comp_left, e]
  · show (1 : TK V ⟶ D.P.A).left = jK V ≫ (1 : 𝟙_ _ ⟶ D.P.A).left
    rw [← e, ← Over.comp_left, MonObj.comp_one]

theorem lamPts_sec (D : DegPre V) (a b : D.X) (k : Fin 4) : lamPts (D.c a) (D.c b) k ≫ D.P.A.hom = 𝟙 _ := by
  fin_cases k <;> exact GlobalTheory.Mum.UnitValuedLeadingSection.left_comp_hom_unit _

theorem tau_diag_pos : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V))
    (y : D.toPre.X), y ≠ 0 → ∃ r ∈ maximalIdeal V, ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = algebraMap V _ r ∧
      ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (lamPts (D.toPre.c y) (D.toPre.c y)) negε),
        ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (TK V).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
          Good D.toPre.P.L z J → val (D.toPre.tau y y) ρ z J = gm ρ z ⊤ (unitOn k) * val u (ρ ≫ jK V) z J := by
  intro V _ _ _ D y hy
  obtain ⟨z₀⟩ : Nonempty (TK V).left := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.Mum.UnitValuedLeadingSection.exists_topGood V D.toPre.P z₀
  obtain ⟨u₁, hu₁⟩ :=
    GlobalTheory.Mum.UnitValuedLeadingSection.tau_diag_eq_unit_mul_psi_sq V D.toPre D.tau_bimult D.psi_even z₀ J₀ hJ₀ y
  obtain ⟨r₀, hr₀, e₀⟩ :=
    (GlobalTheory.Mum.UnitValuedLeadingSection.psiIn_iff_val V D.toPre z₀ J₀ hJ₀ y (maximalIdeal V)).1 (D.psi_pos y hy)
  have hr : (u₁ : V) * r₀ ^ 2 ∈ maximalIdeal V :=
    Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hr₀ 2 two_pos)
  have eT : ((val (D.toPre.tau y y) (𝟙 _) z₀ J₀ : ((TK V).left.presheaf.stalk z₀)ˣ) : (TK V).left.presheaf.stalk z₀) =
      GlobalTheory.Mum.UnitValuedLeadingSection.thK V z₀ (algebraMap V _ ((u₁ : V) * r₀ ^ 2)) := by
    rw [hu₁, Units.val_mul, Units.val_pow_eq_pow_val, e₀, map_mul, map_mul, map_pow, map_pow]
    rfl
  have hr0 : algebraMap V (FractionRing V) ((u₁ : V) * r₀ ^ 2) ≠ 0 := by
    intro h
    have := (val (D.toPre.tau y y) (𝟙 _) z₀ J₀).ne_zero
    rw [eT, h, map_zero] at this
    exact this rfl
  refine ⟨_, hr, Units.mk0 _ hr0, rfl, ?_⟩

  set k : (FractionRing V)ˣ := Units.mk0 _ hr0 with hk
  set φV := lamPts (D.toPre.c y) (D.toPre.c y) with hφVdef
  set φK := lamPts (toUnit (TK V) ≫ D.toPre.c y) (toUnit (TK V) ≫ D.toPre.c y) with hφKdef
  have hφ : ∀ k, φK k = jK V ≫ φV k := lamPts_generic D.toPre y y
  let jst : Fin 4 → D.toPre.P.L.ι := fun k => J₀ (jK V ≫ φV k)
  have hint : ∀ k, φV k ⁻¹ᵁ D.toPre.P.L.U (jst k) = ⊤ := fun k => hJ₀.2 (φV k) (lamPts_sec D.toPre y y k)
  have htop : LB.wchart D.toPre.P.L φV jst = ⊤ := eq_top_iff.2 fun p _ => Set.mem_iInter.2 fun k => by
    have : p ∈ φV k ⁻¹ᵁ D.toPre.P.L.U (jst k) := by rw [hint k]; trivial
    exact this
  have htopK : LB.wchart D.toPre.P.L φK jst = ⊤ := eq_top_iff.2 fun p _ => Set.mem_iInter.2 fun k => by
    have : jK V p ∈ φV k ⁻¹ᵁ D.toPre.P.L.U (jst k) := by rw [hint k]; trivial
    show p ∈ (φK k).base ⁻¹' (D.toPre.P.L.U (jst k) : Set _)
    rw [hφ k]
    exact this
  have hle : ∀ j, LB.wchart D.toPre.P.L φV j ≤ LB.wchart D.toPre.P.L φV j ⊓ LB.wchart D.toPre.P.L φV jst :=
    fun j => le_inf le_rfl (by rw [htop]; exact le_top)
  let u : LB.Gen (LB.LinComb D.toPre.P.L φV negε) := ⟨fun j => res (hle j) ((LB.LinComb D.toPre.P.L φV negε).g j jst)⟩
  obtain ⟨t, htg, ht⟩ := GlobalTheory.PolDeg.Wit.exists_tau D.toPre y y

  have hkey : t.s jst = res le_top (unitOn k) := by
    refine unit_ext fun x hx => ?_
    obtain rfl : x = z₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) x z₀
    refine Units.ext ?_
    rw [gm_res _ x _ hx]
    have e1 : gm (𝟙 _) x ((LB.LinComb D.toPre.P.L φK negε).U jst) (t.s jst) = val t (𝟙 _) x J₀ :=
      (val_of t (𝟙 _) x J₀ jst (fun k => by show J₀ (𝟙 _ ≫ φK k) = J₀ (jK V ≫ φV k); rw [Category.id_comp, hφ k])).symm
    rw [e1, ht _ _ x J₀ hJ₀.1, eT]
    have e2 := GlobalTheory.RefTauCoord.gm_unitOn (R := V) (RingHom.id (FractionRing V)) x k
    have e3 : spMap (RingHom.id (FractionRing V)) = 𝟙 _ := by
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [e3] at e2
    exact e2.symm
  refine ⟨u, fun Z ρ z J hJ => ?_⟩
  have hmK : ρ z ∈ LB.wchart D.toPre.P.L φK jst := by rw [htopK]; trivial
  have hmV : (ρ ≫ jK V) z ∈ LB.wchart D.toPre.P.L φV jst := by rw [htop]; trivial
  have L1 : val (D.toPre.tau y y) ρ z J =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φK negε ρ z (fun k => J (ρ ≫ φK k)) jst * gm ρ z ⊤ (unitOn k) := by
    rw [← ht Z ρ z J hJ]
    refine (gen_trans htg ρ z (hJ.mem φK ρ) hmK).trans ?_
    rw [hkey]
    exact congrArg (_ * ·) (gm_res _ z _ hmK _)
  have L2 : val u (ρ ≫ jK V) z J =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φV negε (ρ ≫ jK V) z (fun k => J ((ρ ≫ jK V) ≫ φV k)) jst := by
    have hm := hJ.mem φV (ρ ≫ jK V)
    exact (gm_res _ z (hle _) hm _).trans (gm_linComb _ _ _ _ z _ _ hm hmV)
  have L3 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φK negε ρ z (fun k => J (ρ ≫ φK k)) jst =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φV negε (ρ ≫ jK V) z (fun k => J ((ρ ≫ jK V) ≫ φV k)) jst := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF
    refine Finset.prod_congr rfl fun k _ => ?_
    have e : ρ ≫ φK k = (ρ ≫ jK V) ≫ φV k := by rw [hφ k, Category.assoc]
    have h : ∀ a b : Z ⟶ D.toPre.P.A.left, a = b →
        gm a z (D.toPre.P.L.U (J a) ⊓ D.toPre.P.L.U (jst k)) (D.toPre.P.L.g (J a) (jst k)) =
          gm b z (D.toPre.P.L.U (J b) ⊓ D.toPre.P.L.U (jst k)) (D.toPre.P.L.g (J b) (jst k)) := by
      rintro a b rfl; rfl
    exact congrArg (· ^ negε k) (h _ _ e)
  rw [L1, L2, L3, mul_comm]

end GlobalTheory.DataPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocal
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

noncomputable section

namespace GlobalTheory.CxForm

variable {n : ℕ}

theorem coefwise_add_of {T : (V n → ℂ) → ℂ} {F G : V n → Alt n}
    (h : ∀ S, T (fun x => (bas n).repr (F x) S + (bas n).repr (G x) S) =
      T (fun x => (bas n).repr (F x) S) + T (fun x => (bas n).repr (G x) S)) :
    coefwise T (fun x => F x + G x) = coefwise T F + coefwise T G := by
  simp only [coefwise, map_add (f := _), Finsupp.add_apply, h, add_smul, Finset.sum_add_distrib]

theorem coefwise_const_smul_of {T : (V n → ℂ) → ℂ} {F : V n → Alt n} (c : ℂ)
    (h : ∀ S, T (fun x => c • (bas n).repr (F x) S) = c • T (fun x => (bas n).repr (F x) S)) :
    coefwise T (fun x => c • F x) = c • coefwise T F := by
  simp only [coefwise, map_smul, Finsupp.smul_apply, h, Finset.smul_sum, smul_assoc]

theorem coefwise_sum_of {T : (V n → ℂ) → ℂ} {ι : Type} (t : Finset ι) {F : ι → V n → Alt n}
    (h : ∀ S, T (fun x => ∑ i ∈ t, (bas n).repr (F i x) S) = ∑ i ∈ t, T (fun x => (bas n).repr (F i x) S)) :
    coefwise T (fun x => ∑ i ∈ t, F i x) = ∑ i ∈ t, coefwise T (F i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coefwise, map_sum, Finsupp.finsetSum_apply, h, Finset.sum_smul]
  exact Finset.sum_comm

theorem delAt_dbarAt_linear_local : ∀ (n : ℕ) (v : V n),
    (∀ F G : V n → Alt n, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
      delAt (fun x => F x + G x) v = delAt F v + delAt G v ∧ dbarAt (fun x => F x + G x) v = dbarAt F v + dbarAt G v) ∧
    (∀ (F : V n → Alt n) (c : ℂ), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      delAt (fun x => c • F x) v = c • delAt F v ∧ dbarAt (fun x => c • F x) v = c • dbarAt F v) ∧
    (∀ (ι : Type) (t : Finset ι) (F : ι → V n → Alt n),
      (∀ i ∈ t, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) →
      delAt (fun x => ∑ i ∈ t, F i x) v = ∑ i ∈ t, delAt (F i) v ∧ dbarAt (fun x => ∑ i ∈ t, F i x) v = ∑ i ∈ t, dbarAt (F i) v) ∧
    (∀ F G : V n → Alt n, F =ᶠ[𝓝 v] G → delAt F v = delAt G v ∧ dbarAt F v = dbarAt G v) ∧
    (∀ c : Alt n, delAt (fun _ => c) v = 0 ∧ dbarAt (fun _ => c) v = 0) := by
  intro n v
  refine ⟨fun F G hF hG => ⟨?_, ?_⟩, fun F c hF => ⟨?_, ?_⟩, fun ι t F hF => ⟨?_, ?_⟩, fun F G h => ⟨?_, ?_⟩,
    fun c => ⟨?_, ?_⟩⟩
  · rw [delAt, delAt, delAt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_add_of fun S => by rw [GlobalTheory.del_add (hF S) (hG S)]; rfl, mul_add]
  · rw [dbarAt, dbarAt, dbarAt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_add_of fun S => by rw [GlobalTheory.dbar_add (hF S) (hG S)]; rfl, mul_add]
  · rw [delAt, delAt, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_const_smul_of c fun S => by rw [GlobalTheory.del_const_smul c (hF S)]; rfl, mul_smul_comm]
  · rw [dbarAt, dbarAt, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_const_smul_of c fun S => by rw [GlobalTheory.dbar_const_smul c (hF S)]; rfl, mul_smul_comm]
  · simp only [delAt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_sum_of t fun S => by
      rw [GlobalTheory.del_sum fun i hi => hF i hi S, ContinuousLinearMap.sum_apply], Finset.mul_sum]
  · simp only [dbarAt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_sum_of t fun S => by
      rw [GlobalTheory.dbar_sum fun i hi => hF i hi S, ContinuousLinearMap.sum_apply], Finset.mul_sum]
  · have e (S) : del (fun x => (bas n).repr (F x) S) v = del (fun x => (bas n).repr (G x) S) v :=
      GlobalTheory.del_congr (h.fun_comp fun y => (bas n).repr y S)
    simp only [delAt, coefwise, e]
  · have e (S) : dbar (fun x => (bas n).repr (F x) S) v = dbar (fun x => (bas n).repr (G x) S) v :=
      GlobalTheory.dbar_congr (h.fun_comp fun y => (bas n).repr y S)
    simp only [dbarAt, coefwise, e]
  · simp [delAt, coefwise]
  · simp [dbarAt, coefwise]

end GlobalTheory.CxForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorDbarOperatorPullbackConstantFormHolom
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.PullDelClosed

open GlobalTheory.CxForm.FormMul GlobalTheory.CxForm.PullClosed

variable {n m : ℕ}

theorem delAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {f : ι → V n → ℂ} (e : ι → Alt n)
    (hf : ∀ i, DifferentiableAt ℝ (f i) v) :
    delAt (fun x => ∑ i, f i x • e i) v = ∑ a, ∑ i, del (f i) v (coordVec a) • (dz a * e i) := by
  unfold delAt
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : coefwise (fun g => del g v (coordVec a)) (fun x => ∑ i, f i x • e i) =
      ∑ i, del (f i) v (coordVec a) • e i := by
    refine (bas n).ext_elem fun S => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [repr_coefwise, repr_sum_smul,
      del_sum (A := fun i x => f i x * (bas n).repr (e i) S) fun i _ => (hf i).mul (differentiableAt_const _),
      ContinuousLinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [del_mul (b := fun _ => (bas n).repr (e i) S) (hf i) (differentiableAt_const _), del_const]
    simp
  rw [h, Finset.mul_sum]
  simp only [mul_smul_comm]

theorem delAt_add {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    delAt (fun x => F x + G x) v = delAt F v + delAt G v := by
  unfold delAt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_add]
  congr 1
  refine (bas n).ext_elem fun S => ?_
  rw [map_add (f := _), Finsupp.add_apply, repr_coefwise, repr_coefwise, repr_coefwise, ← ContinuousLinearMap.add_apply,
    ← del_add (hF S) (hG S)]
  simp only [map_add (f := _), Finsupp.add_apply]

theorem sum_symm_dz {s : Fin n → Fin n → ℂ} (hs : ∀ a c, s a c = s c a) :
    ∑ a, ∑ c, s a c • (dz a * dz c : Alt n) = 0 := by
  have h := congrArg swap (sum_symm_dzb hs)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, map_smul, map_mul, map_zero, fun a : Fin n => (swap_dz a).2] using h

theorem delAt_pull_of_contDiffAt {φ : V n → V m} {v : V n} (hφ : ContDiffAt ℂ 2 φ v) (θ : Alt m) :
    delAt (fun x => pull (fderiv ℂ φ x) θ) v = 0 := by
  have hD : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hJ (w : V n) (b : Fin m) : HasFDerivAt (fun x => fderiv ℂ φ x w b)
      (((EuclideanSpace.proj b : V m →L[ℂ] ℂ).comp (ContinuousLinearMap.apply ℂ (V m) w)).comp
        (fderiv ℂ (fderiv ℂ φ) v)) v :=
    ((EuclideanSpace.proj b : V m →L[ℂ] ℂ).comp (ContinuousLinearMap.apply ℂ (V m) w)).hasFDerivAt.comp v
      hD.hasFDerivAt
  have hJR (w : V n) (b : Fin m) : DifferentiableAt ℝ (fun x => fderiv ℂ φ x w b) v :=
    (hJ w b).differentiableAt.restrictScalars ℝ
  have hJc (w : V n) (b : Fin m) : DifferentiableAt ℝ (fun x => conj (fderiv ℂ φ x w b)) v :=
    Complex.conjCLE.differentiableAt.comp v (hJR w b)
  have hs := hφ.isSymmSndFDerivAt (by simp)
  have hd (θ : Alt m) := (diff_and_closed hφ θ).1
  set P : Alt m → Prop := fun θ => delAt (fun x => pull (fderiv ℂ φ x) θ) v = 0 with hP
  have hconst (r : ℂ) : P (algebraMap ℂ _ r) := by
    simp only [hP, AlgHom.commutes]
    simp [delAt, coefwise]
  have hadd (a b : Alt m) (ha : P a) (hb : P b) : P (a + b) := by
    simp only [hP, map_add (f := _)] at ha hb ⊢
    rw [delAt_add (hd a) (hd b), ha, hb, add_zero]
  have hmul (a b : Alt m) (ha : P a) (hb : P b) : P (a * b) := by
    simp only [hP, map_mul] at ha hb ⊢
    obtain ⟨y, hy⟩ := delAt_mul (hd a) (hd b)
    rw [hy, ha, hb, zero_mul, mul_zero, add_zero]
  have hgen (i : Fin m ⊕ Fin m) : P (ExteriorAlgebra.ι ℂ (Pi.single i 1)) := by
    rcases i with b | b
    · change P (dz b)
      simp only [hP, fun L : V n →L[ℂ] V m => (pull_dz L b).1]
      rw [delAt_sum_smul _ fun c => hJR _ b]
      refine sum_symm_dz fun a c => ?_
      rw [del_eq_fderiv (hJ _ b).differentiableAt, del_eq_fderiv (hJ _ b).differentiableAt,
        (hJ _ b).fderiv, (hJ _ b).fderiv]
      simp [hs.eq (coordVec a) (coordVec c)]
    · change P (dzb b)
      simp only [hP, fun L : V n →L[ℂ] V m => (pull_dz L b).2]
      rw [delAt_sum_smul _ fun c => hJc _ b]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
      rw [del_conj, dbar_eq_zero (hJ _ b).differentiableAt]
      simp
  change P θ
  induction θ using ExteriorAlgebra.induction with
  | algebraMap r => exact hconst r
  | ι u =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pi_eq_sum_univ' u, map_sum]
    refine Finset.sum_induction _ P hadd (by simpa using hconst 0) fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
    exact hmul _ _ (hconst _) (hgen i)
  | mul a b ha hb => exact hmul a b ha hb
  | add a b ha hb => exact hadd a b ha hb

theorem delAt_dbarAt_pull_fderiv : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (γ : Alt n), IsOpen U →
    DifferentiableOn ℂ τ U →
    ∀ v ∈ U, delAt (fun x => pull (fderiv ℂ τ x) γ) v = 0 ∧ dbarAt (fun x => pull (fderiv ℂ τ x) γ) v = 0 :=
  fun _ _ _ _ γ hU hτ _ hv =>
    ⟨delAt_pull_of_contDiffAt (analyticOnNhd_of_holo hU hτ _ hv).contDiffAt γ, dbarAt_pull_fderiv hU hτ hv γ⟩

end GlobalTheory.CxForm.PullDelClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSwapSymmetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.DescSymm

open GlobalTheory.CechPic

theorem eSec_swap {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    eSec (A ⊗ A) ≫ (lift (snd A A) (fst A A)).left = eSec (A ⊗ A) := by
  apply GlobalTheory.SquareDescent.square_hom_ext A
  · rw [Category.assoc, ← Over.comp_left, lift_fst, GlobalTheory.SquareDescent.eSec_snd, GlobalTheory.SquareDescent.eSec_fst]
  · rw [Category.assoc, ← Over.comp_left, lift_snd, GlobalTheory.SquareDescent.eSec_fst, GlobalTheory.SquareDescent.eSec_snd]

theorem lbIso_swap : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hπ hA hA₀ gp hsq hP hP₀ iP ⟨r, hr⟩ iS
  have := hπ.fin
  have := hπ.etale
  have := hπ.onto
  have hA₂₀ : IsAbelianScheme (G2 A₀) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA₀ hA₀
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsq
  have hsw : (lift (snd A A) (fst A A)).left ≫ φ₂ = φ₂ ≫ (lift (snd A₀ A₀) (fst A₀ A₀)).left := by
    apply GlobalTheory.SquareDescent.square_hom_ext A₀
    · rw [Category.assoc, hsq.1, Category.assoc, ← Over.comp_left, lift_fst, ← Category.assoc, ← Over.comp_left,
        lift_fst, hsq.2]
    · rw [Category.assoc, hsq.2, Category.assoc, ← Over.comp_left, lift_snd, ← Category.assoc, ← Over.comp_left,
        lift_snd, hsq.1]
  have h₂ := LB.isLB_pull hP₀ (lift (snd A₀ A₀) (fst A₀ A₀)).left
  have hN := LB.isLB_div h₂ hP₀
  have cN := (CechPic.cls_div h₂ hP₀ hN).trans (by rw [CechPic.cls_pull hP₀ _ h₂])
  have z₀ : CechPic.pull (eSec (G2 A₀)) (CechPic.cls _ hP₀) = 0 :=
    (CechPic.cls_eq_zero_iff (LB.isLB_pull hP₀ _)).2 ⟨r, hr⟩
  have c₁ : CechPic.cls _ hP = CechPic.pull φ₂ (CechPic.cls _ hP₀) :=
    (CechPic.cls_eq_iff hP (LB.isLB_pull hP₀ _)).2 iP
  have c₂ : CechPic.cls _ hP = CechPic.pull (lift (snd A A) (fst A A)).left (CechPic.cls _ hP) :=
    ((CechPic.cls_eq_iff hP (LB.isLB_pull hP _)).2 iS).trans (CechPic.cls_pull hP _ _)
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π (G2 A₀) _ hA₂₀ hN
    inferInstance inferInstance inferInstance ((CechPic.cls_eq_zero_iff (LB.isLB_pull hN _)).1 ?_)
    ((CechPic.cls_eq_zero_iff (LB.isLB_pull hN _)).1 ?_)
  · rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, eSec_swap, z₀, sub_zero]
  · rw [CechPic.cls_pull hN, cN, ← hpb.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp φ₂,
      ← hsw, CechPic.pull_comp, ← c₁, ← c₂, sub_self, map_zero]

end GlobalTheory.DescSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedPolarisationKernelKilledSameInteger
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DescPolKer

theorem pow_eq_one_of_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (e : ℕ), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ (T : Over X) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over Y) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ e hG hA hA₀ hφ hsq hP hP₀ hw hker T x ⟨t, ht⟩
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact pow_zero x
  let T₁ : Over X := Over.mk (pullback.snd T.hom π)
  let ε : T₁.left ⟶ T.left := pullback.fst T.hom π
  have hε : Epi ε := GlobalTheory.GaloisCartDesc.epi_pullback_fst hG T.hom
  let x₁ : T₁ ⟶ A := Over.homMk (hφ.1.lift (ε ≫ x.left) (pullback.snd T.hom π)
    (by simp [ε, pullback.condition])) (hφ.1.lift_snd _ _ _)
  have hx₁ : x₁.left ≫ φ = ε ≫ x.left := hφ.1.lift_fst _ _ _

  have p₀ : IsPullback (snd A₀ T).left (fst A₀ T).left T.hom A₀.hom :=
    (IsPullback.of_hasPullback A₀.hom T.hom).flip
  have w₀ : ((snd A T₁).left ≫ ε) ≫ T.hom = ((fst A T₁).left ≫ φ) ≫ A₀.hom := by
    have a₁ := Over.w (snd A T₁)
    have a₂ := Over.w (fst A T₁)
    simp only [T₁, Over.mk_hom] at a₁
    rw [Category.assoc, Category.assoc, hφ.1.w, ← Category.assoc (fst A T₁).left, a₂, ← a₁, Category.assoc]
    simp [ε, pullback.condition]
    rfl
  let hm : (A ⊗ T₁).left ⟶ (A₀ ⊗ T).left := p₀.lift _ _ w₀
  have hc : (lift (snd A T₁ ≫ x₁) (fst A T₁)).left ≫ φ₂ = hm ≫ (lift (snd A₀ T ≫ x) (fst A₀ T)).left := by
    have p₂ : IsPullback (snd A₀ A₀).left (fst A₀ A₀).left A₀.hom A₀.hom :=
      (IsPullback.of_hasPullback A₀.hom A₀.hom).flip
    apply p₂.hom_ext
    · rw [Category.assoc, hsq.2, ← Category.assoc, GlobalTheory.TripleDescent.lift_left_snd, Category.assoc,
        GlobalTheory.TripleDescent.lift_left_snd, p₀.lift_snd]
    · rw [Category.assoc, hsq.1, ← Category.assoc, GlobalTheory.TripleDescent.lift_left_fst, Category.assoc,
        GlobalTheory.TripleDescent.lift_left_fst, Over.comp_left, Over.comp_left, Category.assoc, hx₁,
        ← Category.assoc, ← Category.assoc, p₀.lift_fst]
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨t', ht', -⟩ := GlobalTheory.FamFieldPull.exists_genPull w hwg hP₀ hP (K := PUnit)
    (fun _ => (lift (snd A T₁ ≫ x₁) (fst A T₁)).left) (fun _ => (lift (snd A₀ T ≫ x) (fst A₀ T)).left)
    (fun _ => 1) hm (fun _ => hc) t ht
  have h₁ : x₁ ^ e = 1 := hker T₁ x₁ ⟨t', ht'⟩

  let j : Over.mk (T₁.hom ≫ π) ⟶ T := Over.homMk ε (by simp [T₁, ε, pullback.condition])
  have hj : (j ≫ x).left = x₁.left ≫ φ := by simp [j, hx₁]
  have hpow : ∀ n : ℕ, ((j ≫ x) ^ (n + 1)).left = (x₁ ^ (n + 1)).left ≫ φ := by
    intro n
    induction n with
    | zero => simpa using hj
    | succ n ih =>
      rw [pow_succ, pow_succ x₁]
      exact hφ.2 T₁ (x₁ ^ (n + 1)) x₁ _ _ ih hj
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have hy : (j ≫ x) ^ (k + 1) * (j ≫ x) ^ (k + 1) = (j ≫ x) ^ (k + 1) := by
    apply Over.OverMorphism.ext
    rw [← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, hpow, hpow,
      show 2 * k + 1 + 1 = (k + 1) + (k + 1) by ring, pow_add, h₁, _root_.one_mul]
  have hy1 := mul_eq_left.1 hy
  apply Over.OverMorphism.ext
  rw [← cancel_epi ε]
  have e₁ : ε ≫ (x ^ (k + 1)).left = (j ≫ x ^ (k + 1)).left := by rw [Over.comp_left]; rfl
  have e₂ : ε ≫ (1 : T ⟶ A₀).left = (j ≫ (1 : T ⟶ A₀)).left := by rw [Over.comp_left]; rfl
  rw [e₁, e₂, MonObj.comp_pow, hy1, MonObj.comp_one]

end GlobalTheory.DescPolKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFormBundleMatricesAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_formBundle_matrices_adjoint : ∀ (K : Type) [Field K] (A A' : PolAV (Sp K)) (W : Matrix (Fin 8) (Fin 8) ℤ) (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ (f f' : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → (∀ u, f' ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → LBIso (cubeLB A'.A ![fst A'.A A'.A ≫ f, snd A'.A A'.A] A'.L) (cubeLB A'.A ![fst A'.A A'.A, snd A'.A A'.A ≫ f'] A'.L) := by
  first | exact @GlobalTheory.E8AdjointPairing.lbIso_cubeLB_adjoint | exact GlobalTheory.E8AdjointPairing.lbIso_cubeLB_adjoint | (intros; apply GlobalTheory.E8AdjointPairing.lbIso_cubeLB_adjoint <;> assumption)
end

