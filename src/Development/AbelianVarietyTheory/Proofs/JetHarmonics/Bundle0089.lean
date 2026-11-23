module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0024
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SpansOverField
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0001
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PremisesInhabited
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPosHermOfPositive
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointStepCompare

open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement
open GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace (Bil leastExponent IsIntegralFn IsPositiveFn IsBalancedSpace evalSum)

section Lattice

variable (E : Type) [Field E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]


end Lattice

section Phi

variable (E : Type) [Field E] [NumberField E]

theorem trace_pos {u : 𝓞 E} (h : ∀ τ : E →+* ℂ, 0 < (τ (u : E)).re) :
    0 < Algebra.trace ℤ (𝓞 E) u := by
  have h1 := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := (u : E)))
  rw [← Algebra.coe_trace_int, Complex.re_sum] at h1
  have h2 : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ (u : E)).re := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact Finset.sum_pos (fun σ _ => h σ.toRingHom) ⟨τ.toRatAlgHom, Finset.mem_univ _⟩
  rw [← h1] at h2
  simpa using h2

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem smul_ne_zero_of_free [Module.Free ℤ X] {c : 𝓞 E} {x : X} (hc : c ≠ 0) (hx : x ≠ 0) :
    c • x ≠ 0 := by
  intro h
  obtain ⟨r, hr, α, hα⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) c).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hc)
  have : r • x = 0 := by
    rw [← algebraMap_smul (𝓞 E) r x, hα, mul_comm, mul_smul, h, smul_zero]
  exact hx ((smul_eq_zero.1 this).resolve_left hr)

theorem projective_of_free [Module.Free ℤ X] [Module.Finite ℤ X] : Module.Projective (𝓞 E) X := by
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.Flat (𝓞 E) X := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨c, hc⟩
    by_contra hx
    exact smul_ne_zero_of_free E (nonZeroDivisors.coe_ne_zero c) hx hc
  have : Module.FinitePresentation (𝓞 E) X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

variable [IsCMField E]

theorem bar_bar (a : 𝓞 E) : bar E (bar E a) = a := by
  ext; simp [IsCMField.coe_ringOfIntegersComplexConj]

theorem emb_bar (τ : E →+* ℂ) (a : 𝓞 E) : τ (bar E a : E) = starRingEnd ℂ (τ (a : E)) :=
  IsCMField.complexEmbedding_complexConj E τ _

theorem trace_bar (a : 𝓞 E) : Algebra.trace ℤ (𝓞 E) (bar E a) = Algebra.trace ℤ (𝓞 E) a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.ringOfIntegersComplexConj E).restrictScalars ℤ) a

theorem sum_pos_of_isPosHerm [Module.Free ℤ X] [Module.Finite ℤ X] {n : ℕ} {x x' : Fin n → X}
    (hl : IsPosHerm E (outer E x x')) (γ : Bil X) (hγ : GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsBalanced E γ)
    (hp : ∀ a, 0 ≤ γ a a) (h0 : γ ≠ 0) : 0 < ∑ i, γ (x i) (x' i) := by
  obtain ⟨N, ι, _, ω, θ, hN, hsum, htr⟩ := exists_traceDual E
  have htr' : ∀ (f : X →ₗ[ℤ] ℤ) (a : X) (α : 𝓞 E),
      Algebra.trace ℤ (𝓞 E) (α * ∑ s, f (ω s • a) • θ s) = N * f (α • a) := fun f a α =>
    htr (f ∘ₗ (LinearMap.toSpanSingleton (𝓞 E) X a).restrictScalars ℤ) α
  let up : (X →ₗ[ℤ] ℤ) → Module.Dual (𝓞 E) X := fun f =>
    { toFun := fun a => ∑ s, f (ω s • a) • θ s
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        rw [← sub_eq_zero]
        refine eq_zero_of_trace_mul E fun α => ?_
        rw [mul_sub, map_sub, htr', RingHom.id_apply, smul_eq_mul, ← mul_assoc, htr', mul_smul,
          sub_self] }
  have hup : ∀ f a, up f a = ∑ s, f (ω s • a) • θ s := fun _ _ => rfl
  have key : ∀ f g : X →ₗ[ℤ] ℤ, Algebra.trace ℤ (𝓞 E) (outer E x x' (up f) (up g)) =
      N * ∑ p : Fin n × ι, f (ω p.2 • x p.1) * g (bar E (θ p.2) • x' p.1) := by
    intro f g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [outer, map_sum, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hup f, Finset.sum_mul, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e : θ s * bar E (up g (x' i)) = bar E (bar E (θ s) * up g (x' i)) := by
      conv_lhs => rw [← bar_bar E (θ s)]
      exact (map_mul (IsCMField.ringOfIntegersComplexConj E) _ _).symm
    rw [smul_mul_assoc, map_smul, e, trace_bar, hup g, htr', smul_eq_mul]
    ring
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h1 := sum_pos_of_tensor_pos X (Fin n × ι) (fun p => ω p.2 • x p.1) (fun p => bar E (θ p.2) • x' p.1)
    (fun f g => by
      apply mul_left_cancel₀ hN'.ne'
      rw [← key, ← key, hl.1 (up g) (up f), trace_bar])
    (fun f hf => by
      have hne : up f ≠ 0 := by
        intro h
        apply hf
        ext a
        have := htr' f a 1
        rw [← hup, h] at this
        simpa [hN.ne'] using this
      have := trace_pos E (hl.2 _ hne)
      rw [key] at this
      exact pos_of_mul_pos_right this hN'.le) γ hγ.1 hp h0
  have h2 : ∑ p : Fin n × ι, γ (ω p.2 • x p.1) (bar E (θ p.2) • x' p.1) =
      N * ∑ i, γ (x i) (x' i) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∀ s, γ (ω s • x i) (bar E (θ s) • x' i) = γ ((θ s * ω s) • x i) (x' i) := fun s => by
      rw [← hγ.2, mul_smul]
    simp only [this]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← LinearMap.sum_apply, ← map_sum, ← Finset.sum_smul, hsum, Nat.cast_smul_eq_nsmul, map_nsmul,
      LinearMap.smul_apply, nsmul_eq_mul]
  rw [h2] at h1
  exact pos_of_mul_pos_right h1 (Nat.cast_nonneg N)

def rankOne (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) : Bil X :=
  LinearMap.mk₂ ℤ (fun a c => (τ (η a : E) * starRingEnd ℂ (τ (η c : E))).re)
    (fun a a' c => by simp [add_mul])
    (fun k a c => by simp [mul_assoc, mul_add])
    (fun a c c' => by simp [mul_add])
    (fun k a c => by simp [mul_add, mul_left_comm])

omit [IsCMField E] in
theorem rankOne_apply (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) (a c : X) :
    rankOne E η τ a c = (τ (η a : E) * starRingEnd ℂ (τ (η c : E))).re := rfl


theorem bar_outer {n : ℕ} (x x' : Fin n → X) (η η' : Module.Dual (𝓞 E) X) :
    bar E (outer E x x' η η') = outer E x' x η' η := by
  have := bar_bar E
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [outer, bar, map_sum, map_mul] at this ⊢
  simp only [this, mul_comm]

theorem re_outer {n : ℕ} (x x' : Fin n → X) (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) :
    (τ (outer E x x' η η : E)).re = ∑ i, rankOne E η τ (x i) (x' i) := by
  simp only [outer, rankOne_apply]
  push_cast
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← emb_bar]

variable {S : Submodule ℝ (Bil X)}

variable [Module.Free ℤ X] [Module.Finite ℤ X]

theorem exists_admissible (hS : IsBalancedSpace E S) :
    ∃ l : S →ₗ[ℝ] ℝ, IsIntegralFn S l ∧ IsPositiveFn S l := by
  let b := Module.finBasis ℤ X
  refine ⟨evalSum S b b, GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum S _ _, fun γ h1 h2 => ?_⟩
  refine sum_pos_of_isPosHerm E ⟨fun η η' => (bar_outer E _ _ _ _).symm, fun η hη τ => ?_⟩ _
    ((hS _).1 γ.2) h1 fun h => h2 (Subtype.ext h)
  rw [re_outer]
  simp only [rankOne_apply, Complex.mul_conj, Complex.ofReal_re]
  refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) fun h0 => hη ?_
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 h0.symm
  have : η.restrictScalars ℤ = 0 := b.ext fun i => by simpa using hz i (Finset.mem_univ _)
  exact LinearMap.ext fun a => LinearMap.congr_fun this a

end Phi

abbrev FormSpaces : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (_ : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)

abbrev FormValues (S : FormSpaces) : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    S E cj Y → ℝ

section Clauses

variable {S : FormSpaces} {φ : FormValues S}

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  (D : DegData V (maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)

end Clauses

end GlobalTheory.PointStepCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProdPullZero
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxPull

open GlobalTheory.BoxPhi

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {F : Type} [Field F] [Algebra (FractionRing V) F] {O : Type} [CommRing O] [StarRing O]

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  by_cases h : f y ∈ U
  · rw [gs_eq f y U h, map_zero, map_zero]
  · exact dif_neg h

theorem prod_pull_zero (D : DegData V (maximalIdeal V)) [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N : ℕ)
    (hN : 1 ≤ N) (χ : D.toPre.X) {U : Type} [CommGroup U] (h : ((TF (R := V) F).left ⟶ D.toPre.P.A.left) → U) :
    ∏ i, h ((DegPre.zF D.toPre F).left ≫ pullφ D F oa a χ i) ^ pullε k N i =
      h (1 : TF (R := V) F ⟶ D.toPre.P.A).left ^ (k * (N - 1)) := by
  have := oa.onB.hom a
  have p₃ := prod_fam D.toPre F (DegPre.zF D.toPre F) (star a • χ) (k * N) h
  have p₄ := prod_fam D.toPre F (DegPre.zF D.toPre F ≫ aF D F oa a) χ k h
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D.toPre F ≫ aF D F oa a) ≫ DegPre.prB D.toPre F = 1 := by
    rw [Category.assoc, aF, lift_snd, ← Category.assoc, z₂, MonObj.one_comp]
  rw [z₂, _root_.mul_one] at p₃
  rw [z₃, _root_.mul_one] at p₄
  simp only [Over.comp_left, Category.assoc] at p₄
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).trans ?_
  rw [← zpow_natCast, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hN]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem aF_pr {j : ℕ} {D D' : DegData V (maximalIdeal V)} (pD : IsPowDeg D'.toPre D.toPre j)
    [Module O D.toPre.X] [Module O D'.toPre.X] (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O) (a : O) (i : Fin j)
    (hact : oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) :
    (aF D' F oa' a).left ≫ prB pD F i = prB pD F i ≫ (aF D F oa a).left := by
  refine congrArg (fun q => q.left) (?_ : aF D' F oa' a ≫ (TF (R := V) F ◁ pD.pw.pr i) =
    (TF (R := V) F ◁ pD.pw.pr i) ≫ aF D F oa a)
  apply CartesianMonoidalCategory.hom_ext
  · simp [aF]
  · simp [aF, hact]

theorem pullAl_box {j : ℕ} {D D' : DegData V (maximalIdeal V)} (pD : IsPowDeg D'.toPre D.toPre j)
    [Module O D.toPre.X] [Module O D'.toPre.X]
    (hx : ∀ (a : O) (x : D'.toPre.X) (i : Fin j), pD.xe (a • x) i = a • pD.xe x i)
    (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O)
    (hact : ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) (a : O) (N k : ℕ) (hN : 1 ≤ N)
    (s : Fin j → Fam D.toPre F k) (s' : Fin j → Fam D.toPre F (k * N)) (S : Fam D'.toPre F k)
    (S' : Fam D'.toPre F (k * N)) (hs : ∀ i, PullAl D F oa a k N (s i) (s' i)) (hS : IsBoxFam pD F k S s)
    (hS' : IsBoxFam pD F (k * N) S' s') : PullAl D' F oa' a k N S S' := by
  have ht := fun i => aF_pr (F := F) pD oa oa' a i (hact a i)
  refine ⟨fun χ' => ?_, fun β' hβ' => ?_⟩
  · choose u hu hc hr using fun i => (hs i).1 (pD.xe χ' i)
    have hφ : ∀ i b, pullφ D' F oa' a χ' b ≫ (pD.pw.pr i).left =
        prB pD F i ≫ pullφ D F oa a (pD.xe χ' i) b := by
      rintro i (b | b)
      · exact ((hS' (star a • χ')).choose i b).trans (by rw [hx]; rfl)
      · show ((aF D' F oa' a).left ≫ DegPre.famφ D'.toPre F χ' b) ≫ _ =
          _ ≫ (aF D F oa a).left ≫ DegPre.famφ D.toPre F (pD.xe χ' i) b
        rw [Category.assoc, (hS χ').choose i b, ← Category.assoc, ht, Category.assoc]
    obtain ⟨v, hv, vv⟩ := exists_box_gen D.toPre.P.isLB D'.toPre.P.isLB pD.w pD.w_gen hφ u hu
    refine ⟨v, hv, corr_of_val D'.toPre.P.isLB fun y J' hJ' => ?_,
      (secRel_iff D'.toPre.P.isLB _ _ _ _ _ _ _ _ _ v).2 fun y J' hJ' => ?_⟩
    · obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
      have e₂ := vv _ (DegPre.zF D'.toPre F).left y J J' hJ hJ'
      let r : (TF (R := V) F).left ⟶ (TK V).left := 𝟙 (TF (R := V) F).left ≫ jFK (R := V) F
      have e₃ : om pD.w y J J' (1 : TF (R := V) F ⟶ D'.toPre.P.A).left * val D'.toPre.rigK r y J' =
          ∏ _i : Fin j, val D.toPre.rigK r y J := by
        have z : (1 : TF (R := V) F ⟶ D'.toPre.P.A).left = r ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A :=
          (show (1 : TF (R := V) F ⟶ D'.toPre.P.A).left =
              jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A by
            show (toUnit _ ≫ η[D'.toPre.P.A]).left = _
            rw [Over.comp_left]
            rfl).trans (congrArg (· ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A)
            (Category.id_comp (jFK (R := V) F)).symm)
        rw [z]
        exact BoxFamily.rig_val pD hJ hJ' r
      have e₅ : ∀ i, val (u i) ((DegPre.zF D'.toPre F).left ≫ prB pD F i) y J =
          val D.toPre.rigK r y J ^ (k * (N - 1)) := fun i => by
        have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (hc i) (𝟙 _)).trans
          ((val_pull hJ _ _ _).trans (BoxFamily.val_powGen _ _ _ _ _ _ _)))
        rw [Category.id_comp] at this
        rw [BoxFamily.zF_pr]
        exact this
      rw [prod_pull_zero D' oa' a k N hN χ', Finset.prod_congr rfl (fun i _ => e₅ i), Finset.prod_pow, ← e₃,
        mul_pow] at e₂
      refine (val_pull hJ' _ _ _).trans (Eq.trans ?_
        ((val_pull hJ' _ _ _).trans (BoxFamily.val_powGen _ _ _ _ _ _ _)).symm)
      rw [Category.id_comp]
      exact mul_left_cancel e₂
    · obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
      have e₁ := fam_val pD hS' (star a • χ') (𝟙 _) y hJ hJ'
      have e₂ := fam_val pD hS χ' (𝟙 _ ≫ (aF D' F oa' a).left) y hJ hJ'
      have e₃ := vv _ (𝟙 _) y J J' hJ hJ'
      have e₄ : ∀ i, sval ((s' i).s (pD.xe (star a • χ') i)) (𝟙 _ ≫ prB pD F i) y J =
          sval ((s i).s (pD.xe χ' i)) ((𝟙 _ ≫ (aF D' F oa' a).left) ≫ prB pD F i) y J *
            (val (u i) (𝟙 _ ≫ prB pD F i) y J).val := fun i => by
        rw [hx, Category.assoc, ht, ← Category.assoc]
        exact (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ (u i)).1 (hr i) _ _ y J hJ
      have e₅ : ∏ b, om pD.w y J J' (𝟙 _ ≫ pullφ D' F oa' a χ' b) ^ pullε k N b =
          (∏ b, om pD.w y J J' (𝟙 _ ≫ DegPre.famφ D'.toPre F (star a • χ') b) ^ DegPre.famε (k * N) b) *
          (∏ b, om pD.w y J J' ((𝟙 _ ≫ (aF D' F oa' a).left) ≫ DegPre.famφ D'.toPre F χ' b) ^
            DegPre.famε k b)⁻¹ := by
        simp only [Category.assoc]
        exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
      rw [Finset.prod_congr rfl (fun i _ => e₄ i), Finset.prod_mul_distrib, ← e₂, ← Units.coe_prod, ← e₃, e₅] at e₁
      exact alg_fin e₁
  · obtain ⟨i, hi⟩ : ∃ i, ∀ χ, pD.xe β' i ≠ star a • χ := by
      by_contra hne
      push Not at hne
      choose χ hχ using hne
      refine hβ' (pD.xe.symm χ) (pD.xe.injective (funext fun i => ?_))
      rw [hx, AddEquiv.apply_symm_apply, hχ]
    have hz := (hs i).2 _ hi
    intro jj
    refine fn_ext fun y hy => ?_
    obtain ⟨J', hJ', e⟩ := sval_trans D'.toPre.P.isLB (S'.s β') y jj hy
    obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
    have e₁ := fam_val pD hS' β' (𝟙 _) y hJ hJ'
    have z₀ : sval ((s' i).s (pD.xe β' i)) (𝟙 _ ≫ prB pD F i) y J = 0 := by
      exact (congrArg (gs _ y _) (hz _)).trans (gs_zero' _ y _)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) z₀, Units.mul_right_eq_zero] at e₁
    rw [e₁, mul_zero] at e
    refine e.trans ?_
    exact (gs_zero' _ y _).symm

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X], (∀ (a : O) (x : D'.toPre.X) (i : Fin j), pD.xe (a • x) i = a • pD.xe x i) → ∀ (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O), (∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) → ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) → ∀ (s : Fin j → Fam D.toPre F k) (s' : Fin j → Fam D.toPre F (k * N)) (S : Fam D'.toPre F k) (S' : Fam D'.toPre F (k * N)), (∀ i, PullAl D F oa a k N (s i) (s' i)) → IsBoxFam pD F k S s → IsBoxFam pD F (k * N) S' s' → PullAl D' F oa' a k N S S' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ pD _ _ _ _ _ _ _ _ hx oa oa' hact a N k hN _ _ s s' S S' hs hS hS' =>
    pullAl_box pD hx oa oa' hact a N k hN s s' S S' hs hS hS'

end GlobalTheory.BoxPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PullAlValueIntegralPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pullAl_value_integral_point :
    Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)), PullAl D F oa a k N s s' → ∀ (χ : D.toPre.X) (m : TWM.TO hϖ hv ⟶ D.toPre.P.A) (r : ℚ), (∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => (m ≫ oa.onB.act a).left ≫ DegPre.famφB D.toPre (χ) i) (DegPre.famε (k))), G₀.IsGen ∧ ∃ x : F, v x = ((r : ℚ) : WithTop ℚ) ∧ ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J → sval (s.s χ) (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m ≫ oa.onB.act a)).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) * (val G₀ (TWM.ιS hϖ hv).left z J).val) → (∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => (m).left ≫ DegPre.famφB D.toPre (star a • χ) i) (DegPre.famε (k * N))), G₀.IsGen ∧ ∃ x : F, v x = ((r : ℚ) : WithTop ℚ) ∧ ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J → sval (s'.s (star a • χ)) (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) * (val G₀ (TWM.ιS hϖ hv).left z J).val) := by
  intro hLaws V _ _ _ ϖ hϖ D Q _ F _ _ _ v hv O _ _ _ oa w0 hw a N k hN _ haa s s' hpull χ m r ⟨G₀, hG₀, x, hx, hval⟩
  have hL := D.toPre.P.isLB
  obtain ⟨u, hu, hcorr, hrel⟩ := hpull.1 χ
  obtain ⟨n, ψ, δ, eB, heB, hform, ve⟩ :=
    pullGen_one hLaws.globalFns D F oa w0 hw a N hN (by rw [mul_comm]; exact haa) k χ u hu hcorr
  have hform' : FormEq (Sum.elim (fun i => (m ≫ oa.onB.act a).left ≫ DegPre.famφB D.toPre χ i)
      (fun i => m.left ≫ ψ i)) (Sum.elim (DegPre.famε k) δ)
      (fun i => m.left ≫ DegPre.famφB D.toPre (star a • χ) i) (DegPre.famε (k * N)) := fun U _ h => by
    refine Eq.trans ?_ (hform U (fun q => h (m.left ≫ q)))
    refine Finset.prod_congr rfl ?_
    rintro (i | i) -
    · simp only [Sum.elim_inl, Over.comp_left, Category.assoc]
    · rfl
  obtain ⟨G₁, hG₁, vG⟩ := exists_gen hL hform'
    (LB.mulGen D.toPre.P.L _ _ _ _ G₀ (LB.pullGen D.toPre.P.L _ _ eB m.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hG₀ (DVR.pullGen_isGen _ _ _ _ heB _))
  refine ⟨G₁, hG₁, x, hx, fun z J hJ => ?_⟩
  have H := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _
    (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left z J hJ
  have e₁ : (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left ≫ (aF D F oa a).left =
      (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m ≫ oa.onB.act a)).left := by
    rw [← Over.comp_left, aF, comp_lift, lift_fst, ← Category.assoc, lift_snd, Category.assoc]
  have e₂ : (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left ≫ (DegPre.prB D.toPre F).left =
      (TWM.ιS hϖ hv).left ≫ m.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  rw [H, e₁, hval z J hJ, ve _ _ z J hJ, e₂, vG _ _ z J hJ, val_mul hJ, val_pull hJ, Units.val_mul, _root_.mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumDeterminantEigenvalueStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_determinant_eigenvalue : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → ∀ (Y : ℂ) (w : R.smSub), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w := by
  first | exact @GlobalTheory.CapelliSmooth.qdet_smooth | exact GlobalTheory.CapelliSmooth.qdet_smooth | (intros; apply GlobalTheory.CapelliSmooth.qdet_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrepStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_raw_of_frep : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ I c y, (RI I).KFin y → R.KFin (io I c y)) ∧ (∀ I c x, R.KFin x → (RI I).KFin (pr I c x)) ∧ (∀ I c, ∀ y ∈ (RI I).TK, io I c y ∈ R.TK) ∧ (∀ I c, ∀ x ∈ R.TK, pr I c x ∈ (RI I).TK) := by
  first | exact @GlobalTheory.tensor_decomposition_kfinite | exact GlobalTheory.tensor_decomposition_kfinite | (intros; apply GlobalTheory.tensor_decomposition_kfinite <;> assumption)
end

